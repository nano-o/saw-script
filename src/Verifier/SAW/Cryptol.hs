{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ViewPatterns #-}

{- |
Module      : Verifier.SAW.Cryptol
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.Cryptol where

import Control.Exception (assert)
import Control.Monad (join, foldM, unless, (<=<))
import qualified Data.IntTrie as IntTrie
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import qualified Data.Vector as Vector
import Prelude ()
import Prelude.Compat

import qualified Cryptol.Eval.Value as V
import qualified Cryptol.Eval.Env as Env
import Cryptol.Eval.Type (evalValType)
import qualified Cryptol.TypeCheck.AST as C
import qualified Cryptol.ModuleSystem.Name as C (asPrim, nameIdent)
import qualified Cryptol.Utils.Ident as C (Ident, packIdent, unpackIdent)
import Cryptol.TypeCheck.TypeOf (fastTypeOf, fastSchemaOf)

import Verifier.SAW.Conversion
import Verifier.SAW.FiniteValue
import qualified Verifier.SAW.Simulator.Concrete as SC
import Verifier.SAW.Prim (BitVector(..))
import Verifier.SAW.Rewriter
import Verifier.SAW.SharedTerm
import Verifier.SAW.Simulator.MonadLazy (force)
import Verifier.SAW.TypedAST (mkSort, mkModuleName, findDef)
import qualified Verifier.SAW.Recognizer as R

unimplemented :: Monad m => String -> m a
unimplemented name = fail ("unimplemented: " ++ name)

--------------------------------------------------------------------------------
-- Type Environments

-- | SharedTerms are paired with a deferred shift amount for loose variables
data Env s = Env
  { envT :: Map Int    (SharedTerm s, Int) -- ^ Type variables are referenced by unique id
  , envE :: Map C.Name (SharedTerm s, Int) -- ^ Term variables are referenced by name
  , envP :: Map C.Prop (SharedTerm s, Int) -- ^ Bound propositions are referenced implicitly by their types
  , envC :: Map C.Name C.Schema            -- ^ Cryptol type environment
  }

emptyEnv :: Env s
emptyEnv = Env Map.empty Map.empty Map.empty Map.empty

liftTerm :: (SharedTerm s, Int) -> (SharedTerm s, Int)
liftTerm (t, j) = (t, j + 1)

-- | Increment dangling bound variables of all types in environment.
liftEnv :: Env s -> Env s
liftEnv env =
  Env { envT = fmap liftTerm (envT env)
      , envE = fmap liftTerm (envE env)
      , envP = fmap liftTerm (envP env)
      , envC = envC env
      }

bindTParam :: SharedContext s -> C.TParam -> Env s -> IO (Env s)
bindTParam sc tp env = do
  let env' = liftEnv env
  v <- scLocalVar sc 0
  return $ env' { envT = Map.insert (C.tpUnique tp) (v, 0) (envT env') }

bindName :: SharedContext s -> C.Name -> C.Schema -> Env s -> IO (Env s)
bindName sc name schema env = do
  let env' = liftEnv env
  v <- scLocalVar sc 0
  return $ env' { envE = Map.insert name (v, 0) (envE env'), envC = Map.insert name schema (envC env') }

bindProp :: SharedContext s -> C.Prop -> Env s -> IO (Env s)
bindProp sc prop env = do
  let env' = liftEnv env
  v <- scLocalVar sc 0
  return $ env' { envP = Map.insert prop (v, 0) (envP env') }

--------------------------------------------------------------------------------

importKind :: SharedContext s -> C.Kind -> IO (SharedTerm s)
importKind sc kind =
  case kind of
    C.KType       -> scDataTypeApp sc "Cryptol.KType" []
    C.KNum        -> scDataTypeApp sc "Cryptol.Num" []
    C.KProp       -> scSort sc (mkSort 0)
    (C.:->) k1 k2 -> join $ scFun sc <$> importKind sc k1 <*> importKind sc k2

importTFun :: SharedContext s -> C.TFun -> IO (SharedTerm s)
importTFun sc tf =
  case tf of
    C.TCWidth         -> scGlobalDef sc "Cryptol.tcWidth"
    C.TCAdd           -> scGlobalDef sc "Cryptol.tcAdd"
    C.TCSub           -> scGlobalDef sc "Cryptol.tcSub"
    C.TCMul           -> scGlobalDef sc "Cryptol.tcMul"
    C.TCDiv           -> scGlobalDef sc "Cryptol.tcDiv"
    C.TCMod           -> scGlobalDef sc "Cryptol.tcMod"
    C.TCExp           -> scGlobalDef sc "Cryptol.tcExp"
    C.TCMin           -> scGlobalDef sc "Cryptol.tcMin"
    C.TCMax           -> scGlobalDef sc "Cryptol.tcMax"
    C.TCLenFromThen   -> scGlobalDef sc "Cryptol.tcLenFromThen"
    C.TCLenFromThenTo -> scGlobalDef sc "Cryptol.tcLenFromThenTo"

importType :: SharedContext s -> Env s -> C.Type -> IO (SharedTerm s)
importType sc env ty =
  case ty of
    C.TVar tvar ->
      case tvar of
        C.TVFree{} {- Int Kind (Set TVar) Doc -} -> unimplemented "TVFree"
        C.TVBound i _k   -> case Map.lookup i (envT env) of
                              Just (t, j) -> incVars sc 0 j t
                              Nothing -> fail "internal error: importType TVBound"
    C.TUser _ _ t  -> go t
    C.TRec fs      -> importTRec sc env (Map.assocs (Map.fromList fs))
    C.TCon tcon tyargs ->
      case tcon of
        C.TC tc ->
          case tc of
            C.TCNum n    -> scCtorApp sc "Cryptol.TCNum" =<< sequence [scNat sc (fromInteger n)]
            C.TCInf      -> scCtorApp sc "Cryptol.TCInf" []
            C.TCBit      -> scCtorApp sc "Cryptol.TCBit" []
            C.TCSeq      -> scCtorApp sc "Cryptol.TCSeq" =<< traverse go tyargs
            C.TCFun      -> scCtorApp sc "Cryptol.TCFun" =<< traverse go tyargs
            C.TCTuple _n -> importTCTuple sc env tyargs
            C.TCNewtype (C.UserTC _qn _k) -> unimplemented "TCNewtype" -- user-defined, @T@
        C.PC pc ->
          case pc of
            C.PEqual         -> scDataTypeApp sc "Cryptol.PEqual" =<< traverse go tyargs -- @_ == _@
            C.PNeq           -> scDataTypeApp sc "Cryptol.PNeq"   =<< traverse go tyargs -- @_ /= _@
            C.PGeq           -> scDataTypeApp sc "Cryptol.PGeq"   =<< traverse go tyargs -- @_ >= _@
            C.PFin           -> scDataTypeApp sc "Cryptol.PFin"   =<< traverse go tyargs -- @fin _@
            C.PHas _selector -> unimplemented "PHas"
            C.PArith         -> scDataTypeApp sc "Cryptol.PArith" =<< traverse go tyargs -- @Arith _@
            C.PCmp           -> scDataTypeApp sc "Cryptol.PCmp"   =<< traverse go tyargs -- @Cmp _@
        C.TF tf ->
          do tf' <- importTFun sc tf
             tyargs' <- traverse go tyargs
             scApplyAll sc tf' tyargs'
  where
    go = importType sc env

-- | Precondition: list argument should be sorted by field name
importTRec :: SharedContext s -> Env s -> [(C.Ident, C.Type)] -> IO (SharedTerm s)
importTRec sc _env [] = scCtorApp sc "Cryptol.TCEmpty" []
importTRec sc env ((n, t) : fs) = do
  n' <- scString sc (C.unpackIdent n)
  t' <- importType sc env t
  fs' <- importTRec sc env fs
  scCtorApp sc "Cryptol.TCField" [n', t', fs']

importTCTuple :: SharedContext s -> Env s -> [C.Type] -> IO (SharedTerm s)
importTCTuple sc _env [] = scCtorApp sc "Cryptol.TCUnit" []
importTCTuple sc env (t : ts) = do
  t' <- importType sc env t
  ts' <- importTCTuple sc env ts
  scCtorApp sc "Cryptol.TCPair" [t', ts']

nameToString :: C.Name -> String
nameToString = C.unpackIdent . C.nameIdent

tparamToString :: C.TParam -> String
--tparamToString tp = maybe "_" nameToString (C.tpName tp)
tparamToString tp = maybe ("u" ++ show (C.tpUnique tp)) nameToString (C.tpName tp)

importType' :: SharedContext s -> Env s -> C.Type -> IO (SharedTerm s)
importType' sc env t = do
  t' <- importType sc env t
  scGlobalApply sc "Cryptol.ty" [t']

importPropsType :: SharedContext s -> Env s -> [C.Prop] -> C.Type -> IO (SharedTerm s)
importPropsType sc env [] ty = importType' sc env ty
importPropsType sc env (prop : props) ty = do
  p <- importType sc env prop
  t <- importPropsType sc env props ty
  scFun sc p t

importPolyType :: SharedContext s -> Env s -> [C.TParam] -> [C.Prop] -> C.Type -> IO (SharedTerm s)
importPolyType sc env [] props ty = importPropsType sc env props ty
importPolyType sc env (tp : tps) props ty = do
  k <- importKind sc (C.tpKind tp)
  env' <- bindTParam sc tp env
  t <- importPolyType sc env' tps props ty
  scPi sc (tparamToString tp) k t

importSchema :: SharedContext s -> Env s -> C.Schema -> IO (SharedTerm s)
importSchema sc env (C.Forall tparams props ty) = importPolyType sc env tparams props ty

proveProp :: SharedContext s -> Env s -> C.Prop -> IO (SharedTerm s)
proveProp sc env prop =
  case Map.lookup prop (envP env) of
    Just (prf, j) -> incVars sc 0 j prf
    Nothing ->
      case prop of
        (C.pIsFin -> Just n)
          -> scGlobalApply sc "Cryptol.ePFin" =<< sequence [ty n]
        (C.pIsArith -> Just t)
          -> scGlobalApply sc "Cryptol.ePArith" =<< sequence [ty t]
        (C.pIsCmp -> Just t)
          -> scGlobalApply sc "Cryptol.ePCmp" =<< sequence [ty t]
        (C.pIsEq -> Just (m, n))
          -> scGlobalApply sc "Cryptol.ePEqual" =<< sequence [ty m, ty n]
        (C.pIsGeq -> Just (m, n))
          -> scGlobalApply sc "Cryptol.ePGeq" =<< sequence [ty m, ty n]
        (pIsNeq -> Just (m, n))
          -> scGlobalApply sc "Cryptol.ePNeq" =<< sequence [ty m, ty n]
        _ -> fail "proveProp: unknown proposition"
  where
    ty = importType sc env

importPrimitive :: SharedContext s -> C.Name -> IO (SharedTerm s)
importPrimitive sc (C.asPrim -> Just nm) =
  case nm of
    "True"          -> scBool sc True
    "False"         -> scBool sc False
    "demote"        -> scGlobalDef sc "Cryptol.ecDemote"      -- Converts a numeric type into its corresponding value.
                                                     -- { val, bits } (fin val, fin bits, bits >= width val) => [bits]
    "+"             -> scGlobalDef sc "Cryptol.ecPlus"        -- {a} (Arith a) => a -> a -> a
    "-"             -> scGlobalDef sc "Cryptol.ecMinus"       -- {a} (Arith a) => a -> a -> a
    "*"             -> scGlobalDef sc "Cryptol.ecMul"         -- {a} (Arith a) => a -> a -> a
    "/"             -> scGlobalDef sc "Cryptol.ecDiv"         -- {a} (Arith a) => a -> a -> a
    "%"             -> scGlobalDef sc "Cryptol.ecMod"         -- {a} (Arith a) => a -> a -> a
    "^^"            -> scGlobalDef sc "Cryptol.ecExp"         -- {a} (Arith a) => a -> a -> a
    "lg2"           -> scGlobalDef sc "Cryptol.ecLg2"         -- {a} (Arith a) => a -> a
    "negate"        -> scGlobalDef sc "Cryptol.ecNeg"         -- {a} (Arith a) => a -> a
    "<"             -> scGlobalDef sc "Cryptol.ecLt"          -- {a} (Cmp a) => a -> a -> Bit
    ">"             -> scGlobalDef sc "Cryptol.ecGt"          -- {a} (Cmp a) => a -> a -> Bit
    "<="            -> scGlobalDef sc "Cryptol.ecLtEq"        -- {a} (Cmp a) => a -> a -> Bit
    ">="            -> scGlobalDef sc "Cryptol.ecGtEq"        -- {a} (Cmp a) => a -> a -> Bit
    "=="            -> scGlobalDef sc "Cryptol.ecEq"          -- {a} (Cmp a) => a -> a -> Bit
    "!="            -> scGlobalDef sc "Cryptol.ecNotEq"       -- {a} (Cmp a) => a -> a -> Bit
    "&&"            -> scGlobalDef sc "Cryptol.ecAnd"         -- {a} a -> a -> a        -- Bits a
    "||"            -> scGlobalDef sc "Cryptol.ecOr"          -- {a} a -> a -> a        -- Bits a
    "^"             -> scGlobalDef sc "Cryptol.ecXor"         -- {a} a -> a -> a        -- Bits a
    "complement"    -> scGlobalDef sc "Cryptol.ecCompl"       -- {a} a -> a             -- Bits a
    "zero"          -> scGlobalDef sc "Cryptol.ecZero"        -- {a} a                  -- Bits a
    "<<"            -> scGlobalDef sc "Cryptol.ecShiftL"      -- {m,n,a} (fin m) => [m] a -> [n] -> [m] a
    ">>"            -> scGlobalDef sc "Cryptol.ecShiftR"      -- {m,n,a} (fin m) => [m] a -> [n] -> [m] a
    "<<<"           -> scGlobalDef sc "Cryptol.ecRotL"        -- {m,n,a} (fin m) => [m] a -> [n] -> [m] a
    ">>>"           -> scGlobalDef sc "Cryptol.ecRotR"        -- {m,n,a} (fin m) => [m] a -> [n] -> [m] a
    "#"             -> scGlobalDef sc "Cryptol.ecCat"         -- {a,b,d} (fin a) => [a] d -> [b] d -> [a + b] d
    "splitAt"       -> scGlobalDef sc "Cryptol.ecSplitAt"     -- {a,b,c} (fin a) => [a+b] c -> ([a]c,[b]c)
    "join"          -> scGlobalDef sc "Cryptol.ecJoin"        -- {a,b,c} (fin b) => [a][b]c -> [a * b]c
    "split"         -> scGlobalDef sc "Cryptol.ecSplit"       -- {a,b,c} (fin b) => [a * b] c -> [a][b] c
    "reverse"       -> scGlobalDef sc "Cryptol.ecReverse"     -- {a,b} (fin a) => [a] b -> [a] b
    "transpose"     -> scGlobalDef sc "Cryptol.ecTranspose"   -- {a,b,c} [a][b]c -> [b][a]c
    "@"             -> scGlobalDef sc "Cryptol.ecAt"          -- {n,a,i} (fin i) => [n]a -> [i] -> a
    "@@"            -> scGlobalDef sc "Cryptol.ecAtRange"     -- {n,a,m,i} (fin i) => [n]a -> [m][i] -> [m]a
    "!"             -> scGlobalDef sc "Cryptol.ecAtBack"      -- {n,a,i} (fin n, fin i) => [n]a -> [i] -> a
    "!!"            -> scGlobalDef sc "Cryptol.ecAtRangeBack" -- {n,a,m,i} (fin n, fin i) => [n]a -> [m][i] -> [m]a
    "fromThen"      -> scGlobalDef sc "Cryptol.ecFromThen"
                               -- fromThen : {first,next,bits,len}
                               --             ( fin first, fin next, fin bits
                               --             , bits >= width first, bits >= width next
                               --             , lengthFromThen first next bits == len
                               --             )
                               --          => [len] [bits]
    "fromTo"        -> scGlobalDef sc "Cryptol.ecFromTo"
                               -- fromTo : {first, last, bits}
                               --           ( fin last, fin bits, last >== first, bits >== width last)
                               --        => [1 + (last - first)] [bits]
    "fromThenTo"    -> scGlobalDef sc "Cryptol.ecFromThenTo"
    "infFrom"       -> scGlobalDef sc "Cryptol.ecInfFrom"     -- {a} (fin a) => [a] -> [inf][a]
    "infFromThen"   -> scGlobalDef sc "Cryptol.ecInfFromThen" -- {a} (fin a) => [a] -> [a] -> [inf][a]
    "error"         -> scGlobalDef sc "Cryptol.ecError"       -- {at,len} (fin len) => [len][8] -> at -- Run-time error
    "pmult"         -> scGlobalDef sc "Cryptol.ecPMul"        -- {a,b} (fin a, fin b) => [a] -> [b] -> [max 1 (a + b) - 1]
    "pdiv"          -> scGlobalDef sc "Cryptol.ecPDiv"        -- {a,b} (fin a, fin b) => [a] -> [b] -> [a]
    "pmod"          -> scGlobalDef sc "Cryptol.ecPMod"        -- {a,b} (fin a, fin b) => [a] -> [b+1] -> [b]
    "random"        -> scGlobalDef sc "Cryptol.ecRandom"      -- {a} => [32] -> a -- Random values
    _ -> fail $ unwords ["Unknown Cryptol primitive name:", C.unpackIdent nm]

importPrimitive _ nm =
  fail $ unwords ["Improper Cryptol primitive name:", show nm]


importExpr :: SharedContext s -> Env s -> C.Expr -> IO (SharedTerm s)
importExpr sc env expr =
  case expr of
    C.EList es t                -> do t' <- importType' sc env t
                                      es' <- traverse go es
                                      scVector sc t' es'
    C.ETuple es                 -> scTuple sc =<< traverse go es
    C.ERec fs                   -> scRecord sc =<< traverse go (Map.fromList fs')
                                     where fs' = [ (C.unpackIdent n, e) | (n, e) <- fs ]
    C.ESel e sel                ->           -- Elimination for tuple/record/list
      case sel of
        C.TupleSel i _maybeLen  -> flip (scTupleSelector sc) (i+1) =<< go e
        C.RecordSel x _         -> flip (scRecordSelect sc) (C.unpackIdent x) =<< go e
        C.ListSel i _maybeLen   -> do let t = fastTypeOf (envC env) e
                                      (n, a) <- case C.tIsSeq t of
                                                  Just (n, a) -> return (n, a)
                                                  Nothing -> fail "ListSel: not a list type"
                                      a' <- importType' sc env a
                                      n' <- importType sc env n
                                      e' <- importExpr sc env e
                                      i' <- scNat sc (fromIntegral i)
                                      scGlobalApply sc "Cryptol.eListSel" [a', n', e', i']
    C.EIf e1 e2 e3              -> do t' <- importType' sc env (fastTypeOf (envC env) e2)
                                      e1' <- importExpr sc env e1
                                      e2' <- importExpr sc env e2
                                      e3' <- importExpr sc env e3
                                      scGlobalApply sc "Prelude.ite" [t', e1', e2', e3']
    C.EComp t e mss             -> importComp sc env t e mss
    C.EVar qname                    ->
      case Map.lookup qname (envE env) of
        Just (e', j)                -> incVars sc 0 j e'
        Nothing                     -> fail "internal error: unknown variable"
    C.ETAbs tp e                    -> do k <- importKind sc (C.tpKind tp)
                                          env' <- bindTParam sc tp env
                                          e' <- importExpr sc env' e
                                          scLambda sc (tparamToString tp) k e'
    C.ETApp e t                     -> join $ scApply sc <$> go e <*> ty t
    C.EApp e1 e2                    -> join $ scApply sc <$> go e1 <*> go e2
    C.EAbs x t e                    -> do t' <- importType' sc env t
                                          env' <- bindName sc x (C.Forall [] [] t) env
                                          e' <- importExpr sc env' e
                                          scLambda sc (nameToString x) t' e'
    C.EProofAbs prop e1             -> do p <- importType sc env prop
                                          env' <- bindProp sc prop env
                                          e <- importExpr sc env' e1
                                          scLambda sc "_P" p e
    C.EProofApp e1                  -> case fastSchemaOf (envC env) e1 of
                                         C.Forall [] (p1 : _) _ ->
                                           do e <- importExpr sc env e1
                                              prf <- proveProp sc env p1
                                              scApply sc e prf
                                         s -> fail $ "EProofApp: invalid type: " ++ show (e1, s)
    C.ECast e1 t2                   -> do let t1 = fastTypeOf (envC env) e1
                                          t1' <- importType' sc env t1
                                          t2' <- importType' sc env t2
                                          e1' <- go e1
                                          aeq <- pure alphaEquiv <*> scWhnf sc t1' <*> scWhnf sc t2'
                                          if aeq
                                             then return e1'
                                             else scGlobalApply sc "Prelude.unsafeCoerce" [t1', t2', e1']
    C.EWhere e dgs                  -> do env' <- importDeclGroups sc env dgs
                                          importExpr sc env' e
  where
    go = importExpr sc env
    ty = importType sc env

-- | Currently this imports declaration groups by inlining all the
-- definitions. (With subterm sharing, this is not as bad as it might
-- seem.) We might want to think about generating let or where
-- expressions instead.
importDeclGroup :: Bool -> SharedContext s -> Env s -> C.DeclGroup -> IO (Env s)

importDeclGroup isTopLevel sc env (C.Recursive [decl]) =
  case C.dDefinition decl of
    C.DPrim ->
     fail $ unwords ["Primitive declarations cannot be recursive:", show (C.dName decl)]
    C.DExpr expr -> do
     env1 <- bindName sc (C.dName decl) (C.dSignature decl) env
     t' <- importSchema sc env (C.dSignature decl)
     e' <- importExpr sc env1 expr
     let x = nameToString (C.dName decl)
     f' <- scLambda sc x t' e'
     rhs <- scGlobalApply sc "Cryptol.fix" [t', f']
     rhs' <- if not isTopLevel then return rhs else scTermF sc (Constant x rhs t')
     let env' = env { envE = Map.insert (C.dName decl) (rhs', 0) (envE env)
                    , envC = Map.insert (C.dName decl) (C.dSignature decl) (envC env) }
     return env'


-- - A group of mutually-recursive declarations -
-- We handle this by "tupling up" all the declarations using a record and
-- taking the fixpoint at this record type.  The desired declarations are then
-- achieved by projecting the field names from this record.
importDeclGroup isTopLevel sc env (C.Recursive decls) =
  do -- build the environment for the declaration bodies
     -- NB: the order of the declarations is reversed to get the deBrujin indices to line up properly
     env1 <- foldM (\e d -> bindName sc (C.dName d) (C.dSignature d) e) env (reverse decls)

     -- shift the environment by one more variable to make room for our recursive record
     let env2 = liftEnv env1
     -- grab a reference to the outermost variable; this will be the record in the body
     -- of the labmda we build later
     recv <- scLocalVar sc 0

     -- the types of the declarations
     ts <- mapM (importSchema sc env . C.dSignature) decls
     -- the type of the recursive record
     rect <- scRecordType sc $ Map.fromList $ zip (map (nameToString . C.dName) decls) ts

     let extractDeclExpr decl =
           case C.dDefinition decl of
             C.DExpr expr -> return expr
             C.DPrim ->
                fail $ unwords ["Primitive declarations cannot be recursive:", show (C.dName decl)]

     -- the raw imported bodies of the declarations
     es <- mapM (importExpr sc env2 <=< extractDeclExpr) decls

     -- build a list of projections from a record variable
     projs <- mapM (\d -> scRecordSelect sc recv (nameToString (C.dName d))) decls

     -- substitute into the imported declaration bodies, replacing bindings by record projections
     -- NB: start at index 1; index 0 is the variable for the record itself
     es' <- mapM (instantiateVarList sc 1 projs) es

     -- the body of the recursive record
     rec <- scRecord sc $ Map.fromList $ zip (map (nameToString . C.dName) decls) es'

     -- build a lambda from the record body...
     f <- scLambda sc "fixRecord" rect rec

     -- and take its fixpoint
     rhs <- scGlobalApply sc "Cryptol.fix" [rect, f]

     -- finally, build projections from the fixed record to shove into the environment
     rhss <- mapM (\d -> scRecordSelect sc rhs (nameToString (C.dName d))) decls

     -- if toplevel, then wrap each binding with a Constant constructor
     let wrap d r t = scTermF sc (Constant (nameToString (C.dName d)) r t)
     rhss' <- if isTopLevel then sequence (zipWith3 wrap decls rhss ts) else return rhss

     let env' = env { envE = foldr (\(r,d) e -> Map.insert (C.dName d) (r, 0) e) (envE env) $ zip rhss' decls
                    , envC = foldr (\d e -> Map.insert (C.dName d) (C.dSignature d) e) (envC env) decls
                    }

     return env'

importDeclGroup isTopLevel sc env (C.NonRecursive decl) =
  case C.dDefinition decl of
    C.DPrim
     | isTopLevel -> do
        rhs <- importPrimitive sc (C.dName decl)
        let env' = env { envE = Map.insert (C.dName decl) (rhs, 0) (envE env)
                      , envC = Map.insert (C.dName decl) (C.dSignature decl) (envC env) }
        return env'
     | otherwise -> do
        fail $ unwords ["Primitive declarations only allowed at top-level:", show (C.dName decl)]

    C.DExpr expr -> do
     rhs <- importExpr sc env expr
     rhs' <- if not isTopLevel then return rhs else do
       t <- importSchema sc env (C.dSignature decl)
       scTermF sc (Constant (nameToString (C.dName decl)) rhs t)
     let env' = env { envE = Map.insert (C.dName decl) (rhs', 0) (envE env)
                    , envC = Map.insert (C.dName decl) (C.dSignature decl) (envC env) }
     return env'

importDeclGroups :: SharedContext s -> Env s -> [C.DeclGroup] -> IO (Env s)
importDeclGroups sc = foldM (importDeclGroup False sc)

importTopLevelDeclGroups :: SharedContext s -> Env s -> [C.DeclGroup] -> IO (Env s)
importTopLevelDeclGroups sc = foldM (importDeclGroup True sc)

--------------------------------------------------------------------------------
-- List comprehensions

importComp :: SharedContext s -> Env s -> C.Type -> C.Expr -> [[C.Match]] -> IO (SharedTerm s)
importComp sc env listT expr mss =
  do let zipAll [] = fail "zero-branch list comprehension"
         zipAll [branch] =
           do (xs, len, ty, args) <- importMatches sc env branch
              m <- importType sc env len
              a <- importType' sc env ty
              return (xs, m, a, [args])
         zipAll (branch : branches) =
           do (xs, len, ty, args) <- importMatches sc env branch
              m <- importType sc env len
              a <- importType' sc env ty
              (ys, n, b, argss) <- zipAll branches
              zs <- scGlobalApply sc "Cryptol.seqZip" [a, b, m, n, xs, ys]
              mn <- scGlobalApply sc "Cryptol.tcMin" [m, n]
              ab <- scTupleType sc [a, b]
              return (zs, mn, ab, args : argss)
     (xs, n, a, argss) <- zipAll mss
     let (_, elemT) = fromMaybe (assert False undefined) (C.tIsSeq listT)
     f <- lambdaTuples sc env elemT expr argss
     b <- importType' sc env elemT
     ys <- scGlobalApply sc "Cryptol.seqMap" [a, b, n, f, xs]
     -- The resulting type might not match the annotation, so we coerce
     t1 <- scGlobalApply sc "Cryptol.seq" [n, b]
     t2 <- importType' sc env listT
     scGlobalApply sc "Prelude.unsafeCoerce" [t1, t2, ys]

lambdaTuples :: SharedContext s -> Env s -> C.Type -> C.Expr -> [[(C.Name, C.Type)]] -> IO (SharedTerm s)
lambdaTuples sc env _ty expr [] = importExpr sc env expr
lambdaTuples sc env ty expr (args : argss) =
  do f <- lambdaTuple sc env ty expr argss args
     if null args || null argss
       then return f
       else do a <- importType' sc env (tNestedTuple (map snd args))
               b <- importType' sc env (tNestedTuple (map (tNestedTuple . map snd) argss))
               c <- importType' sc env ty
               scGlobalApply sc "Prelude.uncurry" [a, b, c, f]

lambdaTuple :: SharedContext s -> Env s -> C.Type -> C.Expr -> [[(C.Name, C.Type)]] -> [(C.Name, C.Type)] -> IO (SharedTerm s)
lambdaTuple sc env ty expr argss [] = lambdaTuples sc env ty expr argss
lambdaTuple sc env ty expr argss ((x, t) : args) =
  do a <- importType' sc env t
     env' <- bindName sc x (C.Forall [] [] t) env
     e <- lambdaTuple sc env' ty expr argss args
     f <- scLambda sc (nameToString x) a e
     if null args
        then return f
        else do b <- importType' sc env (tNestedTuple (map snd args))
                let tuple = tNestedTuple (map (tNestedTuple . map snd) argss)
                c <- importType' sc env (if null argss then ty else C.tFun tuple ty)
                scGlobalApply sc "Prelude.uncurry" [a, b, c, f]

tNestedTuple :: [C.Type] -> C.Type
tNestedTuple [] = C.tTuple []
tNestedTuple [t] = t
tNestedTuple (t : ts) = C.tTuple [t, tNestedTuple ts]


-- | Returns the shared term, length type, element tuple type, bound
-- variables.
importMatches :: SharedContext s -> Env s -> [C.Match]
              -> IO (SharedTerm s, C.Type, C.Type, [(C.Name, C.Type)])
importMatches _sc _env [] = fail "importMatches: empty comprehension branch"

importMatches sc env [C.From name _ty expr] = do
  (len, ty) <- case C.tIsSeq (fastTypeOf (envC env) expr) of
                 Just x -> return x
                 Nothing -> fail $ "internal error: From: " ++ show (fastTypeOf (envC env) expr)
  xs <- importExpr sc env expr
  return (xs, len, ty, [(name, ty)])

importMatches sc env (C.From name _ty1 expr : matches) = do
  (len1, ty1) <- case C.tIsSeq (fastTypeOf (envC env) expr) of
                   Just x -> return x
                   Nothing -> fail $ "internal error: From: " ++ show (fastTypeOf (envC env) expr)
  m <- importType sc env len1
  a <- importType' sc env ty1
  xs <- importExpr sc env expr
  env' <- bindName sc name (C.Forall [] [] ty1) env
  (body, len2, ty2, args) <- importMatches sc env' matches
  n <- importType sc env len2
  b <- importType' sc env ty2
  f <- scLambda sc (nameToString name) a body
  result <- scGlobalApply sc "Cryptol.from" [a, b, m, n, xs, f]
  return (result, (C..*.) len1 len2, C.tTuple [ty1, ty2], (name, ty1) : args)

importMatches sc env [C.Let decl]
  | C.DPrim <- C.dDefinition decl = do
     fail $ unwords ["Primitive declarations not allowed in 'let':", show (C.dName decl)]
  | C.DExpr expr <- C.dDefinition decl = do
     e <- importExpr sc env expr
     ty1 <- case C.dSignature decl of
              C.Forall [] [] ty1 -> return ty1
              _ -> unimplemented "polymorphic Let"
     a <- importType' sc env ty1
     result <- scGlobalApply sc "Prelude.single" [a, e]
     return (result, C.tOne, ty1, [(C.dName decl, ty1)])

importMatches sc env (C.Let decl : matches) =
  case C.dDefinition decl of
    C.DPrim -> do
     fail $ unwords ["Primitive declarations not allowed in 'let':", show (C.dName decl)]
    C.DExpr expr -> do
     e <- importExpr sc env expr
     ty1 <- case C.dSignature decl of
              C.Forall [] [] ty1 -> return ty1
              _ -> unimplemented "polymorphic Let"
     a <- importType' sc env ty1
     env' <- bindName sc (C.dName decl) (C.dSignature decl) env
     (body, len, ty2, args) <- importMatches sc env' matches
     n <- importType sc env len
     b <- importType' sc env ty2
     f <- scLambda sc (nameToString (C.dName decl)) a body
     result <- scGlobalApply sc "Cryptol.mlet" [a, b, n, e, f]
     return (result, len, C.tTuple [ty1, ty2], (C.dName decl, ty1) : args)

pIsNeq :: C.Type -> Maybe (C.Type, C.Type)
pIsNeq ty = case C.tNoUser ty of
              C.TCon (C.PC C.PNeq) [t1, t2] -> Just (t1, t2)
              _                             -> Nothing

--------------------------------------------------------------------------------
-- Utilities

scCryptolType :: SharedContext s -> SharedTerm s -> IO C.Type
scCryptolType sc t = do
  t' <- scWhnf sc t
  case t' of
    (R.asNatLit -> Just n)
      -> return $ C.tNum n
    (R.asPi -> Just (_, t1, t2))
      -> C.tFun <$> scCryptolType sc t1 <*> scCryptolType sc t2
    (R.asBoolType -> Just ())
      -> return C.tBit
    (R.asVectorType -> Just (t1, t2))
      -> C.tSeq <$> scCryptolType sc t1 <*> scCryptolType sc t2
    (R.asTupleType -> Just ts)
      -> C.tTuple <$> traverse (scCryptolType sc) ts
    (R.asRecordType -> Just tm)
       -> do tm' <- traverse (scCryptolType sc) tm
             return $ C.tRec [ (C.packIdent n, ct) | (n, ct) <- Map.assocs tm' ]
    _ -> fail $ "scCryptolType: unsupported type " ++ show t'

scCryptolEq :: SharedContext s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scCryptolEq sc x y = do
  rules <- concat <$> traverse defRewrites (defs1 ++ defs2)
  let ss = addConvs natConversions (addRules rules emptySimpset)
  tx <- scTypeOf sc x >>= rewriteSharedTerm sc ss >>= scCryptolType sc
  ty <- scTypeOf sc y >>= rewriteSharedTerm sc ss >>= scCryptolType sc
  unless (tx == ty) $ fail $ "scCryptolEq: type mismatch: " ++ show (tx, ty)

  -- Actually apply the equality function, along with the bogus "proof" ePCmp
  t <- scTypeOf sc x
  c <- scCryptolType sc t
  k <- importType sc emptyEnv c
  cmpPrf <- scGlobalApply sc "Cryptol.ePCmp" [k]
  scGlobalApply sc "Cryptol.ecEq" [k, cmpPrf, x, y]

  where
    defs1 = map (mkIdent (mkModuleName ["Prelude"])) ["bitvector"]
    defs2 = map (mkIdent (mkModuleName ["Cryptol"])) ["seq", "ty"]
    defRewrites ident =
      case findDef (scModule sc) ident of
        Nothing -> return []
        Just def -> scDefRewriteRules sc def

-- | Convert from SAWCore's Value type to Cryptol's, guided by the
-- Cryptol type schema.
exportValueWithSchema :: C.Schema -> SC.CValue -> V.Value
exportValueWithSchema (C.Forall [] [] ty) v = exportValue (evalValType Env.emptyEnv ty) v
exportValueWithSchema _ _ = V.VPoly (error "exportValueWithSchema")
-- TODO: proper support for polymorphic values

exportValue :: V.TValue -> SC.CValue -> V.Value
exportValue ty v = case ty of

  V.TVBit ->
    V.VBit (SC.toBool v)

  V.TVSeq _ e ->
    case v of
      SC.VWord w -> V.VWord (V.mkBv (toInteger (width w)) (unsigned w))
      SC.VVector xs -> V.VSeq (V.isTBit e) (map (exportValue e . SC.runIdentity . force) (Vector.toList xs))
      _ -> error $ "exportValue (on seq type " ++ show ty ++ ")"

  -- infinite streams
  V.TVStream e ->
    case v of
      SC.VExtra (SC.CStream trie) -> V.VStream [ exportValue e (IntTrie.apply trie n) | n <- [(0::Integer) ..] ]
      _ -> error $ "exportValue (on seq type " ++ show ty ++ ")"

  -- tuples
  V.TVTuple etys -> V.VTuple (exportTupleValue etys v)

  -- records
  V.TVRec fields ->
      V.VRecord (exportRecordValue (Map.assocs (Map.fromList fields)) v)

  -- functions
  V.TVFun _aty _bty ->
    V.VFun (error "exportValue: TODO functions")


exportTupleValue :: [V.TValue] -> SC.CValue -> [V.Value]
exportTupleValue tys v =
  case (tys, v) of
    ([]    , SC.VUnit    ) -> []
    (t : ts, SC.VPair x y) -> exportValue t (run x) : exportTupleValue ts (run y)
    _                      -> error $ "exportValue: expected tuple"
  where
    run = SC.runIdentity . force

exportRecordValue :: [(C.Ident, V.TValue)] -> SC.CValue -> [(C.Ident, V.Value)]
exportRecordValue fields v =
  case (fields, v) of
    ([]         , SC.VEmpty      ) -> []
    ((n, t) : ts, SC.VField _ x y) -> (n, exportValue t (run x)) : exportRecordValue ts y
    _                              -> error $ "exportValue: expected record"
  where
    run = SC.runIdentity . force

exportFiniteValue :: FiniteValue -> V.Value
exportFiniteValue fv =
  case fv of
    FVBit b    -> V.VBit b
    FVWord w x -> V.VWord (V.mkBv (toInteger w) x)
    FVVec t vs -> V.VSeq (t == FTBit) (map exportFiniteValue vs)
    FVTuple vs -> V.VTuple (map exportFiniteValue vs)
    FVRec vm   -> V.VRecord [ (C.packIdent n, exportFiniteValue v) | (n, v) <- Map.assocs vm ]
