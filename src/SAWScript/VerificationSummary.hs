{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
--{-# LANGUAGE ExistentialQuantification #-}
--{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}

{- |
Module      : SAWScript.VerificationSummary
Description : Summaries of verification for human consumption.
License     : BSD3
Maintainer  : atomb
-}

module SAWScript.VerificationSummary
  ( computeVerificationSummary
  , jsonVerificationSummary
  , prettyVerificationSummary
  ) where

import Control.Lens ((^.))
import qualified Data.Set as Set
import Data.String
import Prettyprinter
import qualified Text.PrettyPrint.ANSI.Leijen as Leijen (pretty)
import Data.Aeson (encode, (.=), Value(..), object)
import qualified Data.ByteString.Lazy.Char8 as B
--import Data.ByteString.Lazy (ByteString)

import qualified Lang.Crucible.JVM as CJ
--import qualified SAWScript.Crucible.LLVM.CrucibleLLVM as CL
import SAWScript.Crucible.Common.MethodSpec
import qualified SAWScript.Crucible.Common.MethodSpec as CMS
import qualified SAWScript.Crucible.LLVM.MethodSpecIR as CMSLLVM
import qualified SAWScript.Crucible.JVM.MethodSpecIR as CMSJVM
import SAWScript.Proof
import SAWScript.Prover.SolverStats
import qualified Verifier.SAW.Term.Pretty as PP
import What4.ProgramLoc (ProgramLoc(plSourceLoc))

-- TODO if those were defined in their respective CrucibleMethodSpecIR, could we use non-orphan instance of ToJSON?
type JVMTheorem =  CMS.CrucibleMethodSpecIR CJ.JVM
type LLVMTheorem = CMSLLVM.SomeLLVM CMS.CrucibleMethodSpecIR

data VerificationSummary =
  VerificationSummary
  { vsJVMMethodSpecs :: [JVMTheorem]
  , vsLLVMMethodSpecs :: [LLVMTheorem]
  , vsTheorems :: [Theorem]
  }

vsVerifSolvers :: VerificationSummary -> Set.Set String
vsVerifSolvers vs =
  Set.unions $
  map (\ms -> solverStatsSolvers (ms ^. csSolverStats)) (vsJVMMethodSpecs vs) ++
  map (\(CMSLLVM.SomeLLVM ms) -> solverStatsSolvers (ms ^. csSolverStats)) (vsLLVMMethodSpecs vs)

vsTheoremSolvers :: VerificationSummary -> Set.Set String
vsTheoremSolvers = Set.unions . map getSolvers . vsTheorems
  where getSolvers (Theorem _ ss) = solverStatsSolvers ss

vsAllSolvers :: VerificationSummary -> Set.Set String
vsAllSolvers vs = Set.union (vsVerifSolvers vs) (vsTheoremSolvers vs)

computeVerificationSummary :: [JVMTheorem] -> [LLVMTheorem] -> [Theorem] -> VerificationSummary
computeVerificationSummary = VerificationSummary

msToJSON :: forall ext . Pretty (MethodId ext) => CMS.CrucibleMethodSpecIR ext -> Value
msToJSON cms = object [
    ("type" .= ("method" :: String)),
      ("method" .= (show $ pretty (cms ^. csMethod))),
        ("loc" .= (show $ (Leijen.pretty $ plSourceLoc (cms ^. csLoc)))), -- TODO: What4.ProgramLoc.Position is not an instance of Prettyprinter.Pretty
          ("status", if Set.null (solverStatsSolvers (cms ^. csSolverStats)) then "assumed" else "verified"),
            ("specification" .= ("unknown" :: String)) -- TODO
  ]

thmToJSON :: Theorem -> Value
thmToJSON thm = object [
  ("type" .= ("property" :: String)),
  ("loc" .= ("unknown" :: String)), -- TODO: Theorem has no attached location information
  ("status" .= (if Set.null (solverStatsSolvers (thmStats thm)) then "assumed" else "verified" :: String)),
  ("term" .= (show $ (PP.ppTerm PP.defaultPPOpts (unProp (thmProp thm))))) ]

jsonVerificationSummary :: VerificationSummary -> B.ByteString
jsonVerificationSummary (VerificationSummary jspecs lspecs thms) =
  encode vals where
    vals = foldr (++) [] [jvals, lvals, thmvals]
    jvals = map msToJSON jspecs
    lvals = map (\(CMSLLVM.SomeLLVM ls) -> msToJSON ls) lspecs
    thmvals = map thmToJSON thms

prettyVerificationSummary :: VerificationSummary -> String
prettyVerificationSummary vs@(VerificationSummary jspecs lspecs thms) =
  show $ vsep
  [ prettyJVMSpecs jspecs
  , prettyLLVMSpecs lspecs
  , prettyTheorems thms
  , prettySolvers (Set.toList (vsAllSolvers vs))
  ] where
      section nm = "#" <+> nm
      item txt = "*" <+> txt
      code txt = vsep ["~~~~", txt, "~~~~"]
      subitem = indent 4 . item
      sectionWithItems _ _ [] = mempty
      sectionWithItems nm prt items =
        vsep [section nm, "", vsep (map prt items)]
      verifStatus s = if Set.null (solverStatsSolvers (s ^. CMS.csSolverStats))
                      then "assumed"
                      else "verified"
      -- TODO: ultimately the goal is for the following to summarize all
      -- preconditions made by this verification, but we need to extract
      -- a bunch more information for that to be meaningful.
      {-
      condStatus s = (if null (s ^. (CMS.csPreState . CMS.csConditions))
                      then "without"
                      else "with") <+> "conditions"
                      -}
      prettyJVMSpecs ss =
        sectionWithItems "JVM Methods Analyzed" prettyJVMSpec ss
      prettyJVMSpec s =
        vsep [ item (fromString (s ^. CMSJVM.csMethodName))
             -- , subitem (condStatus s)
             , subitem (verifStatus s)
             ]
      prettyLLVMSpecs ss =
        sectionWithItems "LLVM Functions Analyzed" prettyLLVMSpec ss
      prettyLLVMSpec (CMSLLVM.SomeLLVM s) =
        vsep [ item (fromString (s ^. CMSLLVM.csName))
             -- , subitem (condStatus s)
             , subitem (verifStatus s)
             ]
      prettyTheorems ts =
        sectionWithItems "Theorems Proved or Assumed" (item . prettyTheorem) ts
      prettyTheorem t =
        vsep [ if Set.null (solverStatsSolvers (thmStats t))
               then "Axiom:"
               else "Theorem:"
             , code (indent 2 (PP.ppTerm PP.defaultPPOpts (unProp (thmProp t))))
             , ""
             ]
      prettySolvers ss =
        sectionWithItems "Solvers Used" (item . fromString) ss
