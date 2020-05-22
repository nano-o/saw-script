From Coq          Require Import Lists.List.
From Coq          Require Import String.
From Coq          Require Import Vectors.Vector.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.
From Records      Require Import Records.

From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Import CompMExtra.

Load "linked_list.v".
Import linked_list.

Import SAWCorePrelude.


Lemma no_errors_is_elem : refinesFun is_elem (fun _ _ => noErrorsSpec).
Proof.
  unfold is_elem, is_elem__tuple_fun, noErrorsSpec.
  prove_refinement.
Qed.

Lemma no_errors_is_elem_manual : refinesFun is_elem (fun _ _ => noErrorsSpec).
Proof.
  unfold noErrorsSpec.
  apply refinesFun_multiFixM_fst. intros x l.
  apply refinesM_letRecM0.
  apply refinesM_either_l; intros.
  - eapply refinesM_existsM_r. reflexivity.
  - apply refinesM_if_l; intros.
    + eapply refinesM_existsM_r. reflexivity.
    + rewrite existsM_bindM.
      apply refinesM_existsM_l; intros. rewrite returnM_bindM.
      eapply refinesM_existsM_r. reflexivity.
Qed.

Ltac destructArg_list :=
  (lazymatch goal with
  | |- MaybeDestructArg (list _) ?l ?g =>
    match g with
    | context [Datatypes.list_rect _ _ _ l] =>
      destruct l; simpl; apply noDestructArg
    end
  end).
Hint Extern 1 (MaybeDestructArg _ _ _) => destructArg_list :refinesFun.

(*
Fixpoint is_elem_spec (x:bitvector 64) (l:W64List) : CompM {_:bitvector 64 & unit} :=
  match l with
  | W64Nil => returnM (existT _ (bvNat 64 0) tt)
  | W64Cons y l' =>
    if bvEq 64 y x then returnM (existT _ (bvNat 64 1) tt) else
      is_elem_spec x l'
  end.
*)

Definition is_elem_spec (x:bitvector 64) :
  list {_:bitvector 64 & unit} -> CompM {_:bitvector 64 & unit} :=
  list_rect (fun _ => CompM {_:bitvector 64 & unit})
            (returnM (existT _ (bvNat 64 0) tt))
            (fun y l' rec =>
               if bvEq 64 (projT1 y) x then returnM (existT _ (bvNat 64 1) tt) else rec).

Arguments is_elem_spec /.

Lemma is_elem_correct : refinesFun is_elem is_elem_spec.
Proof.
  unfold is_elem, is_elem__tuple_fun, is_elem_spec.
  prove_refinement.
Qed.
