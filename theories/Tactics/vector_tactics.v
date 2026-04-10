Set Warnings "-uniform-inheritance".
Set Warnings "-ambiguous-paths".
Set Warnings "-meta-collision".
From TRresearch.Tactics Require Import tactics_all.
From TRresearch Require Import Definitions trnum_comparisons.
From Stdlib Require Import Strings.String.
#[local] Obligation Tactic := try (timeout 1 test_jail).


Ltac unify_n_trvec := 
  match goal with 
  | [ v : nat_vec ?m |- _ ] => 
    match goal with 
    | [ H : HasType (Vec _ v) (trvec ?n) |- _ ] => 
      inversion H; subst *;
      match goal with 
      | [ H2 : existT _ _ _ = existT _ _ _ |- _ ] => clear H2
      end
    end 
  end.