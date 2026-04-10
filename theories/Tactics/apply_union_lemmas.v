Set Warnings "-uniform-inheritance".
Set Warnings "-ambiguous-paths".
Set Warnings "-meta-collision".
From TRresearch.Lemmas Require Import Union_Lemmas.
From TRresearch Require Import Definitions.
From Corelib Require Import Program.Tactics.


Ltac apply_not_either_union := 
  match goal with 
  | |- ~ HasType (proj1_sig ?x) U ?A ?B => try (eapply not_either_union; eauto with TRHints)
  end.

Ltac apply_union_not :=
  match goal with 
  | [ x : {trunion ?A ?B} |- _ ] => 
    match goal with 
    | |- HasType (proj1_sig x) A => eapply union_not_right; eauto with TRHints
    end 
  end.