Set Warnings "-uniform-inheritance".
Set Warnings "-ambiguous-paths".
Set Warnings "-meta-collision".
From TRresearch.Lemmas Require Import Pair_Lemmas.
From TRresearch Require Import Definitions.
From TRresearch.Tactics Require Import tactics_all.

Ltac apply_trpair := 
  match goal with 
  | [ H : HasType (?a, ?b) (trpair ?A ?B) |- _ ] => idtac a b;
    match goal with 
    | |- HasType a A => apply (trpair_left b B); autoTR 
    | |- HasType b B => apply (trpair_right a A); autoTR 
    end 
  end.