Set Warnings "-uniform-inheritance".
Set Warnings "-ambiguous-paths".
Set Warnings "-meta-collision".
From TRresearch Require Import Definitions.

Lemma trpair_left : forall {a : TRValues} {A :TRTypes} (b : TRValues) (B : TRTypes), 
  HasType (a, b) (trpair A B) -> 
  HasType a A.
Proof.
  intros. inversion H; auto.
Qed.

Lemma trpair_right : forall {b : TRValues} {B :TRTypes} (a : TRValues) (A : TRTypes), 
  HasType (a, b) (trpair A B) -> 
  HasType b B.
Proof.
  intros. inversion H; auto.
Qed.