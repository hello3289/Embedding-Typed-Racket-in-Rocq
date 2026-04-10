Set Warnings "-uniform-inheritance".
Set Warnings "-ambiguous-paths".
Set Warnings "-meta-collision".
From TRresearch.Tactics Require Import tactics_all apply_predicate_lemmas.
From TRresearch Require Import Definitions Predicates If Basics.
From TRresearch.Lemmas Require Import Lemmas Union_Lemmas Predicate_Lemmas.
From Stdlib Require Import Strings.String.
#[local] Obligation Tactic := try fail.

From TRresearch.Tests Require Import If_test.

(* i don't think this is the correct statement? *)
Lemma eventually_i_will_make_this_better : forall {A B : TRTypes} {P Q : Prop} (x : {A}) (y : {B})
  (pred1 : (forall x : {A}, {>> trbool & P}))
  (pred2 : (forall x : {B}, {>> trbool & Q})),
  proj1_sig (andTR_2 (pred1 x) (pred2 y)) <> Bool false -> 
  P.
Proof. intros.
  destructTR_fresh (pred1 x). destruct x0; try inv_trtype_false_faster.
  destructTR_fresh (pred2 y). destruct x0; try inv_trtype_false_faster.
  destruct b; destruct b0; simpl in H; try (apply x2); try (apply x5); split; auto.
Qed.

Program Definition andTest2 {A B : TRTypes} (x : {A}) (y : {B}) :
  {>> trbool & ((HasType x trnum)  /\ (HasType y trstr))} :=
  andTR_2 (is_number x) (is_string y).