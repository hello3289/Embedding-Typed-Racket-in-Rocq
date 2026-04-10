Set Warnings "-uniform-inheritance".
Set Warnings "-ambiguous-paths".
Set Warnings "-meta-collision".
From TRresearch.Tactics Require Import tactics_all.
From TRresearch.Functions Require Import Predicates.
From TRresearch Require Import Definitions.
From Stdlib Require Import Lia.
From Corelib Require Import Program.Tactics.
#[local] Obligation Tactic := try (timeout 1 test_jail).

(* wow are a lot of these the same lemma but just for different predicates?
   yes they are and I am trying to fix that, which you can view my attempts at in 
   Sadness *)

Lemma is_number_returns_bool : forall {A : TRTypes} (x : {A}), 
  (proj1_sig (is_number x)) = Bool true \/ (proj1_sig (is_number x)) = Bool false.
Proof. intros. destructTR x. destruct x; eauto with TRHints. Qed.

Lemma is_number_trbool : forall {A : TRTypes} {x : {A}},
  HasType (proj1_sig (is_number x)) trbool.
Proof. 
  intros. 
  assert (H : (proj1_sig (is_number x)) = Bool true \/ (proj1_sig (is_number x)) = Bool false) by (apply is_number_returns_bool).
  destruct H; rewrite_jail; auto with TRHints.
Qed. 

Lemma is_string_returns_bool : forall {A : TRTypes} (x : {A}), 
  (proj1_sig (is_string x)) = Bool true \/ (proj1_sig (is_string x)) = Bool false.
Proof. intros. destructTR x. destruct x; eauto with TRHints. Qed.


Lemma is_string_trbool : forall {A : TRTypes} {x : {A}},
  HasType (proj1_sig (is_string x)) trbool.
Proof. 
  intros. 
  assert (H : (proj1_sig (is_string x)) = Bool true \/ (proj1_sig (is_string x)) = Bool false) by (apply is_string_returns_bool).
  destruct H; rewrite_jail; auto with TRHints.
Qed. 

Lemma is_string_trbool' : forall (x : TRValues) {A : TRTypes} 
  (J : (HasType x A) /\ ((HasType x A) /\ x <> Bool false -> True) /\ ((HasType x A) /\ x = Bool false -> True)),
  HasType (proj1_sig (is_string (exist (fun t : TRValues => (HasType t A) /\ 
                                        ((HasType t A) /\ t <> Bool false -> True) /\ 
                                        ((HasType t A) /\ t = Bool false -> True))
                                       x 
                                       J))) trbool.
Proof. intros. apply is_string_trbool. Qed.

Lemma proj1_sig_is_string_true : forall  {A : TRTypes} (x : {A}),
  proj1_sig (is_string x) <> Bool false -> 
  HasType (proj1_sig x) trstr.
Proof. intros. test_jail. Qed.

Lemma proj1_sig_is_string_false : forall  {A : TRTypes} (x : {A}),
  proj1_sig (is_string x) = Bool false -> 
  HasType (proj1_sig x) trstr -> 
  False.
Proof. intros. test_jail. Qed.

Lemma proj1_sig_is_number_true : forall  {A : TRTypes} (x : {A}),
  proj1_sig (is_number x) <> Bool false -> 
  HasType (proj1_sig x) trnum.
Proof. intros. test_jail. Qed.

Lemma proj1_sig_is_number_false : forall  {A : TRTypes} (x : {A}),
  proj1_sig (is_number x) = Bool false -> 
  HasType (proj1_sig x) trnum -> 
  False.
Proof. intros. test_jail. Qed.