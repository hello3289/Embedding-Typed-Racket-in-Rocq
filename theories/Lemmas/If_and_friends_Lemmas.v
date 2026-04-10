Set Warnings "-uniform-inheritance".
Set Warnings "-ambiguous-paths".
Set Warnings "-meta-collision".
From TRresearch.Tactics Require Import tactics_all.
From TRresearch.Functions Require Import Predicates If.
From TRresearch Require Import Definitions.
From Stdlib Require Import Lia.
From Corelib Require Import Program.Tactics.
#[local] Obligation Tactic := try (timeout 1 test_jail).

Create HintDb TRHints.
    Hint Extern 0 => discriminates : TRHints.
    Hint Extern 0 => subst_filtered_var : TRHints.
    Hint Extern 0 => simpl_func : TRHints.
    Hint Extern 0 => rewrite_jail' : TRHints.
    Hint Constructors HasType : TRHints.

Lemma notTR_is_bool : forall {P Q} (x : {>> trbool & P & Q}), 
  HasType (proj1_sig (notTR x)) trbool.
Proof. test_jail. unfold notTR; simpl. destruct b; simpl; auto with TRHints. Qed.

Lemma notTR_bool_true_is_false : forall {t} (x : {t}),
  proj1_sig (notTR (is_bool x)) <> Bool false -> 
  HasType (proj1_sig x) trbool -> 
  False.
Proof. test_jail. Qed.

Lemma notTR_num_true_is_false : forall {t} (x : {t}),
  proj1_sig (notTR (is_number x)) <> Bool false -> 
  HasType (proj1_sig x) trnum -> 
  False.
Proof. test_jail. Qed.

Lemma notTR_bool_false_is_true : forall {t} (x : {t}),
  proj1_sig (notTR (is_bool x)) = Bool false -> 
  HasType (proj1_sig x) trbool.
Proof. test_jail. Qed.

Lemma notTR_num_false_is_true : forall {t} (x : {t}),
  proj1_sig (notTR (is_number x)) = Bool false -> 
  HasType (proj1_sig x) trnum.
Proof. test_jail. Qed.