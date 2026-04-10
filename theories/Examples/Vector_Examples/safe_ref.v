Set Warnings "-uniform-inheritance".
Set Warnings "-ambiguous-paths".
Set Warnings "-meta-collision".
From TRresearch.Tactics Require Import tactics_all vec_unsafe_ref_none_false_tactic.
From TRresearch Require Import Definitions unsafe_ref.
From TRresearch.Functions Require Import Basics Vectors trnum_comparisons.
From TRresearch.Non_TR_Functions Require Import Vectors.
From TRresearch.Lemmas Require Import Vec_unsafe_ref_none_false.
From Stdlib Require Import Strings.String.
#[local] Obligation Tactic := try ((timeout 1 (time really_simple_start)); (timeout 1 (time new_jail))).


Create HintDb TRHints.
  Hint Extern 0 => discriminates : TRHints.
  Hint Extern 0 => subst_filtered_var : TRHints.
  Hint Extern 0 => simpl_func : TRHints.
  Hint Extern 0 => rewrite_jail' : TRHints.
  Hint Constructors HasType : TRHints.
  Hint Extern 0 => deal_with_none_trvec : TRHints.

Program Definition trvec_ref_tr {n} (x : { (trvec n) }) (m : {t >> trnum & ((less_than_equal 0 t) /\ (less_than t n)) & True}) : { trnum } :=
  match (trvec_unsafe_ref_tr x m) with 
  | Some p => p 
  | None => False_rec _ _
  end.

Notation " 'trvec_ref' v n " := 
  (trvec_ref_tr v (make_ltTR n (tr_length v) _)) (at level 0, v at next level, n at next level).
