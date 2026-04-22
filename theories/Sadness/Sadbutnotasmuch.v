Set Warnings "-uniform-inheritance".
Set Warnings "-ambiguous-paths".
Set Warnings "-meta-collision".
From TRresearch.Tactics Require Import tactics_all hastype_tactics.
From TRresearch Require Import Definitions Predicates If Basics.
From Stdlib Require Import Strings.String.
#[local] Obligation Tactic := try (timeout 1 (time test_jail)).

From TRresearch.Tests Require Import If_test.

(* i don't think this is the correct statement? *)


Create HintDb TRHints.
    Hint Extern 1 => apply_if_TR_union_HasType_union : TRHints.
    Hint Extern 1 => apply_andTR_HasType : TRHints.
    Hint Extern 1 => simplify_hypothesis : TRHints.
    Hint Extern 1 => apply_andTR_NotHasType : TRHints.

Print HintDb TRHints. (* WHERE ARE ALL THESE HINTS COMING FROM *)

Program Definition andTest2 {A B : TRTypes} (x : {A}) (y : {B}) :
  {>> trbool & ((HasType x trnum)  /\ (HasType y trstr))} :=
  andTR_2 (is_number x) (is_string y).
  
  