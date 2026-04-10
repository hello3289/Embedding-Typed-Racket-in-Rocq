Set Warnings "-uniform-inheritance".
Set Warnings "-ambiguous-paths".
Set Warnings "-meta-collision".
From TRresearch.Functions Require Import Predicates.
From TRresearch.Lemmas Require Import Predicate_Lemmas.
From TRresearch Require Import Definitions.
From Corelib Require Import Program.Tactics.

Ltac apply_proj1_sig_is_string_true := 
  match goal with 
  | [ H : proj1_sig (is_string ?x) <> Bool false |- HasType (proj1_sig _) trstr] => apply proj1_sig_is_string_true; auto with TRHints 
  end.

Ltac apply_proj1_sig_is_string_false := 
  match goal with 
  | [ H : proj1_sig (is_string ?x) = Bool false |- False] => 
    match goal with 
    | [ H : HasType (proj1_sig x) trstr |- False ] => apply (proj1_sig_is_string_false x); auto with TRHints 
    end 
  end.

Ltac apply_proj1_sig_is_number_true := 
  match goal with 
  | [ H : proj1_sig (is_number ?x) <> Bool false |- HasType (proj1_sig _) trnum] => apply proj1_sig_is_number_true; auto with TRHints 
  | [ H : ~ HasType (proj1_sig ?x) trnum |- _ ] => 
    match goal with 
    | [ H1 : proj1_sig (is_number x) <> Bool false |- _ ] => destruct H; apply proj1_sig_is_number_true; auto with TRHints 
    end
  end.

Ltac apply_proj1_sig_is_number_false := 
  match goal with 
  | [ H : proj1_sig (is_number ?x) = Bool false |- False] => 
    match goal with 
    | [ H : HasType (proj1_sig x) trnum |- False ] => apply (proj1_sig_is_number_false x); auto with TRHints 
    end 
  end.