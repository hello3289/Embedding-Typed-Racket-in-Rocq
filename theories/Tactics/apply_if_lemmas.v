Set Warnings "-uniform-inheritance".
Set Warnings "-ambiguous-paths".
Set Warnings "-meta-collision".
From TRresearch.Lemmas Require Import If_and_friends_Lemmas.
From TRresearch Require Import Definitions If Predicates.
From TRresearch.Tactics Require Import tactics_all.

Ltac apply_notTR_is_bool :=
  match goal with 
  | |- HasType (proj1_sig (notTR ?x)) trbool => apply notTR_is_bool
  end.

Ltac apply_notTR_bool_true_is_false := 
  match goal with 
  | [ H : proj1_sig (notTR (is_bool ?x)) <> Bool false |- _ ] => 
    match goal with 
    | |- get_true_prop (notTR (is_bool x)) => unfold get_true_prop; intro; eapply notTR_bool_true_is_false; eauto with TRHints 
    end 
  | [ H : proj1_sig (notTR (is_number ?x)) <> Bool false |- _ ] => 
    match goal with 
    | |- get_true_prop (notTR (is_number x)) => unfold get_true_prop; intro; eapply notTR_num_true_is_false; eauto with TRHints 
    end 
  end.

Ltac apply_notTR_bool_false_is_true := 
  match goal with 
  | [ H : proj1_sig (notTR (is_bool ?x)) = Bool false |- False ] => 
    match goal with 
    | [ H1 : get_true_prop (notTR (is_bool x)) |- _ ] => unfold get_true_prop in H1; destruct H1; eapply notTR_bool_false_is_true; eauto with TRHints
    end
  | [ H : proj1_sig (notTR (is_number ?x)) = Bool false |- False ] => 
    match goal with 
    | [ H1 : get_true_prop (notTR (is_number x)) |- _ ] => unfold get_true_prop in H1; destruct H1; eapply notTR_num_false_is_true; eauto with TRHints
    end
  end.