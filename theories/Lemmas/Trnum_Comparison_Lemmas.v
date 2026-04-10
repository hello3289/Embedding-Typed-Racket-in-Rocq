Set Warnings "-uniform-inheritance".
Set Warnings "-ambiguous-paths".
Set Warnings "-meta-collision".
From TRresearch Require Import Definitions.
From TRresearch.Functions Require Import trnum_comparisons.
From TRresearch.Tactics Require Import tactics_all.

Lemma less_than_0 :forall (n : nat), less_than_equal (Num 0) (Num n).
  Proof. intros. constructor; unfold leTR; simpl. apply le_0_n. Defined.

Lemma ltb_true_is_lt : forall i n, (Nat.ltb i n) = true -> i < n.
  intros. apply PeanoNat.Nat.ltb_lt; auto. Defined.

Lemma strictly_lessthan : forall (n : nat) (i : nat) (step : nat), 
    i < n + S step -> i < n -> n + S step - (i + S step) < n + S step - i.
Proof. intros. lia. Defined.

Lemma ltTR_B_is_lt : forall i n, (Bool true) = (proj1_sig (ltTR_B (Num i) (Num n))) -> i < n.
Proof. intros. simpl in H. apply ltb_true_is_lt. inversion H. rewrite H1; auto. Defined.

Lemma ltTR_B_is_less_than : forall i n, (Bool true) = (proj1_sig (ltTR_B (Num i) (Num n))) -> less_than (Num i) (Num n).
Proof. intros. simpl in H. constructor. unfold ltTR; simpl. apply ltTR_B_is_lt. inversion H. rewrite H1; auto. Qed.

Lemma ltTR_B_is_ltTR : forall i n, (Bool true) = (proj1_sig (ltTR_B (Num i) (Num n))) -> ltTR (Num i) (Num n).
Proof. intros. apply ltTR_B_is_less_than in H. inversion H; auto. Qed.