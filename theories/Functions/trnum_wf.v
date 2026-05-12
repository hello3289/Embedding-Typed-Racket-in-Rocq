Set Warnings "-uniform-inheritance".
Set Warnings "-ambiguous-paths".
Set Warnings "-meta-collision".
From TRresearch.Tactics Require Import tactics_all.
From TRresearch Require Import Definitions trnum_comparisons.
From Corelib Require Import Program.Wf.
#[local] Obligation Tactic := try (timeout 1 test_jail).

(* "well foundedness for trnum " *)

Program Definition wf_id (n : {trnum}) : nat := 
  match n with 
  | Num n' => n'
  | _r => False_rec _ _
  end.

(* "proof of well-foundedness for ltTR" *)

Lemma wf_ltTR : well_founded ltTR.
Proof. 
  eapply (Wf_nat.well_founded_lt_compat _ wf_id). 
  intros; destruct2 x; destruct2 y.
  destruct x; try inv_trtype_false_faster_2. destruct y; try inv_trtype_false_faster_2. 
  unfold ltTR in H; simpl in H. unfold wf_id; simpl. auto.
Defined.

(* "tactics for solving wf obligations" *)

Ltac well_founded_tactic := 
  match goal with 
  | |- well_founded _ => try (apply measure_wf; apply wf_ltTR)
  end.