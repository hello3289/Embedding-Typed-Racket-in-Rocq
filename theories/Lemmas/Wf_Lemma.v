Set Warnings "-uniform-inheritance".
Set Warnings "-ambiguous-paths".
Set Warnings "-meta-collision".
From TRresearch.Tactics Require Import tactics_all.
From TRresearch Require Import Definitions.
From TRresearch.Functions Require Import trnum_wf trnum_comparisons.
#[local] Obligation Tactic := try (timeout 1 test_jail).

Lemma wf_ltTR : well_founded ltTR.
Proof. 
  eapply (Wf_nat.well_founded_lt_compat _ wf_id). 
  intros; destruct2 x; destruct2 y.
  destruct x; try inv_trtype_false_faster_2. destruct y; try inv_trtype_false_faster_2. 
  unfold ltTR in H; simpl in H. unfold wf_id; simpl. auto.
Defined.

