Set Warnings "-uniform-inheritance".
Set Warnings "-ambiguous-paths".
Set Warnings "-meta-collision".
From TRresearch.Tactics Require Import tactics_all vector_tactics comparison_tactics.
From TRresearch Require Import Definitions trnum_comparisons unsafe_ref.
From Stdlib Require Import Strings.String.
#[local] Obligation Tactic := try (timeout 1 test_jail).

Lemma nat_is_num : forall (n0 : nat), 
  HasType (Num n0) trnum /\
  (HasType (Num n0) trnum /\ (Num n0) <> Bool false -> True) /\
  (HasType (Num n0) trnum /\ (Num n0) = Bool false -> True).
Proof. auto with TRHints. Qed.


Lemma vec_unsafe_ref_none_false : 
  forall {n} 
  (x : { (trvec n) })
  (n0 : nat), 
  n0 < n -> 
  0 <= n0 -> 
  None = trvec_unsafe_ref_tr x (exist 
                                  (fun p => HasType p trnum /\ 
                                            ((HasType p trnum) /\ p <> Bool false -> True) /\
                                            ((HasType p trnum) /\ p = Bool false -> True)) 
                                  (Num n0) (nat_is_num n0)) 
  -> False.
Proof. intros.
  test_jail.
  unify_n_trvec.
  generalize dependent n0. 
  induction n2.
    - lia.
    - intros; induction n1. inversion H1. unfold trvec_unsafe_ref_tr in H1; simpl in *.
      assert (J2 : n1 < n) by lia. (* we need this bc the eapply/eauto will fill in the hole with the wrong thing *)
      eapply IHn2; eauto.  
      unfold leTR; simpl; lia.
      Unshelve. all : eauto; constructor.
Qed.