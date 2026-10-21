(* 
Notation " 'ifTR_am_I_stupid' A B C " := 
  (if_TR A (fun _ => B) (fun _ => C))
  (at level 0, A at next level, B at next level, C at next level).

Program Fixpoint filterTR_again {A B : TRTypes}
    (pred : forall (x : {trtop}), {>> trbool & (HasType x B)}) (* A instead of trtop? *)
    (l : {trlist A})
    {measure (lengthTR l)} : {trlist B} := 
ifTR_am_I_stupid (is_empty l)
    l
    (ifTR_am_I_stupid
            (pred (car l)) 
            (cons (car l) (filterTR_again pred (cdr l)))
            (filterTR_again pred (cdr l))).
Next Obligation.
    intros. simpl. destructTR l. destruct l; try inv_trtype_false_faster_2. repeat split.
    - simpl. auto.
    - intros. destruct l.
      + destruct n. repeat split. repeat constructor.
      + exists t; exists l. auto.
    - intros. intro. destruct H. inversion H1.
Defined. Next Obligation.
    intros; simpl. repeat split. 
    destructTR l; destruct l; try inv_trtype_false_faster_2.
    destruct l.
    + destruct n. repeat split. repeat constructor.
    + simpl. constructor.
Defined. Next Obligation.
    intros; simpl. destructTR l. destruct l; try inv_trtype_false_faster_2. repeat split.
    - simpl. auto.
    - intros. destruct l.
      + destruct n. repeat split. repeat constructor.
      + exists t; exists l. auto.
    - intros. intro. destruct H. inversion H1.
Defined. Next Obligation.
    intros; simpl. destructTR l. destruct l; try inv_trtype_false_faster_2. repeat split.
    - simpl. auto.
    - intros. destruct l.
      + destruct n. repeat split. repeat constructor.
      + exists t; exists l. auto.
    - intros. intro. destruct H. inversion H1.
Defined. Next Obligation.
    intros. destructTR l. destruct l; try inv_trtype_false_faster_2.
    destruct l.
    - exfalso. apply n. repeat constructor.
    - simpl. unfold TRcdr. simpl. unfold lengthTR. simpl.
      eapply PeanoNat.Nat.lt_succ_diag_r.
Defined. Next Obligation.
    intros; exact B. (* obligation 6*)
Defined. Next Obligation.

    intros; simpl. destructTR l. destruct l; try inv_trtype_false_faster_2. repeat split.
    - simpl. auto.
    - intros. destruct l.
      + destruct n. repeat split. repeat constructor.
      + exists t; exists l. auto.
    - intros. intro. destruct H. inversion H1.
Defined. Next Obligation.
    intros. destructTR l. destruct l; try inv_trtype_false_faster_2.
    destruct l.
    - exfalso. apply n. repeat constructor.
    - simpl. unfold TRcdr. simpl. unfold lengthTR. simpl.
      eapply PeanoNat.Nat.lt_succ_diag_r.
Defined. Next Obligation.
    intros. simpl. repeat split.
    destruct (filterTR_again _ _ _ _ _).
    unfold filterTR_again_func_obligation_6.
    assert (H : forall (B0 : TRTypes), true = eqb B0 B0).
    - intro. induction B0; simpl; auto. 
      rewrite <- IHB0_1. rewrite <- IHB0_2. simpl. auto.
      symmetry. apply PeanoNat.Nat.eqb_refl.
      rewrite <- IHB0_1. rewrite <- IHB0_2. simpl. auto.
    - assert (H1 : forall B, tr_union B B = B).
        + intro. unfold tr_union. rewrite <- (H B0). auto.
        + rewrite (H1 B).
        destruct a. auto.
Defined. Next Obligation.
    program_simpl.
Defined. Next Obligation.
        intros; simpl. repeat split. 
    destructTR l; destruct l; try inv_trtype_false_faster_2.
    destruct l.
    + destruct n. repeat split. repeat constructor.
    + simpl. simpl in h. auto.
Defined. Next Obligation.
    intros; simpl. repeat split.
    destruct (pred _).
    destruct
    destruct (if_TR _ _ _).
    give_up.
Admitted. Next Obligation.
    intros. simpl. repeat split.
    destruct (is_empty _). destruct a. destruct x; try inv_trtype_false_faster_2.
    destruct b.
    - simpl. destruct a. constructor. constructor.
    - 
    destruct (if_TR (is_empty l) _ _).
    destruct a. 
    assert (H : forall (B0 : TRTypes), true = eqb B0 B0).
    - intro. induction B0; simpl; auto. 
      rewrite <- IHB0_1. rewrite <- IHB0_2. simpl. auto.
      symmetry. apply PeanoNat.Nat.eqb_refl.
      rewrite <- IHB0_1. rewrite <- IHB0_2. simpl. auto.
    - assert (H1 : forall B, tr_union B B = B).
        + intro. unfold tr_union. rewrite <- (H B0). auto.
        + (* literally right here is where the problem shows up! *) rewrite <- (H1 (trlist B)). auto.
Defined. Next Obligation.
    program_simpl.
Defined. *)

(*
Program Fixpoint filterTR_test {A B : TRTypes}
    (pred : forall (x : {trtop}), {>> trbool & (HasType x B)}) (* A instead of trtop? *)
    (l : {trlist A})
    {measure (lengthTR l)} : {trlist B} := 
ifTR (is_empty l)
    (List nil) 
    (ifTR 
            (pred (car l)) 
            (cons (car l) (filterTR_test pred (cdr l)))
            (filterTR_test pred (cdr l))).
Next Obligation.
    intros. simpl. destructTR l. destruct l; try inv_trtype_false_faster_2. repeat split.
    - simpl. auto.
    - intros. destruct l.
      + destruct n. repeat split. repeat constructor.
      + exists t; exists l. auto.
    - intros. intro. destruct H. inversion H1.
Defined. Next Obligation.
    intros; simpl. repeat split. 
    destructTR l; destruct l; try inv_trtype_false_faster_2.
    destruct l.
    + destruct n. repeat split. repeat constructor.
    + simpl. constructor.
Defined. Next Obligation.
    intros; simpl. destructTR l. destruct l; try inv_trtype_false_faster_2. repeat split.
    - simpl. auto.
    - intros. destruct l.
      + destruct n. repeat split. repeat constructor.
      + exists t; exists l. auto.
    - intros. intro. destruct H. inversion H1.
Defined. Next Obligation.
    intros; simpl. destructTR l. destruct l; try inv_trtype_false_faster_2. repeat split.
    - simpl. auto.
    - intros. destruct l.
      + destruct n. repeat split. repeat constructor.
      + exists t; exists l. auto.
    - intros. intro. destruct H. inversion H1.
Defined. Next Obligation.
    intros. destructTR l. destruct l; try inv_trtype_false_faster_2.
    destruct l.
    - exfalso. apply n. repeat constructor.
    - simpl. unfold TRcdr. simpl. unfold lengthTR. simpl.
      eapply PeanoNat.Nat.lt_succ_diag_r.
Defined. Next Obligation.
    intros; simpl. destructTR l. destruct l; try inv_trtype_false_faster_2. repeat split.
    - simpl. auto.
    - intros. destruct l.
      + destruct n. repeat split. repeat constructor.
      + exists t; exists l. auto.
    - intros. intro. destruct H. inversion H1.
Defined. Next Obligation.
    intros. destructTR l. destruct l; try inv_trtype_false_faster_2.
    destruct l.
    - exfalso. apply n. repeat constructor.
    - simpl. unfold TRcdr. simpl. unfold lengthTR. simpl.
      eapply PeanoNat.Nat.lt_succ_diag_r.
Defined. Next Obligation.
    intros. exact B. (* obligation 8 *)
Defined. Next Obligation.
    program_simpl.
Defined. Next Obligation.
    intros; simpl. repeat split. 
    destructTR l; destruct l; try inv_trtype_false_faster_2.
    destruct l.
    + destruct n. repeat split. repeat constructor.
    + simpl. simpl in h. auto.
Defined. Next Obligation.
    intros. simpl. repeat split.
    destruct (if_TR_union (is_empty l) _ _).
    destruct a. 
    assert (H : forall (B0 : TRTypes), true = eqb B0 B0).
    - intro. induction B0; simpl; auto. 
      rewrite <- IHB0_1. rewrite <- IHB0_2. simpl. auto.
      symmetry. apply PeanoNat.Nat.eqb_refl.
      rewrite <- IHB0_1. rewrite <- IHB0_2. simpl. auto.
    - assert (H1 : forall B, tr_union B B = B).
        + intro. unfold tr_union. rewrite <- (H B0). auto.
        + (* literally right here is where the problem shows up! *) rewrite <- (H1 (trlist B)). auto.
Defined. Next Obligation.
    program_simpl.
Defined. 
*)