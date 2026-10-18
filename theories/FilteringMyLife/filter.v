Set Warnings "-ambiguous-paths".
From TRresearch Require Import Definitions_new.
From TRresearch Require Import Basic_stuff.
Require Import Program.Tactics.
From TRresearch Require Import Lemmas_new.
From Corelib Require Import Lists.ListDef.
Require Import Program.Tactics.
From Corelib Require Import Program.Wf.

Close Scope string_scope.


Program Definition TRcons_new {t1 t2 : TRTypes}
  (head : TRValues)
  (H : (HasType head t1))
  (tail : {trlist t2}) : {trlist (tr_union t1 t2)} := 
  match tail with 
         | List l => List (head :: l) 
         | _r => False_rec _ _ 
         end. 
Next Obligation.
  repeat split.
  constructor. constructor.
  unfold tr_union.
  destruct (eqb t1 t2).
  auto. apply HtUnion_L; auto.
  unfold tr_union. remember (eqb t1 t2).
  destruct b.
  apply eqb_true in Heqb. inversion h.  rewrite Heqb. auto.
  assert (H1 : forall (l : list TRValues) (A B : TRTypes),
               Forall (fun x : TRValues => HasType x B) l -> 
               Forall (fun x : TRValues => HasType x (trunion A B)) l).
      ++ intros. induction l0.
         constructor. 
         inversion H0. specialize (IHl0 H4). 
         subst *. constructor.
         apply HtUnion_R. auto.
         auto.
      ++ apply H1. inversion h. auto.
Defined. Next Obligation.
  destruct tail; try inv_trtype_false_faster_2.
  specialize (n l); destruct n. auto.
Defined.

Notation " 'ifTR_what' t1 A B C " := 
  (@if_TR_union t1 t1 _ _ _ _ _ _ A (fun _ => B) (fun _ => C))
  (at level 0, t1 at next level, A at next level, B at next level, C at next level).


Lemma kill_me : forall (l : list TRValues), Forall (fun x : TRValues => HasType x trtop) l.
Proof. intros. induction l.
    constructor.
    constructor. constructor. auto.
Defined.

Program Definition lengthTR {t : TRTypes} (x : {trlist t}) : nat := 
    match (TRlength x) with 
    | Num n => n 
    | _r => False_rec _ _
    end.
Next Obligation.
    destruct (TRlength [x]).
    destruct a. destruct x0; try inv_trtype_false_faster_2.
    specialize (n n0). destruct n. auto.
Defined.

#[local] Obligation Tactic := try fail.
Program Fixpoint filterTR {A B : TRTypes}
    (pred : forall (x : {trtop}), {>> trbool & (HasType x B)}) (* A instead of trtop? *)
    (l : {trlist A})
    {measure (lengthTR l)} : {trlist B} := 
ifTR_what (trlist B) (is_empty l)
    (List nil) 
    (ifTR_what (trlist B) (is_cons l)
        (ifTR_what (trlist B) (pred (@TRcar _ l)) 
            (@TRcons_new _ _ (@TRcar _ l) _ (filterTR pred (@TRcdr _ l)))
            (filterTR pred (@TRcdr _ l)))
        (False_rec _ _)).
Next Obligation.
    intros; exact True. (* what *)
Defined. Next Obligation.
    intros; exact True. (* what 2 *)
Defined. Next Obligation.
    intros; exact True. (* what *)
Defined.  Next Obligation.
    intros; exact True. (* what 4 *)
Defined.  Next Obligation. (* uses 1 and 3, but True seems to be correct*)
    intros. simpl.
    repeat split. constructor. constructor.
Defined. Next Obligation.
    intros; exact True. (* what 6 *)
Defined. Next Obligation.
    intros; exact True. (* what 7 *)
Defined. Next Obligation.
    intros; exact True. (* what 8 *)
Defined. Next Obligation.
    intros; exact True. (* what 9 *)
Defined. Next Obligation.
    intros; exact True. (* what 10 *)
Defined. Next Obligation.
    intros; exact True. (* what 11 *)
Defined. Next Obligation.
    intros. simpl.
    destructTR l. destruct l; try inv_trtype_false_faster_2.
    destruct l.
    - destruct e. destruct H. inversion H.
    - repeat split.
      constructor. constructor. constructor. apply kill_me.
      intro. exists t; exists l; simpl; auto.
      intros; intro. destruct H. inversion H1.
Defined. Next Obligation.
    intros. exact B. (* what 13 *)
Defined. Next Obligation.
    intros. exact A. (* what 14 *)
Defined. Next Obligation. (* uses 14 *)
    intros. simpl.
    repeat split.
    - destruct l. destruct a. apply h0.
    - intros. destruct l. destruct a. destruct x; try inv_trtype_false_faster_2.
      destruct l.
      + exfalso; apply n. repeat split. constructor. constructor.
      + exists t; exists l; auto.
    - intro. intro. destruct H. 
      rewrite H1 in H. inversion H.
Defined. Next Obligation. (* 16 *)
    intros. simpl. (* uses 13 *) (* can either be A or B.. gotta see*)
    unfold filterTR_func_obligation_13.
    destruct l. simpl in *. destruct a. destruct x; try inv_trtype_false_faster_2.
    destruct l.
    destruct e.  destruct e. inversion e.
    simpl in *. auto.
Defined. Next Obligation.
    intros; exact A. (* what 17 *)
Defined. Next Obligation. (* uses 17*)
    intros. simpl. destruct l. destruct a. 
    repeat split. apply h0.
    intro. destruct x; try inv_trtype_false_faster_2.
    destruct l.
    destruct e. destruct e. inversion e.
    exists t; exists l. auto.
    intro. intro. destruct H. simpl in H1.
    destruct x; try inv_trtype_false_faster_2.
    inversion H1.
Defined. Next Obligation.
    intros. destructTR l. destruct l; try inv_trtype_false_faster_2.
    destruct l.
    - exfalso. apply n. repeat constructor.
    - simpl. unfold TRcdr. simpl. unfold lengthTR. simpl.
      eapply PeanoNat.Nat.lt_succ_diag_r.
Defined.
 Next Obligation. (* uses 17, 16, *) (* 19 *)
    intros. simpl. repeat split.
    destruct (TRcons_new _ _ _).
    destruct a. unfold filterTR_func_obligation_13  in h0.
    assert (H : forall (B0 : TRTypes), true = eqb B0 B0).
    - intro. induction B0; simpl; auto. 
      rewrite <- IHB0_1. rewrite <- IHB0_2. simpl. auto.
      symmetry. apply PeanoNat.Nat.eqb_refl.
      rewrite <- IHB0_1. rewrite <- IHB0_2. simpl. auto.
    - assert (H1 : forall B, tr_union B B = B).
        + intro. unfold tr_union. rewrite <- (H B0). auto.
        + specialize (H1 B). 
          assert (H3 : HasType x (trlist B)). rewrite <- H1. auto.
          simpl. auto.
Defined. Next Obligation. (* what 20*)
    intros. exact A.
Defined. Next Obligation. (* uses 20*) (* 21 *)
    intros. simpl. destruct l. destruct a. 
    repeat split. apply h.
    intro. destruct x; try inv_trtype_false_faster_2.
    destruct l.
    destruct e. destruct e. inversion e.
    exists t; exists l. auto.
    intro. intro. destruct H. simpl in H1.
    destruct x; try inv_trtype_false_faster_2.
    inversion H1.
Defined. Next Obligation.
    intros. destructTR l. destruct l; try inv_trtype_false_faster_2.
    destruct l.
    - exfalso. apply n. repeat constructor.
    - simpl. unfold TRcdr. simpl. unfold lengthTR. simpl.
      eapply PeanoNat.Nat.lt_succ_diag_r.
Defined. Next Obligation. (* uses 16, 17, 20*) (* 22 *)
    intros. simpl. repeat split.
    destruct (if_TR_union (pred (TRcar [proj1_sig l])) _ _).
    destruct a. 
    assert (H : forall (B0 : TRTypes), true = eqb B0 B0).
    - intro. induction B0; simpl; auto. 
      rewrite <- IHB0_1. rewrite <- IHB0_2. simpl. auto.
      symmetry. apply PeanoNat.Nat.eqb_refl.
      rewrite <- IHB0_1. rewrite <- IHB0_2. simpl. auto.
    - assert (H1 : forall B, tr_union B B = B).
        + intro. unfold tr_union. rewrite <- (H B0). auto.
        + rewrite <- (H1 (trlist B)). auto.
Defined. Next Obligation. (* 23 *)
    intros. destructTR l. destruct l; try inv_trtype_false_faster_2.
    destruct l.
    - apply n; repeat constructor.
    - apply n0. exists t; exists l. auto.
Defined. Next Obligation.
    intros. simpl. repeat split.
    destruct (if_TR_union (is_cons l) _ _).
    destruct a. 
    assert (H : forall (B0 : TRTypes), true = eqb B0 B0).
    - intro. induction B0; simpl; auto. 
      rewrite <- IHB0_1. rewrite <- IHB0_2. simpl. auto.
      symmetry. apply PeanoNat.Nat.eqb_refl.
      rewrite <- IHB0_1. rewrite <- IHB0_2. simpl. auto.
    - assert (H1 : forall B, tr_union B B = B).
        + intro. unfold tr_union. rewrite <- (H B0). auto.
        + rewrite <- (H1 (trlist B)). auto.
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
        + rewrite <- (H1 (trlist B)). auto.
Defined. Next Obligation.
    try program_simpl.
Defined.

(*
Program Definition TRcons_new_again {t1 t2 : TRTypes}
  (head : {t1})
  (tail : {trlist t2}) : {trlist (tr_union t1 t2)} := 
  match head with 
  | x => match tail with 
         | List l => List (x :: l) 
         | _r => False_rec _ _ 
         end
  end.
Next Obligation.
  repeat split.
  constructor. constructor.
  unfold tr_union.
  destructTR head. rewrite Heq_head.
  destruct (eqb t1 t2).
  auto. apply HtUnion_L; auto.
  unfold tr_union. remember (eqb t1 t2). destructTR tail.
  destruct b.
  apply eqb_true in Heqb. inversion tail0.  rewrite Heqb. subst *. 
  simpl in Heq_tail. inversion Heq_tail.  auto.
  assert (H1 : forall (l : list TRValues) (A B : TRTypes),
               Forall (fun x : TRValues => HasType x B) l -> 
               Forall (fun x : TRValues => HasType x (trunion A B)) l).
      ++ intros. induction l0.
         constructor. 
         inversion H. specialize (IHl0 H3). 
         subst *. constructor.
         apply HtUnion_R. auto.
         auto.
      ++ apply H1. 
  simpl in Heq_tail. rewrite <- Heq_tail in tail0. inversion tail0. auto.
Defined. Next Obligation.
    intros. destructTR tail.
  destruct tail; try inv_trtype_false_faster_2.
  specialize (n l); destruct n. auto.
Defined. Next Obligation.
    intros. destructTR tail. intro. subst *.
    inversion H.
Defined. Next Obligation.
    intros. destructTR tail. intro. subst *.
    inversion H.
Defined. Next Obligation.
    intros. destructTR tail. intro. subst *.
    inversion H.
Defined. Next Obligation.
    intros. destructTR tail. intro. subst *.
    inversion H.
Defined. Next Obligation.
    intros. destructTR tail. intro. subst *.
    inversion H.
Defined. Next Obligation.
    intros. destructTR tail. intro. subst *.
    inversion H.
Defined. *)

Notation " 'cons' A B " := (@TRcons_new _ _ A _ B) (at level 0, A at next level, B at next level).
Notation " '!' " := (False_rec _ _).

Program Fixpoint filterTR_test {A B : TRTypes}
    (pred : forall (x : {trtop}), {>> trbool & (HasType x B)}) (* A instead of trtop? *)
    (l : {trlist A})
    {measure (lengthTR l)} : {trlist B} := 
ifTR_what (trlist B) (is_empty l)
    (List nil) 
    (ifTR_what (trlist B) (is_cons l)
        (ifTR_what (trlist B) (pred (car l)) 
            (cons (car l) (filterTR pred (cdr l)))
            (filterTR pred (cdr l)))
        !).  
Next Obligation.
    intros; exact True.
Defined. Next Obligation.
    intros; exact True.
Defined. Next Obligation.
    intros; exact True.
Defined. Next Obligation.
    intros; exact True.
Defined. Next Obligation.
    intros. simpl.
    repeat split. repeat constructor.
Defined. Next Obligation.
    intros; exact True.
Defined. Next Obligation.
    intros; exact True.
Defined. Next Obligation.
    intros; exact True.
Defined. Next Obligation.
    intros; exact True.
Defined. Next Obligation.
    intros; exact True.
Defined. Next Obligation.
    intros; exact True.
Defined. Next Obligation.
    intros. simpl. destructTR l. destruct l; try inv_trtype_false_faster_2.
    repeat split.
    auto.
    intro. destruct l. exfalso; apply n; repeat constructor.
    exists t; exists l. auto.
    intro; intro. destruct H. inversion H1.
Defined. Next Obligation.
    intros; simpl. repeat split. constructor.
Defined. Next Obligation.
    intros; exact B.
Defined. Next Obligation.
    intros; simpl. destructTR l. destruct l; try inv_trtype_false_faster_2.
    repeat split.
    auto.
    intro. destruct l. exfalso; apply n; repeat constructor.
    exists t; exists l. auto.
    intro; intro. destruct H. inversion H1.
Defined. Next Obligation.
    intros; simpl. destructTR l. destruct l; try inv_trtype_false_faster_2.
    destruct l. exfalso; apply n; repeat constructor.
    simpl. inversion l0. inversion H1. auto.
Defined. Next Obligation.
    intros. simpl. destructTR l. destruct l; try inv_trtype_false_faster_2.
    repeat split.
    auto.
    intro. destruct l. exfalso; apply n; repeat constructor.
     exists t; exists l. auto.
    intro; intro. destruct H. inversion H1.
Defined. Next Obligation.
    intros. simpl. repeat split.
    destruct (TRcons_new _ _ _).
    destruct a. unfold filterTR_test_func_obligation_14   in h0.
    assert (H : forall (B0 : TRTypes), true = eqb B0 B0).
    - intro. induction B0; simpl; auto. 
      rewrite <- IHB0_1. rewrite <- IHB0_2. simpl. auto.
      symmetry. apply PeanoNat.Nat.eqb_refl.
      rewrite <- IHB0_1. rewrite <- IHB0_2. simpl. auto.
    - assert (H1 : forall B, tr_union B B = B).
        + intro. unfold tr_union. rewrite <- (H B0). auto.
        + specialize (H1 B). 
          assert (H3 : HasType x (trlist B)). rewrite <- H1. auto.
          simpl. auto.
Defined. Next Obligation.
    intros; simpl. destructTR l. destruct l; try inv_trtype_false_faster_2.
    repeat split.
    auto.
    intro. destruct l. exfalso; apply n; repeat constructor.
     exists t; exists l. auto.
    intro; intro. destruct H. inversion H1.
Defined. Next Obligation.
     intros. simpl. repeat split.
    destruct (if_TR_union _ _ _).
    destruct a. 
    assert (H : forall (B0 : TRTypes), true = eqb B0 B0).
    - intro. induction B0; simpl; auto. 
      rewrite <- IHB0_1. rewrite <- IHB0_2. simpl. auto.
      symmetry. apply PeanoNat.Nat.eqb_refl.
      rewrite <- IHB0_1. rewrite <- IHB0_2. simpl. auto.
    - assert (H1 : forall B, tr_union B B = B).
        + intro. unfold tr_union. rewrite <- (H B0). auto.
        + rewrite <- (H1 (trlist B)). auto.
Defined. Next Obligation.
    intros. destructTR l. destruct l; try inv_trtype_false_faster_2.
    destruct l.
    - apply n; repeat constructor.
    - apply n0. exists t; exists l. auto.
Defined. Next Obligation.
    intros. simpl. repeat split.
    destruct (if_TR_union (is_cons l) _ _).
    destruct a. 
    assert (H : forall (B0 : TRTypes), true = eqb B0 B0).
    - intro. induction B0; simpl; auto. 
      rewrite <- IHB0_1. rewrite <- IHB0_2. simpl. auto.
      symmetry. apply PeanoNat.Nat.eqb_refl.
      rewrite <- IHB0_1. rewrite <- IHB0_2. simpl. auto.
    - assert (H1 : forall B, tr_union B B = B).
        + intro. unfold tr_union. rewrite <- (H B0). auto.
        + rewrite <- (H1 (trlist B)). auto.
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
        + rewrite <- (H1 (trlist B)). auto.
Defined. Next Obligation.
    try program_simpl.
Defined.



From Stdlib Require Import Strings.String.
Program Definition filter_test1 := (filterTR is_number (List (Num 5 :: Str "hi" :: nil))).
Eval vm_compute in filter_test1.
