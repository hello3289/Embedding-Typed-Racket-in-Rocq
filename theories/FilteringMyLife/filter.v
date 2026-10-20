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
  (@if_TR t1 _ _ _ _ _ _ A (fun _ => B) (fun _ => C))
  (at level 0, t1 at next level, A at next level, B at next level, C at next level).


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

Notation " 'cons' A B " := (@TRcons_new _ _ A _ B) (at level 0, A at next level, B at next level).
Notation " '!' " := (False_rec _ _).

Program Fixpoint filterTR {A B : TRTypes}
    (pred : forall (x : {trtop}), {>> trbool & (HasType x B)}) (* A instead of trtop? *)
    (l : {trlist A})
    {measure (lengthTR l)} : {trlist B} := 
ifTR_what (trlist B) (is_empty l)
    (List nil) 
    (ifTR_what (trlist B) 
            (pred (car l)) 
            (cons (car l) (filterTR pred (cdr l)))
            (filterTR pred (cdr l))).
Next Obligation.
    intros; exact True.
Defined. Next Obligation.
    intros; exact True.
Defined. Next Obligation.
    intros. simpl. repeat split. repeat constructor.
Defined. Next Obligation.
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
    intros; exact B. (* obligation 10 *)
Defined. Next Obligation.
    intros; simpl. destructTR l. destruct l; try inv_trtype_false_faster_2. repeat split.
    - simpl. auto.
    - intros. destruct l.
      + destruct n. repeat split. repeat constructor.
      + exists t; exists l. auto.
    - intros. intro. destruct H. inversion H1.
Defined. Next Obligation.
    intros; simpl. destructTR l. destruct l; try inv_trtype_false_faster_2.
    destruct l.
    + destruct n. repeat split. repeat constructor.
    + simpl. inversion l0. inversion H1. auto.
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
Defined.  Next Obligation.
    intros; exact True.
Defined. Next Obligation. 
    intros; exact True.
Defined. Next Obligation.
    program_simpl.
Defined. Next Obligation.
    intros; simpl. repeat split.
    destruct (TRcons_new _ _ _).
    destruct a. unfold filterTR_func_obligation_6    in h0.
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
    intros. simpl. repeat split.
    destruct (if_TR (is_empty l) _ _).
    destruct a. auto.
Defined.

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


From Stdlib Require Import Strings.String.
Open Scope string_scope.
Program Definition filter_test1 := (filterTR is_number (List (Num 5 :: Str "hi" :: nil))).
Eval vm_compute in filter_test1.
Program Definition filter_test2 := (filterTR is_bool (List (Num 5 :: Str "hi" :: nil))).
Eval vm_compute in filter_test2.
Program Definition filter_test3 := (filterTR is_string (List (Str "bye" :: Str "hi" :: Str "banana" :: nil))).
Eval vm_compute in filter_test3.
Program Definition filter_test4 := (filterTR is_pair (List ((Pair 5 4) :: Str "hi" :: nil))).
Eval vm_compute in filter_test4.
