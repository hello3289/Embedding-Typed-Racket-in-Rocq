Set Warnings "-meta-collision".
Set Warnings "-uniform-inheritance".
Set Warnings "-ambiguous-paths".

From TRresearch Require Import Functions.
From TRresearch.Tactics Require Import Tactic_jail.
From TRresearch Require Import Definitions.
From TRresearch Require Import VectorExamples.
From Stdlib Require Bool.
From Stdlib Require PeanoNat.
From Stdlib Require Import Lia.
From Corelib Require Import Program.Wf.
From Corelib Require Import Program.Tactics.
From Corelib Require Import Init.Nat.
#[local] Obligation Tactic := try new_jail.
Open Scope string_scope.

Open Scope TR_scope.


Ltac solve_ltB := 
  match goal with 
  | [H : (Bool true) = (proj1_sig ?P) |- _ ] => 
    let P1 := fresh H in 
    let P2 := fresh H in 
    let P3 := fresh H in
    let P4 := fresh H in
      apply what_again_again_TR in H as P1; apply what_again_TR in H as P2; apply what_again_again_again_TR in H as P3; 
      clear H
  end.

Ltac less_than_equal_0 :=
  match goal with 
  | |- less_than_equal (Num 0) (Num ?n) => apply (less_than_0 n)
  end.


(* hell once more... *)
#[local] Obligation Tactic := try (fast_destruct_solve; fail).
Program Fixpoint dot_prod_what_tr_3 {n : nat} 
  (len : { trnum }) 
  (step : {t >> trnum & (less_than 0 t) & ~(less_than 0 t)}) 
  (x : { (trvec n) }) 
  (y : { (trvec n) })  
  (acc : { trnum }) 
  (i : {t >> trnum & (less_than t (sum (Num n) step)) & True}) {measure (proj1_sig (sub (sum n step) i)) ltTR}
   : { trnum } :=
  match (ltTR_B i n) as M with
  | Bool true => @dot_prod_what_tr_3 n len step x y (sum acc (mul (trvec_ref x i) (trvec_ref y i))) (sum i step) _
  | Bool false => acc
  | _r => False_rec _ _
  end.

Next Obligation. very_small_jail. repeat destruct_invert. constructor. Defined. (* hopefully the Hint with help this... *)
Next Obligation. very_small_jail. unfold tr_length. destruct_invert. solve_ltB. auto. (* hopefully the hints will help... *) Defined.
Next Obligation. very_small_jail; destruct_invert. constructor. less_than_equal_0. solve_ltB; auto. Defined.
Next Obligation. very_small_jail. unfold tr_length. destruct_invert. solve_ltB. auto. Defined.
Next Obligation. very_small_jail; destruct_invert. constructor. less_than_equal_0. solve_ltB; auto. Defined.
Next Obligation. 
  very_small_jail; repeat destruct_invert. 
  - constructor. 
  - intro. solve_ltB. constructor; unfold ltTR; simpl.
    lia.
Defined.
Next Obligation. 
  very_small_jail. repeat destruct_invert. unfold ltTR; simpl. solve_ltB. 
  destruct n1. 
  make_hypothesis_not_bool (Num 0) trnum. specialize (step1 J) as K. inversion K. unfold ltTR in H1; simpl in H1.
  inversion H1.
  apply (strictly_lessthan n n0 n1); lia.
Defined. Next Obligation.
  small_jail. destruct i; try inv_trnum_fast. simpl in filtered_var.
  destruct (n0 <? n). destruct H0; auto. destruct H; auto.
Defined. Next Obligation.
  very_small_jail; discriminates.
Defined. Next Obligation.
  very_small_jail; discriminates.
Defined. Next Obligation.
  very_small_jail; discriminates.
Defined. Next Obligation.
  very_small_jail; discriminates.
Defined. Next Obligation.
  very_small_jail; discriminates.
Defined. Next Obligation.
  very_small_jail; discriminates.
Defined. Next Obligation.
  apply measure_wf. apply wf_ltTR.
Defined.


Program Definition make_ltTR_2 (n1 : {trnum}) (n2 : {trnum}) (H : (ltTR n1 n2)) 
    : {t >> trnum & (ltTR n1 n2) & True} :=
  n2.


(* 1. write notation to hide the unused things (like the _ in the signature) and to hide the match 
   2. write another definition of dotproduct to use all trvalue inputs *)
Program Definition dot_prod_tr {n} (x : { (trvec n) }) (y : { (trvec n) }) : { trnum } :=
  match x, y with 
  | Vec _ nv1, Vec _ nv2 => 
    let len := tr_length x in 
      let initial := 0 in 
        let start := 0 in 
          let step := (make_ltTR_2 0 1 _) in (* this is a bit annoying since we have to make the correct type*)
            let loop := dot_prod_what_tr_3 len step x y in 
              loop initial (make_ltTR start (sum (Num n) step) _)
  | _r1, _r2 => False_rec _ _
  end.
Next Obligation.
  intros; unfold ltTR; simpl; auto.
Defined. Next Obligation.
  intros; simpl; repeat split; try constructor. intros; intro; destruct H. discriminate.
Defined. Next Obligation.
  intros; simpl; repeat split; constructor.
Defined. Next Obligation.
  intros; simpl; unfold ltTR; simpl.
  subst start. lia.
Defined. Next Obligation.
  intros; simpl; subst start; repeat split; try constructor.
  - unfold ltTR; simpl. lia. 
Defined. Next Obligation.
  intros. destruct2 x; destruct2 y; simpl in *.
  inversion x0; inversion y0.  eapply n0. subst  x n n1 y. eauto.
  #[local] Obligation Tactic := try vec_inv.
Defined.

Eval compute in dot_prod_tr (cons 10 (cons 5 (cons 2 nil))) (cons 3 (cons 6 (cons 9 nil))).
Eval compute in dot_prod_tr nil nil.
(* Eval compute in dot_prod_tr 5 (cons 3 nil). *) 
