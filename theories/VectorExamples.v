Set Warnings "-meta-collision".
Set Warnings "-uniform-inheritance".
Set Warnings "-ambiguous-paths".

From TRresearch Require Import Functions.
From TRresearch.Tactics Require Import Tactic_jail.
From TRresearch Require Import Definitions.
From TRresearch Require Import StandardFunctions.
From Stdlib.Strings Require Import String. (* bruh *)
From Stdlib Require Import Bool.
From Stdlib Require PeanoNat.
From Stdlib Require Import Lia.
From Corelib Require Import Program.Wf.
From Corelib Require Import Program.Tactics.
From Corelib Require Import Init.Nat.
#[local] Obligation Tactic := try fail.
Open Scope string_scope.


(************************************************************************)
(**************** VEC HELPERS AND LEMMAS AHHHHHHHHHHHHHH ****************)

    (* idk why when i put this in tactic_jail, the subst* freaks out *)
  Ltac invert_equality := 
    match goal with 
    | [H : less_than _ _ |- _ ] =>
        let K1 := fresh "K" in 
        inversion H as [?n ?n K1]; unfold ltTR in K1; simpl in K1; subst *; clear H
    | [H : less_than_equal _ _ |- _ ] =>
        let K1 := fresh "K" in 
        inversion H as [?n ?n K1]; unfold leTR in K1; simpl in K1; subst *; clear H
    end.

  (* this tactic should actually be generalized, this can be used in the examples files too *)
    Ltac get_props := 
    match goal with 
    | [H : HasType ?n ?type /\ ?n <> (Bool false) -> ?P |- _ ] => 
        make_hypothesis_not_bool n type; 
        match goal with 
        | [H2 : HasType n type /\ n <> (Bool false) |- _ ] =>
            let K := fresh "K" in 
            specialize (H H2) as K; match K with 
                                    | ?r1 /\ ?r2 => destruct K 
                                    | ?r => inversion K 
                                    end; 
            clear H; clear H2; repeat invert_equality
        end
    end.

  Close Scope string_scope.

  #[local] Obligation Tactic := try small_jail; try discriminate; try new_jail.
  Program Definition make_ltTR (n1 : {trnum}) (n2 : {trnum}) (H : (ltTR n1 n2)) 
      : {t >> trnum & (ltTR n1 n2) & True} :=
    n1.
  Eval compute in make_ltTR 4 5 _.


(************************************************************************)
(**************** TRVEC_REF_SAFE (AND UNSAFE) AHHHHHHHHH ****************)

#[local] Obligation Tactic := try small_jail; try discriminate; try new_jail.
Program Definition trvec_unsafe_ref_tr {n} (x : { (trvec n) }) (m : {trnum}) : option {trnum} :=
  match x with 
  | Vec a v => match m with 
                | Num m' => match vec_unsafe_ref v m' with 
                           | None => None 
                           | Some p => Some p 
                           end
                | _r2 => False_rec _ _
                end
  | _r1 => False_rec _ _
  end.

Program Definition trvec_ref_tr {n} (x : { (trvec n) }) (m : {t >> trnum & ((less_than_equal 0 t) /\ (less_than t n)) & True}) : { trnum } :=
  match (trvec_unsafe_ref_tr x m) with 
  | Some p => p 
  | None => False_rec _ _
  end.
Next Obligation.
  inversion x0; subst *. clear H1.
  get_props.
  generalize dependent n0. 
  induction n2. intros; lia.
  intros; induction n1. inversion Heq_anonymous. unfold trvec_unsafe_ref_tr in Heq_anonymous; simpl in *.
  assert (J2 : n1 < n) by lia. (* we need this bc the eapply/eauto will fill in the hole with the wrong thing *)
  eapply IHn2; eauto.  
  apply Heq_anonymous.
  repeat split; eauto. unfold leTR; simpl; lia.
  lia.
  Unshelve. all : eauto; constructor.
Defined.

Notation " 'trvec_ref' v n " := 
  (trvec_ref_tr v (make_ltTR n (tr_length v) _)) (at level 0, v at next level, n at next level).

(* tactic to automate this *)
Create HintDb TRHints.
Hint Immediate less_than_0 : TRHints. (* hmmm idk how this works *)
#[local] Obligation Tactic := try small_jail; try discriminate; try new_jail; try constructor; try unfold leTR; simpl; try constructor; try unfold ltTR; simpl; try lia.
Program Definition test_trvec0 := trvec_ref (cons 3 (cons 2 (cons 0 nil))) 0.
Program Definition test_trvec1 := trvec_ref (cons 3 (cons 2 (cons 0 nil))) 1.
Program Definition test_trvec2 := trvec_ref (cons 3 (cons 2 (cons 0 nil))) 2.
(* and same as above with the unsolvable obligations indicating failure *)
Program Definition test_trvec_fail := trvec_ref (cons 3 (cons 2 (cons 0 nil))) 3. 
Next Obligation. Admitted. Next Obligation. Admitted.
Program Definition test_trvec_nil := trvec_ref nil 0.
Next Obligation. Admitted. Next Obligation. Admitted. 

Eval compute in test_trvec0.
Eval compute in test_trvec1.
Eval compute in test_trvec2.


(**************************************************************************************)
(**************************** PRODUCT AHHHHHHHHHHHHHHHHHH *****************************)

Open Scope TR_scope. 
Locate "add".
Hint Unfold leTR : TRHints.
Hint Unfold ltTR : TRHints. (* hmmm idk how this works yet *)
Hint Constructors less_than : TRHints. 
Hint Constructors less_than_equal : TRHints.

#[local] Obligation Tactic := try small_jail; try discriminate; try new_jail.
Program Fixpoint vec_prod_TR {n} 
  (res : {trnum}) 
  (i : {t >> trnum & (less_than_equal t (Num n)) & True}) 
  (x : {trvec n}) 
  {measure (proj1_sig i) ltTR}
  : {trnum} :=
  match i with 
  | Num 0 => res 
  | Num (S i') => vec_prod_TR (mul res (trvec_ref x i')) (Num i') x
  | _r => False_rec _ _ 
  end.
Next Obligation.  
  unfold tr_length; simpl; unfold ltTR; simpl. get_props. lia.
Defined. Next Obligation.
  apply less_than_0. constructor; unfold ltTR; simpl.
  get_props; lia.
Defined. Next Obligation. 
  constructor; unfold leTR; simpl.
  get_props; lia.
Defined. Next Obligation. 
  unfold ltTR; simpl; auto.
Defined. Next Obligation.
  destruct n2; try specialize (H n2); tauto.
Defined. Next Obligation.
  apply measure_wf. apply wf_ltTR.
Defined.


#[local] Obligation Tactic := try new_jail; try (inversion H0; inversion H). 
Program Definition vec_product_tr_loop {n} 
  (x : {(trvec n)})
  (len : {t >> trnum & (less_than_equal t (Num n)) & ~(less_than_equal t (Num n))})
  (res : { trnum }) : {trnum} :=
  vec_prod_TR res len x.

#[local] Obligation Tactic := try vec_inv; try (new_jail; fail).
Program Definition vec_product_tr_new {n} (x : {(trvec n)}) : {trnum} :=
  match x with 
  | Vec m1 nv1 => 
    let loop := vec_product_tr_loop x in 
      let i := (tr_length x) in 
        let res := 1 in 
          loop i res
  | _r1 => False_rec _ _
  end.
Next Obligation.
  intros; simpl; repeat split; try constructor; intro; intro. destruct H; discriminate.
Defined.

Eval compute in vec_product_tr_new (cons 5 (cons 4 (cons 3 (cons 2 (cons 1 nil))))).

(**************************************************************************************)
(**************************** SWAP AHHHHHHHHHHHHHHHHHHHHH *****************************)

#[local] Obligation Tactic := try vec_inv; try small_jail; try discriminate; try new_jail; try new_jail.
Program Definition vec_swap_tr {n} 
  (x : {(trvec n)}) 
  (i : {t >> trnum & ((less_than_equal 0 t) /\ (less_than t n)) & True})
  (j : {t >> trnum & ((less_than_equal 0 t) /\ (less_than t n)) & True}) : {trvoid} :=
  ifTR (eq_numTR i j)
       void 
       (let i_val := (trvec_ref x i) in 
          let j_val := (trvec_ref x j) in 
            let swap1 := (vec_setTR x i) in 
              vec_setTR x j).
Next Obligation. 
  unfold ltTR; simpl. repeat get_props; lia.
Defined. Next Obligation. 
  all : constructor; try unfold leTR; try unfold ltTR; simpl; repeat get_props; lia.
Defined. Next Obligation.
  unfold tr_length; simpl.
  unfold ltTR; simpl.
  repeat get_props; lia.
Defined. Next Obligation.
  apply less_than_0.
  constructor; unfold ltTR; simpl.
  repeat get_props; lia.
Defined. Next Obligation.
  destruct (n1 =? n0); constructor.
Defined.