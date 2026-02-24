Set Warnings "-ambiguous-paths".
Set Warnings "ambiguous-paths".
From TRresearch Require Import Tactic_jail.
From TRresearch Require Import Definitions.
From Stdlib.Strings Require Import String. (* bruh *)
From Stdlib Require Bool.
From Stdlib Require PeanoNat.
From Stdlib Require Import Lia.
Require Import Program.Tactics.
Require Import Init.Nat.
Require Import Program.Wf.
#[local] Obligation Tactic := try new_jail.
Open Scope string_scope.
Set Warnings "-meta-collision".

(************************************************************************)
(********************** Non-TR VEC FUNCTIONS AHHHH **********************)

Fixpoint append_vec {n m} (x : nat_vec n) (y : nat_vec m) : nat_vec (n + m) :=
  match x with
  | nil => y
  | cons n' v => (cons n' (append_vec v y))
  end.


Program Definition head_vec (n : nat) (x : nat_vec (S n)) : nat :=
  (match x in (nat_vec n0) return (n0 = S n -> nat) with
    | nil => fun H : 0 = S n => False_rec _ _
    | @cons n0 x0 nv1 => fun H : S n0 = S n => x0
    end) eq_refl.
Next Obligation. inversion H. Defined.

Eval compute in head_vec 2 (cons 9 (cons 5 (cons 4 nil))).

Program Definition tail_vec (n : nat) (x : nat_vec (S n)) : (nat_vec n) :=
  (match x in (nat_vec n0) return (n0 = S n -> nat_vec n) with
    | nil => fun H : 0 = S n => False_rec _ _ 
    | @cons n0 x0 nv1 => fun H : S n0 = S n => nv1
    end) eq_refl.
Next Obligation. inversion H. Defined.

(* i'm using option as a way to describe "errors" bc False_rec is more like "this shouldn't even happen"*)
(* note to self : you actually can't use False_rec here as we don't have a contradiction anywhere, which 
   is why we're doing the option as error. *)

Fixpoint vec_unsafe_ref {n} (v : nat_vec n) (i : nat) : option nat :=
  match v with 
  | nil => None
  | cons x v' => match i with 
                 | 0 => Some x 
                 | S i' => vec_unsafe_ref v' i'
                 end
  end.

#[local] Obligation Tactic := try new_jail; try inversion H; try inversion H0.
Program Definition what : 
  forall (n : nat) (m : {a : nat | 0 <= a < n}) (x : nat_vec n),
    let filtered_var := vec_unsafe_ref x (proj1_sig m) in
      None = filtered_var -> False.
  intros; simpl. subst filtered_var. induction x.
    - destruct m. destruct a. lia.
    - induction m. destruct x0; destruct p; simpl in H. inversion H. 
      apply PeanoNat.lt_S_n in l0.
      assert (H4: 0 <= x0 < n); try lia.
      specialize (IHx (exist (fun a => 0 <= a < n) x0 H4)) as J; simpl in J. 
      eauto.
Defined.


Program Definition vec_ref_safe {n} (m : {a | ((0 <= a) /\ (a < n)) }) (x : nat_vec n) : nat :=
  match vec_unsafe_ref x m with (* this is the define *)
  | None => False_rec _ _ (* this case is error will never occur *)
  | Some res => res
  end.
Next Obligation.
  eapply what; eauto.
Defined.


#[local] Obligation Tactic := 
  try (intros; subst *; match goal with | [H : {a | ?P} |- _ ] => destruct H end; simpl in *; lia).
Program Fixpoint vec_product {n} (res : nat) (i : {a | a <= n}) (x : nat_vec n) {measure i} : nat :=
  match i with 
  | 0 => res                                
  | S i' => (@vec_product _ (res * (vec_ref_safe i' x)) i' x _)
  end.
Next Obligation.
  simpl. apply measure_wf. apply Wf_nat.well_founded_ltof.
Defined.

Program Definition vec_product_test1 := vec_product 1 5 (cons 5 (cons 4 (cons 3 (cons 2 (cons 2 nil))))).
Next Obligation. simpl; auto. Defined.
Eval compute in vec_product_test1. 