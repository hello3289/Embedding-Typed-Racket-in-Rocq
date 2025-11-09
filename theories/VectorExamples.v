From TRresearch Require Import Functions.
From TRresearch Require Import Tactic_jail.
From TRresearch Require Import Definitions.
Require Import String.
Require Import Bool.
Require Import Program.Tactics.
Require Import Init.Nat.
Require Import PeanoNat.
Require Import Program.Wf.
#[local] Obligation Tactic := try new_jail.
(* #[local] Obligation Tactic := try (program_simpl; easy); try (new_jail; easy). *)

Coercion Num : nat >-> TRValues.
Coercion Str : string >-> TRValues.
Coercion Bool : bool >-> TRValues.
Coercion Vec : nat_vec >-> TRValues.
Coercion Void : Void_ >-> TRValues.
Coercion giveTypeWat (p : TRValues) := giveType p.
(* ok now we just have the problem of trunion *)

(* take trtype and produce something of the given thing 
  - or look up how to case on types *)
Open Scope string_scope.


(* IT LIVES *)

Ltac destruct2 x :=
  destruct x as [?x [?x ?x]].

(************************************************************************)
(**************** MESSING AROUND WITH VEC AHHHHHHHHHHHHH ****************)


Fixpoint append_vec {n m} (x : nat_vec n) (y : nat_vec m) : nat_vec (n + m) :=
  match x with
  | nil => y
  | cons n' v => (cons n' (append_vec v y))
  end.

Eval compute in append_vec (cons 4 (cons 5 nil)) (cons 9 nil).
  

Ltac vec_inv :=
  small_jail; match goal with 
  | [v : nat_vec ?a , n : ?b |- False ] => 
      match goal with 
      [H : ?v = ?a |- _ ] => (try inversion H; fail; clear H) 
      end
  end.

Notation " [[ TYPE ]] " :=
  {v >> TYPE} (at level 0, TYPE at next level).

(* hyperspecific notation for vec for now *)
Notation " {{ f { res } a1 a2 }} " :=
  match a1, a2 with 
  | Vec a v1, Vec b v2 => (Vec res (f v1 v2))
  | _r1, _r2 => False_rec _ _
  end (at level 0, f at next level, res at next level, a1 at next level, a2 at next level).

(* can't put program definition inside notation (since it's expecting a constructor/construct) *)
(* ltac won't work since it needs to produce tactics (hence the name) *)
(* idk lol *)

Program Definition append {n m} (x : [[ (trvec n) ]]) (y : [[ (trvec m) ]]) : [[ (trvec (n + m)) ]] :=
  {{ append_vec {(n + m)} x y }}.

  Next Obligation.
  inversion Heq_anonymous. inversion x0. subst *. inversion y0; auto. 
  Defined. Next Obligation. 
  specialize (n0 n3 n4 n1 n2). destruct n0; auto.
  #[local] Obligation Tactic := try vec_inv.
  Defined. 

Eval compute in append (cons 4 (cons 5 nil)) (cons 9 nil).
Eval compute in append (cons 4 (cons 5 nil)) (append (cons 9 nil) (cons 8 (cons 3 nil))).
(* Eval compute in append (cons 4 (cons 5 nil)) 6. *)

Definition head_vec {n} (x : nat_vec (S n)) : nat.
  inversion x. exact H0.
  
  Defined.
Print head_vec. 
Check eq_ind.
Eval compute in head_vec (cons 9 (cons 5 (cons 4 nil))).

(* taking the definition printed from head_vec, I simplified it down to this
   which was something I was trying to do anyway,  I was just using the wrong comparison 
   (I was trying to do nat_vec = nat_vec basically, which obviously won't work ))*)
(* the reason why you have to do it like this with the function is because this retains the info needed to 
   do the False_rec *)
Program Definition head_bruh (n : nat) (x : nat_vec (S n)) : nat :=
  (match x in (nat_vec n0) return (n0 = S n -> nat) with
    | nil => fun H : 0 = S n => False_rec _ _
    | @cons n0 x0 nv1 => fun H : S n0 = S n => x0
    end) eq_refl.

(* Eval compute in head nil. *) (* so this fails, as expected *)
Eval compute in head_bruh 2 (cons 9 (cons 5 (cons 4 nil))).

Notation " {{ f n x }} " :=
  match x with 
  | Vec a v => f n v
  | _r => False_rec _ _
  end (at level 0, f at next level, n at next level, x at next level).

Program Definition head {n} (x : [[ (trvec (S n)) ]]) : [[ trnum ]] :=
  {{ head_bruh n x }}.

  Next Obligation. new_jail. inversion x0; auto. 
  Defined. Next Obligation.
  small_jail. inversion x0. simpl in filtered_var.
  destruct x; try (inversion x0; fail).
  subst *.
  specialize (n0 (S n) nv). destruct n0. auto.
  Defined.

Eval compute in (head (cons 5 (cons 9 nil))).
(* Eval compute in (head nil). *)

Definition tail_vec {n} (x : nat_vec (S n)) : (nat_vec n).
  inversion x. 
  exact H1.
  Defined. 
  
Print tail_vec.
Eval compute in tail_vec (cons 8 (cons 9 (cons 5 (cons 4 nil)))).
Eval compute in tail_vec (cons 1000 nil).
(* Eval compute in tail_vec nil. *)

Program Definition tail_bruh (n : nat) (x : nat_vec (S n)) : (nat_vec n) :=
  (match x in (nat_vec n0) return (n0 = S n -> nat_vec n) with
    | nil => fun H : 0 = S n => False_rec _ _ 
    | @cons n0 x0 nv1 => fun H : S n0 = S n => nv1
    end) eq_refl.

Program Definition tail {n} (x : {v >> (trvec (S n))}) : {v >> (trvec n)} :=
  {{ tail_bruh n x }}.

  Next Obligation. new_jail. inversion x0; auto. 
  Defined. Next Obligation.
  small_jail. inversion x0. simpl in filtered_var.
  destruct x; try (inversion x0; fail).
  subst *. specialize (n0 (S n) nv). destruct n0. auto.
  Defined.

(* Eval compute in tail nil. *)
Eval compute in tail (cons 9 (cons 5 (cons 4 nil))).

(* i guess this is the unsafe rec version like in the paper *)
Fixpoint vec_ref1 {n} (x : nat_vec n) (m : nat) {P : m < n} : nat.
  inversion x.
  - rewrite <- H in P. exfalso. apply (Nat.nlt_0_r m). auto.
  - destruct m.
    + exact H.
    + specialize (vec_ref1 n0 H0 m). subst *.
      apply Arith_base.lt_S_n_stt in P. apply (vec_ref1 P).
Defined.

Print vec_ref1.
Check eq_rect.

Program Fixpoint vec_ref_bruh (n : nat) (x : nat_vec n) (m : nat) (P : m < n) : nat :=
  (match x in (nat_vec n0) return (n0 = n -> nat) with
  | nil => fun H : 0 = n => False_rec nat _
  | @cons n0 x0 nv1 => fun H : S n0 = n => 
                          match m with
                          | 0 => x0
                          | S m' => vec_ref_bruh _ nv1 m' _
                          end
  end) eq_refl.
  Next Obligation.
  intros; subst *; apply (Nat.nlt_0_r m). auto.
  Defined. Next Obligation.
  intros; subst *; apply Arith_base.lt_S_n_stt in P; auto.
  Defined.

Eval compute in vec_ref_bruh _ (cons 9 (cons 10 (cons 3 nil))) 0.
Eval compute in vec_ref_bruh _ (cons 9 (cons 10 (cons 3 nil))) 1.
Eval compute in vec_ref_bruh _  (cons 9 (cons 10 (cons 3 nil))) 2.
Eval compute in vec_ref_bruh _ (cons 9 (cons 10 (cons 3 nil))) 3. (* match _ with end is False *)
Eval compute in vec_ref_bruh _ nil 0.                             (* match _ with end is False *)
  

(* and this it the safe_rec that checks the type of a *)
Program Definition vec_ref2 {n} (m : {a | a < n }) (x : nat_vec n) : nat :=
  @vec_ref_bruh n x m _.
  Next Obligation. intros; destruct m as [?m ?m]; simpl; auto. Defined.

Program Definition vec_bruh_0 := vec_ref2 0 (cons 9 (cons 10 (cons 3 nil))).
Program Definition vec_bruh_1 := vec_ref2 1 (cons 9 (cons 10 (cons 3 nil))).
Program Definition vec_bruh_2 := vec_ref2 2 (cons 9 (cons 10 (cons 3 nil))).
Program Definition vec_bruh_3 := vec_ref2 3 (cons 9 (cons 10 (cons 3 nil))). Next Obligation. Admitted. (* so this fails because you can't prove the obligation *)
Program Definition vec_bruh_nil := vec_ref2 0 nil. Next Obligation. Admitted.

Eval compute in vec_bruh_0.
Eval compute in vec_bruh_1.
Eval compute in vec_bruh_2.
Eval compute in vec_bruh_3.
Eval compute in vec_bruh_nil.

(* trying some stuff *)
#[local] Obligation Tactic := try (intros; discriminate).
Program Definition gt_zero (x : [[ trnum ]]) : Prop :=
  match x with
  | Num n => 0 <= n
  | _r => False
  end.

Eval compute in gt_zero 7.

#[local] Obligation Tactic := try (intros; intro; simplify_hypothesis; discriminate).
Program Definition gt_tr2 (x : [[ trnum ]]) (y : [[trnum]]) : Prop :=
  match x, y with
  | Num n, Num m => n <= m
  | _r, _r2 => False
  end.

Program Definition gt_tr3 (x : [[ trnum ]]) (y : [[trnum]]) : Prop :=
  match x, y with
  | Num n, Num m => n < m
  | _r, _r2 => False
  end.

Eval compute in gt_tr3 5 7.

(* ok this intereferes with the other notation so i'll have to change this lol *)  
(* Notation "{ t >> T & T1 }" := 
    (sig (fun t : TRValues => (HasType t T) /\ T1 /\
                              (t <> Bool false -> True) /\ 
                              (t = Bool false -> True)))
    (at level 0, t at level 99, T at next level, T1 at next level). *)

#[local] Obligation Tactic := try fail.
Program Definition whaaaaat (x : {v >> trnum}) : {t >> trnum & (gt_tr2 0 x) & ~(gt_tr2 0 x)} :=
  x.
Next Obligation.
intros; simpl. repeat constructor; destruct2 x; simpl; auto. 
all : intros; destruct x; try inv_trtype_false; unfold gt_tr2; simpl. 
  - apply le_0_n.
  - intro. discriminate.
Defined.

Eval compute in whaaaaat 8.

(* maybe tactic that looks like typed racket program, and given that tactic generate a proof term 
  actually maybe not. *)

Close Scope string_scope.
(* this is horrible LOL *)
#[local] Obligation Tactic := try (start_jail; intro; simplify_hypothesis; discriminate).
Program Definition is_less_than (x : [[trnum]]) (y : [[trnum]])
  : {t >> trbool & (gt_tr3 x y) & ~(gt_tr3 x y)} :=
  match x, y with 
  | Num x', Num y' => Bool (x' <? y') 
  | _r1, _r2 => False_rec _ _ 
  end.
Next Obligation.
intros; simpl; repeat constructor; intro; subst *; unfold gt_tr3; rewrite <- Heq_x; rewrite <- Heq_y;
destruct2 x; destruct2 y; destruct x; try inv_trtype_false; destruct y; try inv_trtype_false; simpl in *.
  - apply Nat.ltb_lt. destruct (x' <? y'); auto.
  - intro. apply Nat.ltb_lt in H0. rewrite H0 in H; discriminate.
Defined. 
Next Obligation. new_jail. Defined.
Eval compute in is_less_than 10 3.

(* Program Definition test_gt (n1 : [[trnum]]) (n2 : {t >> trnum & (gt_tr3 t 5) & ~(gt_tr3 t 5)}) : [[trnum]] :=
  n2.
  Next Obligation.
intros; simpl. repeat constructor. Admitted. *)


(* Program Definition trvec_ref_tr {n} (x : [[ (trvec (S n)) ]]) (m : {t >> trnum & (gt_tr3 t (S n)) & ~(gt_tr3 t (S n))}) : [[ trnum ]] :=
  match x with 
  | Vec a v => match m with 
               | Num m' => vec_ref2 m' v
               | _r2 => False_rec _ _ 
               end
  | _r1 => False_rec _ _ 
  end.
  Next Obligation.             
intros. simpl in *. Admitted.
  Next Obligation.
intros. simpl. Admitted.
  Next Obligation.
  intros; simpl. subst *. destruct2 x; destruct2 m. 
  
  
  simpl in filtered_var.
  subst *. inversion x0. destruct m as [?m ?m]. simpl. auto.
  Defined. Next Obligation.
  small_jail. inversion x0. simpl in filtered_var.
  destruct x; try (inversion x0; fail).
  subst *. specialize (n0 (S n) nv). destruct n0. auto.
  Defined. *)



(* should this m be a trnum?  *)
Program Definition trvec_ref {n} (x : [[ (trvec (S n)) ]]) (m : {a | a < (S n) }) : [[ trnum ]] :=
  {{ vec_ref2 m x }}.

  Next Obligation.              (* doing destruct [?x [?x ?x]] is interferring with the notation LOL*)
  intros. simpl in *. destruct2 x. simpl in filtered_var.
  subst *. inversion x0. destruct m as [?m ?m]. simpl. auto.
  Defined. Next Obligation.
  small_jail. inversion x0. simpl in filtered_var.
  destruct x; try (inversion x0; fail).
  subst *. specialize (n0 (S n) nv). destruct n0. auto.
  Defined.

Program Definition trvectest1 := trvec_ref (cons 1 (cons 4 (cons 8 nil))) 2.
Next Obligation. simpl; auto. Defined.
Eval compute in trvectest1.
(* Program Definition trvec_false := trvec_ref 5 2. *)
(* Program Definition test1 := vec_ref2 nil 0. (* so this produces unprovable obligation *) *)
Program Definition test2 := trvec_ref (cons 1 nil) 0.
Next Obligation. simpl; auto. Defined.
Eval compute in test2.
Program Definition test3 := trvec_ref (cons 5 (cons 8 (cons 9 nil))) 1.
Next Obligation. simpl; auto. Defined.
Eval compute in test3.

(**************************************************************************************)
(**************************** DOT PRODUCT AHHHHHHHHHHHHHH *****************************)
Close Scope string_scope.
Lemma what_again : forall i n, (i <? n) = true -> i < n.
intros. apply Nat.ltb_lt; auto. Defined.

Lemma strictly_lessthan : forall (n : nat) (i : nat) (step : nat), 
    i < n + S step -> i < n -> n + S step - (i + S step) < n + S step - i.
Proof. 
  intros n i step H H3. 
  repeat rewrite <- plus_n_Sm. rewrite Nat.sub_succ.
      rewrite <- plus_n_Sm in H. rewrite (Nat.add_comm n step) in H.
      rewrite Nat.add_comm. rewrite (Nat.add_comm i step).
      rewrite <- Arith_base.minus_plus_simpl_l_reverse_stt.
      apply Arith_base.lt_n_Sm_le_stt in H.
      apply Arith_base.minus_Sn_m_stt in H.
      rewrite <- H.
      remember (n - i) as num. 
      apply Nat.lt_le_incl in H3.
      apply (Nat.add_sub_assoc step n _) in H3.
      rewrite <- H3. rewrite <- Heqnum.
      assert (H4 : num <= step + num) by (apply (Nat.le_add_l num step)).
      destruct step.
      + simpl; auto.
      + apply PeanoNat.le_lt_n_Sm; auto.
Defined.

(* can't use let to define sum and i since 1) no side-effects 2) wellfoundness is only with program fixpoint/Function, not fix *)
(* the variable in the article -- the variable here
    start                         no var, just 0
    step                          no var, just 1
    end                             n
    initial                       no var, just 0 
    pos                             i
    acc                            sum*)

(* adding step complicates the proof :( *)
Program Fixpoint dot_product (n : nat) (step : nat) (H2 : step > 0) (x : nat_vec n) (y : nat_vec n) (acc : nat) (i : nat) (H : i < (n + step)) {measure ((n + step) - i)} : nat :=
  match (i <? n) as M with
    | true => @dot_product n step _ x y (acc + ((vec_ref2 i x) * (vec_ref2 i y))) (i + step) _ _
    | false => acc
    end.
  Next Obligation.
  intros; simpl. auto.
  Defined. Next Obligation.
  intros; simpl. subst *. apply what_again; auto.
  Defined. Next Obligation.
  intros; simpl.  subst *. apply what_again; auto.
  Defined. Next Obligation.
  intros; subst *. assert (H3 : i < n) by (apply what_again; auto). 
  apply Arith_base.add_lt_mono_r_proj_l2r; auto.
  Defined. Next Obligation.
  intros; subst *. assert (H3 : i < n) by (apply what_again; auto).
  destruct step. 
    - exfalso; inversion H2.
    - apply strictly_lessthan; auto.
  Defined. Next Obligation.
  simpl; apply measure_wf. apply Wf_nat.well_founded_ltof. (* the wellfounded lt from Nat is opaque!!!! *)
  Defined.

#[local] Obligation Tactic := try try vec_inv; try (intros; subst *; apply (Nat.lt_0_succ _)).
Program Definition dot_prod_bruh_test1 := 
    let len := 1 in 
      let initial := 0 in 
        let start := 0 in 
          let step := 1 in 
            dot_product len step _ (cons 4 nil) (cons 1 nil) initial start _. 
Eval compute in dot_prod_bruh_test1.
Program Definition dot_prod_bruh_test2 := 
  let len := 2 in 
      let initial := 0 in 
        let start := 0 in 
          let step := 2 in 
            dot_product len step _ (cons 3 (cons 9 nil)) (cons 2 (cons 6 nil)) initial start _. 
Eval compute in dot_prod_bruh_test2.


(* should this n be trnum as well *)
(* also should the types of trnum also try to hold like (0 < step) in side of P *)
Program Definition dot_prod_what_tr (n : nat) (step : [[ trnum ]]) (x : [[ (trvec n) ]]) (y : [[ (trvec n) ]])  (acc : [[ trnum ]]) (i : [[ trnum ]])
   : [[ trnum ]] :=
   (* i don't want to do this, but for some reason it was setting everything to i lol *)
   match step with 
   | Num step' => 
    match x, y with 
    | Vec a v1, Vec b v2 => 
      match acc with 
      | Num acc' => 
        match i with 
        | Num i' => 
          match (andb (i' <? (n + step')) (0 <? step')) as M with 
          | true => dot_product n step' _ v1 v2 acc' i' _
          | false => 0 (* if I do False_rec here theres no way to actually prove a False hypothesis unless i give those proofs as well *)
          end
        | _r => False_rec _ _
        end
      | _r => False_rec _ _
      end
    | _r1, _r2 => False_rec _ _
    end
   | _r => False_rec _ _
   end.
   (*match step, x, y, acc, i with 
   |  (Num step'), (Vec a v1), (Vec b v2), (Num acc'), (Num i') => 
    match (andb (i' <? (n + step')) (0 <? step')) as M with 
      | true => dot_product n step' _ v1 v2 acc' i' _
      | false => False_rec _ _
      end
   | _r0, _r1, _r2, _r3, _r4 => False_rec _ _ 
   end.*)
  Next Obligation.
  intros. subst *. apply andb_true_eq in Heq_M. destruct Heq_M.
  apply eq_sym in H0. apply what_again in H0. auto.
  Defined. Next Obligation.
  intros. subst *. destruct2 x. simpl in Heq_x.
  rewrite <- Heq_x in x0. inversion x0; auto.
  Defined. Next Obligation.
  intros. subst *. destruct2 y. simpl in Heq_y.
  rewrite <- Heq_y in y0. inversion y0; auto.
  Defined. Next Obligation.
  intros. subst *. apply andb_true_eq in Heq_M. destruct Heq_M.
  apply eq_sym in H. apply what_again in H. auto.
  Defined. Next Obligation.
  intros. try new_jail.
  Defined. Next Obligation.
  try new_jail.
  Defined. Next Obligation.
  intros. destruct2 x; destruct2 y; simpl in *.
  inversion x0; inversion y0.
  specialize (n0 n1 nv n2 nv1); destruct n0; subst *; auto.
  Defined. Next Obligation.
  try new_jail.
  #[local] Obligation Tactic := try (intros; discriminate).
  Defined.



(* 1. write notation to hide the unused things (like the _ in the signature) and to hide the match 
   2. write another definition of dotproduct to use all trvalue inputs *)
Program Definition dot_prod_tr {n} (x : [[ (trvec n) ]]) (y : [[ (trvec n) ]]) : [[ trnum ]] :=
  match x, y with 
  | Vec _ nv1, Vec _ nv2 => 
    let len := n in (* end is not allowed to be a name sad times *)
      let initial := 0 in 
        let start := 0 in 
          let step := 1 in 
            let loop := dot_prod_what_tr len step x y in 
              loop initial start
  | _r1, _r2 => False_rec _ _
  end.
  Next Obligation.
  intros. destruct2 x; destruct2 y; simpl in *.
  inversion x0; inversion y0.
  specialize (n0 n1 nv n2 nv1); destruct n0; subst *; auto.
  #[local] Obligation Tactic := try vec_inv.
  Defined.

Eval compute in dot_prod_tr (cons 10 (cons 5 (cons 2 nil))) (cons 3 (cons 6 (cons 9 nil))).
Eval compute in dot_prod_tr nil nil.
(* Eval compute in dot_prod_tr 5 (cons 3 nil). *)

Program Fixpoint vec_product {n} (res : nat) (i : nat) (x : nat_vec n) (H : i <= n) {measure i} : nat :=
  match i with 
  | 0 => res                                (* i doesn't make sense here?*)
  | S i' => (@vec_product _ (res * (vec_ref2 i' x)) i' x _ _)
  end.
  Next Obligation.
  intros. apply Nat.le_lteq. constructor 1. rewrite <- Heq_i in H.
  specialize (PeanoNat.le_lt_n_Sm _ _ H); intros. apply (PeanoNat.lt_S_n _ _ H0).
  Defined. Next Obligation.
  simpl; apply measure_wf. apply Wf_nat.well_founded_ltof.
  Defined.

Program Definition vec_product_test1 := vec_product 1 5 (cons 5 (cons 4 (cons 3 (cons 2 (cons 1 nil))))) _.
Eval compute in vec_product_test1. 
(* Program Definition vec_product_test_bad := @vec_product _ 1 6 _ (cons 5 (cons 4 (cons 3 (cons 2 (cons 1 nil))))). (* produces unsolvable obligation*) *)

Program Definition vec_product_tr {n} (x : {v1 >> (trvec n)}) : {n >> trnum} :=
  match x with 
  | Vec m1 nv1 => vec_product 1 m1 nv1 _
  | _r1 => False_rec _ _
  end.
  Next Obligation.
  intros. destruct2 x. destruct x; try (inversion x0; fail).
  simpl in *. specialize (n0 n1 n2). destruct n0; auto.
  Defined.

Eval compute in vec_product_tr (cons 5 (cons 4 (cons 3 (cons 2 (cons 1 nil))))).
(* Eval compute in vec_product_tr 5. *)

(* lol i guess this is actually unit *)
Program Definition vec_set {n} (x : nat_vec n) (i : nat) (H : i < n) : Void_ := void.


Program Definition vec_swap {l} (x : nat_vec l) (i j : nat) (H : i < l)  (H': j < l) : Void_ :=
  match (i =? j) as L with
  | true => void
  | false => 
    let i_val := (vec_ref2 i x) in 
      let j_val := (vec_ref2 j x) in 
        let swap1 := (vec_set x i _) in 
          vec_set x j _
  end.

Program Definition vec_swap_tr {n} (x : {v1 >> (trvec n)}) (i : {a | a < n }) (j : {a | a < n }) : {v >> trvoid} :=
  match x with 
  | Vec m1 nv1 => vec_swap nv1 i j _ _
  | _r => False_rec _ _
  end.
  Next Obligation.
  intros.
  destruct i as [?i ?i]; simpl in *; subst *; 
  destruct j as [?j ?j]; simpl in *; subst *;
  destruct2 x; simpl in *; subst *.
  inversion x0. auto.
  Defined. Next Obligation.

  intros; 
  destruct i as [?i ?i]; simpl in *; subst *; 
  destruct j as [?j ?j]; simpl in *; subst *;
  destruct2 x; simpl in *; subst *.
  inversion x0; auto.
  Defined. Next Obligation.
  intros; destruct2 x; simpl in *; subst *; inversion x0; auto.
  subst *. specialize (n0 n nv). destruct n0; auto.
  Defined.