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

Program Definition test_gt (n1 : [[trnum]]) (n2 : {t >> trnum & (gt_tr3 t 5) & ~(gt_tr3 t 5)}) : [[trnum]] :=
  n2.
  Next Obligation.
  intros; simpl. repeat constructor.


Program Definition trvec_ref_tr {n} (x : [[ (trvec (S n)) ]]) (m : {t >> trnum & (gt_tr3 t (S n)) & ~(gt_tr3 t (S n))}) : [[ trnum ]] :=
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
  Defined.



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
Eval compute in trvectest1.
(* Program Definition trvec_false := trvec_ref 5 2. *)
(* Program Definition test1 := vec_ref2 nil 0. (* so this produces unprovable obligation *) *)
Program Definition test2 := trvec_ref (cons 1 nil) 0.
Eval compute in test2.
Program Definition test3 := trvec_ref (cons 5 (cons 8 (cons 9 nil))) 1.
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
  intros; simpl. subst *. apply what_again; auto.
  Defined. Next Obligation.
  intros; simpl. subst *. apply what_again; auto.
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


(************************************************************************)
(********************** IF AGAIN AHHHHHHHHHHHHHHHH **********************)
 
#[local] Obligation Tactic := try new_jail.
Open Scope string_scope.

Program Definition if_ex1 {t : TRTypes} (x : {v >> t}) : {v >> trnum}:=
  ifTR_v2 (is_number x) (add1 x) 0.
  

Eval compute in if_ex1 5.
Eval compute in if_ex1 "5".

Program Definition if_ex2 (x : {v >> (trunion trstr trnum)}) : {v >> trnum} :=
  ifTR_v2 (is_number x) (add1 x) (strlen x).

 Set Printing Implicit.
  Set Printing Depth 100.
  Print if_ex2.

(* has to use <[]> here since the coercion is only for trstr:( *)
(* ok i think we can't use coercions here bc going from tr__ to trunion requires solving ~something~ *)
Program Definition if_ex2_test1 := if_ex2 <["hi"]>.
Program Definition if_ex2_test2 := if_ex2 <[ 9 ]>.

Eval compute in if_ex2_test1.
Eval compute in if_ex2_test2.

Program Definition if_exWhat (x : {v >> (trunion trstr trnum)}) : {v >> trnum} :=
  ifTR_v2 (is_number x) (add1 x) 4.


Program Definition if_orTest2 {t : TRTypes} (x : {v >> t}) :=
  (orTR_v2 (is_number x) (is_string x)).

  
  Eval compute in if_orTest2 5.
Set Ltac Profiling.

(* trying to use orTR_v2 seems to complicate this more due to the "different" output props, so 
   I'm just using orTR due to the two outputs having the same props *)
Program Definition if_ex4 {t : TRTypes} (x : {v >> t}) : {v >> trnum} :=
  ifTR_v2
       (orTR (is_number x) (is_string x))
       (if_exWhat x)
       0.

Eval compute in if_ex4 9.
Eval compute in if_ex4 "hi".
Eval compute in if_ex4 true.

Program Definition if_ex5 {t r : TRTypes} (x : {v >> t}) (y : {w >> r}) : {v >> trnum} :=
  ifTR_v2  (andTR (is_number x) (is_string y))
           (add_ x (strlen y))
           0.
Eval compute in if_ex5 5 "hi".
Eval compute in if_ex5 5 8.
Eval compute in if_ex5 "hello" 10.
Eval compute in if_ex5 true false.

Program Definition if_ex10 {A B : TRTypes} (p : {v >> (trpair A B)}) : {t >> trnum} :=
  ifTR_v2 (is_number (car p)) (add1 (car p)) 7.

Eval compute in if_ex10 (5, "bye").
Eval compute in if_ex10 (false, 10).

Program Definition if_more_ex3_1 {t : TRTypes} (x : {v >> t}) : {v >> trnum} :=
  ifTR_v2 (is_number x) x 54.


(* #[local] Obligation Tactic := try fail. *)
Program Definition if_more_ex1 {t r : TRTypes} (x : {v >> t}) (y : {w >> r}) 
         : {v >> trbool & 
                 ((HasType x trnum) /\ (HasType y trstr) \/ (HasType x trstr)) & 
                 (~(((HasType x trnum) /\ (HasType y trstr) \/ (HasType x trstr))))} :=
  (ifTR_v2 < all > (is_number x) (is_string y) (is_string x)).
(*Next Obligation. new_jail. Defined.
  Next Obligation. new_jail. Defined.
  Next Obligation. Reset Ltac Profile. new_jail. Show Ltac Profile. Defined.
  (* i think this has to destruct a lot, because most of the calls aren't taking too long,
    i wonder where the 0.6s are going *)
*)
Program Definition if_more_ex3 {t r : TRTypes} (x : {v >> t}) (y : {w >> r}) : {v >> trnum} :=
(ifTR_v2 (if_more_ex1 x y) 
  (ifTR_v2 (is_string x) (strlen x) (add_ x (strlen y)))
  (ifTR_v2 (is_number x) x 54)).
  (* Next Obligation. new_jail. Defined.
  Next Obligation. new_jail. Defined.
  Next Obligation. new_jail. Defined.
  Next Obligation. Reset Ltac Profile. new_jail. Show Ltac Profile. Defined.
  (* the 5 calls to x x0 are from destructing x x0 in each case after destruct y y0,
    which is why this only occurs once
    simpl in * is taking the most time (actually practically all of the time) in do_it
    destructing take half the time of pls_destruct_correctly, so where is 0.4s going?
    and there is 0.2-ish seconds of break_jail that is unaccounted for *)
  (* same slowdown as above, ok a lot faster after getting rid of most simpl in *; subst calls *)
*)
(* #[local] Obligation Tactic := try new_jail. *)

(************************************************************************)
(********************** EXAMPLE 1 AHHHHHHHHHHHHHHH **********************)
Program Definition ex1 {t : TRTypes} (x : {v >> t}) : {v >> trnum}:=
  ifTR (is_number x) (add1 x) 0.

(************************************************************************)
(********************** EXAMPLE 2 AHHHHHHHHHHHHHHH **********************)

Program Definition ex2 (x : {v >> (trunion trstr trnum)}) : {v >> trnum} :=
  ifTR (is_number x) (add1 x) (strlen x). 

Program Definition ex2_test1 := ex2 <[ "hi" ]>.
Program Definition ex2_test2 := ex2 <[ 9 ]>. 

Eval compute in ex2_test1.
Eval compute in ex2_test2.

(************************************************************************)
(********************** EXAMPLE 4 AHHHHHHHHHHHHHHH **********************)

Program Definition ex4 {t : TRTypes} (x : {v >> t}) : {v >> trnum} :=
  ifTR (orTR (is_number x) (is_string x))
       (ex2 x)
       0.
  
Eval compute in ex4 9.
Eval compute in ex4 "hi".
Eval compute in ex4 true.

(************************************************************************)
(********************** EXAMPLE 5 AHHHHHHHHHHHHHHH **********************)

Program Definition ex5 {t r : TRTypes} (x : {v >> t}) (y : {w >> r}) : {v >> trnum} :=
  ifTR  (andTR (is_number x) (is_string y))
           (add_ x (strlen y))
           0.

Eval compute in ex5 5 "hi".
Eval compute in ex5 5 8.
Eval compute in ex5 "hello" 10.
Eval compute in ex5 true false.

(************************************************************************)
(********************** EXAMPLE 7 AHHHHHHHHHHHHHHH **********************)

Program Definition ex7 {t r : TRTypes} (x : {v >> t}) (y : {w >> r}) : {v >> trnum} :=
  (ifTR 
    (ifTR < second > (is_number x) (is_string y) false)
    (add_ x (strlen y))
    0).

Eval compute in ex7 6 "hello".

(************************************************************************)
(********************** EXAMPLE 8 AHHHHHHHHHHHHHHH **********************)

Program Definition ex8 {t : TRTypes} (x : {v >> t}) :=
  orTest x.

Program Definition ex8_test {t : TRTypes} (x : {v >> t}) : {v >> trnum} :=
  (ifTR (ex8 x) (ex2 x) 0).

Eval compute in ex8 6.
Eval compute in ex8_test 6.
Eval compute in ex8 "potatoes".
Eval compute in ex8_test "potatoes".
Eval compute in ex8 true.
Eval compute in ex8_test true.

(************************************************************************)
(********************** EXAMPLE 9 AHHHHHHHHHHHHHHH **********************)

Program Definition ex9 {t : TRTypes} (x : {v >> t}) : {v >> trnum} :=
  (ifTR 
    (let p := (is_number x) in 
      (ifTR < third > p p (is_string x)))
    (ex2 x) 
    0).

Eval compute in ex9 2.

(************************************************************************)
(********************** EXAMPLE 10 AHHHHHHHHHHHHHH **********************)

Program Definition ex10 {A B : TRTypes} (p : {v >> (trpair A B)}) : {t >> trnum} :=
  ifTR (is_number (car p)) (add1 (car p)) 7.

Eval compute in ex10 (5, "bye").
Eval compute in ex10 (false, 10).

(************************************************************************)
(********************** EXAMPLE 11 AHHHHHHHHHHHHHH **********************)

Program Definition g (p : {v >> trpair trnum trnum}) : {t >> trnum} :=
  (add_ (car p) (cdr p)).

Eval compute in g (4, 5). 

(* instead of returning 'no, i'll return 0 *)
Program Definition ex11 {A B : TRTypes} (p : {v >> trpair A B}) : {t >> trnum} :=
  ifTR (andTR (is_number (car p)) (is_number (cdr p))) (g p) 0.
  
Eval compute in ex11 (4, 12).
Eval compute in ex11 (3, false).

(************************************************************************)
(********************** EXAMPLE 12 AHHHHHHHHHHHHHH **********************)

(* back to the scheduled programming *)
Program Definition ex12 {A B : TRTypes} (p : {v >> trpair A B}) : 
  {t >> trbool & (HasType p (trpair trnum B)) & (~ (HasType p (trpair trnum B)))} :=
  (is_number (car p)).
  
  
Program Definition ex12_again {A B : TRTypes} (p : {v >> trpair A B}) : 
{t >> trbool & (HasType (car p) trnum) & (~ (HasType (car p) trnum))} :=
  (is_number (car p)).

Eval compute in ex12 (4, true).
Eval compute in ex12 ("hi", 1).

(************************************************************************)
(********************** EXAMPLE 13/14 AHHHHHHHHHHH **********************)

Program Definition ex13_14 
    (x : {v >> trunion trnum trstr}) 
    (y : {v >> trpair trtop trtop}) :
    {t >> trnum} :=
  condTR [ (andTR (is_number x) (is_number (car y))) (add_ x (car y)) ] 
         [ (is_number (car y)) (add_ (strlen x) (car y)) ] 
         [ else 0].

Program Definition ex_13_14_use := ex13_14 <[14]>  (14, "hello").

Eval compute in ex_13_14_use.

(************************************************************************)
(********************** MORE EXAMPLES AHHHHHHHHHHH **********************)

Program Definition more_ex1 {t r : TRTypes} (x : {v >> t}) (y : {w >> r}) 
         : {v >> trbool & 
                 ((HasType x trnum) /\ (HasType y trstr) \/ (HasType x trstr)) & 
                 (~(((HasType x trnum) /\ (HasType y trstr) \/ (HasType x trstr))))} :=
  (ifTR < all > (is_number x) (is_string y) (is_string x)).

Program Definition more_ex1_use := more_ex1 5 "hello".
Eval compute in more_ex1_use. 

Program Definition more_ex2 {t r : TRTypes} (x : {v >> t}) (y : {w >> r}) : {v >> trnum} :=
  (ifTR (more_ex1 x y) 
    (ifTR (is_string x) (strlen x) (add_ x (strlen y)))
    42).

Program Definition more_ex3 {t r : TRTypes} (x : {v >> t}) (y : {w >> r}) : {v >> trnum} :=
  (ifTR (more_ex1 x y) 
    (ifTR (is_string x) (strlen x) (add_ x (strlen y)))
    (ifTR (is_number x) (add1 x) 54)). 

(************************************************************************)
(********************** EXAMPLES NOT AHHHHHHHHHHHHHHH *******************)
Program Definition not_ex1 {t : TRTypes} (x : {v >> t}) : {v >> trnum} :=
  (ifTR (notTR (notTR (is_number x))) (add1 x) 42).

Eval compute in (not_ex1 5).
Eval compute in (not_ex1 "hi").

Program Definition not_ex2 {t : TRTypes} (x : {v >> t}) : {v >> trnum} :=
  (ifTR (notTR (is_number x)) 
      (ifTR (is_string x) (strlen x) 13)
      42).

Eval compute in (not_ex2 5).
Eval compute in (not_ex2 "hi").
Eval compute in (not_ex2 true).

(************************************************************************)
(****************** LET EXAMPLES???????????????? AHHHHHHHH **************)

Program Definition let_ex1 {t : TRTypes} (x : {v >> t}) : {x >> trnum} :=
  let p := (is_number x) in
    (ifTR_v2 p (add1 x) 0).
  #[local] Obligation Tactic := try fail.
  (* look at refl in the textbook from last semester *)
  Next Obligation.
    start_jail; conclusion_jail; simplify_hypothesis; try unfold_jail; auto;
    pls_destruct_correctly; do_it;
    assert (H : Bool true <> Bool false) by (intro; discriminate);
    try (destruct b; simpl; try constructor; exfalso; pose proof (p1 H); inv_trtype_false).
  Defined.

Eval compute in (let_ex1 9).
Eval compute in (let_ex1 "hi").

#[local] Obligation Tactic := try new_jail.
(************************************************************************)
(****************** EXAMPLES FROM IF-T BENCHMARK AHHHHHHHH **************)
Program Definition car_add {t r : TRTypes} (p : {v >> (trpair t r)}) : {v >> trnum} :=
(ifTR_v2 (is_number (car p)) (add1 (car p)) 0).

Eval compute in (car_add ("hi", 9)).
Eval compute in (car_add (18, 4)).

(* just write your own lol *)
Program Definition pos_success {t : TRTypes} (x : {v >> t}) : {v >> trtop} :=
  (ifTR_v2 (is_string x) (strlen x) x).
Eval compute in (pos_success "potatoes").
Eval compute in (pos_success 8).
Eval compute in (pos_success true).
Eval compute in (pos_success ("hi", false)).

(* this doesn't directly fail, but it generates unsolvable obligations
Program Definition pos_fail {t : TRTypes} (x : {v >> t}) : {v >> trtop} :=
  (ifTR_v2 (is_string x) (add1 x) x). *)
  (* maybe find a way to should that this will fail? *)

Program Definition neg_success (x : {v >> trunion trstr trnum}) : {v >> trnum} :=
  (ifTR_v2 (is_string x) (strlen x) (add1 x)).

Program Definition neg_succ_test1 := (neg_success <["hi"]>).
Program Definition neg_succ_test2 := (neg_success <[7]>).

Eval compute in neg_succ_test1.
Eval compute in neg_succ_test2.


(* same as above, the obligations are unsolvable. If you put 0 instead of add1 x, it gets defined
Program Definition neg_fail (x : {v >> trunion trstr (trunion trnum trbool)}) : {v >> trnum} :=
  (ifTR_v2 (is_string x) (strlen x) (add1 x)). *)

Program Definition f (x : {v >> trunion trstr trnum}) : {v >> trnum} :=
  ifTR_v2 (notTR (is_number x)) (strlen x) 0.

Program Definition g2 (x : {v >> trtop}) : {v >> trnum} :=
  ifTR_v2 (orTR (is_number x) (is_string x))
          (f x)
          0.

Program Definition g2_test1 := g2 <[5]>.
Program Definition g2_test2 := g2 <["potatoes"]>.
Program Definition g2_test3 := g2 <[false]>.

Eval compute in g2_test1.
Eval compute in g2_test2.
Eval compute in g2_test3.

Program Definition h (x : {v >> trunion trstr (trunion trnum trbool)}) : {v >> trnum} :=
  ifTR_v2 (andTR (notTR (is_bool x)) (notTR (is_number x)))
          (strlen x)
          0.
  Next Obligation.
  destruct n. intro. inv_trtype_false.
  Defined. (* ok i'm assuming it takes a long time to define bc it's trying to resolve the remaining obligations *)


Program Definition h_test1 := h <["potatoes"]>.
Program Definition h_test2 := h <[5]>.
Program Definition h_test3 := h <[Bool false]>.

Eval compute in h_test1.
Eval compute in h_test2.
Eval compute in h_test3.

Program Definition f2 (x : {v >> trunion trstr (trunion trnum trbool)}) : {v >> trnum} :=
  ifTR_v2 (notTR (is_string x))
          (ifTR_v2 (notTR (is_bool x))
                   (add1 x)
                   0)
          0.
  #[local] Obligation Tactic := try fail.
  Next Obligation. (* i basically need to deal with nested trunions and ~ better *)
  start_jail. simpl in *. repeat split. 
  inversion x0; subst *. try (destruct n; auto).
  inversion H1; subst *; auto. destruct n0; auto.
  Defined.
  Next Obligation.
  new_jail.
  Defined.   

  #[local] Obligation Tactic := try new_jail.
  Program Definition f2_test1 := f2 <[5]>.
  Program Definition f2_test2 := f2 <["hi"]>.
  Program Definition f2_test3 := f2 <[true]>.

  Eval compute in f2_test1.
  Eval compute in f2_test2.
  Eval compute in f2_test3.

(************************************************************************)
(******************* RANDOM STUFF WE HAVE TRIED TO DO *******************)

(* trying to do something but failing spectacularly *)
Lemma ok : True.
Proof. auto. Qed.

Lemma wtf2 : HasType (Num 5) trnum.
Proof. constructor. Qed.

Program Definition what {p3 p4 : TRValues} {A B : TRTypes} : HasType (Pair p3 p4) (trpair A B) /\ ((Pair p3 p4) <> Bool false -> True) /\
  ((Pair p3 p4) = Bool false -> True).
Proof. repeat split; auto. Admitted. (* i don't think we can prove this? *)

Program Definition what2 {t1 : TRValues} {A : TRTypes} : HasType t1 A /\ (t1 <> Bool false -> True) /\
  (t1 = Bool false -> True).
Proof. repeat split; auto. Admitted. (* same with this *)


(* Disable Notation "[ e ]" := (exist _ e _). *)
Check what.

Lemma trying_prequel : forall (p3 : TRValues), 
  proj1_sig (exist (fun _ => True) p3 ok) = p3.
  Proof. intros; simpl; auto. Defined.

Lemma trying : forall (p1 p2 : TRValues) (A B : TRTypes), 
  HasType p1 A -> HasType p2 B -> 
  proj1_sig (car (exist (fun x => (HasType x (trpair A B)) /\ 
                    (x <> Bool false -> True) /\
                    (x = Bool false -> True)) 
          (Pair p1 p2) 
          what)) = 
          p1.
  Proof. intros. simpl; auto. Defined.
(* this does work, but i don't know if it's useful *)
(* but this doesn't work when we don't have proj1_sig like [p3] = [p3] 
bc they have different proofs that can't compute to the same thing*)

Check car.

Lemma trying_pt2 : forall (P Q : Prop) (p1 p2 : TRValues) (A B : TRTypes) Z W, 
  HasType p1 A -> HasType p2 B -> 
 proj1_sig (car (exist (fun x => (HasType x (trpair A B)) /\ (x <> Bool false -> P) /\ (x = Bool false -> Q)) 
          (Pair p1 p2) 
             Z)) = 
      proj1_sig (exist (fun x => (HasType x A /\(x <> Bool false -> True) /\ (x = Bool false -> True)) )
          p1
             W).
  Proof. intros. unfold car. destruct p1; simpl; auto. Qed.

    (*
Lemma trying_pt3 : forall  (p1 p2 : TRValues) (A B : TRTypes), 
  HasType p1 A -> HasType p2 B -> 
 proj1_sig (car (giveType(Pair p1 p2))) = proj1_sig [p1].
  Proof. intros. unfold car. destruct p1; simpl; auto. Qed.

    unfold car. simpl.
  
  Admitted.
  (* i think the implicit parameters of what are causing a problem, which is not surprising i guess *)
*)

Lemma want : forall T A B  (p  q : T) P Q, p = q ->
 proj1_sig (exist A p P) = proj1_sig (exist B q Q).
 Proof. 
  intros.
 simpl.
 auto.
Qed.

(* i forgot what we wanted to do with this *)

Lemma is_num_type: (forall T P Q (W : {v >> T & P & Q}), HasType (@proj1_sig TRValues (fun t : TRValues =>
HasType t trbool /\
(t <> Bool false -> (HasType (proj1_sig W) trnum)) /\
(t = Bool false -> ~(HasType (proj1_sig W) trnum))) (@is_number _ _ _  W)) trbool).
Proof. intros. destruct W; destruct x; simpl; constructor. Qed.

Lemma test : forall T P Q (x : { v >> T & P & Q }), HasType (proj1_sig (is_number x)) trbool.
Proof. apply is_num_type. Defined.

(* hehe *)