(* 
From TRresearch Require Import Functions.
From TRresearch Require Import Tactic_jail.
From TRresearch Require Import Definitions.
From TRresearch Require Import VectorExamples.
From TRresearch Require Import VectorExamples_dotproduct.
Require Import String.
Require Import Bool.
Require Import Program.Tactics.
Require Import Init.Nat.
Require Import PeanoNat.
Require Import Program.Wf.
#[local] Obligation Tactic := try new_jail.
Open Scope string_scope.
Open Scope TR_scope.


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

(* Lemma trying : forall (p1 p2 : TRValues) (A B : TRTypes), 
  HasType p1 A -> HasType p2 B -> 
  proj1_sig (car (exist (fun x => (HasType x (trpair A B)) /\ 
                    (x <> Bool false -> True) /\
                    (x = Bool false -> True)) 
          (Pair p1 p2) 
          what)) = 
          p1.
  Proof. intros. simpl; auto. Defined. *)
(* this does work, but i don't know if it's useful *)
(* but this doesn't work when we don't have proj1_sig like [p3] = [p3] 
bc they have different proofs that can't compute to the same thing*)

Check car.

(* Lemma trying_pt2 : forall (P Q : Prop) (p1 p2 : TRValues) (A B : TRTypes) Z W, 
  HasType p1 A -> HasType p2 B -> 
 proj1_sig (car (exist (fun x => (HasType x (trpair A B)) /\ (x <> Bool false -> P) /\ (x = Bool false -> Q)) 
          (Pair p1 p2) 
             Z)) = 
      proj1_sig (exist (fun x => (HasType x A /\(x <> Bool false -> True) /\ (x = Bool false -> True)) )
          p1
             W).
  Proof. intros. unfold car. destruct p1; simpl; auto. Qed.
*)
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

(* Lemma is_num_type: (forall T P Q (W : {v >> T & P & Q}), HasType (@proj1_sig TRValues (fun t : TRValues =>
HasType t trbool /\
(t <> Bool false -> (HasType (proj1_sig W) trnum)) /\
(t = Bool false -> ~(HasType (proj1_sig W) trnum))) (@is_number _ _ _  W)) trbool).
Proof. intros. destruct W; destruct x; simpl; constructor. Qed.

Lemma test : forall T P Q (x : { v >> T & P & Q }), HasType (proj1_sig (is_number x)) trbool.
Proof. apply is_num_type. Defined. *)

Program Definition trvec_ref_tr {n} (x : { (trvec n) }) (m : {t >> trnum & ((less_than_equal 0 t) /\ (less_than t n)) & True}) : { trnum } :=
  match x with 
  | Vec a v => match m with 
               | Num m' => vec_ref_safe m' v
               | _r2 => False_rec _ _ 
               end
  | _r1 => False_rec _ _ 
  end.
Next Obligation. 
  intros; simpl. destruct2 m; simpl in *. (* ok actually I think this might work :) *)
  destruct2 x; simpl in *; subst *.
  destruct m1.
  assert (H3 : HasType (Num m') trnum /\ (Num m') <> (Bool false)).
    - split; auto. intro; discriminate.
    - specialize (H H3). destruct H. inversion H1. unfold ltTR in *. simpl in *.
      inversion x0; split; auto. apply le_0_n.
  Defined. Next Obligation.
  new_jail.
  Defined. Next Obligation.
  intros. destruct2 x. inversion x0. specialize (n0 n1 nv). simpl in filtered_var; subst *. destruct n0; auto.
Defined.

Definition vec_ref0 {n} (v : nat_vec n) (i : nat) : option nat :=
  if (andb (0 <=? i) (i <=? (n - 1)))
    then vec_unsafe_ref v i 
    else None.
  


Program Definition what : forall (n : nat) (m : {a : nat | 0 <= a < n}) (x : nat_vec n),
let filtered_var := vec_unsafe_ref x (proj1_sig m) in
None = filtered_var -> False.
intros; simpl. subst filtered_var. induction x.
  - destruct m. destruct a. apply (PeanoNat.Nat.nlt_0_r x); auto.
  - induction m. destruct x0; destruct p; simpl in H. inversion H.
    apply PeanoNat.lt_S_n in l0.
    assert (H4: 0 <= x0 < n).
    + constructor; auto. apply (PeanoNat.Nat.le_0_l x0).
    + specialize (IHx (exist (fun a => 0 <= a < n) x0 H4)) as J. simpl in J. 
      eauto.
Defined.


(* and this it the safe_rec that checks the type of a *)
Program Definition vec_ref_safe {n} (m : {a | ((0 <= a) /\ (a < n)) }) (x : nat_vec n) : nat :=
  match vec_unsafe_ref x m with (* this is the define *)
  | None => False_rec _ _ (* this case is error will never occur *)
  | Some res => res
  end.
Next Obligation.
  apply what.
Defined.

Program Definition vec_ref_safe_0 := vec_ref_safe 0 (cons 9 (cons 10 (cons 3 nil))).
Program Definition vec_ref_safe_1 := vec_ref_safe 1 (cons 9 (cons 10 (cons 3 nil))).
Program Definition vec_ref_safe_2 := vec_ref_safe 2 (cons 9 (cons 10 (cons 3 nil))).
(* the next two tests "fail" in that you can't prove the obligation generated by (a < n) (3 < 3, 0 < 0) *)
Program Definition vec_ref_safe_fail := vec_ref_safe 3 (cons 9 (cons 10 (cons 3 nil))). Next Obligation. simpl; split; auto. Admitted. 
Program Definition vec_ref_safe_nil := vec_ref_safe 0 nil. Next Obligation. simpl; split; auto. Admitted.

Eval compute in vec_ref_safe_0.
Eval compute in vec_ref_safe_1.
Eval compute in vec_ref_safe_2.
(* these are left with partial terms waiting for the unsolvable obligations *)
Eval compute in vec_ref_safe_fail.
Eval compute in vec_ref_safe_nil.

#[local] Obligation Tactic := try new_jail; try inversion H. (* lmao *)
Program Definition sucTR (x : {trnum}) : {trnum} := 
  match x with 
  | Num n => Num (S n)
  | _r => False_rec _ _ 
  end.

Eval compute in sucTR 5.

Inductive leTR_2 (x : {trnum}) : { t >> trnum & True & True } -> Prop :=
  | leTR_n : leTR_2 x x 
  | leTR_s : forall (m : {trnum}), leTR_2 x m -> leTR_2 x (sucTR m).

Eval compute in leTR_2 2 0.

Definition ltTR_2 (n m : {trnum}) : Prop := leTR_2 (sucTR n) m.

Eval compute in ltTR_2 3 4.

(* "well here is something that used to work and is now giving an uncaught exception"*)
#[local] Obligation Tactic := try fail.
Program Definition whaaaaat (x : { trnum }) : { >> trnum & (leTR 0 x) & True } :=
  x.
Next Obligation.
  intros; simpl. repeat constructor; destruct2 x; simpl; auto. 
  all : intros; destruct x; try inv_trtype_false; unfold leTR; simpl. 
    - apply le_0_n.
Defined.

Eval compute in whaaaaat 8.

Close Scope string_scope.
#[local] Obligation Tactic := try (start_jail; intro; simplify_hypothesis; discriminate).

Program Definition is_less_than (x : {trnum}) (y : {trnum})
  : {t >> trbool & (ltTR x y) & ~(ltTR x y)} :=
  match x, y with 
  | Num x', Num y' => Bool (x' <? y') 
  | _r1, _r2 => False_rec _ _ 
  end.
Next Obligation.
  intros; simpl; repeat constructor; intro; subst *; unfold ltTR; rewrite <- Heq_x; rewrite <- Heq_y;
  destruct2 x; destruct2 y; destruct x; try inv_trtype_false; destruct y; try inv_trtype_false; simpl in *.
    - apply PeanoNat.Nat.ltb_lt. destruct (x' <? y'); destruct H; auto.
    - intro. apply PeanoNat.Nat.ltb_lt in H0. destruct H. rewrite H0 in H1. discriminate.
  Defined. Next Obligation. 
  new_jail. 
Defined.

Eval compute in is_less_than 10 3.

Program Definition what : forall (n : nat) (m : {a : nat | 0 <= a < n}) (x : nat_vec n),
let filtered_var := vec_unsafe_ref x (proj1_sig m) in
None = filtered_var -> False.
intros; simpl. subst filtered_var. induction x.
  - destruct m. destruct a. apply (PeanoNat.Nat.nlt_0_r x); auto.
  - induction m. destruct x0; destruct p; simpl in H. inversion H.
    apply PeanoNat.lt_S_n in l0.
    assert (H4: 0 <= x0 < n).
    + constructor; auto. apply (PeanoNat.Nat.le_0_l x0).
    + specialize (IHx (exist (fun a => 0 <= a < n) x0 H4)) as J. simpl in J. 
      eauto.
Defined.

Program Definition vec_ref_safe {n} (m : {a | ((0 <= a) /\ (a < n)) }) (x : nat_vec n) : nat :=
  match vec_unsafe_ref x m with (* this is the define *)
  | None => False_rec _ _ (* this case is error will never occur *)
  | Some res => res
  end.
Next Obligation.
  apply what.
Defined.
#[local] Obligation Tactic := try fail.
Program Fixpoint dot_product (n : nat) (step : nat) (H2 : 0 < step) (x : nat_vec n) (y : nat_vec n) (acc : nat) (i : nat) (H : i < (n + step)) {measure ((n + step) - i)} : nat :=
  match (i <? n) as M with
    | true => @dot_product n step _ x y (acc + ((vec_ref_safe i x) * (vec_ref_safe i y))) (i + step) _ _
    | false => acc
    end.
Next Obligation.
    intros; simpl. auto.
    Defined. Next Obligation. 
    intros; simpl. subst *. split. apply le_0_n. apply what_again; auto.
    Defined. Next Obligation.
    intros; simpl.  subst *. split. apply le_0_n. apply what_again; auto.
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

#[local] Obligation Tactic := try try vec_inv; try (intros; subst *; apply (PeanoNat.Nat.lt_0_succ _)).
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




(* Set Printing Coercions. *)
(* should this n be trnum as well *)
(* also should the types of trnum also try to hold like (0 < step) in side of P *)
(* alright the coercions are causing me some problems *)
Program Definition dot_prod_what_tr {n : nat} 
  (len : { trnum }) 
  (step : {t >> trnum & (less_than 0 t) & ~(less_than 0 t)}) 
  (x : { (trvec n) }) 
  (y : { (trvec n) })  
  (acc : { trnum }) 
  (i : {t >> trnum & (less_than t (sum (Num n) step)) & ~(less_than t (sum (Num n) step))})
   : { trnum } :=
   (* i don't want to do this, but for some reason it was setting everything to i lol *)
   match step with 
   | Num step' => 
    match x, y with 
    | Vec a v1, Vec b v2 => 
      match acc with 
      | Num acc' => 
        match i with 
        | Num pi => dot_product n step' _ v1 v2 acc' pi _
        | _r1 => False_rec _ _
        end
      | _r => False_rec _ _
      end
    | _r1, _r2 => False_rec _ _
    end
   | _r => False_rec _ _
   end.
Next Obligation.
  intros. subst *. destruct step as [?s ?s]; destruct2 s0.
  assert (H10 : HasType s trnum /\ s <> (Bool false)) by 
    (repeat split; auto; intro; destruct s; try inv_trtype_false; discriminate).
  specialize (s1 H10) as L. simpl in Heq_step. rewrite <- Heq_step in L. 
  inversion L; unfold lt in H1; simpl in H1. auto.
Defined. Next Obligation.
  intros. subst *. destruct2 x. simpl in Heq_x.
  clear Heq_i. clear i.
  rewrite <- Heq_x in x0. inversion x0; auto.
Defined. Next Obligation.
  intros. subst *. destruct2 y. simpl in Heq_y.
  clear Heq_i. clear i.
  rewrite <- Heq_y in y0. inversion y0; auto.
Defined. Next Obligation.
  intros. subst *. 
  clear Heq_acc. clear Heq_x; clear Heq_y. 
  destruct i as [?i ?i]; destruct2 i0.
  assert (H10 : HasType i trnum /\ i <> (Bool false)) by 
    (repeat split; auto; intro; destruct i; try inv_trtype_false; discriminate).
  specialize (i1 H10) as L. simpl in Heq_i. rewrite <- Heq_i in L.
  inversion L.  destruct2 step; simpl in *. subst *. unfold lt in H1. simpl in H1.
  simpl in H0. inversion H0. rewrite H2 in H1; auto.
Defined. Next Obligation.
  intros. subst *. try new_jail.
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

(* lol i guess this is actually unit *)
Program Definition vec_set {n} (x : nat_vec n) (i : nat) (H : i < n) : Void_ := void.


Program Definition vec_swap {n} (x : nat_vec n) (i : {a | ((0 <= a) /\ (a < n)) }) (j : {a | ((0 <= a) /\ (a < n)) }) : Void_ :=
  match (i =? j) with
  | true => void
  | false => 
    let i_val := (vec_ref_safe i x) in 
      let j_val := (vec_ref_safe j x) in 
        let swap1 := (vec_set x i _) in 
          vec_set x j _
  end.
Next Obligation. intros. destruct i; simpl. destruct a; auto. Defined.
Next Obligation. intros. destruct j; simpl. destruct a; auto. Defined.

Program Definition vec_prod_TR_2 {n} 
  (res : {trnum}) 
  (i : {t >> trnum & (less_than_equal t (Num n)) & True}) 
  (x : {trvec n}) : {trnum} :=
  match res, i, x with 
  | (Num res'), (Num i'), (Vec m nv1) => vec_product res' i' nv1
  | _r1, _r2, _r3 => False_rec _ _ 
  end.
Next Obligation.
  new_jail. 
  assert (J2 : HasType (Num n0) trnum /\ (Num n0) <> (Bool false)) by (repeat split; try constructor; try (intro K; inversion K)).
  specialize (i1 J2).
  inversion i1; unfold leTR in H1; simpl in H1. inversion Heq_i. inversion x0; subst *. auto.
  Defined. Next Obligation.
  new_jail. eapply n0; eauto.
  Defined. Next Obligation. (* this is stupid lol *)
  small_jail. inversion H1.
  Defined. Next Obligation.
  small_jail. inversion H1.
  Defined. Next Obligation.
  small_jail. inversion H1.
  Defined. Next Obligation.
  small_jail. inversion H1.
  Defined. Next Obligation.
  small_jail. inversion H1.
  Defined. Next Obligation.
  small_jail. inversion H1. 
  Defined. Next Obligation.
  small_jail. inversion H. 
  Defined. Next Obligation.
  small_jail. inversion H. 
  Defined. Next Obligation.
  small_jail. inversion H. 
  Defined. Next Obligation.
  small_jail. inversion H. 
  Defined. Next Obligation.
  small_jail. inversion H. 
  Defined. Next Obligation.
  small_jail. inversion H. 
  Defined. Next Obligation.
  small_jail. inversion H0. 
  Defined. Next Obligation.
  small_jail. inversion H0. 
  Defined. Next Obligation.
  small_jail. inversion H0.
  Defined. Next Obligation.
  small_jail. inversion H0.
  Defined. Next Obligation.
  small_jail. inversion H0.
  Defined. Next Obligation.
  small_jail. inversion H0.
Defined.


#[local] Obligation Tactic := try vec_inv.
Program Fixpoint dot_prod_what_tr_2 {n : nat} 
  (len : { trnum }) 
  (step : {t >> trnum & (less_than 0 t) & ~(less_than 0 t)}) 
  (x : { (trvec n) }) 
  (y : { (trvec n) })  
  (acc : { trnum }) 
  (i : {t >> trnum & (less_than t (sum (Num n) step)) & ~(less_than t (sum (Num n) step))}) {measure (proj1_sig (sub (sum n step) i)) ltTR}
   : { trnum } :=
   (* i don't want to do this, but for some reason it was setting everything to i lol *)
   match step with 
   | Num step' => 
    match x, y with 
    | Vec a v1, Vec b v2 => 
      match acc with 
      | Num acc' => 
        match i with 
        | Num pi => match (pi <? n) as M with
                    | true => @dot_prod_what_tr_2 n len step x y (sum acc (mul (trvec_ref x i) (trvec_ref y i))) (sum i step) _
                    | false => acc
                    end
        | _r1 => False_rec _ _
        end
      | _r => False_rec _ _
      end
    | _r1, _r2 => False_rec _ _
    end
   | _r => False_rec _ _
   end.
Next Obligation.
 try small_jail; try discriminate; try new_jail.
Defined. Next Obligation.
  small_jail. simpl. pls_destruct_correctly. unfold ltTR; simpl; subst *. eapply what_again; eauto. inversion Heq_i. rewrite <- H0. auto.
Defined. Next Obligation.
  small_jail. simpl. pls_destruct_correctly. apply (less_than_0 n0). simpl. inversion i0. constructor; unfold ltTR; simpl; subst *. eapply what_again; eauto. inversion Heq_i. rewrite <- H2. auto.
Defined. Next Obligation.
  small_jail. simpl. pls_destruct_correctly. unfold ltTR; simpl; subst *. eapply what_again; eauto. inversion Heq_i. rewrite <- H0. auto.
Defined. Next Obligation.
  small_jail. simpl. pls_destruct_correctly. apply (less_than_0 n0). simpl. inversion i0. constructor; unfold ltTR; simpl; subst *. eapply what_again; eauto. inversion Heq_i. rewrite <- H2. auto.
Defined. Next Obligation.
  start_jail. destruct i; try inv_trtype_false. destruct step; try inv_trtype_false. repeat split. 
    - simpl; constructor.
    - simpl in H. unfold ltTR; simpl; subst *. 
    assert (J : (pi <? n) = true) by auto. eapply what_again in J. inversion Heq_i. subst *. lia.
    - intro. destruct H. simpl in H0. inversion H0.
Defined. Next Obligation.
  intros. destruct step as [?step [?step ?step]]. destruct i as [?i [?i ?i]]. destruct step; try inversion step0. destruct i; try inversion i0.
  simpl. unfold ltTR; simpl. induction n0.
  - destruct step1. make_hypothesis_not_bool (Num 0) trnum.
    pose proof (l J). inversion H. unfold ltTR in H4; simpl in H4. inversion H4.
  - apply (strictly_lessthan n n2 n0). 
    + make_hypothesis_not_bool (Num n2) trnum.
      destruct i1. pose proof (l J). simpl in H. inversion H. unfold ltTR in H4; simpl in H4. auto.
    + subst *. simpl in Heq_i. inversion Heq_i. rewrite <- H0. assert (J : (pi <? n) = true) by auto. apply (what_again pi n); auto.
Defined. Next Obligation.
  small_jail; try discriminate; try new_jail.
Defined. Next Obligation.
  small_jail. simpl in filtered_var. destruct acc; try inv_trtype_false. apply (n0 n1); auto.
Defined. Next Obligation. 
  small_jail. simpl in filtered_var. simpl in filtered_var0. destruct x; try inv_trtype_false. 
  destruct y; try inv_trtype_false. apply (n0 n1 n2 n3 n4); repeat split; auto.
Defined. Next Obligation.
  small_jail. simpl in filtered_var. destruct step; try inv_trtype_false. apply (n0 n1); auto.
Defined. Next Obligation.
  small_jail. inversion H.
Defined. Next Obligation.
  small_jail. inversion H.
Defined. Next Obligation.
  small_jail. inversion H.
Defined. Next Obligation.
  small_jail. inversion H.
Defined. Next Obligation.
  small_jail. inversion H.
Defined. Next Obligation.
  apply measure_wf. apply wf_ltTR.
Defined.
*)