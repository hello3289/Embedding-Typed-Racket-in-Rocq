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