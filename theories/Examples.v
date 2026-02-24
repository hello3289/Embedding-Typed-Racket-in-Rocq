Set Warnings "-ambiguous-paths".
From TRresearch Require Import Functions.
From TRresearch Require Import Tactic_jail.
From TRresearch Require Import Definitions.
From TRresearch Require Import VectorExamples. (* this is just so I compile this first *)
From Stdlib.Strings Require Import String.
From Stdlib Require Bool.
From Stdlib Require PeanoNat.
Require Import Program.Tactics.
Require Import Init.Nat.
Require Import Program.Wf.
#[local] Obligation Tactic := try new_jail.
Open Scope string_scope.
Open Scope TR_scope.
Set Warnings "ambiguous-paths".
Set Warnings "-meta-collision".



(* IT LIVES *)


(************************************************************************)
(********************** IF AGAIN AHHHHHHHHHHHHHHHH **********************) 

#[local] Obligation Tactic := try small_jail; try discriminate; try new_jail.
Program Definition if_ex1 {t : TRTypes} (x : {t}) : {trnum}:=
  ifTR (is_number x) (add1 x) 0. (* whyy :((((((( *)
  

Eval compute in if_ex1 5.
Eval compute in if_ex1 "5".

Program Definition if_ex2 (x : {(U trstr trnum)}) : {trnum} :=
  ifTR (is_number x) (add1 x) (strlen x).

(* has to use <[]> here since the coercion is only for trstr :( *)
(* ok i think we can't use coercions here bc going from tr__ to trunion requires solving ~something~ *)
Program Definition if_ex2_test1 := if_ex2 <["hi"]>.
Program Definition if_ex2_test2 := if_ex2 <[ 9 ]>.

Eval compute in if_ex2_test1.
Eval compute in if_ex2_test2.

Program Definition if_exWhat (x : {(U trstr trnum)}) : {trnum} :=
  ifTR (is_number x) (add1 x) 4.

#[local] Obligation Tactic := try fail. (* ok these obligations are just a little strange *)
Program Definition if_orTest2 {t : TRTypes} (x : {t}) : {trbool} :=
  orTR (is_number x) (is_string x).
Next Obligation. intros. exact trbool. Defined. (* bruh *)
Solve All Obligations with (try unfold if_orTest2_obligation_1; try new_jail).
  (* can't tell from looking at the proof why the tactic doesn't work, will have to fix *)
Next Obligation. 
  intros; simpl in *; repeat split; destruct x; simpl; destruct a as [?a [?a ?a]]; unfold if_orTest2_obligation_1.
  - destruct x; simpl; constructor.
  - intro. destruct H. destruct x; simpl in *; try (destruct H0; auto; fail). right. subst P';
    unfold get_true_prop; constructor.
  - intro. destruct H. intro. destruct H1; try (destruct n; auto; fail). subst P'. unfold get_true_prop in H1.
    destruct x; simpl in *; try inv_trtype_false_faster_2. discriminate.
  Defined.
Next Obligation. new_jail. Defined.
  
Eval compute in if_orTest2 5.



#[local] Obligation Tactic := try small_jail; try discriminate; try new_jail.
Program Definition if_ex4 {t : TRTypes} (x : {t}) : {trnum} :=
  ifTR
       (orTR (is_number x) (is_string x))
       (if_exWhat x)
       0.

Eval compute in if_ex4 9.
Eval compute in if_ex4 "hi".
Eval compute in if_ex4 true.

Program Definition if_ex5 {t r : TRTypes} (x : {t}) (y : {r}) : {trnum} :=
  ifTR  (andTR (is_number x) (is_string y))
           (sum x (strlen y)) 
           0.
Eval compute in if_ex5 5 "hi".
Eval compute in if_ex5 5 8.
Eval compute in if_ex5 "hello" 10.
Eval compute in if_ex5 true false.

Program Definition if_ex10 {A B : TRTypes} (p : {(trpair A B)}) : {trnum} :=
  ifTR (is_number (car p)) (add1 (car p)) 7.

Eval compute in if_ex10 (5, "bye").
Eval compute in if_ex10 (false, 10).

Program Definition if_more_ex3_1 {t : TRTypes} (x : {t}) : {trnum} :=
  ifTR (is_number x) x 54.


Program Definition if_more_ex1 {t r : TRTypes} (x : {t}) (y : {r}) 
         : {t >> trbool & 
                 ((HasType x trnum) /\ (HasType y trstr) \/ (HasType x trstr))} :=
  (ifTR < all > (is_number x) (is_string y) (is_string x)).


Program Definition if_more_ex3 {t r : TRTypes} (x : {t}) (y : {r}) : {trnum} :=
(ifTR (if_more_ex1 x y) 
  (ifTR (is_string x) (strlen x) (sum x (strlen y)))
  (ifTR (is_number x) x 54)).

(************************************************************************)
(********************** EXAMPLE 1 AHHHHHHHHHHHHHHH **********************)
Program Definition ex1 {t : TRTypes} (x : {t}) : {trnum}:=
  ifTR (is_number x) (add1 x) 0.

(************************************************************************)
(********************** EXAMPLE 2 AHHHHHHHHHHHHHHH **********************)

Program Definition ex2 (x : {(U trstr trnum)}) : {trnum} :=
  ifTR (is_number x) (add1 x) (strlen x). 

Program Definition ex2_test1 := ex2 <[ "hi" ]>.
Program Definition ex2_test2 := ex2 <[ 9 ]>. 

Eval compute in ex2_test1.
Eval compute in ex2_test2.

(************************************************************************)
(********************** EXAMPLE 4 AHHHHHHHHHHHHHHH **********************)

Program Definition ex4 {t : TRTypes} (x : {t}) : {trnum} :=
  ifTR (orTR (is_number x) (is_string x))
       (ex2 x)
       0.
  
Eval compute in ex4 9.
Eval compute in ex4 "hi".
Eval compute in ex4 true.

(************************************************************************)
(********************** EXAMPLE 5 AHHHHHHHHHHHHHHH **********************)

Program Definition ex5 {t r : TRTypes} (x : {t}) (y : {r}) : {trnum} :=
  ifTR  (andTR (is_number x) (is_string y))
           (sum x (strlen y))
           0.

Eval compute in ex5 5 "hi".
Eval compute in ex5 5 8.
Eval compute in ex5 "hello" 10.
Eval compute in ex5 true false.

(************************************************************************)
(********************** EXAMPLE 7 AHHHHHHHHHHHHHHH **********************)

Program Definition ex7 {t r : TRTypes} (x : {t}) (y : {r}) : {trnum} :=
  (ifTR 
    (ifTR < second > (is_number x) (is_string y) false)
    (sum x (strlen y))
    0).

Eval compute in ex7 6 "hello".

(************************************************************************)
(********************** EXAMPLE 8 AHHHHHHHHHHHHHHH **********************)

Program Definition ex8 {t : TRTypes} (x : {t}) :=
  orTest x.

Program Definition ex8_test {t : TRTypes} (x : {t}) : {trnum} :=
  (ifTR (ex8 x) (ex2 x) 0).

Eval compute in ex8 6.
Eval compute in ex8_test 6.
Eval compute in ex8 "potatoes".
Eval compute in ex8_test "potatoes".
Eval compute in ex8 true.
Eval compute in ex8_test true.

(************************************************************************)
(********************** EXAMPLE 9 AHHHHHHHHHHHHHHH **********************)

Program Definition ex9 {t : TRTypes} (x : {t}) : {trnum} :=
  (ifTR 
    (let p := (is_number x) in 
      (ifTR < third > p p (is_string x)))
    (ex2 x) 
    0).
    Next Obligation. 
    assert (HasType false trbool /\ Bool false = Bool false) as H1; auto. 
    apply p2 in H1; destruct H1; auto.
    Defined.

Eval compute in ex9 2.

(************************************************************************)
(********************** EXAMPLE 10 AHHHHHHHHHHHHHH **********************)

Program Definition ex10 {A B : TRTypes} (p : {(trpair A B)}) : {trnum} :=
  ifTR (is_number (car p)) (add1 (car p)) 7.

Eval compute in ex10 (5, "bye").
Eval compute in ex10 (false, 10).

(************************************************************************)
(********************** EXAMPLE 11 AHHHHHHHHHHHHHH **********************)

Program Definition g (p : {trpair trnum trnum}) : {trnum} :=
  (sum (car p) (cdr p)).

Eval compute in g (4, 5). 

(* oof this takes a while *)
Program Definition ex11 {A B : TRTypes} (p : {trpair A B}) : {trnum} :=
  ifTR (andTR (is_number (car p)) (is_number (cdr p))) (g p) 0.
  
Eval compute in ex11 (4, 12).
Eval compute in ex11 (3, false).

(************************************************************************)
(********************** EXAMPLE 12 AHHHHHHHHHHHHHH **********************)

(* back to the scheduled programming *)
Program Definition ex12 {A B : TRTypes} (p : {trpair A B}) : 
  {t >> trbool & (HasType p (trpair trnum B))} :=
  (is_number (car p)).
  
  
Program Definition ex12_again {A B : TRTypes} (p : {trpair A B}) : 
{t >> trbool & (HasType (car p) trnum)} :=
  (is_number (car p)).

Eval compute in ex12 (4, true).
Eval compute in ex12 ("hi", 1).

(************************************************************************)
(********************** MORE EXAMPLES AHHHHHHHHHHH **********************)

Program Definition more_ex1 {t r : TRTypes} (x : {t}) (y : {r}) 
         : {t >> trbool & ((HasType x trnum) /\ (HasType y trstr) \/ (HasType x trstr))} :=
  (ifTR < all > (is_number x) (is_string y) (is_string x)).

Program Definition more_ex1_use := more_ex1 5 "hello".
Eval compute in more_ex1_use. 

Program Definition more_ex2 {t r : TRTypes} (x : {t}) (y : {r}) : {trnum} :=
  (ifTR (more_ex1 x y) 
    (ifTR (is_string x) (strlen x) (sum x (strlen y)))
    42).

Program Definition more_ex3 {t r : TRTypes} (x : {t}) (y : {r}) : {trnum} :=
  (ifTR (more_ex1 x y) 
    (ifTR (is_string x) (strlen x) (sum x (strlen y)))
    (ifTR (is_number x) (add1 x) 54)). 

(************************************************************************)
(********************** EXAMPLES NOT AHHHHHHHHHHHHHHH *******************)
Program Definition not_ex1 {t : TRTypes} (x : {t}) : {trnum} :=
  (ifTR (notTR (notTR (is_number x))) (add1 x) 42).

Eval compute in (not_ex1 5).
Eval compute in (not_ex1 "hi").

Program Definition not_ex2 {t : TRTypes} (x : {t}) : {trnum} :=
  (ifTR (notTR (is_number x)) 
      (ifTR (is_string x) (strlen x) 13)
      42).

Eval compute in (not_ex2 5).
Eval compute in (not_ex2 "hi").
Eval compute in (not_ex2 true).

(************************************************************************)
(****************** LET EXAMPLES???????????????? AHHHHHHHH **************)


(*  this takes much longer than anticipated, i will have to look at my tactic *) 
#[local] Obligation Tactic := try fail.
Program Definition let_ex1 {t : TRTypes} (x : {t}) : {trnum} :=
  let p := (is_number x) in
    (ifTR p (add1 x) 0).
Next Obligation.
  intros; simpl. repeat split; auto.
Defined. Next Obligation.
  intros; simpl; repeat split. destruct p. destruct a; destruct x0; try inv_trtype_false_faster_2.
  destruct b. 
  - simpl. destruct a. 
    make_hypothesis_not_bool (Bool true) trbool.
    specialize (h0 J) as H1. destruct x. destruct a. simpl in *. 
    destruct x; try inv_trtype_false_faster_2.
    unfold add1; simpl. 
    constructor.
  - simpl. destruct a. constructor.
Defined.

Eval compute in (let_ex1 9).
Eval compute in (let_ex1 "hi").
(************************************************************************)
(****************** EXAMPLES FROM IF-T BENCHMARK AHHHHHHHH **************)
#[local] Obligation Tactic := try new_jail.
Program Definition car_add {t r : TRTypes} (p : {(trpair t r)}) : {trnum} :=
(ifTR (is_number (car p)) (add1 (car p)) 0).

Eval compute in (car_add ("hi", 9)).
Eval compute in (car_add (18, 4)).

(* just write your own lol *)
Program Definition pos_success {t : TRTypes} (x : {t}) : {trtop} :=
  (ifTR (is_string x) (strlen x) x).
Eval compute in (pos_success "potatoes").
Eval compute in (pos_success 8).
Eval compute in (pos_success true).
Eval compute in (pos_success ("hi", false)).

(* this doesn't directly fail, but it generates unsolvable obligations
Program Definition pos_fail {t : TRTypes} (x : {v >> t}) : {v >> trtop} :=
  (ifTR_v2 (is_string x) (add1 x) x). *)
  (* maybe find a way to should that this will fail? *)

Program Definition neg_success (x : {U trstr trnum}) : {trnum} :=
  (ifTR (is_string x) (strlen x) (add1 x)).

Program Definition neg_succ_test1 := (neg_success <["hi"]>).
Program Definition neg_succ_test2 := (neg_success <[7]>).

Eval compute in neg_succ_test1.
Eval compute in neg_succ_test2.


(* same as above, the obligations are unsolvable. If you put 0 instead of add1 x, it gets defined
Program Definition neg_fail (x : {v >> trunion trstr (trunion trnum trbool)}) : {v >> trnum} :=
  (ifTR_v2 (is_string x) (strlen x) (add1 x)). *)

Program Definition is_strnum {t : TRTypes} (x : {t}) : 
                  {t >> trbool & ((HasType x trstr) \/ (HasType x trnum))} :=
  (orTR (is_string x) (is_number x)).

Program Definition f (x : {U trstr trnum}) : {trnum} :=
  ifTR (is_number x) (add1 x) (strlen x).

Program Definition g2 (x : {trtop}) : {trnum} :=
  ifTR (is_strnum x)
       (f x)
       0.

Program Definition g2_test1 := g2 <[5]>.
Program Definition g2_test2 := g2 <["potatoes"]>.
Program Definition g2_test3 := g2 <[false]>.

Eval compute in g2_test1.
Eval compute in g2_test2.
Eval compute in g2_test3.

Program Definition h (x : {U trstr (U trnum trbool)}) : {trnum} :=
  ifTR (andTR (notTR (is_bool x)) (notTR (is_number x)))
          (strlen x)
          0.
Next Obligation.
  destruct n. intro. inv_trtype_false_faster_2.
Defined. 
(* i wonder why this define takes so much time *)

Program Definition h_test1 := h <["potatoes"]>.
Program Definition h_test2 := h <[5]>.
Program Definition h_test3 := h <[Bool false]>.

Eval compute in h_test1.
Eval compute in h_test2.
Eval compute in h_test3.

Program Definition f2 (x : {U trstr (U trnum trbool)}) : {trnum} :=
  ifTR (notTR (is_string x))
          (ifTR (notTR (is_bool x))
                   (add1 x)
                   0)
          0.
  #[local] Obligation Tactic := try fail.
Next Obligation. (* i  need to deal with nested trunions and ~ better *)
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
(********************** EXAMPLE 13/14 AHHHHHHHHHHH **********************)

(* this takes a humble 4 minutes (?) to solve... *)
#[local] Obligation Tactic := try small_jail; try discriminate; try new_jail.
Program Definition ex13_14 
    (x : {U trnum trstr}) 
    (y : {trpair trtop trtop}) :
    {trnum} :=
  condTR [ (andTR (is_number x) (is_number (car y))) (sum x (car y)) ] 
         [ (is_number (car y)) (sum (strlen x) (car y)) ] 
         [ else 0].

Program Definition ex_13_14_use := ex13_14 <[14]>  (14, "hello").

Eval compute in ex_13_14_use.

(* hehe *)