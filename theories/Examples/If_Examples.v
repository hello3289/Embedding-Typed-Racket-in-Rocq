Set Warnings "-uniform-inheritance".
Set Warnings "-ambiguous-paths".
Set Warnings "-meta-collision".
From TRresearch.Tactics Require Import tactics_all apply_predicate_lemmas prove_ifTR_branches apply_union_lemmas apply_if_lemmas.
From TRresearch Require Import Definitions Predicates If Basics.
From TRresearch.Lemmas Require Import Lemmas Union_Lemmas Predicate_Lemmas.
From Stdlib Require Import Strings.String.
#[local] Obligation Tactic := try ((timeout 1 (time really_simple_start)); (timeout 1 (time new_jail))).

(* "HintDb" *)
Create HintDb TRHints.
    Hint Extern 0 => discriminates : TRHints.
    Hint Extern 0 => subst_filtered_var : TRHints.
    Hint Extern 0 => simpl_func : TRHints.
    Hint Extern 0 => rewrite_jail' : TRHints.
    Hint Constructors HasType : TRHints.
    Hint Unfold is_number : TRHints.
    Hint Unfold get_true_prop : TRHints.
    Hint Immediate is_top : TRHints.
    Hint Immediate is_top_pair : TRHints.
    Hint Immediate pair_left : TRHints.
    Hint Immediate pair_right : TRHints.
    Hint Immediate is_number_trbool : TRHints.
    Hint Immediate is_string_trbool : TRHints.
    Hint Extern 1 => prove_if_TR_branches : TRHints.
    Hint Extern 1 => apply_proj1_sig_is_string_true : TRHints.
    Hint Extern 1 => apply_proj1_sig_is_string_false : TRHints.
    Hint Extern 1 => apply_proj1_sig_is_number_true : TRHints.
    Hint Extern 0 => unfold_get_true_prop_hypothesis : TRHints.
    Hint Extern 1 => apply_union_not : TRHints.
    Hint Extern 1 => apply_not_either_union : TRHints.
    Hint Extern 1 => apply_notTR_is_bool : TRHints.
    Hint Extern 1 => apply_notTR_bool_true_is_false : TRHints. 
    Hint Extern 1 => apply_notTR_bool_false_is_true : TRHints.
Open Scope string_scope.

(* some of these overlap with the tests in If_test... *)

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

Program Definition orTest {A : TRTypes} (x : {A}) : 
    {>> trbool & ((HasType x trnum) \/ (HasType x trstr))} :=
    orTR (is_number x) (is_string x).

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

Program Definition ex11 {A B : TRTypes} (p : {trpair A B}) : {trnum} :=
  ifTR (andTR (is_number (car p)) (is_number (cdr p))) (g p) 0.


(************************************************************************)
(********************** EXAMPLE 12 AHHHHHHHHHHHHHH **********************)

Program Definition ex12 {A B : TRTypes} (p : {trpair A B}) : 
  {t >> trbool & (HasType p (trpair trnum B))} :=
  (is_number (car p)).

Program Definition ex12_again {A B : TRTypes} (p : {trpair A B}) : 
{t >> trbool & (HasType (car p) trnum)} :=
  (is_number (car p)).

Eval compute in ex12 (4, true).
Eval compute in ex12 ("hi", 1).

Program Definition ex12_string {A B : TRTypes} (p : {trpair A B}) : 
  {t >> trbool & (HasType p (trpair trstr B))} :=
  (is_string (car p)).

Program Definition ex12_boolean {A B : TRTypes} (p : {trpair A B}) : 
  {t >> trbool & (HasType p (trpair trbool B))} :=
  (is_bool (car p)).

(************************************************************************)
(********************** MORE EXAMPLES AHHHHHHHHHHH **********************)

Program Definition if_more_ex1 {t r : TRTypes} (x : {t}) (y : {r}) 
         : {t >> trbool & ((HasType x trnum) /\ (HasType y trstr) \/ (HasType x trstr))} :=
  (ifTR < all > (is_number x) (is_string y) (is_string x)).

Program Definition more_ex2 {t r : TRTypes} (x : {t}) (y : {r}) : {trnum} :=
  (ifTR (if_more_ex1 x y) 
    (ifTR (is_string x) (strlen x) (sum x (strlen y)))
    42).

Program Definition more_ex3 {t r : TRTypes} (x : {t}) (y : {r}) : {trnum} :=
  (ifTR (if_more_ex1 x y) 
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

Program Definition let_ex1 {t : TRTypes} (x : {t}) : {trnum} :=
  let p := (is_number x) in
    (ifTR p (add1 x) 0).

(************************************************************************)
(****************** EXAMPLES FROM IF-T BENCHMARK AHHHHHHHH **************)

Program Definition car_add {t r : TRTypes} (p : {(trpair t r)}) : {trnum} :=
(ifTR (is_number (car p)) (add1 (car p)) 0).

Eval compute in (car_add ("hi", 9)).
Eval compute in (car_add (18, 4)).

Program Definition pos_success {t : TRTypes} (x : {t}) : {trtop} :=
  (ifTR (is_string x) (strlen x) x).

Eval compute in (pos_success "potatoes").
Eval compute in (pos_success 8).
Eval compute in (pos_success true).
Eval compute in (pos_success ("hi", false)).

Program Definition neg_success (x : {U trstr trnum}) : {trnum} :=
  (ifTR (is_string x) (strlen x) (add1 x)).

Program Definition neg_succ_test1 := (neg_success <["hi"]>).
Program Definition neg_succ_test2 := (neg_success <[7]>).

Eval compute in neg_succ_test1.
Eval compute in neg_succ_test2.

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

Program Definition h_test1 := h <["potatoes"]>.
Program Definition h_test2 := h <[5]>.
Program Definition h_test3 := h <[Bool false]>.

Eval compute in h_test1.
Eval compute in h_test2.
Eval compute in h_test3.

(* i am a bit confused as to why adding this hint before the previous
  example causes the tactics to run extremely slow, so I'm putting this
  here instead *)
Hint Extern 1 => one_of_union_type : TRHints.

Program Definition f2 (x : {U trstr (U trnum trbool)}) : {trnum} :=
  ifTR (notTR (is_string x))
          (ifTR (notTR (is_bool x))
                   (add1 x)
                   0)
          0.
  
Program Definition f2_test1 := f2 <[5]>.
Program Definition f2_test2 := f2 <["hi"]>.
Program Definition f2_test3 := f2 <[true]>.

Eval compute in f2_test1.
Eval compute in f2_test2.
Eval compute in f2_test3.

Program Definition ex13_14 
    (x : {U trnum trstr}) 
    (y : {trpair trtop trtop}) :
    {trnum} :=
  condTR [ (andTR (is_number x) (is_number (car y))) (sum x (car y)) ] 
         [ (is_number (car y)) (sum (strlen x) (car y)) ] 
         [ else 0].

Program Definition ex_13_14_use := ex13_14 <[14]>  (14, "hello").

Eval compute in ex_13_14_use.