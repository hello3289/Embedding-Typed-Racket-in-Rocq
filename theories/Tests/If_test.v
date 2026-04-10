Set Warnings "-uniform-inheritance".
Set Warnings "-ambiguous-paths".
Set Warnings "-meta-collision".
From TRresearch.Tactics Require Import tactics_all apply_predicate_lemmas prove_ifTR_branches.
From TRresearch Require Import Definitions Predicates If Basics.
From TRresearch.Lemmas Require Import Lemmas Union_Lemmas Predicate_Lemmas.
From Stdlib Require Import Strings.String.
#[local] Obligation Tactic := try ((timeout 0 (time really_simple_start)); (timeout 0 (time new_jail))).

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
    Hint Extern 0 => unfold_get_true_prop_hypothesis : TRHints.
Open Scope string_scope.


Program Definition orTest {A : TRTypes} (x : {A}) : 
    {>> trbool & ((HasType x trnum) \/ (HasType x trstr))} :=
    orTR (is_number x) (is_string x).

Eval compute in (orTest 5).
Eval compute in (orTest "hi").
Eval compute in (orTest true).
Eval compute in (orTest (5, "potato")).

Program Definition andTest {A B : TRTypes} (x : {A}) (y : {B}) :
  {>> trbool & ((HasType x trnum)  /\ (HasType y trstr))} :=
  andTR (is_number x) (is_string y).

Eval compute in (andTest 5 "potato").
Eval compute in (andTest 3 false).
Eval compute in (andTest true "pasta").
Eval compute in (andTest (5, "potato") false).

Program Definition ifTest_1 {t : TRTypes} (x : {t}) : {trnum} :=
  ifTR (is_number x) x 0.

Eval compute in (ifTest_1 5).
Eval compute in (ifTest_1 false).
Eval compute in (ifTest_1 "pasta").
Eval compute in (ifTest_1 (5, "potato")).

Program Definition ifTest_2 {t : TRTypes} (x : {t}) : {trnum}:=
  ifTR (is_number x) (add1 x) 0.

Eval compute in (ifTest_2 5).
Eval compute in (ifTest_2 false).
Eval compute in (ifTest_2 "pasta").
Eval compute in (ifTest_2 (5, "potato")).

Program Definition ifTest_3 (x : {(U trstr trnum)}) : {trnum} :=
  ifTR (is_number x) (add1 x) (strlen x).

(* as a reminder, I need the <[]> as I couldn't find a way to write a coercion
  to a union type, so you have to manually give it the type *)
Program Definition ifTest_3_1 := ifTest_3 <[5]>.
Program Definition ifTest_3_2 := ifTest_3 <["potato cheesecake"]>.

Eval compute in ifTest_3_1.
Eval compute in ifTest_3_2.

Program Definition ifTest_4 (x : {(U trstr trnum)}) : {trnum} :=
  ifTR (is_number x) (add1 x) 4.

Program Definition ifTest_4_1 := ifTest_4 <[5]>.
Program Definition ifTest_4_2 := ifTest_4 <["potato cheesecake"]>.

Eval compute in ifTest_4_1.
Eval compute in ifTest_4_2.

Program Definition condTest {A B : TRTypes}
    (x : {A})
    (y : {B}) :
    {trnum} :=
  condTR [ (is_number x) (add1 x) ] 
         [ (is_string y) (strlen y) ]
         [ else 0 ].

Eval compute in (condTest 5 9).
Eval compute in (condTest false "pasta lasagna").
Eval compute in (condTest "potato" false).
Eval compute in (condTest (5, "potato") (8, "hi")).


Program Definition orTest2 {A : TRTypes} (x : {A}) : 
    {>> trbool & ((HasType x trnum) \/ (HasType x trstr))} :=
    orTR_2 (is_number x) (is_string x).

Eval compute in (orTest2 5).
Eval compute in (orTest2 "hi").
Eval compute in (orTest2 true).
Eval compute in (orTest2 (5, "potato")).

Program Definition andTest2 {A B : TRTypes} (x : {A}) (y : {B}) :
  {>> trbool & ((HasType x trnum)  /\ (HasType y trstr))} :=
  andTR_2 (is_number x) (is_string y).

Eval compute in (andTest2 5 "potato").
Eval compute in (andTest2 3 false).
Eval compute in (andTest2 true "pasta").
Eval compute in (andTest2 (5, "potato") false).

Program Definition if_combined_test {t : TRTypes} (x : {t}) : {trnum} :=
  ifTR
    (orTR (is_number x) (is_string x))
    (ifTest_3 x)
    0.

Eval compute in (if_combined_test 5).
Eval compute in (if_combined_test "cranberry pie").
Eval compute in (if_combined_test true).

Program Definition ifTest_5 {t r : TRTypes} (x : {t}) (y : {r}) : {trnum} :=
  ifTR (andTR (is_number x) (is_string y))
       (sum x (strlen y)) 
       0.

Eval compute in (ifTest_5 5 "ice cream cake").
Eval compute in (ifTest_5 5 9).
Eval compute in (ifTest_5 "potato" "cheese").
Eval compute in (ifTest_5 (5, "potato") (8, "hi")).

Program Definition ifTest_6 {A B : TRTypes} (p : {(trpair A B)}) : {trnum} :=
  ifTR (is_number (car p)) (add1 (car p)) 7.

Eval compute in (ifTest_6 (9, "hi")).
Eval compute in (ifTest_6 ("cheese balls", 10)).

(* this is the test that caused the move to ifTR_union! *)
Program Definition ifTest_7 {t : TRTypes} (x : {t}) : {trnum} :=
  ifTR (is_number x) x 54.

Eval compute in (ifTest_7 9).
Eval compute in (ifTest_7 "cat").

Program Definition ifTest_8 {t r : TRTypes} (x : {t}) (y : {r}) 
         : {t >> trbool & ((HasType x trnum) /\ (HasType y trstr) \/ (HasType x trstr))} :=
  (ifTR < all > (is_number x) (is_string y) (is_string x)).

Eval compute in (ifTest_8 5 "ice cream cake").
Eval compute in (ifTest_8 5 9).
Eval compute in (ifTest_8 "potato" "cheese").
Eval compute in (ifTest_8 (5, "potato") (8, "hi")).

Program Definition ifTest_9 {t r : TRTypes} (x : {t}) (y : {r}) : {trnum} :=
(ifTR (ifTest_8 x y) 
  (ifTR (is_string x) (strlen x) (sum x (strlen y)))
  (ifTR (is_number x) x 54)).

Eval compute in (ifTest_9 5 "ice cream cake").
Eval compute in (ifTest_9 5 9).
Eval compute in (ifTest_9 "potato" "cheese").
Eval compute in (ifTest_9 (5, "potato") (8, "hi")).