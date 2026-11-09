Set Warnings "-uniform-inheritance".
Set Warnings "-ambiguous-paths".
Set Warnings "-meta-collision".
From TRresearch.Tactics Require Import tactics_all apply_predicate_lemmas prove_ifTR_branches hastype_tactics.
From TRresearch Require Import Definitions Predicates If Basics.
From TRresearch.Lemmas Require Import Lemmas Union_Lemmas Predicate_Lemmas.
From Stdlib Require Import Strings.String.
#[local] Obligation Tactic := try ((timeout 1 (time really_simple_start)); (timeout 1 (time new_jail))).

Ltac solve_if_TR_hastype := 
    match goal with 
    | |- (fun t : TRValues => HasType t _ /\ _ /\ _ ) (proj1_sig (if_TR _ _ _)) => 
          destruct (if_TR _ _ _)
    end; simpl;
    match goal with 
    | |- HasType ?a ?t /\ ?p /\ ?q => repeat split;
      match goal with
      | [ H : HasType a t /\ _ /\ _ |- _ ] => destruct H; auto
      end
    end; try (intuition; fail).

Ltac not_A_A := 
  match goal with 
  | [ H : ?A |- _] => 
    match goal with 
    | [ H1 : ~A |- _ ] => destruct H1; auto 
    end 
  | [ H : get_true_prop ?A |- _ ] => 
    match goal with 
    | [ H1 : get_false_prop ?A |- _ ] => 
      unfold get_true_prop in H; 
      unfold get_false_prop in H1; 
      try not_A_A
    end
  | [ H : get_false_prop ?A |- _ ] => 
    match goal with 
    | [ H1 : get_true_prop ?A |- _ ] => 
      unfold get_true_prop in H; 
      unfold get_false_prop in H1; 
      try not_A_A
    end
  end.


Definition get_true_prop_func {T : TRTypes} {P Q A : Prop} (v : A -> { t >> T & P & Q }) : Prop.
Proof.
  exact P.
Defined.

Definition get_false_prop_func {T} {P Q A : Prop} (v : A -> { t >> T & P & Q }) : Prop.
Proof. 
  exact Q.
Defined.

Notation " 'ifTR' < T > A B C " := 
  (let P   := (get_true_prop A) in
  (let Q   := (get_false_prop A) in 
  (let P'  := (get_true_prop_func (fun _ : P => B)) in (* need to do this for the Rocq type checker *)
  (let Q'  := (get_false_prop_func (fun _ : P => B)) in 
  (let P'' := (get_true_prop_func (fun _ : Q => C)) in 
  (let Q'' := (get_false_prop_func (fun _ : Q => C)) in 
    (@if_TR T 
          P 
          (P /\ P')
          (Q /\ P'')
          Q 
          (P /\ Q')
          (Q /\ Q'') 
          A (fun _ => B) (fun _ => C)))))))) 
  (at level 0, T at next level, A at next level, B at next level, C at next level).  



Ltac unfold_get_false_prop_hypothesis := 
  match goal with 
  | [ H : get_false_prop _ |- _ ] => unfold get_false_prop in H 
  end.

  Lemma is_number_false_not_number : 
  forall {t} (x : {t}),
  proj1_sig (is_number x) = (Bool false) -> 
  ~ HasType (proj1_sig x) trnum.
Proof.
  intros. intro. 
  destruct x; destruct x; simpl in H0; try inv_trtype_false_faster.
  simpl in H. discriminate.
Qed.

Ltac apply_is_number_false_not_number := 
  match goal with 
  | |- ~ HasType (proj1_sig ?x) trnum => 
    match goal with 
    | [ H : proj1_sig (is_number x) = (Bool false) |- _ ] => 
       apply (is_number_false_not_number _ H) 
    end 
  end.


(* "HintDb" "the locals here are a bit useless as I have no reason to 
    believe you'll be importing this file, but just in case " *)
Create HintDb TRHints.
    #[local] Hint Unfold is_number : TRHints.
    #[local] Hint Unfold get_true_prop : TRHints.
    #[local] Hint Unfold get_false_prop : TRHints.
    #[local] Hint Unfold get_true_prop_func : TRHints.
    #[local] Hint Unfold get_false_prop_func : TRHints.
    #[local] Hint Immediate is_top : TRHints.
    #[local] Hint Immediate is_top_pair : TRHints.
    #[local] Hint Immediate pair_left : TRHints.
    #[local] Hint Immediate pair_right : TRHints.
    #[local] Hint Immediate is_number_trbool : TRHints.
    #[local] Hint Immediate is_string_trbool : TRHints.
    #[local] Hint Extern 1 => apply_proj1_sig_is_string_true : TRHints.
    #[local] Hint Extern 1 => apply_proj1_sig_is_string_false : TRHints.
    #[local] Hint Extern 0 => unfold_get_true_prop_hypothesis : TRHints.
    #[local] Hint Extern 0 => unfold_get_false_prop_hypothesis : TRHints.
    #[local] Hint Extern 1 => apply_proj1_sig_is_number_true : TRHints.
    #[local] Hint Extern 1 => apply_andTR_HasType : TRHints.
    #[local] Hint Extern 1 => apply_andTR_NotHasType : TRHints.
    #[local] Hint Extern 1 => solve_if_TR_hastype : TRHints.
    #[local] Hint Extern 1 => not_A_A : TRHints.
    #[local] Hint Extern 1 => apply_is_number_false_not_number : TRHints.
Open Scope string_scope.


Program Definition orTest {A : TRTypes} (x : {A}) : 
    {>> trbool & ((HasType x trnum) \/ (HasType x trstr))} :=
    orTR (is_number x) (is_string x).

Eval compute in (orTest 5).
Eval compute in (orTest "hi").
Eval compute in (orTest true).
Eval compute in (orTest (5, "potato")).

#[local] Obligation Tactic := try fail.

Program Definition andTest {A B : TRTypes} (x : {A}) (y : {B}) :
  {>> trbool & ((HasType x trnum)  /\ (HasType y trstr))} :=
  andTR (is_number x) (is_string y).
Next Obligation.
  really_simple_start.
Defined. Next Obligation.
  really_simple_start. 
Defined. Next Obligation. (* here *)
  really_simple_start. solve_if_TR_hastype. intuition.
  exfalso; intuition.
Defined.

Eval compute in (andTest 5 "potato").
Eval compute in (andTest 3 false).
Eval compute in (andTest true "pasta").
Eval compute in (andTest (5, "potato") false).

#[local] Obligation Tactic := try ((timeout 1 (time really_simple_start)); (timeout 1 (time new_jail))).

Program Definition ifTest_1 {t : TRTypes} (x : {t}) : {trnum} :=
  ifTR <trnum> (is_number x) x <[0]>. (* same here *)

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

(* repeat of example above 
(* this is the test that caused the move to ifTR_union! *)
Program Definition ifTest_7 {t : TRTypes} (x : {t}) : {trnum} :=
  ifTR (is_number x) x 54.

Eval compute in (ifTest_7 9).
Eval compute in (ifTest_7 "cat"). *)

#[local] Obligation Tactic := try fail. 
Program Definition ifTest_8 {t r : TRTypes} (x : {t}) (y : {r}) 
         : {t >> trbool & ((HasType x trnum) /\ (HasType y trstr) \/ (HasType x trstr))} :=
  (ifTR < all > (is_number x) (is_string y) (is_string x)).
Next Obligation.
  really_simple_start.
Defined. Next Obligation.
  really_simple_start.
Defined. Next Obligation. (* here *)
  intros. solve_if_TR_hastype. intuition.
  subst P; subst Q; subst Q''; subst Q'.
  unfold_get_true_prop_hypothesis; unfold_get_false_prop_hypothesis.

  destruct x. destruct x; simpl in H2; simpl in H1; try inv_trtype_false_faster.

Defined.

Eval compute in (ifTest_8 5 "ice cream cake").
Eval compute in (ifTest_8 5 9).
Eval compute in (ifTest_8 "potato" "cheese").
Eval compute in (ifTest_8 (5, "potato") (8, "hi")).

#[local] Obligation Tactic := try ((timeout 1 (time really_simple_start)); (timeout 1 (time new_jail))).

Program Definition ifTest_9 {t r : TRTypes} (x : {t}) (y : {r}) : {trnum} :=
(ifTR (ifTest_8 x y) 
  (ifTR (is_string x) (strlen x) (sum x (strlen y)))
  (ifTR < trnum > (is_number x) x <[54]>)). (* try to fix this without making another notation? *)

Eval compute in (ifTest_9 5 "ice cream cake").
Eval compute in (ifTest_9 5 9).
Eval compute in (ifTest_9 "potato" "cheese").
Eval compute in (ifTest_9 (5, "potato") (8, "hi")).