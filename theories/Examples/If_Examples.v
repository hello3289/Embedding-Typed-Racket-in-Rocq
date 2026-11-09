Set Warnings "-uniform-inheritance".
Set Warnings "-ambiguous-paths".
Set Warnings "-meta-collision".
From TRresearch.Tactics Require Import tactics_all apply_predicate_lemmas prove_ifTR_branches apply_union_lemmas apply_if_lemmas hastype_tactics.
From TRresearch Require Import Definitions Predicates If Basics.
From TRresearch.Lemmas Require Import Lemmas Union_Lemmas Predicate_Lemmas.
From Stdlib Require Import Strings.String.
#[local] Obligation Tactic := try ((timeout 1 (time really_simple_start)); (timeout 1 (time new_jail))).

Ltac unfold_get_false_prop_hypothesis := 
  match goal with 
  | [ H : get_false_prop _ |- _ ] => unfold get_false_prop in H 
  end.

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

Lemma is_top : 
  forall {t} (x : {t}),
  HasType (proj1_sig x) trtop.
Proof. constructor. Qed.


Lemma car_is_number : 
  forall {A B} (p : {trpair A B}),
  proj1_sig (is_number (car p)) <> false -> 
  HasType (proj1_sig p) (trpair trnum B).
Proof. test_jail.
  destruct (is_number _) in H.
  destruct a. destruct x; try inv_trtype_false_faster.
  destruct b. test_jail. inversion p0.
  constructor; auto.
  test_jail. 
Qed.


Lemma car_is_not_number : 
  forall {A B} (p : {trpair A B}),
  proj1_sig (is_number (car p)) = false -> 
  HasType (proj1_sig p) (trpair trnum B) -> 
  False.
Proof. test_jail.
  destruct (is_number _) in H.
  destruct a. destruct x; try inv_trtype_false_faster.
  destruct b. test_jail. destruct a. test_jail.
  inversion H0. intuition.
Qed.

Lemma car_is_string : 
  forall {A B} (p : {trpair A B}),
  proj1_sig (is_string (car p)) <> false -> 
  HasType (proj1_sig p) (trpair trstr B).
Proof. test_jail.
  destruct (is_string _) in H.
  destruct a. destruct x; try inv_trtype_false_faster.
  destruct b. test_jail. inversion p0.
  constructor; auto.
  test_jail. 
Qed.

Lemma car_is_not_string : 
  forall {A B} (p : {trpair A B}),
  proj1_sig (is_string (car p)) = false -> 
  HasType (proj1_sig p) (trpair trstr B) -> 
  False.
Proof. test_jail.
  destruct (is_string _) in H.
  destruct a. destruct x; try inv_trtype_false_faster.
  destruct b. test_jail. destruct a. test_jail.
  inversion H0. intuition.
Qed.

Lemma car_is_bool : 
  forall {A B} (p : {trpair A B}),
  proj1_sig (is_bool (car p)) <> false -> 
  HasType (proj1_sig p) (trpair trbool B).
Proof. test_jail.
  destruct (is_bool _) in H.
  destruct a. destruct x; try inv_trtype_false_faster.
  destruct b. test_jail. inversion p0.
  constructor; auto.
  test_jail. 
Qed.

Lemma car_is_not_bool : 
  forall {A B} (p : {trpair A B}),
  proj1_sig (is_bool (car p)) = false -> 
  HasType (proj1_sig p) (trpair trbool B) -> 
  False.
Proof. test_jail.
  destruct (is_bool _) in H.
  destruct a. destruct x; try inv_trtype_false_faster.
  destruct b. test_jail. destruct a. test_jail.
  inversion H0. intuition.
Qed.

Lemma car_cdr_type_pair : 
  forall {A B C D} (p : {trpair A B}),
  HasType (proj1_sig (car p)) C -> 
  HasType (proj1_sig (cdr p)) D -> 
  HasType (proj1_sig p) (trpair C D).
Proof. 
  intros. destructTR p. destruct p; try inv_trtype_false_faster.
  simpl in H; simpl in H0.
  constructor; auto.
Qed.

Ltac apply_car_is_not_number := 
  match goal with 
  | [ H : proj1_sig (is_number (car ?p)) = Bool false |- _ ] => 
    match goal with 
    | [ H1 : HasType (proj1_sig p) (trpair trnum ?B) |- _ ] => 
      apply (car_is_not_number p H H1)
    end 
  | [ H : proj1_sig (is_bool (car ?p)) = Bool false |- _ ] => 
    match goal with 
    | [ H1 : HasType (proj1_sig p) (trpair trbool ?B) |- _ ] => 
      apply (car_is_not_bool p H H1)
    end 
  | [ H : proj1_sig (is_string (car ?p)) = Bool false |- _ ] => 
    match goal with 
    | [ H1 : HasType (proj1_sig p) (trpair trstr ?B) |- _ ] => 
      apply (car_is_not_string p H H1)
    end 
  end.


  Ltac apply_car_cdr_type_pair := 
  match goal with 
  | [ H : HasType (proj1_sig (car ?p)) ?A |- _ ] => 
    match goal with 
    | [ H1 : HasType (proj1_sig (cdr p)) ?B |- _ ] => 
      match goal with 
      | |- HasType (proj1_sig p) (trpair A B) => 
        apply (car_cdr_type_pair p H H1)
      end 
    end 
  end.

Program Definition false_val : {>> trbool & False & True}.
  econstructor. constructor. exact (HtBool false).
  repeat split. intro. destruct H as [?H ?H]. destruct H0; auto.
Defined.

Ltac false_prop := 
  match goal with 
  | [ H : get_true_prop false_val |- _ ] => 
    exfalso; auto 
  end.

(* "HintDb" *)
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
    #[local] Hint Immediate is_bool_trbool : TRHints.
    #[local] Hint Immediate car_is_bool : TRHints.
    #[local] Hint Immediate car_is_number : TRHints.
    #[local] Hint Immediate car_is_string : TRHints.
    #[local] Hint Extern 1 => prove_if_TR_branches : TRHints.
    #[local] Hint Extern 1 => apply_proj1_sig_is_string_true : TRHints.
    #[local] Hint Extern 1 => apply_proj1_sig_is_string_false : TRHints.
    #[local] Hint Extern 1 => apply_proj1_sig_is_number_true : TRHints.
    #[local] Hint Extern 0 => unfold_get_true_prop_hypothesis : TRHints.
    #[local] Hint Extern 0 => unfold_get_false_prop_hypothesis : TRHints.
    #[local] Hint Extern 1 => apply_union_not : TRHints.
    #[local] Hint Extern 1 => apply_not_either_union : TRHints.
    #[local] Hint Extern 1 => apply_notTR_is_bool : TRHints.
    #[local] Hint Extern 1 => apply_notTR_bool_true_is_false : TRHints. 
    #[local] Hint Extern 1 => apply_notTR_bool_false_is_true : TRHints.
    #[local] Hint Extern 1 => not_A_A : TRHints.
    #[local] Hint Extern 1 => apply_is_number_false_not_number : TRHints.
    #[local] Hint Extern 0 => solve_if_TR_hastype : TRHints.
    #[local] Hint Extern 1 => apply_car_is_not_number : TRHints.
    #[local] Hint Extern 1 => apply_car_cdr_type_pair : TRHints.
    #[local] Hint Extern 1 => false_prop : TRHints.
    #[local] Hint Constructors HasType : TRHints.

    (* #[local] Hint Extern 1 => solve_if_TR_hastype : TRHints. *)
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
  ifTR (andTR (is_number x) (is_string y))
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
    (ifTR < all > (is_number x) (is_string y) false_val)
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
      (ifTR < all > p p (is_string x)))
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

#[local] Obligation Tactic := try fail.

Program Definition if_more_ex1 {t r : TRTypes} (x : {t}) (y : {r}) 
         : {t >> trbool & (((HasType x trnum) /\ (HasType y trstr)) \/ (HasType x trstr))} :=
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
    
#[local] Obligation Tactic := try ((timeout 1 (time really_simple_start)); (timeout 1 (time new_jail))).

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
  ifTR < trtop > (is_string x) (strlen x) x.

Eval compute in (pos_success "potatoes").
Eval compute in (pos_success 8).
Eval compute in (pos_success true).
Eval compute in (pos_success ("hi", false)).

Program Definition neg_success (x : {U trstr trnum}) : {trnum} :=
  (ifTR (is_string x) (strlen x) (add1 x)).

Program Definition neg_succ_test1 := (neg_success <["hi"]>).
Program Definition neg_succ_test2 := (neg_success <[7]>).

Eval compute in neg_succ_test2.
Eval compute in neg_succ_test1.

    

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

#[local] Obligation Tactic := try fail.

Program Definition h (x : {U trstr (U trnum trbool)}) : {trnum} :=
  ifTR (andTR (notTR (is_bool x)) (notTR (is_number x)))
       (strlen x)
       0.
Next Obligation.
  really_simple_start. test_jail. (* here *)
Defined. Next Obligation.
  really_simple_start.
Defined. Next Obligation.
  really_simple_start.
Defined. Next Obligation.
  really_simple_start.
Defined.

#[local] Obligation Tactic := try ((timeout 1 (time really_simple_start)); (timeout 1 (time new_jail))).

Program Definition h_test1 := h <["potatoes"]>.
Program Definition h_test2 := h <[5]>.
Program Definition h_test3 := h <[Bool false]>.

Eval compute in h_test1.
Eval compute in h_test2.
Eval compute in h_test3.


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