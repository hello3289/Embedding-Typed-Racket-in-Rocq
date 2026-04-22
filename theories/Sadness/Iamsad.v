Set Warnings "-uniform-inheritance".
Set Warnings "-ambiguous-paths".
Set Warnings "-meta-collision".
From TRresearch.Tactics Require Import tactics_all apply_predicate_lemmas hastype_tactics.
From TRresearch Require Import Definitions Predicates If Basics.
From TRresearch.Lemmas Require Import Lemmas Union_Lemmas Predicate_Lemmas.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Logic.EqdepFacts.
From Stdlib Require Import ProofIrrelevance.
#[local] Obligation Tactic := try (timeout 1 (time test_jail)).

From TRresearch.Tests Require Import If_test.

(* "HintDb" *)
Create HintDb TRHints.
    Hint Extern 0 => discriminates : TRHints.
    Hint Extern 0 => subst_filtered_var : TRHints.
    Hint Extern 0 => simpl_func : TRHints.
    Hint Extern 0 => rewrite_jail' : TRHints.
    Hint Extern 1 => apply_if_TR_union_HasType_union : TRHints.
    Hint Constructors HasType : TRHints.
    Hint Unfold is_number : TRHints.
    Hint Unfold get_true_prop : TRHints.
    Hint Immediate is_top : TRHints.
    Hint Immediate is_top_pair : TRHints.
    Hint Immediate pair_left : TRHints.
    Hint Immediate pair_right : TRHints.
    Hint Immediate is_number_trbool : TRHints.
    Hint Immediate is_string_trbool : TRHints.


(* "the thing" *)


(* "OK this is so i don't have to use an axiom but it's also extremely annoying " *)
Lemma car_driving_by : forall {A t : TRTypes} {P Q : Prop} (x : {>> A & P & Q}),
  HasType (proj1_sig x) (trunion t t) -> 
  HasType (proj1_sig x) t.
Proof. intros. inversion H; auto. Qed.

  (* "ok i'm quickly realizing that this is not the correct lemma statements at least if 
  i want to make this general" *)
Lemma bus_driving_by : forall {A t : TRTypes} {P Q : Prop} (x : {>> A & P & Q}),
  HasType (proj1_sig x) (trunion t (trunion t t)) -> 
  HasType (proj1_sig x) (trunion t t).
Proof. intros. inversion H; auto. constructor. auto. Qed.

Lemma truck_driving_by : forall {A t : TRTypes} {P Q : Prop} (x : {>> A & P & Q}),
  HasType (proj1_sig x) (trunion (trunion t t) t) -> 
  HasType (proj1_sig x) (trunion t t).
Proof. intros. inversion H; auto. constructor. auto. Qed.

From TRresearch.Lemmas Require Import HasType_lemmas.

#[local] Obligation Tactic := try fail.
Program Definition condTest {A B : TRTypes}
    (x : {A})
    (y : {B}) :
    {trnum} :=
  condTR [ (is_number x) (add1 x) ] 
         [ (is_string y) (strlen y) ]
         [ else 0 ].
Next Obligation.
  test_jail.
Defined. Next Obligation.
  test_jail.
Defined. Next Obligation.
  intros; simpl; repeat split.

  Ltac find actual_type type H := 
    match actual_type with
    | trunion type type => eapply car_driving_by in H; auto 
    | trunion type ?something_else => eapply bus_driving_by in H; find (trunion type type) type H
    | trunion ?something_else type => eapply truck_driving_by in H; find (trunion type type) type H
    end.

  match goal with 
  | |- HasType (proj1_sig (if_TR_union ?pred ?true_branch ?false_branch)) ?type => 
    match type of (if_TR_union pred true_branch false_branch) with
    | {t : TRValues | HasType t ?actual_type /\ _ /\ _ } => idtac actual_type ; 
      tryif (guard actual_type = type) 
            then try auto; idtac "fuck" 
            else 
              let H := fresh "H" in 
              eassert (HasType (proj1_sig (if_TR_union pred true_branch false_branch)) actual_type) as H by (apply if_TR_union_HasType_union);
              find actual_type type H
    end 
  end.


  (* 
  refine (i_hate_my_life_4 (is_number x)
                           (fun H : HasType (proj1_sig x) trnum => add1 [proj1_sig x])
                           (fun _ : ~ HasType (proj1_sig x) trnum =>
                              if_TR_union (is_string y)
                              (fun H : HasType (proj1_sig y) trstr => strlen [proj1_sig y])
                              (fun _ : ~ HasType (proj1_sig y) trstr => 0))).

  refine (i_hate_my_life_3 (HasType (proj1_sig x) trnum) True (True \/ True) (~(HasType (proj1_sig x) trnum)) True (True \/ True) trnum (is_number x) 
           (fun H : HasType (proj1_sig x) trnum => add1 [proj1_sig x])
(fun _ : ~ HasType (proj1_sig x) trnum =>
if_TR_union (is_string y)
(fun H : HasType (proj1_sig y) trstr => strlen [proj1_sig y])
(fun _ : ~ HasType (proj1_sig y) trstr => 0))).


  
  pose proof i_hate_my_life.

  specialize (H (HasType (proj1_sig x) trnum) True True (~(HasType (proj1_sig x) trnum)) True True trnum (is_number x)).

  specialize
    (H (fun P : HasType (proj1_sig x) trnum => 
          (add1 (idk_what_to_call_this x P)))).

  pose proof (i_hate_my_life (HasType (proj1_sig y) trstr) True True (~(HasType (proj1_sig y) trstr)) True True trnum (is_string y)).

  specialize 
    (H0 (fun P : HasType (proj1_sig y) trstr => 
            (strlen (idk_what_to_call_this y P)))).

  specialize
    (H0 (fun Q : ~ HasType (proj1_sig y) trstr => 
          0)).

  
  specialize 
    (H (fun Q : ~ HasType (proj1_sig x) trnum => 
          (@idk_what_to_call_this _ trnum _ _
            (if_TR_union (is_string y)
              (fun H1 : HasType (proj1_sig y) trstr => strlen [proj1_sig y])
              (fun _ : ~ HasType (proj1_sig y) trstr => 0))
            H0))).
  
  

  assert (forall P  , P -> (P /\ (P /\ ((proj1_sig x) <> false) -> True) /\ (P /\ ((proj1_sig x) = false) -> True))).
  intros; auto.
  assert (forall P  , P -> (P /\ (P /\ ((proj1_sig y) <> false) -> True) /\ (P /\ ((proj1_sig y) = false) -> True))).
  intros; auto.
  specialize (H (HasType (proj1_sig x) trnum)) as J0.
  specialize (H0 (HasType (proj1_sig y) trstr)) as J1.

  pose proof (i_hate_my_life (HasType (proj1_sig x) trnum) True
  True (~ (HasType (proj1_sig x) trnum )) True True trnum (is_number x)
  (fun H0 : HasType (proj1_sig x) trnum => 
      add1 (exist (fun t => (HasType t trnum /\ 
                            (((HasType t trnum) /\ (t <> Bool false )) -> True) /\ 
                            (((HasType t trnum) /\ (t = Bool false )) -> True))) 
                  (proj1_sig x)
                  (J0 H0)
                  ))).
  pose proof (i_hate_my_life (HasType (proj1_sig y) trstr) True True
  (~ HasType (proj1_sig y) trstr) True True trnum (is_string y)
  (fun H2 : HasType (proj1_sig y) trstr =>
    strlen (exist (fun t => (HasType t trstr /\ 
                            (((HasType t trstr) /\ (t <> Bool false )) -> True) /\ 
                            (((HasType t trstr) /\ (t = Bool false )) -> True))) 
                  (proj1_sig y)
                  (J1 H2)
                  ))
  (fun _ : ~ HasType (proj1_sig y) trstr => 0)).

  pose proof (has_type_to_exists _ H2).

  pose proof (fun _ : ~ HasType (proj1_sig x) trnum =>
if_TR_union (is_string y)
(fun H3 : HasType (proj1_sig y) trstr =>
strlen [proj1_sig y])
(fun _ : ~ HasType (proj1_sig y) trstr => 0)).

  assert ((HasType
(proj1_sig
(if_TR_union (is_string y)
(fun H2 : HasType (proj1_sig y) trstr => strlen [proj1_sig y])
(fun _ : ~ HasType (proj1_sig y) trstr => 0))) trnum) ->
(HasType
(proj1_sig
(if_TR_union (is_string y)
(fun H2 : HasType (proj1_sig y) trstr => strlen [proj1_sig y])
(fun _ : ~ HasType (proj1_sig y) trstr => 0))) trnum) /\ 
((HasType
(proj1_sig
(if_TR_union (is_string y)
(fun H2 : HasType (proj1_sig y) trstr => strlen [proj1_sig y])
(fun _ : ~ HasType (proj1_sig y) trstr => 0))) trnum) /\ 
(proj1_sig (if_TR_union (is_string y)
(fun H2 : HasType (proj1_sig y) trstr => strlen [proj1_sig y])
(fun _ : ~ HasType (proj1_sig y) trstr => 0))) <> (Bool false) -> True) /\ 
((HasType
(proj1_sig
(if_TR_union (is_string y)
(fun H2 : HasType (proj1_sig y) trstr => strlen [proj1_sig y])
(fun _ : ~ HasType (proj1_sig y) trstr => 0))) trnum) /\ 
(proj1_sig (if_TR_union (is_string y)
(fun H2 : HasType (proj1_sig y) trstr => strlen [proj1_sig y])
(fun _ : ~ HasType (proj1_sig y) trstr => 0))) = (Bool false) -> True)) as J2.
  intro; auto.

  pose proof (H0 ((fun _ : ~ HasType (proj1_sig x) trnum =>
    (exist (fun t => (HasType t trnum /\ 
                            (((HasType t trnum) /\ (t <> Bool false )) -> True) /\ 
                            (((HasType t trnum) /\ (t = Bool false )) -> True)))
    (if_TR_union (is_string y)
      (fun H2 : HasType (proj1_sig y) trstr =>
      strlen [proj1_sig y])
      (fun _ : ~ HasType (proj1_sig y) trstr => 0)))
    H1))).


  (fun _ : (~ HasType (proj1_sig x) trnum) =>
if_TR_union (is_string y)
(fun H1 : HasType (proj1_sig y) trstr =>
strlen [proj1_sig y])
(fun _ : ~ HasType (proj1_sig y) trstr => 0))                
                  
                  
                  ).
  eapply H0.
  test_jail. *)
