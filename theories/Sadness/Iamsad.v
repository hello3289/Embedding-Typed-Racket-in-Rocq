Set Warnings "-uniform-inheritance".
Set Warnings "-ambiguous-paths".
Set Warnings "-meta-collision".
From TRresearch.Tactics Require Import tactics_all apply_predicate_lemmas.
From TRresearch Require Import Definitions Predicates If Basics.
From TRresearch.Lemmas Require Import Lemmas Union_Lemmas Predicate_Lemmas.
From Stdlib Require Import Strings.String.
#[local] Obligation Tactic := try fail.

From TRresearch.Tests Require Import If_test.

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

Lemma i_hate_my_life : forall (P P' P'' Q Q' Q'' : Prop) (t : TRTypes) (x : {>> trbool & P & Q } )
  (y : P -> {>> t & P' & Q'})
  (z : Q -> {>> t & P'' & Q''}),
  HasType (proj1_sig (if_TR_union x y z))
          t.
Proof. intros. destructTR x. destruct x; try inv_trtype_false_faster.
  simpl. destruct b; simpl.
  - destructTR y; simpl. apply y1.
  - destructTR z; simpl. apply z1.
Qed.

(* this is for attempting what carlo told sam, who told me to do *)
Lemma i_hate_my_life_2 : forall (P P' P'' Q Q' Q'' : Prop) (t : TRTypes) 
  (x : {>> trbool & P & Q } )
  (y : P -> {>> t & P' & Q'})
  (z : Q -> {>> t & P'' & Q''}),
  HasType (proj1_sig (if_TR_union x y z))
          t.
Proof. intros. destructTR x. destruct x; try inv_trtype_false_faster.
  simpl. destruct b; simpl.
  - destructTR y; simpl. apply y1.
  - destructTR z; simpl. apply z1.
Qed.

Lemma an_incredibly_specific_i_hate_my_life : forall {P P' P'' Q Q' Q'' : Prop} (x : {>> trbool & P & Q } )
  (y : {>> trnum & P' & Q'})
  (z : {>> trnum & P'' & Q''}), 
  (exists (n : nat), 
    (proj1_sig 
      (if_TR_union x 
                   (fun _ => y)
                   (fun _ => z))) 
      = 
      (Num n)).
Proof.
  intros. destructTR x. destruct x; try inv_trtype_false_faster.
  destruct b.
  - destructTR y; destruct y; try inv_trtype_false_faster. simpl. exists n; reflexivity.
  - destructTR z; destruct z; try inv_trtype_false_faster. simpl. exists n; reflexivity.
Qed.

Lemma why_has_my_life_come_to_this : forall {A : TRTypes} (x : {A}),
  HasType (proj1_sig x) trnum -> 
  exists n : nat, proj1_sig x = Num n.
Proof. intros. destructTR x; destruct x; simpl in H; try inv_trtype_false_faster. exists n; reflexivity. Qed.

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
  test_jail.