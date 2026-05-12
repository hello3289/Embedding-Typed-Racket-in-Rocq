Set Warnings "-uniform-inheritance".
Set Warnings "-ambiguous-paths".
Set Warnings "-meta-collision".
From TRresearch.Tactics Require Import tactics_all.
From TRresearch Require Import Definitions If.

Lemma if_TR_union_HasType_union : forall {P P' P'' Q Q' Q'' : Prop} {t1 t2 : TRTypes} 
  (x : {>> trbool & P & Q } )
  (y : P -> {>> t1 & P' & Q'})
  (z : Q -> {>> t2 & P'' & Q''}),
  HasType (proj1_sig (if_TR_union x y z))
          (tr_union t1 t2).
Proof. intros. destructTR x. destruct x; try inv_trtype_false_faster.
  simpl. destruct b; simpl.
  - destructTR y; simpl. 
    unfold tr_union.
    destruct (eqb t1 t2).
    + auto.
    + apply HtUnion_L. auto.
  - destructTR z; simpl.
    unfold tr_union.
    remember (eqb t1 t2).
    destruct b.
    + apply eqb_true in Heqb. rewrite Heqb. auto.
    + apply HtUnion_R. auto.
Qed.

Lemma andTR_HasType_left : forall {A B t1 t2 : TRTypes} {x : {A}} {y : {B}}
  {pred1 : (forall x0 : {A}, {>> trbool & (HasType (proj1_sig x0) t1)})}
  {pred2 : (forall y0 : {B}, {>> trbool & (HasType (proj1_sig y0) t2)})},
  proj1_sig (andTR_2 (pred1 x) (pred2 y)) <> Bool false -> 
  (HasType (proj1_sig x) t1).
Proof. intros.
  destructTR_fresh (pred1 x). destruct x0; try inv_trtype_false_faster.
  destructTR_fresh (pred2 y). destruct x0; try inv_trtype_false_faster.
  destruct b; destruct b0; simpl in H; try discriminates.
  apply x2; split; auto.
Qed.

Lemma andTR_HasType_right : forall {A B t1 t2 : TRTypes} {x : {A}} {y : {B}}
  {pred1 : (forall x0 : {A}, {>> trbool & (HasType (proj1_sig x0) t1)})}
  {pred2 : (forall y0 : {B}, {>> trbool & (HasType (proj1_sig y0) t2)})},
  proj1_sig (andTR_2 (pred1 x) (pred2 y)) <> Bool false -> 
  (HasType (proj1_sig y) t2).
Proof. intros.
  destructTR_fresh (pred1 x). destruct x0; try inv_trtype_false_faster.
  destructTR_fresh (pred2 y). destruct x0; try inv_trtype_false_faster.
  destruct b; destruct b0; simpl in H; try discriminates.
  apply x5; split; auto.
Qed.

Lemma andTR_HasType_false : forall {A B t1 t2 : TRTypes} {x : {A}} {y : {B}}
  {pred1 : (forall x0 : {A}, {>> trbool & (HasType (proj1_sig x0) t1)})}
  {pred2 : (forall y0 : {B}, {>> trbool & (HasType (proj1_sig y0) t2)})},
  proj1_sig (andTR_2 (pred1 x) (pred2 y)) = Bool false -> 
  ~(HasType (proj1_sig x) t1 /\ HasType (proj1_sig y) t2).
Proof. intros.
  destructTR_fresh (pred1 x). destruct x0; try inv_trtype_false_faster.
  destructTR_fresh (pred2 y). destruct x0; try inv_trtype_false_faster.
  intro H0; destruct H0.
  destruct b; destruct b0; simpl in H; try discriminates.
  apply x6; repeat split; auto.
  apply x3; repeat split; auto.
  apply x6; repeat split; auto.
Qed.

Lemma hastype_union {t1 t2 A : TRTypes} {P Q : Prop} 
  {x : {>> A & P & Q}} (H : HasType (proj1_sig x) (U t1 t2)) : HasType (proj1_sig x) t1 \/ HasType (proj1_sig x) t2.
  destructTR x.
  inversion H; auto.
Qed.