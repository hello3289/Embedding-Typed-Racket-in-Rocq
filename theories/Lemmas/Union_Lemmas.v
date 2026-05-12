Set Warnings "-uniform-inheritance".
Set Warnings "-ambiguous-paths".
Set Warnings "-meta-collision".
From TRresearch.Tactics Require Import tactics_all.
From TRresearch Require Import Definitions.
From TRresearch.Lemmas Require Import Lemmas.

Create HintDb TRHints.
  #[local] Hint Immediate is_top : TRHints.
  #[local] Hint Immediate is_top_pair : TRHints.

Lemma unionL : forall A B (P Q : Prop), {>> A & P & Q} -> {>> (U A B) & P & Q}.
Proof.
  intros.
  destructTR H.
  assert (HasType H (trunion A B) /\ (HasType H (trunion A B) /\ H <> Bool false -> P) /\ (HasType H (trunion A B) /\ H = Bool false -> Q)).
  -  repeat split; eauto with TRHints; intros; destruct H3; smarter_apply; split; auto.
  - exact (exist (fun t : TRValues => 
                    HasType t (trunion A B) /\ 
                    (HasType t (trunion A B) /\ t <> Bool false -> P) /\ 
                    (HasType t (trunion A B) /\ t = Bool false -> Q))
                 H
                 H3).
Defined.

Lemma unionR : forall A B (P Q : Prop), {>> B & P & Q} -> {>> (U A B) & P & Q}.
Proof.
  intros.
  destructTR H.
  assert (HasType H (trunion A B) /\ (HasType H (trunion A B) /\ H <> Bool false -> P) /\ (HasType H (trunion A B) /\ H = Bool false -> Q)).
  -  repeat split; eauto with TRHints; intros; destruct H3; smarter_apply; split; auto.
  - exact (exist (fun t : TRValues => 
                    HasType t (trunion A B) /\ 
                    (HasType t (trunion A B) /\ t <> Bool false -> P) /\ 
                    (HasType t (trunion A B) /\ t = Bool false -> Q))
                 H
                 H3).
Defined.
          
Lemma union_not_left : forall {A B} (x : {trunion A B}),
  ~ HasType (proj1_sig x) A -> 
  HasType (proj1_sig x) B.
Proof. really_simple_start. 
  destructTR x. 
  inversion x0; subst *; try (destruct H; auto; fail); auto.
Qed.

Lemma union_not_right : forall {A B} (x : {trunion A B}),
  ~ HasType (proj1_sig x) B -> 
  HasType (proj1_sig x) A.
Proof. really_simple_start. 
  destructTR x. 
  inversion x0; subst *; try (destruct H; auto; fail); auto.
Qed.
  
Lemma not_either_union : forall {t} {A B} (x : {t}),
  ~ HasType (proj1_sig x) A -> 
  ~ HasType (proj1_sig x) B -> 
  ~ HasType (proj1_sig x) U A B.
Proof. really_simple_start. inversion H1; 
  try (destruct H; auto; fail); try (destruct H0; auto).
Qed.
