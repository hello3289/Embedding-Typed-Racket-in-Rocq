Set Warnings "-uniform-inheritance".
Set Warnings "-ambiguous-paths".
Set Warnings "-meta-collision".
From TRresearch.Tactics Require Import tactics_all.
From TRresearch Require Import Definitions.
From TRresearch.Lemmas Require Import Lemmas Union_Lemmas.
From Stdlib Require Import EqNat.
#[local] Obligation Tactic := try (timeout 1 test_jail).


Create HintDb TRHints.
#[local] Hint Immediate pair_left : TRHints.
#[local] Hint Immediate pair_right : TRHints.

Lemma subsume : forall  {A} (P P' Q Q' : Prop),
  (P -> P') -> (Q -> Q') ->
  {>> A & P & Q} -> {>> (A) & P'  & Q'}.
Proof.
  intros.
  destruct H1 as [x [H2 [H3 H4]]].
  econstructor. 
  make_constructor; eauto.
Defined.

Lemma subsume' : forall  A (P' P'' Q' Q'' : Prop), {>> (A) & P'' & Q''} -> {>> (A) & P' \/ P'' & Q' \/ Q''}.
Proof.
  intros. apply subsume with P'' Q''; auto.
Defined.


Definition if_TR {A : TRTypes} {P P' Q Q' : Prop} 
                          (x : {t >> trbool & P & Q})                        
                          (y : P -> {t >> A & P' & Q'})
                          (z : Q -> {t >> A & P' & Q'}) : 
                          {t >> A & P' & Q'}. (* A union B *)
Proof. 
  destructTR x;
  destruct x;
  try destruct b; 
  try (apply y; apply x1; split; try (auto; discriminate); fail).
  apply z; apply x2; split; auto.
Defined.

Ltac idk_man := 
  match goal with 
  | [ b : bool |- _ ] => destruct b; (apply unionL; idk_man_part2 false; fail) + (apply unionR; idk_man_part2 true)
  | [ n : ?type |- _ ] =>  
      apply unionL; idk_man_part2 false
  end.

Fixpoint eqb (a b : TRTypes) : bool := 
  match a , b with 
  | trnum , trnum => true 
  | trbool , trbool => true 
  | trstr , trstr => true 
  | trvoid , trvoid => true 
  | (trpair A B) , (trpair A' B') => andb (eqb A A') (eqb B B')
  | (trvec n) , (trvec n') => (Nat.eqb n n')
  | trlist , trlist => true 
  | (trunion A B) , (trunion A' B') => andb (eqb A A') (eqb B B')
  | trtop , trtop => true 
  | _ , _ => false 
  end.

Definition tr_union (a b : TRTypes) : TRTypes :=
  if (eqb a b) then a else (trunion a b).

Lemma eqb_true : forall (A B : TRTypes), 
  true = eqb A B -> eq A B.
Proof. intros. generalize dependent B.
  induction A; intros.
  induction B; simpl in H; try inversion H; auto.
  induction B; simpl in H; try inversion H; auto.
  induction B; simpl in H; try inversion H; auto.
  induction B; simpl in H; try inversion H; auto.
  destruct B; simpl in H; try inversion H; auto.
    specialize (IHA1 B1).
    specialize (IHA2 B2).
    symmetry in H.
    apply (Bool.andb_true_iff _ _) in H.
    destruct H; symmetry in H; symmetry in H0.
    specialize (IHA1 H).
    specialize (IHA2 H0).
    rewrite IHA1. rewrite IHA2. auto.
  destruct B; simpl in H; try inversion H; auto.
  symmetry in H. apply (PeanoNat.Nat.eqb_eq _ _) in H. rewrite H; auto.
  destruct B; simpl in H; try inversion H; auto.
  destruct B; simpl in H; try inversion H; auto.
    specialize (IHA1 B1).
    specialize (IHA2 B2).
    symmetry in H.
    apply (Bool.andb_true_iff _ _) in H.
    destruct H; symmetry in H; symmetry in H0.
    specialize (IHA1 H).
    specialize (IHA2 H0).
    rewrite IHA1. rewrite IHA2. auto.
  destruct B; simpl in H; try inversion H; auto.
Qed.
  

Eval compute in tr_union trnum trnum.
Eval compute in tr_union trnum trstr.

Definition if_TR_union {A B : TRTypes} {P P' P'' Q Q' Q'' : Prop} 
                          (x : {>> trbool & P & Q})                        
                          (y : P -> {>> A & P' & Q'})
                          (z : Q -> {>> B & P'' & Q''}) : 
                          {>> (tr_union A B) & (P' \/ P'') & (Q' \/ Q'')}.
Proof.
  destructTR x.
  destruct x; try inv_trtype_false_faster.
  destruct b.
  - assert (J : (Bool true) <> (Bool false)) by (intro H; inversion H).
    assert (J1 : HasType true trbool /\ Bool true <> Bool false) by (split; auto).
    specialize (x1 J1).
    specialize (y x1).
    destructTR y.
    eassert (J2 : 
      ((HasType y (tr_union A B)) /\ 
       (HasType y (tr_union A B) /\ y <> Bool false -> P' \/ P'') /\ 
       (HasType y (tr_union A B) /\ y = Bool false -> Q' \/ Q''))).
      + repeat split.
        unfold tr_union. destruct (eqb A B); try apply HtUnion_L; auto.
        all : (intro; left; apply y1 + apply y2; split; destruct H; auto).
      + exact 
        (exist (fun t => 
                HasType t (tr_union A B) /\
                (HasType t (tr_union A B) /\ t <> false -> P' \/ P'') /\
                (HasType t (tr_union A B) /\ t = false -> Q' \/ Q''))
              y
              J2).
  - assert (J : (Bool false) = (Bool false)) by autoTR.
    assert (J1 : HasType false trbool /\ Bool false = Bool false) by (split; auto).
    specialize (x2 J1).
    specialize (z x2).
    destructTR z.
    eassert (J2 : 
      ((HasType z (tr_union A B)) /\ 
       (HasType z (tr_union A B) /\ z <> Bool false -> P' \/ P'') /\ 
       (HasType z (tr_union A B) /\ z = Bool false -> Q' \/ Q''))).
      + repeat split.
        unfold tr_union. remember (eqb A B). 
        destruct b. apply eqb_true in Heqb. rewrite Heqb.
        auto.
        try apply HtUnion_R; auto.
        all : (intro; right; apply z1 + apply z2; split; destruct H; auto).
      + exact 
        (exist (fun t => 
                HasType t (tr_union A B) /\
                (HasType t (tr_union A B) /\ t <> false -> P' \/ P'') /\
                (HasType t (tr_union A B) /\ t = false -> Q' \/ Q''))
              z
              J2).
Defined.

Lemma tr_union_subsume: forall {a A B}, HasType a (tr_union A B) -> HasType a (trunion A B).
Proof.
  intros.
  unfold tr_union in H.
  remember (eqb A B).
  destruct b.
  - apply HtUnion_L; auto.
  - auto.
Qed.


Program Definition notTR {P Q : Prop} (x : {>> trbool & P & Q}) : {>> trbool & Q & P} :=
  match x with
  | Bool false => Bool true
  | _r => Bool false
  end.

(* "Notations" *)
(* one day i will make these notations into one... *)
Notation " 'ifTR' < 'second' > A B C " := 
  (let P := (get_true_prop A) in
    (let P' := (get_true_prop B) in
      (@if_TR _ P 
              (P /\ P') 
              (~P) 
              (~(P /\ P')) 
              A (fun _ => B) (fun _ => giveType C)))) 
  (at level 0, A at next level, 
  B at next level, C at next level).

Notation " 'ifTR' < 'third' > A B C " := 
  (let P := (get_true_prop A) in
    (let P' := (get_true_prop C) in 
      (@if_TR _ P 
             (P \/ P') 
             (~P) 
             (~(P \/ P')) 
             A (fun _ => B) (fun _ => C)))) 
  (at level 0, A at next level, 
  B at next level, C at next level).

Notation " 'ifTR' < 'all' > A B C " := 
  (let P := (get_true_prop A) in
    (let Q := (get_true_prop B) in
      (let R := (get_true_prop C) in 
        (@if_TR trbool P (* hmm *)
              ((P /\ Q) \/ R) 
              (~P) 
              (~((P /\ Q) \/ R)) 
              A (fun _ => B) (fun _ => C))))) 
  (at level 0, A at next level, B at next level, C at next level).  

Notation " 'ifTR' A B C " := 
  (if_TR_union A (fun _ => B) (fun _ => C))
  (at level 0, A at next level, B at next level, C at next level). 
 

Notation " 'condTR' [ A B ] [ C D ] [ 'else' E ]" :=
  (ifTR A B (ifTR C D E)) (A at level 0, C at next level, E at next level).

Notation " 'orTR' A B " :=
  (ifTR < third > A A B)
  (at level 10, A at next level, B at next level).

Notation " 'andTR' A B " :=
  (ifTR < second > A B A) 
  (at level 10, A at next level, B at next level).


Notation " 'orTR_2' A B " :=
  (ifTR A A B)
  (at level 10, A at next level, B at next level).

Notation " 'andTR_2' A B " :=
  (ifTR A B A)
  (at level 10, A at next level, B at next level).