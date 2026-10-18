Set Warnings "-ambiguous-paths".
From TRresearch Require Import Definitions_new.
From TRresearch Require Import Lemmas_new.
From Corelib Require Import Lists.ListDef.
Require Import Program.Tactics.

Lemma subsume : forall  {A} (P P' Q Q' : Prop),
  (P -> P') -> (Q -> Q') ->
  {>> A & P & Q} -> {>> (A) & P'  & Q'}.
Proof.
  intros.
  destruct H1 as [x [H2 [H3 H4]]].
  econstructor. 
  repeat split. eauto. intros. apply (H (H3 H1)). intros. apply (H0 (H4 H1)).
Defined.

Lemma subsume' : forall  A (P' P'' Q' Q'' : Prop), {>> (A) & P'' & Q''} 
                    -> {>> (A) & P' \/ P'' & Q' \/ Q''}.
Proof.
  intros. apply subsume with P'' Q''; auto.
Defined.


Definition if_TR {A : TRTypes} {P P' Q Q' : Prop} 
                          (x : {t >> trbool & P & Q})                        
                          (y : P -> {t >> A & P' & Q'})
                          (z : Q -> {t >> A & P' & Q'}) : 
                          {t >> A & P' & Q'}. 
Proof. 
  destruct x as [?x [?x [?x ?x]]].
  destruct x; try (exfalso; inversion x0; fail).
  try destruct b; 
  try (apply y; apply x1; split; try (auto; discriminate); fail).
  apply z; apply x2; split; auto.
Defined.



Definition if_TR_union {A B : TRTypes} {P P' P'' Q Q' Q'' : Prop} 
                          (x : {>> trbool & P & Q})                        
                          (y : P -> {>> A & P' & Q'})
                          (z : Q -> {>> B & P'' & Q''}) : 
                          {>> (tr_union A B) & (P' \/ P'') & (Q' \/ Q'')}.
Proof.
  destruct x as [?x [?x [?x ?x]]].
  destruct x; try inv_trtype_false_faster_2.
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
  - assert (J : (Bool false) = (Bool false)) by constructor.
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

Notation " 'ifTR' A B C " := 
  (if_TR_union A (fun _ => B) (fun _ => C))
  (at level 0, A at next level, B at next level, C at next level).



Program Definition is_number {t : TRTypes} (x : {t}) : 
                  {>> trbool & (HasType x trnum)} :=
  match x with
  | Num n => Bool true
  | _r => Bool false
  end.
Next Obligation.
  repeat split; try constructor. intro H; destruct H as [a b]; inversion b.
Defined. Next Obligation.
  repeat split; try constructor. 
  intro H; destruct H as [a b]; destruct b; auto.
  intro H; intro J; inversion J; subst *.
  specialize (n n0) as J1; destruct J1; auto. 
Defined.

Program Definition is_string {t : TRTypes} (x : {t}) : 
                  {>> trbool & (HasType x trstr)} :=
  match x with
  | Str s => Bool true
  | _r => Bool false
  end.
Next Obligation.
  repeat split; try constructor. intro H; destruct H as [a b]; inversion b.
Defined. Next Obligation.
  repeat split; try constructor. 
  intro H; destruct H as [a b]; destruct b; auto.
  intro H; intro J; inversion J; subst *.
  specialize (n s) as J1; destruct J1; auto. 
Defined.
  
Program Definition is_bool {t : TRTypes} (x : {t}) : 
                  {>> trbool & (HasType x trbool)} :=
  match x with
  | Bool b => Bool true
  | _r => Bool false
  end.
Next Obligation.
  repeat split; try constructor. intro H; destruct H as [a b1]; inversion b1.
Defined. Next Obligation.
  repeat split; try constructor. 
  intro H; destruct H as [a b]; destruct b; auto.
  intro H; intro J; inversion J; subst *.
  specialize (n b) as J1; destruct J1; auto. 
Defined.

Program Definition is_pair {t : TRTypes} (x : {t}) : 
  {>> trbool & (HasType x (trpair trtop trtop))} :=
  match x with
  | Pair a b => Bool true
  | _r => Bool false
  end.
Next Obligation.
  repeat split; try constructor; try constructor. 
  intro H; destruct H as [a1 b1]; inversion b1.
Defined. Next Obligation.
  repeat split; try constructor. 
  intro H; destruct H as [a b]; destruct b; auto.
  intro H; intro J; inversion J; subst *.
  specialize (n t2 t3) as J1; destruct J1; auto. 
Defined.

Program Definition is_empty {t : TRTypes} (x : {t}) :=
  match x as v return
  {>> trbool & (v = List nil /\ HasType v (trlist trtop))} (* can make this (forall a : TRTypes, HasType v (trlist a))?*)
  with
  | List nil => Bool true 
  | _r => Bool false 
  end.
Next Obligation.
  repeat split; try constructor; try destruct H2; try destruct H3; auto.
  intro. intro. destruct H3. inversion H4.
Defined. Next Obligation.
  repeat split; try constructor; try destruct H2; try destruct H3; auto.
  intro. intro. destruct H3. inversion H4.
Defined. Next Obligation.
  repeat split; try constructor; try destruct H2; try destruct H3; auto.
  intro. intro. destruct H3. inversion H4.
Defined. Next Obligation.
  repeat split; try constructor; try destruct H2; try destruct H3; auto.
  intro. intro. destruct H3. inversion H4.
Defined. Next Obligation.
  repeat split; try constructor. constructor.
  intro. destruct H2 as [J1 J2]; inversion J2.
Defined. Next Obligation.
  repeat split; try constructor; try (destruct H2 as [J1 J2]; destruct J2; auto).
  intro. intro. destruct H3. inversion H3.
Defined. Next Obligation.
  repeat split; try constructor; try (destruct H2 as [J1 J2]; destruct J2; auto).
  intro. intro. destruct H3. inversion H3.
Defined. Next Obligation.
  repeat split; try constructor; try (destruct H2 as [J1 J2]; destruct J2; auto).
  intro. intro. destruct H3. inversion H3.
Defined.

Program Definition is_cons {t : TRTypes} (x : {t}) :=
  match x as v return
  {>> trbool & (exists (head : TRValues) (tail : list TRValues),
                   (v = List (head :: tail)))}
  with
  | List (x :: l) => Bool true 
  | _r => Bool false 
  end.
Next Obligation.
  repeat split; try constructor; try (intro H2; destruct H2 as [J1 J2]; destruct J2; auto). 
  intro. destruct H2. destruct H2. inversion H2.
Defined. Next Obligation.
  repeat split; try constructor; try (intro H2; destruct H2 as [J1 J2]; destruct J2; auto). 
  intro. destruct H2. destruct H2. inversion H2.
Defined. Next Obligation.
  repeat split; try constructor; try (intro H2; destruct H2 as [J1 J2]; destruct J2; auto). 
  intro. destruct H2. destruct H2. inversion H2.
Defined. Next Obligation.
  repeat split; try constructor; try (intro H2; destruct H2 as [J1 J2]; destruct J2; auto). 
  intro. destruct H2. destruct H2. inversion H2.
Defined. Next Obligation.
  repeat split; try constructor; try (intro H2; destruct H2 as [J1 J2]; destruct J2; auto). 
  intro. destruct H2. destruct H2. inversion H2.
Defined. Next Obligation.
  repeat split; try constructor. intro H2. exists x; exists l; auto.
  intro H2; intro. destruct H2 as [J1 J2]; inversion J2.
Defined. Next Obligation.
  repeat split; try constructor; try (intro H2; destruct H2 as [J1 J2]; destruct J2; auto). 
  intro. destruct H2. destruct H2. inversion H2.
Defined. Next Obligation.
  repeat split; try constructor; try (intro H2; destruct H2 as [J1 J2]; destruct J2; auto). 
  intro. destruct H2. destruct H2. inversion H2.
Defined.

Program Definition TRcar {t : TRTypes} 
  (x : {v >> (trlist t) & 
             (exists (head : TRValues) (tail : list TRValues),
                (v = List (head :: tail)))}) : {t} := 
  match x with 
  | List (h :: t) => h 
  | _r => False_rec _ _ 
  end.
Next Obligation.
  repeat split. inversion h0. inversion H1. auto.
Defined. Next Obligation. 
  destruct x; try inv_trtype_false_faster_2.
  destruct l.
  - assert (H : HasType (List nil) (trlist t) /\ List nil <> false). split; try constructor.
    constructor. intro. inversion H.
    specialize (e H). destruct e. destruct H0. inversion H0.
  - specialize (n t0 l). destruct n; auto.
Defined. 

Program Definition getListType {t : TRTypes} (x : {trlist t}) : TRTypes := 
  t.

Notation " 'car' L" := (@TRcar (getListType L) L) (at level 0, L at next level).

Program Definition test_TRCar := car (List (Num 5 :: nil)).
Next Obligation.
  repeat split; try constructor. constructor. constructor. constructor.
  intro. exists 5; exists nil. auto.
  intro; intro. destruct H. inversion H1.
Defined.

Eval compute in test_TRCar.

Program Definition TRcdr {t : TRTypes} 
  (x : {v >> (trlist t) & 
             (exists (head : TRValues) (tail : list TRValues),
                (v = List (head :: tail)))}) : {trlist t} := 
  match x with 
  | List (h :: t) => List t
  | _r => False_rec _ _ 
  end.
Next Obligation.
  repeat split. inversion h0. inversion H1. auto. 
  constructor. auto.
Defined. Next Obligation.
  destruct x; try inv_trtype_false_faster_2.
  destruct l.
  - assert (H : HasType (List nil) (trlist t) /\ List nil <> false). split; try constructor.
    constructor. intro. inversion H.
    specialize (e H). destruct e. destruct H0. inversion H0.
  - specialize (n t0 l). destruct n; auto.
Defined.

Notation " 'cdr' L" := (@TRcdr (getListType L) L) (at level 0, L at next level).

Program Definition test_TRCdr := cdr (List (Num 5 :: nil)).
Next Obligation.
  repeat split; try constructor. constructor. constructor. constructor.
  intro. exists 5; exists nil. auto.
  intro; intro. destruct H. inversion H1.
Defined.

Eval compute in test_TRCdr.

Program Definition TRlength {t : TRTypes}
  (x : {trlist t}) : {trnum} :=
  match x with 
  | List l => length l 
  | _r => False_rec _ _ 
  end.
Next Obligation.
  destruct x; try inv_trtype_false_faster_2.
  specialize (n l); destruct n. auto.
Defined.

Program Definition TRcons {t : TRTypes}
  (head : {t})
  (tail : {trlist t}) : {trlist t} := 
  match head with 
  | x => match tail with 
         | List l => List (x :: l) 
         | _r => False_rec _ _ 
         end 
  end.
Next Obligation.
  repeat split.
  constructor. constructor. auto. inversion h. auto.
Defined. Next Obligation.
  destruct tail; try inv_trtype_false_faster_2.
  specialize (n l); destruct n. auto.
Defined.