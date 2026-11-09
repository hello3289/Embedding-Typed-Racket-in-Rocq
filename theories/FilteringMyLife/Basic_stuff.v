Set Warnings "-ambiguous-paths".
From TRresearch Require Import Definitions_base.
From TRresearch Require Import Lemmas_new.
From TRresearch Require Import If Predicates.
From Corelib Require Import Lists.ListDef.
Require Import Program.Tactics.


Notation " 'ifTR_what' t1 A B C " := 
  (@if_TR t1 _ _ _ _ _ _ A (fun _ => B) (fun _ => C))
  (at level 0, t1 at next level, A at next level, B at next level, C at next level).



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

Program Definition lengthTR {t : TRTypes} (x : {trlist t}) : nat := 
    match (TRlength x) with 
    | Num n => n 
    | _r => False_rec _ _
    end.
Next Obligation.
    destruct (TRlength [x]).
    destruct a. destruct x0; try inv_trtype_false_faster_2.
    specialize (n n0). destruct n. auto.
Defined.