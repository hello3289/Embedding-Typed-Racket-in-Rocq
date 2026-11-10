Set Warnings "-ambiguous-paths".
From TRresearch Require Import Definitions.
From TRresearch Require Import If Predicates tactics_all Basic_stuff_tactics.
From Corelib Require Import Lists.ListDef.
Require Import Program.Tactics.
#[local] Obligation Tactic := try really_simple_start; try new_jail; try auto with TRHints.
Set Warnings "-meta-collision".

(******** "Hint Database" ********)
Create HintDb TRHints.
    #[local] Hint Extern 1 => list_false : TRHints. 
    #[local] Hint Extern 1 => first_type : TRHints.
    #[local] Hint Extern 1 => rest_type : TRHints.
    #[local] Hint Extern 1 => first_rest_type : TRHints.


(******** "Basic Functions for Lists " ********)

Program Definition TRcar {t : TRTypes} 
  (x : {v >> (trlist t) & 
             (exists (head : TRValues) (tail : list TRValues),
                (v = List (head :: tail)))}) : {t} := 
  match x with 
  | List (h :: t) => h 
  | _r => False_rec _ _ 
  end.

Program Definition TRcdr {t : TRTypes} 
  (x : {v >> (trlist t) & 
             (exists (head : TRValues) (tail : list TRValues),
                (v = List (head :: tail)))}) : {trlist t} := 
  match x with 
  | List (h :: t) => List t
  | _r => False_rec _ _ 
  end.

Program Definition TRcons {t : TRTypes}
  (head : {t})
  (tail : {trlist t}) : {trlist t} := 
  match head with 
  | x => match tail with 
         | List l => List (x :: l) 
         | _r => False_rec _ _ 
         end 
  end.

Program Definition TRlength {t : TRTypes}
  (x : {trlist t}) : {trnum} :=
  match x with 
  | List l => length l 
  | _r => False_rec _ _ 
  end.

(******** "length of TRList to Rocq nat" ********)

Ltac destruct_trlength := 
    match goal with 
    | [ H : context[ TRlength _ ] |- _ ] => 
        let a1 := fresh "a" in 
        let a2 := fresh "a" in 
        let a3 := fresh "a" in 
        destruct (TRlength _) as [a1 [a2 a3]]
    end.

(* a bit annoying to use a different tactic here but eh *)
#[local] Obligation Tactic := try really_simple_start; try destruct_trlength; try new_jail.
Program Definition lengthTR {t : TRTypes} (x : {trlist t}) : nat := 
  match (TRlength x) with 
  | Num n => n 
  | _r => False_rec _ _
  end.

(******** "Notations" ********)

Program Definition getListType {t : TRTypes} (x : {trlist t}) : TRTypes :=  t.

Notation " 'ifTR' t1 A B C " := 
  (@if_TR t1 _ _ _ _ _ _ A (fun _ => B) (fun _ => C))
  (at level 0, t1 at next level, A at next level, B at next level, C at next level).

Notation " 'car' L" := (@TRcar (getListType L) L) (at level 0, L at next level).

Notation " 'cdr' L" := (@TRcdr (getListType L) L) (at level 0, L at next level).
