Set Warnings "-uniform-inheritance".
Set Warnings "-ambiguous-paths".
Set Warnings "-meta-collision".
From TRresearch.Tactics Require Import tactics_all apply_pair_lemmas.
From TRresearch Require Import Definitions.
From Stdlib Require Import Strings.String.
#[local] Obligation Tactic := try (timeout 1 test_jail).


(* "Create Hint Database and put in the 0 tactics (annoying that you 
   have to do this every time but oh well)"*)
Create HintDb TRHints.
  Hint Extern 0 => discriminates : TRHints.
  Hint Extern 0 => subst_filtered_var : TRHints.
  Hint Extern 0 => simpl_func : TRHints.
  Hint Extern 0 => rewrite_jail' : TRHints.
  Hint Extern 1 => apply_trpair : TRHints.
  Hint Constructors HasType : TRHints.

(* "trnum comparisons" *)  

Program Definition eqTR (x : { trnum }) (y : { trnum }) : Prop :=
  match x, y with
  | Num n, Num m => n = m
  | _r, _r2 => False
  end.

Program Definition leTR (x : { trnum }) (y : { trnum }) : Prop :=
  match x, y with
  | Num n, Num m => n <= m
  | _r, _r2 => False
  end.

Program Definition ltTR (x : { trnum }) (y : { trnum }) : Prop :=
  match x, y with
  | Num n, Num m => n < m
  | _r, _r2 => False
  end.

Program Definition eqTR_B (x : { trnum }) (y : { trnum }) : {trbool} :=
  match x, y with
  | Num n, Num m => Nat.eqb n m
  | _r, _r2 => False_rec _ _
  end.

Program Definition ltTR_B (x : { trnum }) (y : { trnum }) : {trbool} :=
  match x, y with
  | Num n, Num m => Nat.ltb n m
  | _r, _r2 => False_rec _ _
  end.

Program Definition leTR_B (x : { trnum }) (y : { trnum }) : {trbool} :=
  match x, y with
  | Num n, Num m => Nat.leb n m
  | _r, _r2 => False_rec _ _
  end.

Inductive equal : TRValues -> TRValues -> Prop :=
  | valid_eq : forall (n m : nat), eqTR (Num n) (Num m) -> equal (Num n) (Num m).  

Inductive less_than_equal : TRValues -> TRValues -> Prop :=
  | valid_le : forall (n m : nat), leTR (Num n) (Num m) -> less_than_equal (Num n) (Num m).

Inductive less_than : TRValues -> TRValues -> Prop :=
  | valid_lt : forall (n m : nat), ltTR (Num n) (Num m) -> less_than (Num n) (Num m).

Program Definition make_ltTR (n1 : {trnum}) (n2 : {trnum}) (H : (ltTR n1 n2)) 
    : {t >> trnum & (ltTR n1 n2) & True} :=
  n1.

Program Definition make_leTR (n1 : {trnum}) (n2 : {trnum}) (H : (leTR n1 n2)) 
    : {t >> trnum & (leTR n1 n2) & True} :=
  n1.

Program Definition make_eqTR (n1 : {trnum}) (n2 : {trnum}) (H : (eqTR n1 n2)) 
    : {t >> trnum & (eqTR n1 n2) & True} :=
  n1.