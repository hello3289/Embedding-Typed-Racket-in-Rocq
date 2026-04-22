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
#[local] Hint Extern 0 => discriminates : TRHints.
#[local] Hint Extern 0 => subst_filtered_var : TRHints.
#[local] Hint Extern 0 => simpl_func : TRHints.
#[local] Hint Extern 0 => rewrite_jail' : TRHints.
#[local] Hint Extern 1 => apply_trpair : TRHints.
#[local] Hint Constructors HasType : TRHints.

(*********************************)
(* "Simple Arithmetic Functions" *)

Program Definition add1 (n : {trnum}) : {trnum} :=
   match n with
   | Num x => S x
   | _r => False_rec _ _
   end.

Eval compute in (add1 5).
Eval compute in (add1 2).

Program Definition sum (n : {trnum}) (m : {trnum}) : {trnum} :=
  match n, m with 
  | Num n', Num m' => n' + m' 
  | _r1, _r2 => False_rec _ _ 
  end.

Eval compute in (sum 4 3).
Eval compute in (sum 0 3).

Program Definition mult (n : {trnum}) (m : {trnum}) : {trnum} :=
  match n, m with 
  | Num n', Num m' => n' * m' 
  | _r1, _r2 => False_rec _ _ 
  end.

Eval compute in (mult 4 3).
Eval compute in (mult 0 3).  

Program Definition sub (n : {trnum}) (m : {trnum}) : {trnum} :=
  match n, m with 
  | Num n', Num m' => n' - m' 
  | _r1, _r2 => False_rec _ _ 
  end.

Eval compute in (sub 7 3).
Eval compute in (sub 3 8).   

(*****************************)
(* "Simple String Functions" *)
Program Definition strlen (s : {trstr}) : {trnum} :=
  match s with
  | Str s => length s
  | _r => False_rec _ _
  end.

Open Scope string_scope.  
Eval compute in (strlen "potato").
Eval compute in (strlen "").
Close Scope string_scope.  

Program Definition car {A B : TRTypes} (l : {(trpair A B)}) : {A} :=
  match l with
  | Pair a b => a
  | _r => False_rec _ _
  end.  

Eval compute in (car (5, 3)).
Eval compute in (car (car ((1, 2), 5))).

Program Definition cdr {X Y : Prop} {A B : TRTypes} (l : {>> (trpair A B) & X & Y}) : {B} :=
  match l with
  | Pair a b => b
  | _r => False_rec _ _
  end.
Eval compute in (cdr (5, 3)).
Eval compute in (cdr (cdr (5, (1, 2)))).