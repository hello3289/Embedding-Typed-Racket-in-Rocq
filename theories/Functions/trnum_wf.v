Set Warnings "-uniform-inheritance".
Set Warnings "-ambiguous-paths".
Set Warnings "-meta-collision".
From TRresearch.Tactics Require Import tactics_all.
From TRresearch Require Import Definitions.
#[local] Obligation Tactic := try (timeout 1 test_jail).

(* "Create Hint Database and put in the 0 tactics (annoying that you 
   have to do this every time but oh well)"*)
Create HintDb TRHints.
  Hint Extern 0 => discriminates : TRHints.
  Hint Extern 0 => subst_filtered_var : TRHints.
  Hint Extern 0 => simpl_func : TRHints.
  Hint Extern 0 => rewrite_jail' : TRHints.
  Hint Constructors HasType : TRHints.

(* "well foundedness for trnum " *)

Program Definition wf_id (n : {trnum}) : nat := 
  match n with 
  | Num n' => n'
  | _r => False_rec _ _
  end.