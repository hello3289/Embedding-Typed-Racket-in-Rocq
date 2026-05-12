Set Warnings "-uniform-inheritance".
Set Warnings "-ambiguous-paths".
Set Warnings "-meta-collision".
From TRresearch.Tactics Require Import tactics_all.
From TRresearch Require Import Definitions.
From TRresearch.Lemmas Require Import Lemmas.
#[local] Obligation Tactic := try (timeout 1 test_jail).
(* if writing other predicates causes issues, change this to "try fail" 
  and use "Solve All Obligations with test_jail" instead *)


(* "Create Hint Database and put in the 0 tactics (annoying that you 
   have to do this every time but oh well)"*)
Create HintDb TRHints.
#[local] Hint Immediate is_top : TRHints.
#[local] Hint Immediate is_top_pair : TRHints.


Print HintDb TRHints.
(****************)
(* "Predicates" *)
Program Definition is_number {t : TRTypes} (x : {t}) : 
                  {>> trbool & (HasType x trnum)} :=
  match x with
  | Num n => Bool true
  | _r => Bool false
  end.

Program Definition is_string {t : TRTypes} (x : {t}) : 
                  {>> trbool & (HasType x trstr)} :=
  match x with
  | Str s => Bool true
  | _r => Bool false
  end.
  
Program Definition is_bool {t : TRTypes} (x : {t}) : 
                  {>> trbool & (HasType x trbool)} :=
  match x with
  | Bool b => Bool true
  | _r => Bool false
  end.

Program Definition is_pair {t : TRTypes} (x : {t}) : 
  {>> trbool & (HasType x (trpair trtop trtop))} :=
  match x with
  | Pair a b => Bool true
  | _r => Bool false
  end.

