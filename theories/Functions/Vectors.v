Set Warnings "-uniform-inheritance".
Set Warnings "-ambiguous-paths".
Set Warnings "-meta-collision".
From TRresearch.Tactics Require Import tactics_all.
From TRresearch Require Import Definitions Basics trnum_comparisons.
From TRresearch.Lemmas Require Import Lemmas.
From TRresearch.Non_TR_Functions Require Import Vectors.
#[local] Obligation Tactic := try ((timeout 0 test_jail); (timeout 0 new_jail)).

(* "HintDb" *)
Create HintDb TRHints.
    Hint Extern 0 => discriminates : TRHints.
    Hint Extern 0 => subst_filtered_var : TRHints.
    Hint Extern 0 => simpl_func : TRHints.
    Hint Extern 0 => rewrite_jail' : TRHints.
    Hint Constructors HasType : TRHints.



Notation " {{ f { res } a1 a2 }} " :=
  match a1, a2 with 
  | Vec a v1, Vec b v2 => (Vec res (f v1 v2))
  | _r1, _r2 => False_rec _ _
  end 
(at level 0, f at next level, res at next level, a1 at next level, a2 at next level).

Notation " {{ f n x }} " :=
  match x with 
  | Vec a v => f n v
  | _r => False_rec _ _
  end 
(at level 0, f at next level, n at next level, x at next level).

Program Definition append_tr {n m} (x : { (trvec n) }) (y : { (trvec m) }) : { (trvec (n + m)) } :=
  match x, y with 
  | Vec a v1, Vec b v2  => (Vec (n + m) (append_vec v1 v2))
  | _r1, _r2 => False_rec _ _
  end.

Eval compute in append_tr (cons 4 (cons 5 nil)) (cons 9 nil).
Eval compute in append_tr (cons 4 (cons 5 nil)) (append_vec (cons 9 nil) (cons 8 (cons 3 nil))).


Program Definition head_tr {n} (x : { (trvec (S n)) }) : { trnum } :=
  match x with 
  | Vec a v => head_vec n v
  | _r => False_rec _ _
  end.

Eval compute in (head_tr (cons 5 (cons 9 nil))).

Program Definition tail_tr {n} (x : {(trvec (S n))}) : {(trvec n)} :=
  match x with 
  | Vec a v => tail_vec n v
  | _r => False_rec _ _
  end.

Eval compute in tail_tr (cons 9 (cons 5 (cons 4 nil))).

Program Definition tr_length {n} (x : { (trvec n) }) : { trnum } := 
  n.

Eval compute in tr_length (cons 1 (cons 5 nil)).

Program Definition vec_setTR {n} 
  (x : {(trvec n)}) 
  (i : {t >> trnum & ((less_than_equal 0 t) /\ (less_than t n)) & True}) : {trvoid} := 
  void.