Set Warnings "-uniform-inheritance".
Set Warnings "-ambiguous-paths".
Set Warnings "-meta-collision".
From TRresearch.Tactics Require Import tactics_all.
From TRresearch Require Import Definitions Basics trnum_comparisons.
From TRresearch.Lemmas Require Import Lemmas.
From TRresearch.Non_TR_Functions Require Import Vectors.
#[local] Obligation Tactic := try ((timeout 1 test_jail); (timeout 1 new_jail)).


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

Eval compute in append_tr (vec_cons 4 (vec_cons 5 vec_nil)) 
                          (vec_cons 9 vec_nil).
Eval compute in append_tr (vec_cons 4 (vec_cons 5 vec_nil)) 
                          (append_vec (vec_cons 9 vec_nil) 
                                      (vec_cons 8 (vec_cons 3 vec_nil))).


Program Definition head_tr {n} (x : { (trvec (S n)) }) : { trnum } :=
  match x with 
  | Vec a v => head_vec n v
  | _r => False_rec _ _
  end.

Eval compute in (head_tr (vec_cons 5 (vec_cons 9 vec_nil))).

Program Definition tail_tr {n} (x : {(trvec (S n))}) : {(trvec n)} :=
  match x with 
  | Vec a v => tail_vec n v
  | _r => False_rec _ _
  end.

Eval compute in tail_tr (vec_cons 9 (vec_cons 5 (vec_cons 4 vec_nil))).

Program Definition tr_length {n} (x : { (trvec n) }) : { trnum } := 
  n.

Eval compute in tr_length (vec_cons 1 (vec_cons 5 vec_nil)).

Program Definition vec_setTR {n} 
  (x : {(trvec n)}) 
  (i : {t >> trnum & ((less_than_equal 0 t) /\ (less_than t n)) & True}) : {trvoid} := 
  void.