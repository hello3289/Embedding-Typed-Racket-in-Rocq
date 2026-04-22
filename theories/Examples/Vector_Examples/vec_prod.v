Set Warnings "-uniform-inheritance".
Set Warnings "-ambiguous-paths".
Set Warnings "-meta-collision".
From TRresearch.Tactics Require Import tactics_all comparison_tactics well_founded_tactic.
From TRresearch Require Import Definitions safe_ref.
From TRresearch.Functions Require Import Basics Vectors trnum_comparisons.
From Stdlib Require Import Strings.String.
#[local] Obligation Tactic := try (timeout 1 (time test_jail)).


Create HintDb TRHints.
  Hint Extern 0 => discriminates : TRHints.
  Hint Extern 0 => subst_filtered_var : TRHints.
  Hint Extern 0 => simpl_func : TRHints.
  Hint Extern 0 => rewrite_jail' : TRHints.
  Hint Extern 0 => well_founded_tactic : TRHints.
  Hint Extern 0 => apply_le_ident : TRHints.
  Hint Extern 0 => force_unequal : TRHints.
  Hint Constructors HasType : TRHints.
  Hint Constructors less_than : TRHints.
  Hint Constructors less_than_equal : TRHints.
  Hint Unfold leTR : TRHints.
  Hint Unfold ltTR : TRHints.
  Hint Unfold tr_length : TRHints.
  Hint Extern 1 => less_than_equal_0 : TRHints.
  Hint Extern 1 => immediate_TR : TRHints.
  Hint Extern 2 => solve_lt_lte : TRHints.
  Hint Extern 2 => lia : TRHints.
  Hint Extern 2 => destruct_nat : TRHints.


(* the stuff *)

Program Fixpoint vec_prod_TR {n} 
  (res : {trnum}) 
  (i : {t >> trnum & (less_than_equal t (Num n)) & True}) 
  (x : {trvec n}) 
  {measure (proj1_sig i) ltTR}
  : {trnum} :=
  match i with 
  | Num 0 => res 
  | Num (S i') => vec_prod_TR (mult res (trvec_ref x i')) (Num i') x
  | _r => False_rec _ _ 
  end.

Program Definition vec_product_tr_loop {n} 
  (x : {(trvec n)})
  (len : {t >> trnum & (less_than_equal t (Num n)) & ~(less_than_equal t (Num n))})
  (res : { trnum }) : {trnum} :=
  vec_prod_TR res len x.


Program Definition vec_product_tr_new {n} (x : {(trvec n)}) : {trnum} :=
  match x with 
  | Vec m1 nv1 => 
    let loop := vec_product_tr_loop x in 
      let i := (tr_length x) in 
        let res := 1 in 
          loop i res
  | _r1 => False_rec _ _
  end.