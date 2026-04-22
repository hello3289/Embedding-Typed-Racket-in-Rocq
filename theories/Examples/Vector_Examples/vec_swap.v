Set Warnings "-uniform-inheritance".
Set Warnings "-ambiguous-paths".
Set Warnings "-meta-collision".
From TRresearch.Tactics Require Import tactics_all comparison_tactics well_founded_tactic apply_predicate_lemmas prove_ifTR_branches apply_union_lemmas apply_if_lemmas.
From TRresearch Require Import Definitions safe_ref.
From TRresearch.Functions Require Import Basics If Vectors trnum_comparisons.
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
  Hint Extern 1 => less_than_equal_0 : TRHints.
  Hint Extern 1 => immediate_TR : TRHints.
  Hint Extern 1 => prove_if_TR_branches : TRHints.
  Hint Extern 2 => solve_lt_lte : TRHints.
  Hint Extern 2 => lia : TRHints.
  Hint Extern 2 => destruct_nat : TRHints.
  Hint Extern 2 => destructB : TRHints.
  Hint Constructors HasType : TRHints.
  Hint Unfold tr_length : TRHints.




Program Definition vec_swap_tr {n} 
  (x : {(trvec n)}) 
  (i : {t >> trnum & ((less_than_equal 0 t) /\ (less_than t n)) & True})
  (j : {t >> trnum & ((less_than_equal 0 t) /\ (less_than t n)) & True}) : {trvoid} :=
  ifTR (eqTR_B i j)
       void 
       (let i_val := (trvec_ref x i) in 
          let j_val := (trvec_ref x j) in 
            let swap1 := (vec_setTR x i) in 
              vec_setTR x j).