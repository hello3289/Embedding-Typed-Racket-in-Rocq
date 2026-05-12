Set Warnings "-uniform-inheritance".
Set Warnings "-ambiguous-paths".
Set Warnings "-meta-collision".
From TRresearch.Tactics Require Import tactics_all comparison_tactics dot_product_tactics.
From TRresearch Require Import Definitions safe_ref.
From TRresearch.Functions Require Import Basics If Vectors trnum_comparisons trnum_wf.
From TRresearch.Lemmas Require Import Trnum_Comparison_Lemmas.

#[local] Obligation Tactic := try well_founded_tactic; try (timeout 2 (time test_jail)).

Create HintDb TRHints.
  #[local] Hint Extern 0 => well_founded_tactic : TRHints.
  #[local] Hint Extern 0 => apply_le_ident : TRHints.
  #[local] Hint Extern 0 => force_unequal : TRHints.
  #[local] Hint Constructors less_than : TRHints.
  #[local] Hint Constructors less_than_equal : TRHints.
  #[local] Hint Unfold leTR : TRHints.
  #[local] Hint Unfold ltTR : TRHints.
  #[local] Hint Unfold tr_length : TRHints.
  #[local] Hint Extern 1 => less_than_equal_0 : TRHints.
  #[local] Hint Extern 0 => immediate_TR : TRHints.
  #[local] Hint Extern 2 => solve_lt_lte : TRHints.
  #[local] Hint Extern 2 => lia : TRHints.
  #[local] Hint Extern 2 => destruct_nat : TRHints.
  #[local] Hint Unfold get_true_prop : TRHints.
  #[local] Hint Extern 1 => destruct_application : TRHints.
  #[local] Hint Extern 1 => bool_not_true_or_false : TRHints.
  #[local] Hint Extern 1 => normalize_to_less_than_equal_0 : TRHints.
  #[local] Hint Extern 1 => solve_less_than : TRHints.
  #[local] Hint Extern 1 => solve_the_thing_new : TRHints.  

Program Fixpoint dot_product_tr {n : nat} 
  (len : { trnum }) 
  (step : {t >> trnum & (less_than 0 t) & ~(less_than 0 t)}) 
  (x : { (trvec n) }) 
  (y : { (trvec n) })  
  (acc : { trnum }) 
  (i : {t >> trnum & (less_than t (sum (Num n) step)) & True}) {measure (proj1_sig (sub (sum n step) i)) ltTR}
   : { trnum } :=
  match (ltTR_B i n) as M with
  | Bool true => @dot_product_tr n len step x y (sum acc (mult (trvec_ref x i) (trvec_ref y i))) (sum i step) _
  | Bool false => acc
  | _r => False_rec _ _
  end.