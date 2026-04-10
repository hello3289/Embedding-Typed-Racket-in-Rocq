Set Warnings "-uniform-inheritance".
Set Warnings "-ambiguous-paths".
Set Warnings "-meta-collision".
From TRresearch.Tactics Require Import tactics_all vec_unsafe_ref_none_false_tactic comparison_tactics well_founded_tactic.
From TRresearch Require Import Definitions safe_ref.
From TRresearch.Functions Require Import Basics Vectors trnum_comparisons.
From TRresearch.Non_TR_Functions Require Import Vectors.
From TRresearch.Lemmas Require Import Vec_unsafe_ref_none_false.
From Stdlib Require Import Strings.String.
#[local] Obligation Tactic := try ((timeout 1 (time really_simple_start)); (timeout 1 (time new_jail))).


Create HintDb TRHints.
  Hint Extern 0 => discriminates : TRHints.
  Hint Extern 0 => subst_filtered_var : TRHints.
  Hint Extern 0 => simpl_func : TRHints.
  Hint Extern 0 => rewrite_jail' : TRHints.
  Hint Constructors HasType : TRHints.
  Hint Extern 0 => sometimes_things_need_to_be_fast_tracked : TRHints.
  Hint Unfold leTR : TRHints.
  Hint Unfold ltTR : TRHints.
  Hint Constructors less_than_equal : TRHints.
  Hint Constructors less_than : TRHints.
  Hint Unfold tr_length : TRHints.
  Hint Extern 1 (ltTR _ _) => repeat (progress get_props) : TRHints.
  Hint Extern 1 (less_than_equal _ _) => repeat (progress get_props) : TRHints.
  Hint Extern 2 => lia : TRHints.
  Hint Extern 0 => well_founded_tactic : TRHints.
  Hint Extern 1 => less_than_equal_0 : TRHints.


(* the stuff *)

  Ltac destruct_nat := 
  match goal with 
  | [ H : forall n : nat, _ <> (Num ?m) |- False ] => idtac m;
    match goal with 
    | [ H2 : (Num 0) <> (Num m) |- False ] =>  idtac "there";
      destruct m; try spec; try discriminates
    end 
  end.
Hint Extern 2 => destruct_nat : TRHints.
#[local] Obligation Tactic := try fail.
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
Next Obligation.
  really_simple_start.
  destructTR i. autoTR.
Defined. Next Obligation.

  really_simple_start.
  unfold tr_length.
  destructTR i; destruct i; try inv_trtype_false_faster.
  get_props.
  simpl in Heq_i.
  inversion Heq_i.
  rewrite <- H4 in H1.
  unfold ltTR; simpl.
  lia.

Defined. Next Obligation.
  really_simple_start.
  destructTR i; destruct i; try inv_trtype_false_faster.
  get_props.
  simpl in Heq_i.
  inversion Heq_i.
  rewrite <- H6 in H3.
  constructor.
  unfold ltTR; simpl.
  lia.

Defined. Next Obligation.
    really_simple_start.
    destructTR i; destruct i; try inv_trtype_false_faster.
  get_props.
  simpl in Heq_i.
  inversion Heq_i.
  rewrite <- H6 in H3.
  constructor.
  unfold leTR; simpl.
  lia.
    
Defined. Next Obligation.

    really_simple_start.
    destructTR i; destruct i; try inv_trtype_false_faster.
  get_props.
  simpl in Heq_i.
  inversion Heq_i.
  unfold ltTR; simpl. 
  subst *.
  lia.

Defined. Next Obligation.
  test_jail.
Defined. Next Obligation.
  test_jail.
Defined. Next Obligation.
  test_jail.
Defined. Next Obligation.
  test_jail.
Defined. Next Obligation.
  test_jail.
Defined. Next Obligation.
  test_jail.
Defined. Next Obligation.
  test_jail.
Defined. Next Obligation.
  test_jail.
Defined.
