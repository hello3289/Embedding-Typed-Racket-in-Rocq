Set Warnings "-uniform-inheritance".
Set Warnings "-ambiguous-paths".
Set Warnings "-meta-collision".
From TRresearch.Tactics Require Import tactics_all vector_tactics comparison_tactics.
From TRresearch Require Import Definitions trnum_comparisons unsafe_ref.
From TRresearch Require Import Vec_unsafe_ref_none_false.
From Stdlib Require Import Strings.String.
#[local] Obligation Tactic := try (timeout 1 test_jail).

(* requires the trvec to not be destructed!! *)
Ltac apply_vec_unsafe_ref_none_false := 
  match goal with 
  | [ H : None = trvec_unsafe_ref_tr ?v ?x |- _ ] =>
    match x with 
    | [ Num ?n ] => apply (vec_unsafe_ref_none_false v n); auto;
                    destructTR v; destruct v; try inv_trtype_false_faster_2; auto
    end
  end. 

Ltac deal_with_none_trvec := 
  match goal with 
  | [ n : {_ : TRValues | _ /\ (_ /\ _ -> less_than_equal _ _ /\ _ ) /\ _} |- _ ] => 
      destructTR n; destruct n; try inv_trtype_false_faster_2; get_props;
      match goal with 
      | [ H : context[ [?n] ] |- _ ] => simpl in H; apply_vec_unsafe_ref_none_false
      end 
  end.

Ltac sometimes_things_need_to_be_fast_tracked := 
  match goal with 
  | |- context[ let filtered_var := trvec_unsafe_ref_tr _ _ in None = filtered_var -> _ ] => idtac "trvec_unsafe_ref_tr in goal";
      intros; subst_filtered_var; deal_with_none_trvec
  end.