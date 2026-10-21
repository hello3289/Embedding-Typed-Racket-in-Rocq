Set Warnings "-ambiguous-paths".
From TRresearch Require Import Definitions_new.
From TRresearch Require Import Basic_stuff.
From TRresearch Require Import filter_tactics.
Require Import Program.Tactics.
From TRresearch Require Import Lemmas_new.
From Corelib Require Import Lists.ListDef.
Require Import Program.Tactics.
From Corelib Require Import Program.Wf.

(* "HintDb" *)
Create HintDb TRHints.
    #[local] Hint Extern 0 => give_true : TRHints.
    #[local] Hint Extern 0 => HasType_list : TRHints.
    #[local] Hint Extern 1 => exists_list : TRHints.
    #[local] Hint Extern 0 => negation_intro : TRHints.
    #[local] Hint Extern 0 => simpl_goals : TRHints.
    #[local] Hint Extern 0 => falsities : TRHints.
    #[local] Hint Extern 0 => trtop_all : TRHints.
    #[local] Hint Extern 1 => cdr_length : TRHints.
    #[local] Hint Extern 1 => car_is_type : TRHints.
    #[local] Hint Extern 1 => destruct_inside_hastype : TRHints.
    #[local] Hint Extern 1 => tr_union_union : TRHints.

Program Definition TRcons_new {t1 t2 : TRTypes}
  (head : TRValues)
  (H : (HasType head t1))
  (tail : {trlist t2}) : {trlist (tr_union t1 t2)} := 
  match tail with 
         | List l => List (head :: l) 
         | _r => False_rec _ _ 
         end. 
Next Obligation.
  repeat split.
  HasType_list.
  deal_tr_union.
  apply_tr_union_right_list.
Defined. Next Obligation.
    false_list.
Defined.

Notation " 'cons' A B " := (@TRcons_new _ _ A _ B) (at level 0, A at next level, B at next level).



#[local] Obligation Tactic := try (trtactic; fail); 
                              try (program_simpl; fail);
                              try fail.
Program Fixpoint filterTR {A B : TRTypes}
    (pred : forall (x : {trtop}), {>> trbool & (HasType x B)}) (* A instead of trtop? *)
    (l : {trlist A})
    {measure (lengthTR l)} : {trlist B} := 
ifTR_what (trlist B) (is_empty l)
    (List nil) 
    (ifTR_what (trlist B) 
            (pred (car l)) 
            (cons (car l) (filterTR pred (cdr l)))
            (filterTR pred (cdr l))).


From Stdlib Require Import Strings.String.
Open Scope string_scope.
Program Definition filter_test1 := (filterTR is_number (List (Num 5 :: Str "hi" :: nil))).
Eval vm_compute in filter_test1.
Program Definition filter_test2 := (filterTR is_bool (List (Num 5 :: Str "hi" :: nil))).
Eval vm_compute in filter_test2.
Program Definition filter_test3 := (filterTR is_string (List (Str "bye" :: Str "hi" :: Str "banana" :: nil))).
Eval vm_compute in filter_test3.
Program Definition filter_test4 := (filterTR is_pair (List ((Pair 5 4) :: Str "hi" :: nil))).
Eval vm_compute in filter_test4.
