From research Require Import Definitions.
Require Import String.
Require Import Bool.

(* i'm dying there is still the "trying to automate my life file" *)

Ltac inv_trnum :=
  match goal with
  | H : HasType (Bool ?b) trnum |- _ => inversion H
  | H : HasType (Str ?b) trnum |- _ => inversion H
  | H : HasType (Pair ?b ?p) trnum |- _ => inversion H
  end.
Ltac inv_trbool :=
  match goal with
  | H : HasType (Num ?b) trbool |- _ => inversion H
  | H : HasType (Str ?b) trbool |- _ => inversion H
  | H : HasType (Pair ?b ?p) trbool |- _ => inversion H
  end.
Ltac inv_trstr :=
  match goal with
  | H : HasType (Bool ?b) trstr |- _ => inversion H
  | H : HasType (Num ?b) trstr |- _ => inversion H
  | H : HasType (Pair ?b ?p) trstr |- _ => inversion H
  end.
Ltac inv_trpair :=
  match goal with
  | H : HasType (Bool ?b) (trpair ?x ?y) |- _ => inversion H
  | H : HasType (Str ?b) (trpair ?x ?y) |- _ => inversion H
  | H : HasType (Num ?b) (trpair ?x ?y) |- _ => inversion H
  end.

(* looks at hypothesis for a false "HasType" to invert *)
Ltac inv_trtype_false  :=
 try inv_trbool; try inv_trnum; try inv_trstr; try inv_trpair; fail.

(* starts and simplifies hypotheses that hold the propositions *)
Ltac start_jail :=
   intros; subst; simpl in *;
   repeat 
   (match goal with
   | [ H : {v >> (?t)} |- _ ] => destruct H as [H [?H [?H ?H]]]
   | [ H : {v >> (?t) & ?P & ?Q} |- _ ] => destruct H as [H [?H [?H ?H]]]
   end); subst.

(* i don't know why i can't do subst *? *)

(* destructs HasType with variable ( may need to be more specific ) *)
Ltac pls_destruct_correctly := (* add case for filtered_var destruct *)
    repeat
    (match goal with
    | [ x : TRValues |- _ ] => 
      match goal with
      | [ H : HasType x ?t |- _ ] => destruct x
      end
    end; simpl in *; try inv_trtype_false).
    
Ltac car_cdr_jail :=
  match goal with
  | [ |- context[[Pair ?a ?b]]] => destruct a; destruct b
  | [ b : TRValues, H : HasType (Pair ?a ?b) (trpair ?A ?B) |- HasType ?b _ ] => destruct b
  | [ a : TRValues, H : HasType (Pair ?a ?b) (trpair ?A ?B) |- HasType ?a _ ] => destruct a
  end.

(* eliminates goals with this specific false equality *)
Ltac equal_trv :=
  match goal with
  | [ H : (Bool true) = (Bool false) |- _ ] => inversion H
  | [ H : (Bool false) = (Bool true) |- _ ] => inversion H
  end.

(* runs throuhgh every possible way to generalize a for all hypothesis and tries
 to solve the goal until it does *)
Ltac generalize_jail n :=
  match n with
      | S ?n' =>
        match goal with
          | [ H : forall x : ?t, ?P |- _ ] =>
          (match goal with
            | [ y : t |- _ ] => generalize (H y); intro; auto; generalize_jail n'
            end)
        end
  end.

(* eliminates goals with a false inequality *)
Ltac unequal_false :=
  match goal with
  | [ H : (Bool true) <> (Bool true) |- _ ] => destruct H
  | [ H : (Bool false) <> (Bool false) |- _ ] => destruct H
  end; auto.

Ltac simplify_hypothesis :=
  match goal with
    | [ H : _ \/ _ |- _ ] => destruct H
    | [ H : ?a /\ ?b |- _ ] => destruct H
    (*| [ H : (get_true_prop _) |- _ ] => idtac 13; unfold get_true_prop in *; simpl in *
    | |- context[ (get_true_prop _) ] => idtac 14; unfold get_true_prop in *; simpl in * 
    decided not to do this as there are too many ways that get_true_prop come up *)
    end; auto.

Ltac hypothesis_jail :=
    (match goal with
    | [ H : HasType _ (trunion _ _) |- _] => inversion H; simpl in *; subst; clear H
    end); auto.

(* if conclusion is a "properly" formed HasType, call constructor *)
Ltac ht_good_hehe :=
  match goal with
  | [ |- HasType _ trtop ] => constructor
  | [ |- HasType (Bool _) trbool ] => constructor
  | [ |- HasType (Num _) trnum ] => constructor
  | [ |- HasType (Str _) trstr ] => constructor
  | [ |- HasType (Pair ?a ?b) (trpair ?t1 ?t2) ] => constructor
  | [ |- HasType _ (trunion _ _) ] => try (apply HtUnion_L; auto; constructor; fail) || apply HtUnion_R; auto; constructor; fail
  | [ H : HasType (Pair ?a ?b) (trpair ?A ?B) |- HasType ?a ?A ] => inversion H; auto
  | [ H : HasType (Pair ?a ?b) (trpair ?A ?B) |- HasType ?b ?B ] => inversion H; auto
  end.

(* simplifies the conclusion *)
Ltac conclusion_jail :=
  repeat 
  (match goal with
  | [ |- _ /\ _ ] => constructor
  | [ |- _ -> _ ] => intro
  | [ |- ~_ ] => intro
  | [ |- _ \/ _ ] => try (left; constructor); try (right; constructor) (* may change *)
  end).

(* make tactic that "solves" goals aka it shouldn't make new goals just solve them 
  ht_good_hehe, generalize_jail, simplify hypothesis?  *)


(* then there are tactics that simplify conclusion and hypothesis but doesn't gen 
more goals like almost conclusion jail ( will make more goals with \/) and simplify_hypothesis? 
though simplify_hypothesis also solves goals *)

Ltac pair_thing :=
  match goal with 
  | [ H : HasType (Pair ?a ?b) (trpair ?A ?B) |- _ ] => simpl in *; subst; inversion H; clear H
  end.

Ltac eq_refl_special :=
  match goal with
  | [ H : ?a = ?a -> _ |- _ ] => try specialize (H eq_refl)
  end.

(* this shouldn't change the goal except simplifying it, and the hypothesis should be simplified *)
Ltac simple_jail :=
  match goal with 
  | [ filtered_var := _ |- _ ] => subst filtered_var
  | _ => idtac
  end; simpl in *; subst; try (repeat simplify_hypothesis); try pair_thing; try conclusion_jail; try hypothesis_jail; auto.

Ltac solve_pls :=
  try (repeat ht_good_hehe); try eq_refl_special; try generalize_jail 3; try (repeat simplify_hypothesis); try inv_trtype_false; try equal_trv; try unequal_false; auto.

Ltac do_it :=
  simple_jail; solve_pls.

Ltac hopefully_this_works n :=
  match n with
  | S ?n' =>
      do_it; pls_destruct_correctly; try car_cdr_jail; do_it; 
      try (match goal with 
      | [ H : ~ HasType _ _ |- _ ] => destruct H
      | [ H : ~ (HasType _ _ /\ HasType _ _) |- _ ] => destruct H
      (* i'm doing this bc match on ~ _ matches to _ <> _ which i don't want (if i remember correctly)*)
      (* if there's a way to not match to that, i'll do it but i tired *)
      end); do_it; hopefully_this_works n'
  | O => idtac
  end.

Ltac unfold_jail := (* maybe if we add more definitions that need to be unfolded *)
  unfold get_true_prop in *; simpl in *.

Ltac pls_jail :=
  start_jail; simpl in *; conclusion_jail; try simplify_hypothesis; try unfold_jail; hopefully_this_works 2.
