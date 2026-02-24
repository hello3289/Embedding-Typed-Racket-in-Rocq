From TRresearch Require Import Definitions.
From TRresearch.Lemmas Require Import Lemmas.
From Stdlib.Strings Require String.
From Stdlib Require Import Bool.

(* i'm dying there is still the "trying to automate my life file" *)

(************************************************************************)
(********************** HasType FALSE INVERSIONS AH *********************)
(* looks at hypothesis for a false "HasType" to invert *)

Ltac inv_trnum_fast_2 :=
  match goal with
  | H : HasType (Bool ?b) trnum |- _ => apply (bool_not_trnum b H)
  | H : HasType (Str ?b) trnum |- _ => apply (str_not_trnum b H)
  | H : HasType (Pair ?b ?p) trnum |- _ => apply (pair_not_trnum b p H)
  | H : HasType (Vec _ ?b) trnum |- _ => apply (vec_not_trnum b H)
  | H : HasType (List ?l) trnum |- _ => apply (list_not_trnum l H)
  | H : HasType (Void ?v) trnum |- _ => apply (void_not_trnum v H)
  end.

Ltac inv_trbool_fast_2 :=
  match goal with
  | H : HasType (Num ?b) trbool |- _ => apply (num_not_trbool b H)
  | H : HasType (Str ?b) trbool |- _ => apply (str_not_trbool b H)
  | H : HasType (Pair ?b ?p) trbool |- _ => apply (pair_not_trbool b p H)
  | H : HasType (Vec _ ?b) trbool |- _ => apply (vec_not_trbool b H)
  | H : HasType (List ?l) trbool |- _ => apply (list_not_trbool l H)
  | H : HasType (Void ?v) trbool |- _ => apply (void_not_trbool v H)
  end.

Ltac inv_trstr_fast_2 :=
  match goal with
  | H : HasType (Bool ?b) trstr |- _ => apply (bool_not_trstr b H)
  | H : HasType (Num ?b) trstr |- _ => apply (num_not_trstr b H)
  | H : HasType (Pair ?b ?p) trstr |- _ => apply (pair_not_trstr b p H)
  | H : HasType (Vec _ ?b) trstr |- _ => apply (vec_not_trstr b H)
  | H : HasType (List ?l) trstr |- _ => apply (list_not_trstr l H)
  | H : HasType (Void ?v) trstr |- _ => apply (void_not_trstr v H)
  end.

Ltac inv_trpair_fast_2 :=
  match goal with
  | H : HasType (Bool ?b) (trpair ?x ?y) |- _ => apply (bool_not_trpair b H)
  | H : HasType (Str ?b) (trpair ?x ?y) |- _ => apply (str_not_trpair b H)
  | H : HasType (Num ?b) (trpair ?x ?y) |- _ => apply (num_not_trpair b H)
  | H : HasType (Vec _ ?b) (trpair ?x ?y) |- _ => apply (vec_not_trpair b H)
  | H : HasType (List ?l) (trpair ?x ?y) |- _ => apply (list_not_trpair l H)
  | H : HasType (Void ?v) (trpair ?x ?y) |- _ => apply (void_not_trpair v H)
  end.

Ltac inv_trlist_fast_2 :=
  match goal with
  | H : HasType (Bool ?b) trlist |- _ => apply (bool_not_trlist b H)
  | H : HasType (Str ?b) trlist |- _ => apply (str_not_trlist b H)
  | H : HasType (Pair ?b ?p) trlist |- _ => apply (pair_not_trlist b p H)
  | H : HasType (Vec _ ?b) trlist |- _ => apply (vec_not_trlist b H)
  | H : HasType (Num ?l) trlist |- _ => apply (num_not_trlist l H)
  | H : HasType (Void ?v) trlist |- _ => apply (void_not_trlist v H)
  end.

Ltac inv_trvec_fast_2 :=
  match goal with
  | H : HasType (Bool ?b) (trvec _) |- _ => apply (bool_not_trvec b H)
  | H : HasType (Str ?b) (trvec _) |- _ => apply (str_not_trvec b H)
  | H : HasType (Pair ?b ?p) (trvec _) |- _ => apply (pair_not_trvec b p H)
  | H : HasType (Num ?b) (trvec _) |- _ => apply (num_not_trvec b H)
  | H : HasType (List ?l) (trvec _) |- _ => apply (list_not_trvec l H)
  | H : HasType (Void ?v) (trvec _) |- _ => apply (void_not_trvec v H)
  end.

Ltac inv_trvoid_fast_2 :=
  match goal with
  | H : HasType (Bool ?b) trvoid |- _ => apply (bool_not_trvoid b H)
  | H : HasType (Str ?b) trvoid |- _ => apply (str_not_trvoid b H)
  | H : HasType (Pair ?b ?p) trvoid |- _ => apply (pair_not_trvoid b p H)
  | H : HasType (Vec _ ?b) trvoid |- _ => apply (vec_not_trvoid b H)
  | H : HasType (List ?l) trvoid |- _ => apply (list_not_trvoid l H)
  | H : HasType (Num ?v) trvoid |- _ => apply (num_not_trvoid v H)
  end.

Ltac inv_trtype_false_faster_2  :=
  exfalso; try inv_trnum_fast_2; try inv_trbool_fast_2; try inv_trstr_fast_2; 
  try inv_trpair_fast_2; try inv_trvec_fast_2; try inv_trlist_fast_2; fail.

(************************************************************************)
(********************** START_JAIL AHHHHHHHHHHHHHH **********************)
 (* starts and simplifies hypotheses that hold the propositions *)

 Ltac start_jail :=
   intros;
   repeat 
   (match goal with
   | [ H : { ?t } |- _ ] => destruct H as [H [?H [?H ?H]]]
   | [ H : { t >> ?t & ?P } |- _ ] => destruct H as [H [?H [?H ?H]]]
   | [ H : { t >> ?t & ?P & ?Q} |- _ ] => destruct H as [H [?H [?H ?H]]]
   end); subst.

(* i don't know why i can't do subst *? *)

(************************************************************************)
(********************** CONCLUSION_JAIL AHHHHHHHHHHHHHH *****************)
(* simplifies the conclusion, leaves \/ alone *)
Ltac conclusion_jail :=
  repeat 
  (match goal with
  | [ |- _ /\ _ ] => constructor
  | [ |- _ -> _ ] => intro
  | [ |- ~_ ] => intro
  end); auto.

(************************************************************************)
(********************** TEMP \/ SOLUTION AHHHHHHHHHHHHH *****************)
(* temporarily solves \/  *)

Ltac temp_or_jail :=
  repeat
  (match goal with
  | [ |- _ \/ _ ] => try (left; constructor); try (right; constructor)
  end).

(************************************************************************)
(********************** SIMPLIFY_HYPOTHESIS AHHHHHHHHHH *****************)
(* destructs combined hypotheses  *)

Ltac simplify_hypothesis :=
  repeat
  (match goal with
    | [ H : _ \/ _ |- _ ] => destruct H
    | [ H : ?a /\ ?b |- _ ] => destruct H
    end); auto.

(************************************************************************)
(********************** UNFOLD_JAIL AHHHHHHHHHHHHHHHHHH *****************)
(* unfolds definitions  *)

Ltac unfold_jail := (* maybe if we add more definitions that need to be unfolded *)
  unfold get_true_prop in *; 
  unfold get_false_prop in *; 
  unfold get_type in *.
  
(************************************************************************)
(********************** TRUNION_JAIL AHHHHHHHHHHHHHHHHH *****************)
(* separates trunion hypotheses, may need to change? if trunion doesn't need to be separated and can
be solved with the false tactics, then I might change either the order or how the tactic works in general  *)

Ltac trunion_jail :=
    (match goal with
    | [ H : HasType _ (trunion _ _) |- _ ] => inversion H; subst
    end); auto.


(* destructs HasType with variable ( may need to be more specific ) *)
Ltac pls_destruct_correctly := (* add case for filtered_var destruct *)
    repeat
    (match goal with
    | [ x : TRValues |- _ ] => 
      match goal with
      | [ H : HasType x ?t |- _ ] => (* idtac x H; *) destruct x
      end
    end; try inv_trtype_false_faster_2).
    
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

(* if conclusion is a "properly" formed HasType, call constructor *)
Ltac ht_good_hehe :=
  match goal with
  | [ |- HasType _ trtop ] => constructor
  | [ |- HasType (Bool _) trbool ] => constructor
  | [ |- HasType (Num _) trnum ] => constructor
  | [ |- HasType (Str _) trstr ] => constructor
  | [ |- HasType (Pair ?a ?b) (trpair ?t1 ?t2) ] => constructor
  | [ |- HasType _ (trunion _ _) ] => try (apply HtUnion_L; auto; constructor; ht_good_hehe; fail) || apply HtUnion_R; auto; constructor; ht_good_hehe; fail
  | [ H : HasType (Pair ?a ?b) (trpair ?A ?B) |- HasType ?a ?A ] => inversion H; auto
  | [ H : HasType (Pair ?a ?b) (trpair ?A ?B) |- HasType ?b ?B ] => inversion H; auto
  | [ |- HasType (Void _) trvoid ] => constructor
  end.

(* make tactic that "solves" goals aka it shouldn't make new goals just solve them 
  ht_good_hehe, generalize_jail, simplify hypothesis?  *)


(* then there are tactics that simplify conclusion and hypothesis but doesn't gen 
more goals like almost conclusion jail ( will make more goals with \/) and simplify_hypothesis? 
though simplify_hypothesis also solves goals *)

Ltac pair_thing :=
  match goal with 
  | [ H : HasType (Pair ?a ?b) (trpair ?A ?B) |- _ ] => inversion H; clear H
  end.

Ltac eq_refl_special :=
  match goal with
  | [ H : ?a = ?a -> _ |- _ ] => try specialize (H eq_refl)
  end.

Ltac solve_pls :=
  try (repeat ht_good_hehe); try eq_refl_special; try generalize_jail 3; 
  simplify_hypothesis; try inv_trtype_false_faster_2; try equal_trv; try unequal_false; auto.

  
(* this shouldn't change the goal except simplifying it, and the hypothesis should be simplified *)
Ltac simple_jail :=
  match goal with 
  | [ filtered_var := _ |- _ ] => subst filtered_var
  | _ => idtac
  end; 
  simpl in *; subst; simplify_hypothesis; try pair_thing; 
  conclusion_jail; try (temp_or_jail; fail); 
  try trunion_jail; auto.

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

(* old tactic *)
Ltac pls_jail :=
  start_jail; simpl in *; conclusion_jail; temp_or_jail; try simplify_hypothesis; try unfold_jail; hopefully_this_works 2.


(* ************************************************************* *)
(* ***************** NEW STUFF ********************************* *)

Ltac break_jail n :=
  match n with
  | S ?n' =>
    do_it; try (
      match goal with
      | [ H : ~ HasType _ _ |- _ ] => destruct H
      | [ H : ~ (HasType _ _ /\ HasType _ _) |- _ ] => destruct H
      end
    ); pls_destruct_correctly; do_it; try car_cdr_jail; try (
      match goal with
      | [ |- _ \/ _ ] => try (left; break_jail 1; fail); try (right; break_jail 1; fail)
      end
    );
    break_jail n'
  | 0 => idtac
  end.

Ltac small_jail :=
  start_jail; conclusion_jail; simplify_hypothesis; try unfold_jail; auto.

Ltac vec_inv :=
  small_jail; match goal with 
  | [v : nat_vec ?a , n : ?b |- False ] => 
      match goal with 
      [H : ?v = ?a |- _ ] => (try inversion H; fail; clear H) 
      end
  end.
  
(* when should a tactic have try inside of the tactic and when should it be used with try instead?
like should unfold_jail be defined with try or should i use it with try as i did below? *)
Ltac apply_hypotheses :=
  match goal with 
  | [H : _ -> ?P |- ?P ] => apply H
  end.

Ltac new_jail :=
  start_jail; conclusion_jail; simplify_hypothesis; try unfold_jail; repeat apply_hypotheses; auto;
  (* this first part is definitely a "solve the trivial goals" part *)
  repeat (
    match goal with
    | [ |- _ \/ _ ] => try (left; break_jail 1; fail); try (right; break_jail 1; fail)
    end
  );
  break_jail 3. 

Ltac unify_vec := 
  match goal with
  | [ H : HasType ?v (trvec ?n) |- _ ] => inversion H
  end.

Ltac destruct2 x :=
  destruct x as [?x [?x ?x]].

Ltac make_val val type :=
  assert (HasType val type /\ val = (Bool false) -> True) as ?J by (repeat split; try constructor; try intro K; inversion K);
  assert (HasType val type /\ val <> (Bool false) -> True) as ?J by (repeat split; try constructor; try intro K; inversion K);
  assert (HasType val type) as ?J by constructor. 

Ltac make_hypothesis_not_bool val type :=
  let K := fresh "K" in 
  assert (HasType val type /\ val <> (Bool false)) as ?J by (repeat split; try constructor; try intro K; inversion K).


Ltac inv_trnum_fast :=
  exfalso;
  match goal with
  | H : HasType (Bool ?b) trnum |- _ => apply (bool_not_trnum b H)
  | H : HasType (Str ?b) trnum |- _ => apply (str_not_trnum b H)
  | H : HasType (Pair ?b ?p) trnum |- _ => apply (pair_not_trnum b p H)
  | H : HasType (Vec _ ?b) trnum |- _ => apply (vec_not_trnum b H)
  | H : HasType (List ?l) trnum |- _ => apply (list_not_trnum l H)
  | H : HasType (Void ?v) trnum |- _ => apply (void_not_trnum v H)
  end.

Ltac inv_trbool_fast :=
  exfalso;
  match goal with
  | H : HasType (Num ?b) trbool |- _ => apply (num_not_trbool b H)
  | H : HasType (Str ?b) trbool |- _ => apply (str_not_trbool b H)
  | H : HasType (Pair ?b ?p) trbool |- _ => apply (pair_not_trbool b p H)
  | H : HasType (Vec _ ?b) trbool |- _ => apply (vec_not_trbool b H)
  | H : HasType (List ?l) trbool |- _ => apply (list_not_trbool l H)
  | H : HasType (Void ?v) trbool |- _ => apply (void_not_trbool v H)
  end.

Ltac inv_trstr_fast :=
  exfalso;
  match goal with
  | H : HasType (Bool ?b) trstr |- _ => apply (bool_not_trstr b H)
  | H : HasType (Num ?b) trstr |- _ => apply (num_not_trstr b H)
  | H : HasType (Pair ?b ?p) trstr |- _ => apply (pair_not_trstr b p H)
  | H : HasType (Vec _ ?b) trstr |- _ => apply (vec_not_trstr b H)
  | H : HasType (List ?l) trstr |- _ => apply (list_not_trstr l H)
  | H : HasType (Void ?v) trstr |- _ => apply (void_not_trstr v H)
  end.

Ltac inv_trpair_fast :=
  exfalso;
  match goal with
  | H : HasType (Bool ?b) (trpair ?x ?y) |- _ => apply (bool_not_trpair b H)
  | H : HasType (Str ?b) (trpair ?x ?y) |- _ => apply (str_not_trpair b H)
  | H : HasType (Num ?b) (trpair ?x ?y) |- _ => apply (num_not_trpair b H)
  | H : HasType (Vec _ ?b) (trpair ?x ?y) |- _ => apply (vec_not_trpair b H)
  | H : HasType (List ?l) (trpair ?x ?y) |- _ => apply (list_not_trpair l H)
  | H : HasType (Void ?v) (trpair ?x ?y) |- _ => apply (void_not_trpair v H)
  end.

Ltac inv_trlist_fast :=
  exfalso;
  match goal with
  | H : HasType (Bool ?b) trlist |- _ => apply (bool_not_trlist b H)
  | H : HasType (Str ?b) trlist |- _ => apply (str_not_trlist b H)
  | H : HasType (Pair ?b ?p) trlist |- _ => apply (pair_not_trlist b p H)
  | H : HasType (Vec _ ?b) trlist |- _ => apply (vec_not_trlist b H)
  | H : HasType (Num ?l) trlist |- _ => apply (num_not_trlist l H)
  | H : HasType (Void ?v) trlist |- _ => apply (void_not_trlist v H)
  end.

Ltac inv_trvec_fast :=
  exfalso;
  match goal with
  | H : HasType (Bool ?b) (trvec _) |- _ => apply (bool_not_trvec b H)
  | H : HasType (Str ?b) (trvec _) |- _ => apply (str_not_trvec b H)
  | H : HasType (Pair ?b ?p) (trvec _) |- _ => apply (pair_not_trvec b p H)
  | H : HasType (Num ?b) (trvec _) |- _ => apply (num_not_trvec b H)
  | H : HasType (List ?l) (trvec _) |- _ => apply (list_not_trvec l H)
  | H : HasType (Void ?v) (trvec _) |- _ => apply (void_not_trvec v H)
  end.

Ltac inv_trvoid_fast :=
  exfalso;
  match goal with
  | H : HasType (Bool ?b) trvoid |- _ => apply (bool_not_trvoid b H)
  | H : HasType (Str ?b) trvoid |- _ => apply (str_not_trvoid b H)
  | H : HasType (Pair ?b ?p) trvoid |- _ => apply (pair_not_trvoid b p H)
  | H : HasType (Vec _ ?b) trvoid |- _ => apply (vec_not_trvoid b H)
  | H : HasType (List ?l) trvoid |- _ => apply (list_not_trvoid l H)
  | H : HasType (Num ?v) trvoid |- _ => apply (num_not_trvoid v H)
  end.

Ltac inv_trtype_false_faster  :=
  try inv_trnum_fast; try inv_trbool_fast; try inv_trstr_fast; 
  try inv_trpair_fast; try inv_trvec_fast; try inv_trlist_fast; fail.


Ltac find_destruct := 
  match goal with 
  | [H : {t : TRValues | ?P } |- _ ] => 
    match goal with 
    | |- context [ H ] => let name := H in destruct H as [?name [?name [?name ?name]]]
    end
  end.

Ltac fast_destruct_solve :=
  intros; find_destruct; auto.

Ltac destruct_invert :=
  match goal with 
  | [H : {t : TRValues | (HasType ?val ?type) /\ ?T /\ ?F } |- _ ] => 
    match goal with 
    | |- context [ H ] => let name := H in let val := fresh name in destruct H as [val [?name [?name ?name]]]; destruct val;
          match type with 
          | trnum => try inv_trnum_fast
          | trbool => try inv_trbool_fast
          | trstr => try inv_trstr_fast
          | trlist => try inv_trlist_fast
          | trpair ?x ?y => try inv_trpair_fast
          | trvec ?n => try inv_trvec_fast
          end; simpl
    end
  end.

Ltac very_small_jail :=
  intros; simpl; repeat split; try 
                              (match goal with 
                              | [ filtered_var := _ |- _ ] => subst filtered_var
                              end).