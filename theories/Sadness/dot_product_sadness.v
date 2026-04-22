Set Warnings "-uniform-inheritance".
Set Warnings "-ambiguous-paths".
Set Warnings "-meta-collision".
From TRresearch.Tactics Require Import tactics_all comparison_tactics well_founded_tactic apply_predicate_lemmas prove_ifTR_branches apply_union_lemmas apply_if_lemmas.
From TRresearch Require Import Definitions safe_ref.
From TRresearch.Functions Require Import Basics If Vectors trnum_comparisons.
From TRresearch.Lemmas Require Import Trnum_Comparison_Lemmas.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Logic.EqdepFacts.
From Stdlib Require Import ProofIrrelevance.
#[local] Obligation Tactic := try well_founded_tactic; try (timeout 2 (time test_jail)).


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
  Hint Extern 0 => immediate_TR : TRHints.
  Hint Extern 2 => solve_lt_lte : TRHints.
  Hint Extern 2 => lia : TRHints.
  Hint Extern 2 => destruct_nat : TRHints.
  Hint Unfold get_true_prop : TRHints.
  Hint Extern 1 => prove_if_TR_branches : TRHints.
  Hint Extern 1 => apply_proj1_sig_is_string_true : TRHints.
  Hint Extern 1 => apply_proj1_sig_is_string_false : TRHints.
  Hint Extern 1 => apply_proj1_sig_is_number_true : TRHints.
  Hint Extern 2 => destructB : TRHints.

Ltac solve_ltB := 
  let P1 := fresh "H" in 
  let P2 := fresh "H" in 
  let P3 := fresh "H" in
  let P4 := fresh "H" in
  match goal with
  | [H : (Bool true) = (proj1_sig (ltTR_B _ _)) |- _ ] => 
      apply ltTR_B_is_lt in H as P1; apply ltTR_B_is_less_than in H as P2; apply ltTR_B_is_ltTR in H as P3; 
      try clear H
  | [ H : (Bool true) = (Bool (Nat.ltb _ _)) |- _ ] => 
      apply ltTR_B_is_lt in H as P1; apply ltTR_B_is_less_than in H as P2; apply ltTR_B_is_ltTR in H as P3; 
      try clear H
  end.

Ltac less_than_equal_0 :=
  match goal with 
  | |- less_than_equal (Num 0) (Num ?n) => apply (less_than_0 n)
  end.


Ltac destruct_application :=
  match goal with 
  | |- HasType (proj1_sig (?func ?op1)) ?type => destruct (func op1)
  | |- HasType (proj1_sig (?func ?op1 ?op2)) ?type => destruct (func op1 op2)
  end.

Hint Extern 1 => destruct_application : TRHints.



Ltac ltTR_goal := 
  match goal with 
  | [ H : Bool true = proj1_sig (ltTR_B [proj1_sig ?x] ?n) |- ltTR [proj1_sig ?x] ?n] => 
    match goal with 
    | [ x : {t : TRValues | ?P} |- _ ] => destructTR x; destruct x; try inv_trtype_false_faster
    end
  end.
  
Hint Extern 1 => ltTR_goal : TRHints.
Hint Extern 0 => solve_ltB : TRHints.

Close Scope string_scope.


Ltac normalize_to_less_than_equal_0 :=
  repeat (progress 
  match goal with 
  | |- less_than_equal (Num 0) ?n => 
    match goal with
    | [ n : { _ : TRValues | _ } |- context[ n ] ] => idtac n; destructTR n; destruct n; try inv_trtype_false_faster
    | _ => idtac n;
      match type of n with 
      | TRValues => simpl
      | nat => idtac
      end 
    end
  end); less_than_equal_0.

Ltac solve_less_than :=
  match goal with 
  | |- less_than ?n ?m => 
    match goal with 
    | |- context[ proj1_sig ?n0 ] => destructTR n0; destruct n0; try inv_trtype_false_faster
    end;
    match goal with 
    | |- context[ proj1_sig ?m0 ] => destructTR m0; destruct m0; try inv_trtype_false_faster
    end; constructor
  | |- ltTR ?n ?m => 
    match goal with 
    | |- context[ proj1_sig ?n0 ] => destructTR n0; destruct n0; try inv_trtype_false_faster; simpl
    end;
    match goal with 
    | |- context[ proj1_sig ?m0 ] => destructTR m0; destruct m0; try inv_trtype_false_faster; simpl
    end
  end; unfold ltTR; simpl; solve_ltB; auto; try lia.

Ltac solve_specific_thing :=
  match goal with 
  |  [ H : _ /\ _ -> less_than (Num 0) (Num ?m) |- _ ] => idtac H;
    match goal with 
    | |- ?n + m - (?o + m) < ?n + m - ?o => destruct m; idtac m;
      match goal with 
      | |- n + 0 - (o + 0) < n + 0 - o => 
        make_hypothesis_not_bool (Num 0) trnum;
        let J := fresh "J" in 
        match goal with 
        | [ J1 : HasType (Num 0) trnum /\ (Num 0) <> (Bool false) |- _ ] => idtac J1; try apply H in J1;
          inversion J1; subst *;
          match goal with 
          | [ H1 : ltTR (?func (Num 0)) (?func (Num 0)) |- _ ] => idtac func; unfold ltTR in H1; simpl in H1; lia
          end
        end
      | |- _ => apply strictly_lessthan; lia
      end
    end
  end.

Lemma what : forall (n n0 n1 : nat), 
  (HasType (Num n0) trnum /\ (Num n0) <> (Bool false) -> less_than (Num 0) (Num n0)) -> 
  n1 < n -> 
  n + n0 - (n1 + n0) < n + n0 - n1.
Proof. intros. solve_specific_thing. Qed.

Ltac solve_the_thing :=
  match goal with 
  | |- ltTR [proj1_sig (sub (sum ?n _) _)]
            [proj1_sig (sub (sum ?n _) _)] =>
    repeat match goal with 
    | |- context[ [proj1_sig ?x] ] => 
      destructTR x; destruct x; try inv_trtype_false_faster; simpl
    end; unfold ltTR; simpl;
    solve_ltB; apply what; auto
  end.

Ltac bool_not_true_or_false :=
  match goal with 
  | [ H : (Bool false) <> proj1_sig (ltTR_B ?n ?m) |- False ] => 
    match goal with 
    | [ H1 : (Bool true) <> proj1_sig (ltTR_B n m) |- False ] => 
      destruct (ltTR_B n m); 
      match goal with 
      | [ a : _ /\ _ /\ _ , H1_new : (Bool false) <> proj1_sig [ ?x ] |- _ ] => 
        destruct2 a; destruct x; try inv_trtype_false_faster; simpl in H; simpl in H1;
        match goal with 
        | [ H_new' : (Bool false) <> (Bool ?b) |- _ ] => destruct b; discriminates
        end
      end
    end 
  end.

Hint Extern 1 => bool_not_true_or_false : TRHints.


Hint Extern 1 => normalize_to_less_than_equal_0 : TRHints.
Hint Extern 1 => solve_less_than : TRHints.


Ltac search_lt :=
    match goal with 
    | |- ?n < ?m => 
      match goal with 
      | [ H : (Bool true) = (Bool (Nat.ltb n m)) |- _ ] => symmetry in H; inversion H
      | [ H : (Bool (Nat.ltb n m)) = (Bool true) |- _ ] => inversion H
      end
    end; apply (ltb_true_is_lt _ _); auto.

Hint Extern 1 => search_lt : TRHints.
Hint Extern 1 => solve_the_thing : TRHints.


#[local] Obligation Tactic := try fail.
Program Fixpoint dot_prod_what_tr_3 {n : nat} 
  (len : { trnum }) 
  (step : {t >> trnum & (less_than 0 t) & ~(less_than 0 t)}) 
  (x : { (trvec n) }) 
  (y : { (trvec n) })  
  (acc : { trnum }) 
  (i : {t >> trnum & (less_than t (sum (Num n) step)) & True}) {measure (proj1_sig (sub (sum n step) i)) ltTR}
   : { trnum } :=
  match (ltTR_B i n) as M with
  | Bool true => @dot_prod_what_tr_3 n len step x y (sum acc (mult (trvec_ref x i) (trvec_ref y i))) (sum i step) _
  | Bool false => acc
  | _r => False_rec _ _
  end.
Next Obligation.
  test_jail.
Defined. 
Next Obligation.
  test_jail.
Defined. 
Next Obligation.
  test_jail.
Defined. 
Next Obligation.
  test_jail.
Defined. 
Next Obligation.
  test_jail.
Defined. 
Next Obligation.
  test_jail.
Defined. 
Next Obligation.
  test_jail.


Defined. 
Next Obligation.
  test_jail.
Defined. 
Next Obligation.
  test_jail.
Defined. 
Next Obligation.
  test_jail. (* slowish *)
Defined. 
Next Obligation.
  test_jail.
Defined. 
Next Obligation.
  test_jail.
Defined. 
Next Obligation.
  test_jail.
Defined. 
Next Obligation.
  test_jail.
Defined. 
Next Obligation.
  intros; simpl.

  destructTR step; destruct step.


  Lemma what_now : forall (x : TRValues),
    HasType x trnum ->
    (exists (n : nat),
      x = (Num n)).
  Proof.
  intros. destruct x; try inv_trtype_false_faster. exists n; auto. Qed.

  Lemma reallay_specific_lemma : forall 
    (step : {t : TRValues
    |  HasType t trnum /\
      (HasType t trnum /\ t <> (Bool false) -> less_than (Num 0) t) /\
      (HasType t trnum /\ t = (Bool false) -> ~ less_than (Num 0) t)}),
    HasType (proj1_sig step) trnum /\
      (HasType (proj1_sig step) trnum /\ (proj1_sig step) <> (Bool false) -> less_than (Num 0) (proj1_sig step)) /\
      (HasType (proj1_sig step) trnum /\ (proj1_sig step) = (Bool false) -> ~ less_than (Num 0) (proj1_sig step)).
Proof. intros. destructTR step; simpl. split; auto. Qed.

    Lemma reallay_specific_lemma2 : forall {m} 
    (step : {t : TRValues
    |  HasType t trnum /\
      (HasType t trnum /\ t <> (Bool false) -> less_than t m) /\
      (HasType t trnum /\ t = (Bool false) -> True)}),
    HasType (proj1_sig step) trnum /\
      (HasType (proj1_sig step) trnum /\ (proj1_sig step) <> (Bool false) -> less_than (proj1_sig step) m) /\
      (HasType (proj1_sig step) trnum /\ (proj1_sig step) = (Bool false) -> True).
Proof. intros. destructTR step; simpl. split; auto. Qed.

Lemma what_what : forall (step : {t : TRValues
    |  HasType t trnum /\
      (HasType t trnum /\ t <> (Bool false) -> less_than (Num 0) t) /\
      (HasType t trnum /\ t = (Bool false) -> ~ less_than (Num 0) t)}) {n0 : nat} {H H2}, 
  (proj1_sig step) = (Num n0) ->
  (exist (fun t => (HasType t trnum) /\ (((HasType t trnum) /\ (t <> (Bool false))) -> True) /\ (((HasType t trnum) /\ (t = (Bool false))) -> True))
         (proj1_sig step)
         H) = 
  (exist (fun t => (HasType t trnum) /\ (((HasType t trnum) /\ (t <> (Bool false))) -> True) /\ (((HasType t trnum) /\ (t = (Bool false))) -> True))
         (Num n0)
         H2).
  Proof. intros. destructTR step; simpl in *. subst *. 
    destruct H as [?H [?H ?H]].
    destruct H2 as [?H [?H ?H]].
    apply eq_dep_eq_sig.

    assert (J : (conj H
(conj H0
H1)) = (conj H2
(conj H3
H4))).
    - f_equal. apply proof_irrelevance. f_equal; apply proof_irrelevance.
    - rewrite J. apply eq_dep_refl.
  Qed. 

  
  pose proof (reallay_specific_lemma step).
  destruct H as [?H [?H ?H]].
  pose proof (what_now (proj1_sig step)).
  destruct H2 as [?n ?H]; auto.

  pose proof (reallay_specific_lemma2 i).
  destruct H3 as [?H [?H ?H]].
  pose proof (what_now (proj1_sig i)).
  destruct H6 as [?n ?H]; auto.

  assert (J5 : HasType (Num n0) trnum /\
((HasType (Num n0) trnum /\ ((Num n0) <> (Bool false))) -> True) /\
((HasType (Num n0) trnum /\ ((Num n0) = (Bool false))) -> True)). repeat split; auto; constructor.
  assert (J6 : HasType (proj1_sig step) trnum /\
((HasType (proj1_sig step) trnum /\ ((proj1_sig step) <> (Bool false))) -> True) /\
((HasType (proj1_sig step) trnum /\ ((proj1_sig step) = (Bool false))) -> True)).
 repeat split; auto.

  pose proof (@what_what step _ J6 J5 H2).

  assert ((exist
(fun t : TRValues =>
HasType t trnum /\
(HasType t trnum /\ t <> false -> True) /\
(HasType t trnum /\ t = false -> True))
(proj1_sig step)
(dot_prod_what_tr_3_func_obligation_2 n step
(exist
(fun t : TRValues =>
HasType t trnum /\
(HasType t trnum /\ t <> false ->
less_than t
(proj1_sig
(sum n
(exist
(fun t0 : TRValues =>
HasType t0 trnum /\
(HasType t0 trnum /\
t0 <> false -> True) /\
(HasType t0 trnum /\
t0 = false -> True))
(proj1_sig step)
(dot_prod_what_tr_3_func_obligation_1
step))))) /\
(HasType t trnum /\ t = false -> True))
(proj1_sig
(sum
(exist
(fun t : TRValues =>
HasType t trnum /\
(HasType t trnum /\ t <> false ->
True) /\
(HasType t trnum /\ t = false ->
True)) (proj1_sig i)
(dot_prod_what_tr_3_func_obligation_12
n step i dot_prod_what_tr_3
Heq_M))
(exist
(fun t : TRValues =>
HasType t trnum /\
(HasType t trnum /\ t <> false ->
True) /\
(HasType t trnum /\ t = false ->
True)) (proj1_sig step)
(dot_prod_what_tr_3_func_obligation_13
n step i dot_prod_what_tr_3
Heq_M))))
(dot_prod_what_tr_3_func_obligation_14 n
step i dot_prod_what_tr_3 Heq_M)))) = (exist
(fun t : TRValues =>
HasType t trnum /\
(HasType t trnum /\ t <> false -> True) /\
(HasType t trnum /\ t = false -> True)) (proj1_sig step) J6)).
  - destructTR step; simpl.
    apply eq_dep_eq_sig.
    (assert (K : (dot_prod_what_tr_3_func_obligation_2 n [step]
[proj1_sig (sum [proj1_sig i] [step])]) = J6)).
    apply eq_dep_refl.
  rewrite H7.

  subst H6.
  
  really_simple_start.
  
Defined.
Next Obligation.
  test_jail.
Defined. 
Next Obligation.
  test_jail.
Defined.
Next Obligation.
  test_jail.
Defined.
Next Obligation.
  test_jail.
Defined.
Next Obligation.
  test_jail.
Defined.
Next Obligation.
  test_jail.
Defined.
Next Obligation.
  test_jail.
Defined.
Next Obligation.
  well_founded_tactic.
Defined.