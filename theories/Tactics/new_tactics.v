Set Warnings "-uniform-inheritance".
Set Warnings "-ambiguous-paths".
Set Warnings "-meta-collision".
From TRresearch.Tactics Require Import Tactic_jail.
From TRresearch Require Import Definitions.
From Corelib Require Import Program.Tactics.


Ltac rewrite_jail' := 
  match goal with 
  | [ H : ?r = ?x |- _ ] => (rewrite H in *) + (rewrite <- H in *) ; clear H
  | _ => fail "rewrite_jail' match fail"
  end.

Create HintDb TRHints.

(* from crush *)
Definition done (T : Type) (x : T) := True.

Ltac instantiate' T e trace := 
  match goal with 
  | [ H : T |- _ ] =>
    match trace with 
    | 1 => 
      match goal with 
      | [ H2 : done T H |- _ ] => fail 2
      end
    | _ => 
      let S := fresh "S" in 
      let C := fresh "C" in 
        specialize (e H) as S; 
        assert (done T H) as C by constructor;
        instantiate' T e 1 
    end
  | _ => match trace with | 0 => fail 1 | _ => clear e end
  end.

Ltac undone := 
  match goal with 
  | [ H : done _ _ |- _ ] => clear H 
  end.

Ltac spec := 
  match goal with 
  | [ H : forall x : ?T, _ |- _ ] => idtac "spec" H T; instantiate' T H 0
  end.

Ltac specify := 
  repeat spec; repeat undone.

Ltac subst_definition' := 
  match goal with 
  | [ def := _ |- _ ] =>
    match goal with 
    | [ H : context [ def ] |- _ ] => simpl in def; subst def
    | |- context [ def ] => simpl in def; subst def
    | _ => fail "no hypothesis uses " def
    end 
  | _ => fail "no definition"
  end.

Ltac match_union_type x y type := 
  tryif (constr_eq_strict x type) 
  then idtac type "is in union" 
  else (constr_eq_strict y type).

Ltac inv_trtype_choice t := 
  match t with 
  | trnum => inv_trnum_fast
  | trbool => inv_trbool_fast
  | trstr => inv_trstr_fast
  | trvec => inv_trvec_fast
  | trvoid => inv_trvoid_fast
  | trpair => inv_trpair_fast
  | trlist => inv_trlist_fast
  end.

Ltac inv_trtype_union H t1 t2 := 
  inversion H; try inv_trtype_choice t1; inv_trtype_choice t2.



Ltac check_union := 
  match goal with
  | H : HasType (Bool ?b) (trunion ?x ?y) |- _ =>  idtac "first" x "second" y; 
    tryif match_union_type x y trbool 
    then idtac "union is a match"
    else inv_trtype_union H x y
  | H : HasType (Str ?b) (trunion ?x ?y) |- _ => idtac "first" x "second" y; 
    tryif match_union_type x y trstr 
    then idtac "union is a match"
    else inv_trtype_union H x y
  | H : HasType (Num ?b) (trunion ?x ?y) |- _ => idtac "first" x "second" y; 
    tryif match_union_type x y trnum 
    then idtac "union is a match"
    else inv_trtype_union H x y
  | H : HasType (Vec _ ?b) (trunion ?x ?y) |- _ => idtac "first" x "second" y; 
    tryif match_union_type x y trvec 
    then idtac "union is a match"
    else inv_trtype_union H x y
  | H : HasType (List ?l) (trunion ?x ?y) |- _ => idtac "first" x "second" y; 
    tryif match_union_type x y trlist 
    then idtac "union is a match"
    else inv_trtype_union H x y
  | H : HasType (Void ?v) (trunion ?x ?y) |- _ =>  idtac "first" x "second" y; 
    tryif match_union_type x y trvoid 
    then idtac "union is a match"
    else inv_trtype_union H x y
  | H : HasType (Pair ?a ?b) (trunion ?x ?y) |- _ => idtac "first" x "second" y; 
    tryif match_union_type x y trpair 
    then idtac "union is a match"
    else inv_trtype_union H x y
  end. 

Ltac check_union_false := 
  match goal with 
  | [H : HasType ?x (trunion ?t1 ?t2) |- _ ] => 
    tryif (constr_eq_strict t1 trtop)
    then fail "union is top"
    else tryif (constr_eq_strict t2 trtop)
         then fail "union is top"
         else check_union
  end.

Ltac solve_union := 
  match goal with 
  | [ H : ~  ?Maybe |- _ ] => destruct H; trivial with TRHints; fail
  | [ H : HasType ?x (trunion ?T1 ?T2) |- _ ] => repeat (progress check_union)

  end.

Ltac destructTR_if_needed' := 
  match goal with 
  | [ x : TRValues |- _ ] => 
    match goal with 
    | [ H : HasType x _ |- _ ] => 
      match goal with 
      | |- False => idtac "goal is False" x; destruct x; try inv_trtype_false_faster; repeat (progress check_union)
      | |- context [ x ] => idtac "goal has " x; destruct x; try inv_trtype_false_faster; repeat (progress check_union) 
      end 
    | _ => fail "no HasType for " x " in destruct_TR"
    end
  end.

Definition hide (T : Type) (x : T) := True.

Ltac hide_definitions :=
  match goal with 
  | [ H := ?a : _ |- _ ] =>
    match goal with 
    | |- context [ H ] => idtac "didn't hide" H "as it's used in the goal"
    | [ H1 : context [ H ] |- _ ] => idtac "didn't hide" H "as it's used in" H1 
    | _ => 
      match type of H with 
      | ?A => let i := fresh "i" in (pose (i := a)); assert (hide A i) by constructor; subst i; clear H 
      end 
    end 
  end.

Ltac unfold_definitions H := 
  try unfold get_true_prop in H.

Ltac unfold_definitions_goal := 
  try unfold get_true_prop.

Ltac simpl_function_calls_hypothesis := 
  match goal with 
  | [ H : context[ [?x] ] |- _ ] => unfold_definitions H; simpl in H
  end.

Ltac simpl_function_calls_goal := 
  match goal with 
  | |- context[ [?x] ] => unfold_definitions_goal; simpl
  end.

(* why do I have these tactics here instead of vector_tactics? idk man :( )*)
Ltac rewrite_vec trace :=
  match goal with 
  | [ v1 : nat_vec ?n1 |- _ ] => idtac v1 "first";
    match goal with 
    | [ H : HasType (Vec _ v1) (trvec ?n2) |- _ ] => idtac H; 
      match goal with 
      | |- context [ n1 ] => 
        match goal with 
        | |- context [ n2 ] => 
          match trace with 
          | 0 => inversion H; 
                 let S := fresh "S" in 
                 assert (done (nat_vec n1) v1) by constructor; 
                 idtac v1 H "inverted"; rewrite_vec 1 
          | _ => 
            match goal with 
            | [ P : done (nat_vec n1) v1 |- _ ] => fail 3
            | _ => inversion H; 
                    let S := fresh "S" in 
                    assert (done (nat_vec n1) v1) by constructor; 
                    idtac v1 H "inverted"; rewrite_vec 1 
            end
          end
        end
      end 
    end 
  | _ => idtac trace
  end.

Ltac vec_inversion := 
  rewrite_vec 0.

Lemma false_is_trbool : HasType false trbool /\ (Bool false) = (Bool false).
Proof. repeat constructor. Qed.

Lemma true_is_trbool : HasType true trbool /\ (Bool true) <> (Bool false).
Proof. repeat constructor. intro. discriminates. Qed.

Ltac specialize_booleans := 
  match goal with 
  | [ H : HasType (Bool false) trbool /\ (Bool false) = (Bool false) -> _ |- _ ] => specialize (H false_is_trbool)
  | [ H : HasType (Bool true) trbool /\ (Bool true) <> (Bool false) -> _ |- _ ] => specialize (H true_is_trbool)
  end.

Ltac really_simple_start := 
  try intros; simpl;
  repeat subst_definition';
  repeat rewrite_jail';
  conclusion_jail;
  simplify_hypothesis; 
  auto with TRHints.

Ltac test_jail := 
  try (really_simple_start; fail);
  start_jail; 
  repeat (match goal with 
  | |- ~ _ => intro 
  | |- _ <> _ => intro
  end);
  repeat subst_definition';
  try (match goal with 
  | [ H : context [ trvec ] |- _ ] => repeat rewrite_jail'; vec_inversion
  end );
  try (match goal with 
  | |- (HasType _ _) /\ _ /\ _ => make_constructor
  end); auto with TRHints; 
  repeat (match goal with 
  | |- _ /\ _ => split 
  end); auto with TRHints; 
  repeat (match goal with 
  | [ H : _ /\ _ |- _ ] => destruct H 
  end);
  repeat (progress simpl_function_calls_hypothesis);
  repeat (progress destructTR_if_needed'); auto with TRHints;
  repeat hide_definitions;
  repeat (match goal with 
  | [ H : (HasType _ _) /\ _ -> True |- _ ] => clear H
  end);
  repeat (progress simpl_function_calls_hypothesis);
  repeat (progress simpl_function_calls_goal);
  try match goal with 
  | [ H : (HasType _ _) /\ _ -> True |- _ ] => fail 1
  | [ H : forall _:_, _ |- _ ] => specify 
  end; auto with TRHints;
  try match goal with 
  | [ H : (HasType _ _) \/ (HasType _ _) |- _ ] => destruct H; try inv_trtype_false_faster
  end;
  try rewrite_jail';
  try specialize_booleans;
  try solve_union; 
  auto with TRHints.

Ltac unfold_get_true_prop_hypothesis :=
  match goal with 
  | [ H : context[ get_true_prop ] |- _ ] => unfold get_true_prop in H 
  end.

Ltac destructTR_fresh x := 
  let a := fresh "x" in destruct x as [?a [?a [?a ?a]]].

Ltac autoTR := 
  auto with TRHints.

Ltac union_input := 
  match goal with 
  | [ H : HasType ?val (trunion ?t1 ?t2) |- _ ] =>
    match goal with 
    | [ H1 : ~(HasType (proj1_sig [val]) t1) |- (HasType (proj1_sig [val]) t2) ] => inversion H; auto; destruct H1; trivial with TRHints
    | [ H1 : ~(HasType (proj1_sig [val]) t2) |- (HasType (proj1_sig [val]) t1) ] => inversion H; auto; destruct H1; trivial with TRHints
    end
  end.

Ltac P_and_not_P :=
  match goal with 
  | [ H1 : ~ ?P |- _ ] => 
    match goal with 
    | [ H : P |- _ ] => destruct H1; auto 
    end
  | [ H1 : ~ (?P1 /\ ?P2) |- _ ] => 
    match goal with 
    | [ H : P1 , H2 : P2 |- _ ] => destruct H1; split; auto
    end
  end.

Ltac one_of_union_type :=
  let find_type x type := 
    match goal with 
    | [ H : HasType x (trunion ?type1 ?type2) |- HasType (proj1_sig [x]) type ] => 
      match goal with 
      | [ H2 : (done (HasType x (trunion type1 type2)) H) |- _ ] => fail 1 
      | _ => 
        inversion H; subst *;
        let J := fresh "J" in 
          assert (done (HasType x (trunion type1 type2)) H) as J by constructor
      end
    | [ H : ~ (HasType (proj1_sig [x]) ?type1) |- _ ] => simpl in H;
      match goal with 
      | [ H2 : HasType x type1 |- _ ] => P_and_not_P
      end
    | [ H : HasType x type |- _ ] => autoTR
    end
  in
  match goal with 
  | [ x : {trunion ?type1 ?type2} |- HasType ?val ?type ] =>
    match goal with 
    | |- HasType (proj1_sig x) type => destructTR x; repeat (progress find_type x type)
    end
  end.

Ltac invert_Num := 
  match goal with 
  | [ H : (Num ?n) = (Num ?m) |- _ ] => inversion H 
  end.

Ltac make_done type val := 
  let K := fresh "K" in 
    assert (K : done type val) by constructor. 

  
Ltac simpl_proj1_sig :=
  repeat (progress 
    match goal with 
    | [ H : context[ proj1_sig [ ?x ] ] |- _ ] => simpl in H 
    | |- context[ proj1_sig [ ?x ] ] => simpl
    end).

Ltac can_form val :=
  destruct val; try inv_trtype_false_faster.

Ltac immediate_TR := 
  match goal with 
  | [ x : {t : _ | HasType t ?type /\ _ /\ _} |- _ ] => 
    match goal with 
    | |- HasType (proj1_sig x) type => destructTR x; autoTR 
    end 
  | [ x : HasType ?v ?type /\ _ /\ _ |- _ ] => 
    match goal with 
    | |- HasType (proj1_sig [v]) type => destruct2 x; autoTR
    end
  end.

Ltac destruct_nat := 
  match goal with 
  | [ H : forall n : nat, _ <> (Num ?m) |- False ] => idtac m;
    match goal with 
    | [ H2 : (Num 0) <> (Num m) |- False ] =>  idtac "there";
      destruct m; try spec; try discriminates
    end 
  end.

Ltac force_unequal :=
  match goal with 
  | [ H : ?n = ?m |- _ ] => 
    match type of n with 
    | ?A => 
      match type of m with 
      | A => fail 
      | ?B => discriminates
      end 
    end 
  end. 

Ltac destructB := 
  match goal with 
  | |- context[ Nat.eqb ?n1 ?n2 ] => destruct (Nat.eqb n1 n2)
  end.