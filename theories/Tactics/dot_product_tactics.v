Set Warnings "-uniform-inheritance".
Set Warnings "-ambiguous-paths".
Set Warnings "-meta-collision".
From TRresearch.Tactics Require Import tactics_all.
From TRresearch Require Import Definitions.
From TRresearch.Functions Require Import Basics trnum_comparisons.
From TRresearch.Lemmas Require Import Trnum_Comparison_Lemmas.

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

Ltac reserve :=
  match goal with 
  | [ x : {t : TRValues | ?T /\ ?P /\ ?Q } |- _ ] => 
    match goal with 
    | [ H : (done _ x) |- _ ] => fail 1
    | |- context [proj1_sig x] => 
      assert (done {t : TRValues | T /\ P /\ Q } x ) by constructor
    end 
end.


Ltac generalize_operands :=
  match goal with 
  | |- ltTR 
      [proj1_sig 
        (sub (sum ?n [proj1_sig ?step])
              [proj1_sig (sum [proj1_sig ?i] [proj1_sig ?step])])]
      [proj1_sig 
        (sub (sum ?n [proj1_sig ?step]) [proj1_sig ?i])] => 
    let z1 := fresh "z" in 
    let z2 := fresh "z" in 
    eset (z1 := [proj1_sig (sub (sum n [proj1_sig step]) [proj1_sig (sum [proj1_sig i] [proj1_sig step])])]);
    eset (z2 := [proj1_sig (sub (sum n [proj1_sig step]) [proj1_sig i])])
  end.


Ltac solve_the_thing_new :=
repeat reserve; generalize_operands;
match goal with 
| |- ltTR ?z1 ?z2 => 
  repeat match goal with 
  | [ H : done _ ?x |- _ ] => destructTR x; destruct x; try inv_trtype_false_faster; clear H
  end; unfold ltTR; simpl; subst *;
  solve_ltB; apply what; auto
end.