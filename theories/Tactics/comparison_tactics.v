Set Warnings "-uniform-inheritance".
Set Warnings "-ambiguous-paths".
Set Warnings "-meta-collision".
From TRresearch.Tactics Require Import tactics_all apply_pair_lemmas.
From TRresearch Require Import Definitions trnum_comparisons.
From TRresearch.Lemmas Require Import Trnum_Comparison_Lemmas.
From Stdlib Require Import Strings.String.
#[local] Obligation Tactic := try (timeout 1 test_jail).

Ltac invert_equality := 
    match goal with 
    | [H : less_than _ _ |- _ ] =>
        let K1 := fresh "K" in 
        inversion H as [?n ?n K1]; unfold ltTR in K1; simpl in K1; subst *; clear H
    | [H : less_than_equal _ _ |- _ ] =>
        let K1 := fresh "K" in 
        inversion H as [?n ?n K1]; unfold leTR in K1; simpl in K1; subst *; clear H
    | [ H : leTR _ _ |- _ ] => unfold leTR in H; simpl in H
    | [ H : ltTR _ _ |- _ ] => unfold ltTR in H; simpl in H
    | _ => idtac "nothing else in invert_equality"
    end.

Ltac get_props := 
match goal with 
| [H : HasType ?n ?type /\ ?n <> (Bool false) -> ?P |- _ ] => idtac H;
  match goal with 
  | [ H1 : done _ H |- _ ] => fail 1 
  | _ => 
    match goal with 
    | [ H : context [ less_than_equal ] |- _ ] => idtac "2";
    make_hypothesis_not_bool n type; 
        match goal with 
        | [H2 : HasType n type /\ n <> (Bool false) |- _ ] => idtac "3";
            let K := fresh "K" in 
            let C := fresh "C" in 
            specialize (H H2) as K; idtac "yes"; inversion K; idtac "here"; clear K;
            assert (done (HasType n type /\ n <> (Bool false) -> P) H) by constructor;
            repeat (progress invert_equality)
        end
    end
  end
end.

Ltac less_than_equal_0 :=
  match goal with 
  | |- less_than_equal (Num 0) (Num ?n) => apply (less_than_0 n)
  end.