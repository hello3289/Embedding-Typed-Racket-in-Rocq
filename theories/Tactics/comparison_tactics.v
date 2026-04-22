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
  | |- less_than_equal (Num 0) (proj1_sig ?n) => 
      destructTR n; destruct n; try inv_trtype_false_faster; simpl; apply less_than_0
  end.

Ltac get_P val type H :=
  make_hypothesis_not_bool val type; 
  match goal with 
  | [ H1 : (HasType val type /\ (val <> (Bool false))) |- _ ] => 
    let K := fresh "K" in 
    let J1 := fresh "J" in 
    let J2 := fresh "J" in 
      specialize (H H1) as K; 
      match goal with 
      | [ H2 : _ /\ _ |- _ ] =>
        destruct H2 as [J1 J2]
      | _ => idtac
      end; try (inversion K); try (inversion J1); try (inversion J2);
      repeat (progress 
        match goal with 
        | [ H2 : ltTR _ _ |- _ ] => unfold ltTR in H2; simpl in H2
        | [ H2 : leTR _ _ |- _ ] => unfold leTR in H2; simpl in H2
        | [ H2 : eqTR _ _ |- _ ] => unfold eqTR in H2; simpl in H2
        end)
  end.

Ltac unpack_props x flag :=
  destructTR x; can_form x;
  match flag with 
  | 0 =>
    match goal with 
    | [ H : (HasType ?n trnum /\ ?F) -> less_than_equal _ _ |- _ ] => 
      get_P n trnum H 
    | [ H : (HasType ?n trnum /\ ?F) -> (less_than_equal _ _ /\ _) |- _ ] => 
      get_P n trnum H 
    | [ H : (HasType ?n trnum /\ ?F) -> less_than _ _ |- _ ] =>
      get_P n trnum H 
    | [ H : (HasType ?n trnum /\ ?F) -> (less_than _ _ /\ _) |- _ ] =>
      get_P n trnum H 
    end
  | _ => idtac
  end; 
  simpl_proj1_sig.

Ltac solve_lt_lte := 
  match goal with 
  | |- ltTR ?n [ proj1_sig ?m ] => 
      match type of m with 
      | ?type => make_done type m; unpack_props m 0; idtac "done"; progress solve_lt_lte
      end
  | |- ltTR [ proj1_sig ?n ] ?m =>
      match type of n with 
      | ?type => make_done type n; unpack_props n 0; idtac "done"; progress solve_lt_lte
      end
  | |- ltTR ?n ?m => unfold ltTR; simpl
  | |- leTR ?n ?m => unfold leTR; simpl
  | |- less_than ?n ?m => constructor; unfold ltTR; simpl 
  | |- less_than_equal ?n ?m => constructor; unfold leTR; simpl 
  | |- ?n < ?m => idtac "already constructor lt"
  | |- ?n <= ?m => idtac "already constructor le"
  end; 
  match goal with 
  | |- ?n ?comp ?m => idtac n comp m "here"; 
    match goal with 
    | [ H : (done {t : TRValues | ?P /\ (?Q -> ?COMP) /\ ?R} _) |- _ ] => idtac H
    | [ x : {t : TRValues | ?P /\ (?Q -> less_than_equal t (Num n)) /\ ?R } |- _ ] => unpack_props x 0
    | [ x : {t : TRValues | ?P /\ (?Q -> less_than_equal (Num n) t) /\ ?R } |- _ ] => unpack_props x 0
    | [ x : {t : TRValues | ?P /\ (?Q -> less_than_equal t (Num m)) /\ ?R } |- _ ] => unpack_props x 0
    | [ x : {t : TRValues | ?P /\ (?Q -> less_than_equal (Num m) t) /\ ?R } |- _ ] => unpack_props x 0
    end
  end; 
  try invert_Num; subst *.

Ltac apply_le_ident :=
  match goal with 
  | [ n : nat |- _ ] => 
    match goal with 
    | |- less_than_equal (Num n) (Num n) => constructor; apply le_ident
    | |- leTR (Num n) (Num n) => apply le_ident
    end 
  end.