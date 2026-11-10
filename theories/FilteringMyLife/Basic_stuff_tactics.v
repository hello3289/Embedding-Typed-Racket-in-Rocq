Set Warnings "-ambiguous-paths".
From TRresearch Require Import Definitions.
From TRresearch Require Import tactics_all.
From Corelib Require Import Lists.ListDef.

Ltac get_exists_hypothesis := 
    match goal with 
    | [ H0 : HasType (List ?l) (trlist ?type) |- _ ] => 
      match goal with 
      | [ H2 : HasType (List l) (trlist type) /\ List l <> Bool false -> 
              exists _ _, List l = _ |- False ] => 
        let J       := fresh "J" in 
        let intro_H := fresh "H" in 
        let J2      := fresh "J" in
        let first   := fresh "first" in 
        let rest    := fresh "rest" in 
        let J3      := fresh "J" in 
          assert (J : HasType (List l) (trlist type) /\ List l <> Bool false ) by 
            (split; try auto; intro intro_H; inversion intro_H);
          specialize (H2 J) as J2; destruct J2 as [first [rest J3]]
      end 
    end.
Ltac list_false := 
  match goal with 
  | [ H0 : HasType (List ?l) (trlist ?type) |- False ] => 
    match goal with 
    | [ H1 : forall (_f: TRValues) (_r : list TRValues),
            List (_f :: _r) <> List l,
        H2 : HasType (List l) (trlist type) /\ List l <> Bool false -> 
            exists _ _, List l = _ |- False ] => 
      get_exists_hypothesis; 
      match type of l with 
      | list TRValues => 
        let c := fresh "c" in 
        let d := fresh "d" in
        let K := fresh "K" in 
        destruct l as [| c d ]; 
        match goal with 
        | [ H3 : List nil = List (_ :: _) |- False ] => inversion H3 
        | [ H3 : List (c :: d) = List (_ :: _) |- False ] => 
            specialize (H1 c d) as K; destruct K; auto
        | [ H3 : List (_ :: _) = List (c :: d) |- False ] => 
            specialize (H1 c d) as K; destruct K; auto
        end
      | _ => fail 3
      end
    end
  end.

  Ltac Forall_inversion := 
  match goal with 
  | [ H : Forall (fun _r : TRValues => ?P) _ |- _ ] => inversion H 
  end.

Ltac first_type := 
  match goal with 
  | [ H : HasType (List (?h :: ?t)) (trlist ?type) |- _ ] => 
    match goal with 
    | |- HasType h type => inversion H; Forall_inversion; auto 
    end 
  end.

Ltac rest_type := 
  match goal with 
  | [ H : HasType (List (?h :: ?t)) (trlist ?type) |- _ ] => 
    match goal with 
    | |- HasType (List t) (trlist type) => 
        inversion H; Forall_inversion; constructor; auto
    end 
  end.

Ltac first_rest_type := 
  match goal with 
  | [ H : HasType (List ?l) (trlist ?type) |- _ ] => 
    match goal with 
    | [H1 : HasType ?t ?type |- _ ] => 
      match goal with 
      | |- HasType (List (t :: l)) (trlist type) => 
          inversion H; constructor; constructor; auto
      end
    end 
  end.
