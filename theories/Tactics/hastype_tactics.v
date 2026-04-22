Set Warnings "-uniform-inheritance".
Set Warnings "-ambiguous-paths".
Set Warnings "-meta-collision".
From TRresearch.Tactics Require Import tactics_all.
From TRresearch Require Import Definitions If.
From TRresearch.Lemmas Require Import HasType_lemmas.

Axiom trunion_eq : forall (t : TRTypes), 
  t = (trunion t t).

Ltac unify_trunion_type type t1 t2 label := 
  let H0 := fresh "H" in 
    assert (H0 : type = (trunion type type)) by apply trunion_eq;
    assert (label : type = (trunion t1 t2)) by ((repeat (rewrite <- H0)); auto).
  

Ltac apply_if_TR_union_HasType_union :=
  match goal with 
  | |- HasType (proj1_sig (if_TR_union ?pred  ?true_branch ?false_branch)) ?type => 
    match type of true_branch with 
    | ?P -> {t : TRValues | HasType t ?type1 /\ _ /\ _} => idtac type1;
      match type of false_branch with 
      | ?Q -> {t : TRValues | HasType t ?type2 /\ _ /\ _} => idtac type2;
            let H1 := fresh "H" in 
              unify_trunion_type type type1 type2 H1;
              rewrite H1;
              refine (if_TR_union_HasType_union 
                        pred 
                        true_branch 
                        false_branch)
      end
    end
  end.

Ltac apply_andTR_HasType :=
  match goal with 
    | [H : HasType (proj1_sig (andTR_2 (?pred1 ?x) (?pred2 ?y))) trbool |- HasType (proj1_sig _) ?type ] => 
      (match type of (pred1 x) with 
      | {t : TRValues | _ /\ (_ /\ _ -> HasType _ type) /\ _} =>
        match goal with 
        | [ H0 : proj1_sig (andTR_2 (pred1 x) (pred2 y)) <> (Bool false) |- HasType (proj1_sig x) type ] => 
          refine (andTR_HasType_left H0)
        end
      end) + 
      (match type of (pred2 y) with 
      | {t : TRValues | _ /\ (_ /\ _ -> HasType _ type) /\ _} =>
        match goal with 
        | [ H0 : proj1_sig (andTR_2 (pred1 x) (pred2 y)) <> (Bool false) |- HasType (proj1_sig y) type ] => 
          refine (andTR_HasType_right H0)
        end
      end)
    end.

Ltac apply_andTR_NotHasType :=
  match goal with 
    | [H : HasType (proj1_sig (andTR_2 (?pred1 ?x) (?pred2 ?y))) trbool |- ~(HasType (proj1_sig _) ?type1 /\ HasType (proj1_sig _) ?type2) ] => 
      match type of (pred1 x) with 
      | {t : TRValues | _ /\ (_ /\ _ -> HasType _ type1) /\ _} =>
        match type of (pred2 y) with 
        | {t : TRValues | _ /\ (_ /\ _ -> HasType _ type2) /\ _} =>
          match goal with 
          | [ H0 : proj1_sig (andTR_2 (pred1 x) (pred2 y)) = (Bool false) |- ~(HasType (proj1_sig x) type1 /\ HasType (proj1_sig y) type2) ] => 
            refine (andTR_HasType_false H0)
          end
        end
      end
    end.