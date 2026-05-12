Set Warnings "-uniform-inheritance".
Set Warnings "-ambiguous-paths".
Set Warnings "-meta-collision".
From TRresearch.Tactics Require Import tactics_all.
From TRresearch Require Import Definitions If.
From TRresearch.Lemmas Require Import HasType_lemmas.


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

Ltac solve_if_TR_union_hastype :=
    let rec find_single_type H type := 
      match type of H with 
      | HasType ?x type => auto
      | HasType ?x (trunion ?t1 ?t2) => 
        let new_H1 := fresh "H" in 
        let new_H2 := fresh "H" in
        pose proof (hastype_union H) as new_H1;
        clear H;
        destruct new_H1 as [new_H2 | new_H2];
        find_single_type new_H2 type
      end in 
      match goal with 
      | |- HasType (proj1_sig (if_TR_union ?pred ?true_branch ?false_branch)) ?type => 
        match type of (if_TR_union pred true_branch false_branch) with
        | {t : TRValues | HasType t ?actual_type /\ _ /\ _ } => idtac actual_type ;
          let H := fresh "H" in 
            eassert (HasType (proj1_sig (if_TR_union pred true_branch false_branch)) actual_type) as H by (apply if_TR_union_HasType_union);
            find_single_type H type
        end 
      end.

Ltac solve_if_TR_hastype :=
  match goal with 
  | |- HasType (proj1_sig (if_TR_union ?pred ?true_branch ?false_branch)) ?type => 
    match type of (if_TR_union pred true_branch false_branch) with
    | {t : TRValues | HasType t ?actual_type /\ _ /\ _ } => idtac actual_type ;
      let H := fresh "H" in 
        epose proof ( if_TR_union_HasType_union pred true_branch false_branch) as H;
        eapply H
    end 
  end.