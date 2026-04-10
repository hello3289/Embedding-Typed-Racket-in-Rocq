Set Warnings "-uniform-inheritance".
Set Warnings "-ambiguous-paths".
Set Warnings "-meta-collision".
From TRresearch Require Import Definitions.
From TRresearch.Functions Require Import If.
From TRresearch.Tactics Require Import tactics_all.
From Corelib Require Import Program.Tactics.

Ltac prove_if_TR_branches := 
  let rec solve_branch := idtac "solve-branch";
    match goal with 
    | [ x : {?A} |- context[ (if_TR_union _ _ _) ] ] => prove_if_TR_branches
    | [ x : {?A} |- HasType (proj1_sig _) ?type ] => idtac type "first";
      match goal with 
    | |- context [ x ] => idtac x;
        match goal with 
        | |- context[ let (_, _) := ?func ?op1 ?op2 in _] => idtac "new 1" func op1 op2;
          match type of (func op1 op2) with 
          | {type} => destruct (func op1 op2);
            match goal with 
            | [ x1 : _ /\ _ /\ _ |- _ ] => idtac x1; destruct x1 as [?x1 [?x1 ?x1]]; try autoTR; idtac "complete"
            end
          end
        | |- context[ let (_, _) := ?func ?op in _ ] => idtac "new 2" func op;
          match type of (func op) with 
          | {type} => destruct (func op);
            match goal with 
            | [ x1 : _ /\ _ /\ _ |- _ ] => idtac x1; destruct x1 as [?x1 [?x1 ?x1]]; try autoTR; idtac "complete"
            end
          end
        | |- context[ let (_, _) := x in _ ] => idtac x; destruct x;
          match goal with 
          | [ x1 : _ /\ _ /\ _ |- _ ] => idtac x1; destruct x1 as [?x1 [?x1 ?x1]]; try autoTR; idtac "complete"
          end
        end
      end
    end 
  in 
  match goal with 
  | [ x : {?A} |- context[ if_TR_union ?pred ?true_branch ?false_branch ] ] => idtac "matched";
    destructTR_fresh pred; (* destructs the predicate to get to the boolean *)
    match goal with 
    | [ H3 : HasType ?x1 trbool |- _ ] => idtac "boolean"; destruct x1; try inv_trtype_false_faster; (* actually gets the boolean *)
      match goal with 
      | [ b : bool |- _ ] => idtac "destruct boolean"; destruct b; simpl; (* destruct the boolean to get to the cases *)
        match goal with 
        | |- context[ true ] => idtac true_branch ; try solve_branch
        | |- context[ false ] => idtac false_branch; try solve_branch
        | |- HasType _ _ => autoTR
        end
      end
    end
  end.