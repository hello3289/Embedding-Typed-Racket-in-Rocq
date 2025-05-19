From research Require Import Definitions.

(* i'm dying there is still the "trying to automate my life file" *)

Ltac destruct_jail :=
  repeat (
    match goal with
    | n : TRValues |- _ =>
      match goal with
      | H : HasType n _ |- _ => destruct n
      end
    | |- context [_ /\ _] => split
    end).

Ltac inv_trnum :=
  match goal with
  | H : HasType (Bool ?b) trnum |- _ => inversion H
  | H : HasType (Str ?b) trnum |- _ => inversion H
  | H : HasType (Pair ?b ?p) trnum |- _ => inversion H
  end.
Ltac inv_trbool :=
  match goal with
  | H : HasType (Num ?b) trbool |- _ => inversion H
  | H : HasType (Str ?b) trbool |- _ => inversion H
  | H : HasType (Pair ?b ?p) trbool |- _ => inversion H
  end.
Ltac inv_trstr :=
  match goal with
  | H : HasType (Bool ?b) trstr |- _ => inversion H
  | H : HasType (Num ?b) trstr |- _ => inversion H
  | H : HasType (Pair ?b ?p) trstr |- _ => inversion H
  end.
Ltac inv_trpair :=
  match goal with
  | H : HasType (Bool ?b) (trpair ?x ?y) |- _ => inversion H
  | H : HasType (Str ?b) (trpair ?x ?y) |- _ => inversion H
  | H : HasType (Num ?b) (trpair ?x ?y) |- _ => inversion H
  end.

Ltac inv_trtype_false  :=
 try inv_trbool; try inv_trnum; try inv_trstr; try inv_trpair; fail.


Ltac destruct_forall_jail :=
  match goal with
  | H : forall _ : ?t, _ |- _ => 
        match goal with
        | H0 : t |- _ => destruct (H H0)
        end
  | H : forall _ _ : ?t, _ |- _ => 
        match goal with
        | H0 : t |- _ => 
            match goal with
            | H1 : t |- _ => destruct (H H0 H1) (* is there a way to say that H0 and H1 are not the same? *)
            end
        end
  end; auto.

Ltac start_jail :=
  simpl; intros;
  repeat (
    match goal with 
    | H : {_ >> _} |- _ => destruct H as [?H [?H [?H ?H]]]
    | H : {_ >> _ & _ & _} |- _ => destruct H as [?H [?H [?H ?H]]]
    | H : _ = proj1_sig _ |- _ => simpl in H
    end);
  destruct_jail; try inv_trtype_false; auto.

Ltac false_jail :=
  match goal with
  | H : HasType (?t ?v) ?tr |- False => inversion H
  | H : ?b ?x <> ?b ?x |- _ => destruct H; auto
  end.

Ltac split_jail := 
  repeat
    match goal with
    | |- context [_ /\ _] => split
    | |- context [HasType (?t ?v) ?tr] => constructor
    | |- context [_ -> _] => intro
    | |- context [~ HasType _ _] => intro
    | H : ?t1 ?v1 = ?t1 ?v2 |- _ => inversion H
    end.

Ltac destruct_HTContext_jail :=
  match goal with 
  | H : TRValues |- HasType ?r _ => destruct r 
  end.

Ltac rewrite_jail :=
  match goal with
    | H : ?r = ?b |- _ =>
      match goal with
      | H0 : HasType ?r _ |- _ => rewrite H in H0; try inversion H0
      end
    end.

Ltac try_jail_tactics :=
  repeat (
    try destruct_forall_jail; 
    try destruct_HTContext_jail; 
    try split_jail; 
    try false_jail; 
    try rewrite_jail).

Ltac jail :=
  start_jail; destruct_jail; try_jail_tactics.

Ltac why_jail :=
  start_jail; destruct_jail; try constructor; try intro H;
  repeat (
    match goal with
    | H : Bool false = Bool true |- _ => inversion H
    | H : Bool true = Bool false |- _ => inversion H
    | H : bool |- _ => destruct H; auto
    | H : {t >> ?P & ?Q & ?R} |- _ => destruct H as [?H [?H ?H]]
    | H : _ = proj1_sig [?t] |- _ => simpl in H (* how do i say like "in any hypothesis that contains proj1"?*)
    | H : ?P <> ?P |- _ => destruct H; auto
    | H : _ = ?x |-_ => rewrite <- H in *; auto
    | H : _ /\ _ |- _ => destruct H; auto
    | H : _ \/ _ |- _ => destruct H; auto
    | |- context [~ ?P] => intro; auto
    end
  ); auto.

  Ltac specific_jail T :=
  start_jail; 
  match goal with
    | H : TRValues |- _ => destruct H
  end;
  match goal with
    | H : TRValues |- _ => destruct H
  end;
  why_jail; 
  try (inv_trtype_false).

Definition eq_type_dec : forall t1 t2 : TRTypes, {t1 = t2} + {t1 <> t2}.
  decide equality.
Defined.