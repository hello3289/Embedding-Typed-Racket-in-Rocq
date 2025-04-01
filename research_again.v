Require Import String.
Require Import Bool.
Require Import Coq.Program.Tactics.
Require Import JMeq.
#[local] Obligation Tactic := try now program_simpl.
Notation "[ e ]" := (exist _ e _).

Inductive TRValues : Type := 
  | Num (n : nat)
  | Bool (b : bool)
  | Str (s : string)
  | Pair  (a : TRValues) (b : TRValues).

  (* got rid of trall *)
Inductive TRTypes : Type := 
  | trnum : TRTypes
  | trbool : TRTypes
  | trstr : TRTypes
  | trpair : TRTypes -> TRTypes -> TRTypes
  | trunion : TRTypes -> TRTypes -> TRTypes.

  (* Pair and union? *)
Inductive HasType : TRValues -> TRTypes -> Prop :=
  | HtNum   : forall (n : nat), HasType (Num n) trnum
  | HtBool  : forall (b : bool), HasType (Bool b) trbool
  | HtStr   : forall (s : string), HasType (Str s) trstr
  | HtPair : forall (t1 t2 : TRValues) (A B : TRTypes) ,  
                HasType t1 A -> 
                HasType t2 B -> 
                HasType (Pair t1 t2) (trpair A B)
  | HtUnion : forall (t1 : TRValues) (A B : TRTypes),
                (HasType t1 A) \/ (HasType t1 B) ->
                HasType t1 (trunion A B).

Eval compute in HtPair (Num 5) (Bool true) trnum trbool.


(* not exactly sure if this is what we want but ok *)
Definition typeCheck : forall (v : TRValues), {t | HasType v t}.
refine 
(fix F (v : TRValues) : {t | HasType v t} :=
    match v return {t | HasType v t} with
    | Num n => [trnum]
    | Bool b => [trbool]
    | Str s => [trstr]
    | Pair a b => 
        match (F a) with
        | [A] => match (F b) with
               | [B] => [trpair A B]
               end
        end
    end); constructor; auto.
Defined.

Eval simpl in typeCheck (Num 5).
Eval simpl in typeCheck (Pair (Num 9) (Str "hello")).

(* lol idk don't ask*)
Program Definition getType' (v : TRValues) (t : {t | HasType v t}) :=
    match t return {v | HasType v t} with 
    | _ => v
    end.

(* wow this is ugly *)
Eval compute in getType' (Num 5) (typeCheck (Num 5)).

Program Definition getType (v : TRValues) :=
    getType' v (typeCheck v).

Eval compute in getType (Num 5).

(* automating proof with lots of helpers *)
Ltac start_jail :=
  simpl; intros;
  repeat (
    match goal with 
    | H : {_ : TRValues | HasType _ _} |- _ => destruct H as []
    | H : _ = proj1_sig _ |- _ => simpl in H
    end).

Ltac destruct_jail :=
  match goal with
  | H : {_ : TRValues | HasType _ _} |- _ => destruct H as []
  | H : HasType ?r _ |- _ => destruct r
  | |- context [_ /\ _] => split
  end.

Ltac destruct_forall_jail :=
  match goal with
  | H : forall _ : ?t, _ <> _ |- _ => 
        match goal with
        | H0 : t |- _ => destruct (H H0)
        end
  end; auto.

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

(* a slowly dying attempt at doing a "simple" function *)
Program Definition add1' (n : {v | HasType v trnum}) : {v | HasType v trnum} :=
   match n with
   | Num x => getType (Num (S x))
   | _r => False_rec _ _
   end.
   Next Obligation. jail. Defined.        

Eval compute in add1' (getType (Num 5)).
Eval compute in add1' (add1' (getType (Num 5))).
(* Eval compute in add1' (getType (Bool true)). *) (*yay*)

Program Definition is_number {t : TRTypes} (x : {v | HasType v t}) : 
                  {t : TRValues | (HasType t trbool) /\
                                  (t <> Bool false -> (HasType x trnum)) /\
                                  (t = Bool false -> ~(HasType x trnum))} :=
  match x with
  | Num n => Bool true
  | _r => Bool false
  end.
  Next Obligation. jail. Defined. 
  Next Obligation. jail. Defined.


Program Definition ex1 {t : TRTypes} (x : {v | HasType v t}) : {v | HasType v trnum} :=
(* use if here *).
