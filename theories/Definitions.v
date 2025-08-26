From Stdlib Require Import Strings.String.
From Stdlib Require Import Bool.
From Stdlib Require Import Program.Tactics.
#[local] Obligation Tactic := try now program_simpl.

(************************************************************************)
(**************** OUR VALUE AND TYPE DEFINITIONS AHHHHHH ****************)

Inductive TRValues : Type := 
  | Num (n : nat)
  | Bool (b : bool)
  | Str (s : string)
  | Pair  (a : TRValues) (b : TRValues).


Inductive TRTypes : Type := 
  | trnum : TRTypes
  | trbool : TRTypes
  | trstr : TRTypes
  | trpair : TRTypes -> TRTypes -> TRTypes
  | trunion : TRTypes -> TRTypes -> TRTypes
  | trtop : TRTypes.


Inductive HasType : TRValues -> TRTypes -> Prop :=
  | HtTop :forall (v : TRValues), HasType v trtop
  | HtNum   : forall (n : nat), HasType (Num n) trnum
  | HtBool  : forall (b : bool), HasType (Bool b) trbool
  | HtStr   : forall (s : string), HasType (Str s) trstr
  | HtPair : forall (t1 t2 : TRValues) (A B : TRTypes) ,  
                HasType t1 A -> 
                HasType t2 B -> 
                HasType (Pair t1 t2) (trpair A B)
  | HtUnion_L : forall (t1 : TRValues) (A B : TRTypes),
                (HasType t1 A) -> HasType t1 (trunion A B)
  | HtUnion_R : forall (t1 : TRValues) (A B : TRTypes),
                (HasType t1 B) -> HasType t1 (trunion A B).

(************************************************************************)
(**************************** NOTATIONS AHHH ****************************)

Notation "[ e ]" := (exist _ e _).

Notation "{ t >> T }" := 
    (sig (fun t : TRValues => (HasType t T) /\ 
                               (t <> Bool false -> True) /\ 
                               (t = Bool false -> True)))
    (at level 0, t at level 99, T at next level).
    
Notation "{ t >> T & P & Q }" := 
    (sig (fun t : TRValues => (HasType t T) /\ 
                              (t <> Bool false -> P) /\ 
                              (t = Bool false -> Q)))
    (at level 0, t at level 99, T at next level).

(************************************************************************)
(*************************** GIVE THOSE TYPES ***************************)

Definition typeCheck : forall (v : TRValues), {t : TRTypes | HasType v t}.
refine 
(fix F (v : TRValues) : {t : TRTypes | HasType v t} :=
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

Program Definition getType' (v : TRValues) (t : {t | HasType v t}) :=
    match t return {v >> t} with 
    | _ => v
    end.

Program Definition giveType (v : TRValues) :=
    getType' v (typeCheck v).

Program Definition TRUnionL {t1 t2 : TRTypes} (x : {v >> t1}) : {v >> (trunion t1 t2)} :=
  x.
  Next Obligation. 
    simpl. 
    intros. 
    destruct x; simpl. 
    destruct a as [?H [?H ?H]].
    split; try apply HtUnion_L; auto. Defined.

Program Definition TRUnionR {t1 t2 : TRTypes} (x : {v >> t2}) : {v >> (trunion t1 t2)} :=
  x.
  Next Obligation. 
    simpl. 
    intros. 
    destruct x; simpl. 
    destruct a as [?H [?H ?H]].
    split; try apply HtUnion_R; auto. Defined.

Definition get_true_prop {T} {P Q : Prop} (v : {v : TRValues | (HasType v T) /\ (v <> Bool false -> P) /\ (v = Bool false -> Q)}) : Prop.
Proof.
  exact P.
Defined.

Definition get_false_prop {T} {P Q : Prop} (v : {v : TRValues | (HasType v T) /\ (v <> Bool false -> P) /\ (v = Bool false -> Q)}) : Prop.
Proof. 
  exact Q.
Defined.

Definition get_type {T} {P Q : Prop} (v : {v : TRValues | (HasType v T) /\ (v <> Bool false -> P) /\ (v = Bool false -> Q)}) : TRTypes.
Proof. 
    exact T.
Defined.

(************************************************************************)
(*********************** TWO MORE NOTATIONS AHHH ************************)

Program Definition top_pair { S T : TRTypes } (v : { t >> (trpair S T) }) : { t >> (trpair trtop trtop) } :=
  v.
  Next Obligation.
  intros; simpl.
  repeat split. destruct v. destruct a. destruct a.
  destruct x; try inversion h.
  constructor; constructor.
  Defined. 

Notation " <[ e ]> " :=
    (giveType e) (e at level 0).
