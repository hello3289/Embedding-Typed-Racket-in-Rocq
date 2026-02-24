Require Import Strings.String.
Require Import Bool.
Require Import Program.Tactics.
#[local] Obligation Tactic := try now program_simpl.

(************************************************************************)
(**************** OUR VALUE AND TYPE DEFINITIONS AHHHHHH ****************)

Inductive Void_ := void.

Inductive TRList : Type :=
  | empty
  | some (a : nat) (b : TRList). (* lol *)

Inductive nat_vec : nat -> Type :=
  | nil : nat_vec O
  | cons : forall {n : nat} , nat -> (nat_vec n) -> nat_vec (S n).

Check nat_vec_ind.

Inductive TRValues : Type := 
  | Num (n : nat)
  | Bool (b : bool)
  | Str (s : string)
  | Pair  (a : TRValues) (b : TRValues)
  | List (l : TRList)
  | Vec : forall (n : nat),  (nat_vec n) -> TRValues
  | Void (v : Void_).

Check (cons 5 (cons 7 nil)).
Definition len {n} (v : nat_vec n): nat := n.
Eval compute in (len (cons 5 (cons 7 nil))).
Check (some 5 (some 7 empty)).


Inductive TRTypes : Type := 
  | trnum : TRTypes
  | trbool : TRTypes
  | trstr : TRTypes
  | trvoid : TRTypes
  | trpair : TRTypes -> TRTypes -> TRTypes
  | trvec : nat -> TRTypes
  | trlist : TRTypes
  | trunion : TRTypes -> TRTypes -> TRTypes
  | trtop : TRTypes.


Inductive HasType : TRValues -> TRTypes -> Prop :=
  | HtTop     : forall (v : TRValues), HasType v trtop
  | HtNum     : forall (n : nat), HasType (Num n) trnum
  | HtBool    : forall (b : bool), HasType (Bool b) trbool
  | HtStr     : forall (s : string), HasType (Str s) trstr
  | HtVoid    : forall (v : Void_), HasType (Void v) trvoid
  | HtPair    : forall (t1 t2 : TRValues) (A B : TRTypes) ,  
                  HasType t1 A -> 
                  HasType t2 B -> 
                  HasType (Pair t1 t2) (trpair A B)
  | HtList    : forall (l : TRList), HasType (List l) trlist
  | HtVec     : forall (n : nat) (nv : nat_vec n), HasType (Vec n nv) (trvec n)
  | HtUnion_L : forall (t1 : TRValues) (A B : TRTypes),
                (HasType t1 A) -> HasType t1 (trunion A B)
  | HtUnion_R : forall (t1 : TRValues) (A B : TRTypes),
                (HasType t1 B) -> HasType t1 (trunion A B).

Check HasType_ind.

(************************************************************************)
(**************************** NOTATIONS AHHH ****************************)

Notation "[ e ]" := (exist _ e _).

Notation "{ t >> T & P & Q }" := 
    (sig (fun t : TRValues => (HasType t T) /\ 
                              ((HasType t T) /\ t <> Bool false -> P) /\ 
                               ((HasType t T) /\ t = Bool false -> Q)))
    (at level 0, t at level 99, T at next level, P at next level, Q at next level).

Notation "{ t >> T & P  }" := 
    { t >> T & P & (~P)}
    (at level 0, t at level 99, T at next level, P at next level).

Notation "{ >> T & P  }" := 
    { t >> T & P & (~P)}
    (at level 0, T at next level, P at next level).

Notation "{ >> T & P & Q  }" := 
    { t >> T & P & Q }
    (at level 0, T at next level, P at next level).

Notation "{ T }" := 
    { t >> T & True & True }
    (at level 0, T at level 99).

Notation " 'U' A B " :=
  (trunion A B) (at level 0, A at next level, B at next level). 
  

(************************************************************************)
(*************************** GIVE THOSE TYPES ***************************)

Definition typeCheck : forall (v : TRValues), {t : TRTypes | HasType v t}.
refine 
(fix F (v : TRValues) : {t : TRTypes | HasType v t} :=
    match v return {t | HasType v t} with
    | Void v => [trvoid]
    | Num n => [trnum]
    | Bool b => [trbool]
    | Str s => [trstr]
    | Vec n v => [trvec n]
    | List l => [trlist]
    | Pair a b => 
        match (F a) with
        | [A] => match (F b) with
               | [B] => [trpair A B]
               end
        end
    end); constructor; auto.
Defined.

Program Definition getType' (v : TRValues) (t : {t | HasType v t}) :=
    match t return { t } with 
    | _ => v
    end.

Program Definition giveType (v : TRValues) :=
    getType' v (typeCheck v).

Eval compute in giveType (Vec _ (cons 5 (cons 8 nil))).


Program Definition TRUnionL {t1 t2 : TRTypes} (x : { t1 }) : { (U t1 t2) } :=
  x.
  Next Obligation. 
    simpl. 
    intros. 
    destruct x; simpl. 
    destruct a as [?a ?a];
    split; try apply HtUnion_L; auto. Defined.

Program Definition TRUnionR {t1 t2 : TRTypes} (x : { t2 }) : { (U t1 t2) } :=
  x.
  Next Obligation. 
    simpl. 
    intros. 
    destruct x; simpl. 
    destruct a as [?a ?a];
    split; try apply HtUnion_R; auto. Defined.

    
Definition get_true_prop {T : TRTypes} {P Q : Prop} (v : { t >> T & P & Q }) : Prop.
Proof.
  exact P.
Defined.

Definition get_false_prop {T} {P Q : Prop} (v : { t >> T & P & Q }) : Prop.
Proof. 
  exact Q.
Defined.

Definition get_type {T} {P Q : Prop} (v : { t >> T & P & Q }) : TRTypes.
Proof. 
    exact T.
Defined.

(************************************************************************)
(*********************** TWO MORE NOTATIONS AHHH ************************)

Program Definition top_pair { S T : TRTypes } (v : { (trpair S T) }) : { (trpair trtop trtop) } :=
  v.
  Next Obligation.
  intros; simpl.
  repeat split. destruct v. destruct a. destruct a.
  destruct x; try inversion h.
  constructor; constructor.
  Defined. 

Program Definition union_same {t : TRTypes} (x : { (U t t) }) : { t } :=
  x.
  Next Obligation.
  intros; simpl in *; repeat split. destruct x as [?x ?x]. destruct x0 as [?x ?x].
  inversion x0; auto.
  Defined.

Notation " <[ e ]> " :=
    (giveType e) (e at level 0).
Notation "( a , b )" := (Pair a b).
 

(************************************************************************)
(*********************** COERCIONS **************************************)


Coercion Num : nat >-> TRValues.
Coercion Str : string >-> TRValues.
Coercion Bool : bool >-> TRValues.
Coercion Vec : nat_vec >-> TRValues.
Coercion Void : Void_ >-> TRValues.
Coercion giveTypeWat (p : TRValues) := giveType p.
Set Warnings "-uniform-inheritance".
Set Warnings "-ambiguous-paths".
Coercion simplifyUnion {t : TRTypes} (p : {(trunion t t)}) := union_same p.
Set Warnings "uniform-inheritance".
Set Warnings "ambiguous-paths".