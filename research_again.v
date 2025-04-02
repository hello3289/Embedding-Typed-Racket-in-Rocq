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

  (* I changed HtUnion so check! *)
Inductive HasType : TRValues -> TRTypes -> Prop :=
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

(* Maybe i'll make the second type an input? Or maybe it'll make sense when i make the definition that uses union *)
Program Definition TRUnionL {t1 t2 : TRTypes} (x : {v | HasType v t1}) : {v | HasType v (trunion t1 t2)} :=
  x.
  Next Obligation. simpl; intros; destruct x; constructor 5; auto. Defined.

Program Definition TRUnionR {t1 t2 : TRTypes} (x : {v | HasType v t2}) : {v | HasType v (trunion t1 t2)} :=
  x.
  Next Obligation. simpl; intros; destruct x; constructor 6; auto. Defined.

Eval compute in TRUnionR (getType (Num 5)).

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

Eval compute in is_number (getType (Num 5)).

Program Definition is_string {t : TRTypes} (x : {v | HasType v t}) : 
                  {t : TRValues | (HasType t trbool) /\
                                  (t <> Bool false -> (HasType x trstr)) /\
                                  (t = Bool false -> ~(HasType x trstr))} :=
  match x with
  | Str s => Bool true
  | _r => Bool false
  end.
  Next Obligation. jail. Defined. 
  Next Obligation. jail. Defined.

Program Definition is_bool {t : TRTypes} (x : {v | HasType v t}) : 
                  {t : TRValues | (HasType t trbool) /\
                                  (t <> Bool false -> (HasType x trbool)) /\
                                  (t = Bool false -> ~(HasType x trbool))} :=
  match x with
  | Bool b => Bool true
  | _r => Bool false
  end.
  Next Obligation. jail. Defined. 
  Next Obligation. jail. Defined.

(* So this is a littly janky as there's nothing saying that a : A and b : B
Program Definition is_pair {t A B : TRTypes} (x : {v | HasType v t}) : 
                  {t : TRValues | (HasType t trbool) /\
                                  (t <> Bool false -> (HasType x (trpair A B))) /\
                                  (t = Bool false -> ~(HasType x (trpair A B)))} :=
  match x with
  | Pair a b => Bool true
  | _r => Bool false
  end.
  Next Obligation. 
*)

(* HERE IS WHERE EVERYTHING STARTS FALLING APART *)

(* ok for now i'll dumb it down to only accept bool, though this will probably have to be more complex aka union *)
(* or maybe make the more complicated one a separate function *)
Program Definition or_TR {A B : TRTypes} (x : {v | HasType v A}) (y : {v | HasType v B}) : {v | HasType v trbool} :=
    match x with
    | Bool false => match y with 
                    | Bool false => Bool false
                    | _ => Bool true
                    end
    | _ => Bool true
end.
Next Obligation. start_jail; constructor. Defined.
Next Obligation. start_jail; constructor. Defined.
Next Obligation. start_jail; constructor. Defined.

Eval compute in or_TR (getType (Num 5)) (getType (Bool false)).
Eval compute in or_TR (getType (Bool false)) (getType (Bool false)).

(* same with and *)
Program Definition and_TR {A B : TRTypes} (x : {v | HasType v A}) (y : {v | HasType v B}) : {v | HasType v trbool} :=
    match x with
    | Bool false => Bool false
    | _ => match y with 
            | Bool false => Bool false
            | _ => Bool true
            end
end.
Next Obligation. start_jail; constructor. Defined.
Next Obligation. start_jail; constructor. Defined.
Next Obligation. start_jail; constructor. Defined.

Eval compute in and_TR (getType (Num 5)) (getType (Bool false)).
Eval compute in and_TR (getType (Bool false)) (getType (Str "hello")).
Eval compute in or_TR (getType (Bool false)) (getType (Bool false)).
Eval compute in and_TR (getType (Num 5)) (getType (Str "hello")).


(* QUESTIONNNNN : bc if i want to do add1', it has to return P->HasType.. as the type, but if i have something
like add1_huh, then it can't unify HasType n trnum -> HasType n trnum with HasType (Num 5) trnum -> yeh*)
(* I think my main question is, shouldn't if be the one generating P/Q -> HasType..., instead of it
    being an input *)
(* yeah there's a big problem with if ahhhhhhhhh me sad *)

Lemma wtf : forall n s, ~ HasType (Num n) trbool /\ ~ HasType (Str s) trbool.
Proof.
  intros.
  split;
  intro;
  inversion H.
  Qed.

Lemma wtf2 : forall n s, ~ HasType (Pair s n) trbool .
Proof.
  intros.
  intro;
  inversion H.
  Qed.

Definition if_TR {A : TRTypes} {P : Prop} 
                          (x : {t : TRValues | (HasType t trbool) /\
                                  (t <> Bool false -> P) /\
                                  (t = Bool false -> ~P)})                        
                          (y : P -> {t : TRValues | (HasType t A)}) (* P -> HasType ...*)
                          (z : ~P -> {t : TRValues | (HasType t A)}) : (* Q -> HasType ... *)
                          {t : TRValues | (HasType t A)}.
Proof.
  destruct x.
  destruct a as [H0 [H1 H2]].
  destruct x; try (apply y; apply H1; discriminate).
  - destruct b.
    * apply y. apply H1. discriminate.
    * apply z. apply H2. auto.
  Defined.
(*
        
    match x with 
    | (Bool false) => z
    | _ => y
end.
*)
(* this is not exactly correct either since it needs to know what the if input is*)
Program Definition add1_huh (x : {v | HasType v trnum}) : {v | (HasType v trnum)} :=
  add1' x.

Eval compute in add1_huh (getType (Num 5)). 


(* ok so i can't do anything like (add1' Str "hi") which almost seems like a problem 
Eval compute in if_TR (is_number (getType (Str "hello"))) (add1_huh (getType (Num 5))) (getType (Num 0)).
*)

(* TOMORROW : if, ex1, ok there might be a big problem with the union type bc how do you generate something of the union type
maybe another function*)
(* i was thinking maybe i should write an interpreter? so that i can "manually" pass the correct typed value to add1 and such?*)

(* Ok so the problem i noticed earlier is definitely a problem here, doing (add1' x) is not working *)
Program Definition ex1 {t : TRTypes} (x : {v | HasType v t}) : {v | HasType v trnum}:=
  if_TR (is_number x) 
        (fun _ => (add1' x)) 
        (fun _ => (getType (Num 0))).

Print ex1.

Eval compute in ex1 (getType (Num 5)).
Eval compute in ex1 (getType (Str "5")).
