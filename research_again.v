Require Import String.
Require Import Bool.
Require Import Coq.Program.Tactics.
Require Import JMeq.
#[local] Obligation Tactic := try now program_simpl.
Notation "[ e ]" := (exist _ e _).
(* From theories Require Import jail. *)

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
  | trunion : TRTypes -> TRTypes -> TRTypes.


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


Program Definition getType' (v : TRValues) (t : {t | HasType v t}) :=
    match t return {v | HasType v t} with 
    | _ => v
    end.


Eval compute in getType' (Num 5) (typeCheck (Num 5)).

Program Definition giveType (v : TRValues) :=
    getType' v (typeCheck v).

Eval compute in giveType (Num 5).

(* Maybe i'll make the second type an input? Or maybe it'll make sense when i make the definition that uses union *)
Program Definition TRUnionL {t1 t2 : TRTypes} (x : {v | HasType v t1}) : {v | HasType v (trunion t1 t2)} :=
  x.
  Next Obligation. simpl; intros; destruct x; constructor 5; auto. Defined.

Program Definition TRUnionR {t1 t2 : TRTypes} (x : {v | HasType v t2}) : {v | HasType v (trunion t1 t2)} :=
  x.
  Next Obligation. simpl; intros; destruct x; constructor 6; auto. Defined.

Eval compute in TRUnionR (giveType (Num 5)).

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
   | Num x => giveType (Num (S x))
   | _r => False_rec _ _
   end.
   Next Obligation. jail. Defined.        

Eval compute in add1' (giveType (Num 5)).
Eval compute in add1' (add1' (giveType (Num 5))).
(* Eval compute in add1' (giveType (Bool true)). *) (*yay*)

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

Eval compute in is_number (giveType (Num 5)).

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

(* making up tactics left and right for absolutely no reason at all*)
Ltac why_jail :=
  try (start_jail; destruct_jail; constructor; intro H);
  repeat (
    match goal with
    | H : bool |- _ => destruct H; auto
    | H : {t : TRValues | ?P /\ ?Q /\ ?R} |- _ => destruct H as [?H [?H ?H]]
    | H : _ = proj1_sig [?t] |- _ => simpl in H (* how do i say like "in any hypothesis that contains proj1"?*)
    | H : ?P <> ?P |- _ => destruct H; auto
    | H : _ = ?x |-_ => rewrite <- H in *; auto
    | H : _ /\ _ |- _ => destruct H; auto
    | H : _ \/ _ |- _ => destruct H; auto
    | |- context [~ ?P] => intro; auto
    end
  ); auto.

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
  | H : HasType (Bool ?b) trpair |- _ => inversion H
  | H : HasType (Str ?b) trpair |- _ => inversion H
  | H : HasType (Num ?b ?p) trpair |- _ => inversion H
  end.

Ltac inv_trtype_false T :=
  match T with
  | trnum => inv_trnum
  | trbool => inv_trbool
  | trstr => inv_trstr
  | trpair => inv_trpair
  end.

Ltac specific_jail T :=
  start_jail; 
  match goal with
    | H : TRValues |- _ => destruct H
  end;
  match goal with
    | H : TRValues |- _ => destruct H
  end;
  why_jail; 
  try (inv_trtype_false T).



Program Definition or_TR {P Q : Prop} (x : {t : TRValues | (HasType t trbool) /\
                                    (t <> Bool false -> P) /\
                                    (t = Bool false -> ~P)}) 
                              (y : {t : TRValues | (HasType t trbool) /\
                                    (t <> Bool false -> Q) /\
                                    (t = Bool false -> ~Q)}) : 
                              {t | (HasType t trbool) /\
                                    (t <> Bool false -> P \/ Q) /\
                                    (t = Bool false -> ~(P \/ Q))} :=
  match x, y with 
  | (Bool false),(Bool false) => (Bool false)
  | (Bool _p), (Bool _q) => (Bool true)
  | _n, _m => False_rec _ _
  end. 
  Next Obligation.
  why_jail.
    + apply H3 in H; auto.
    + apply H1 in H; auto.
  Defined. Next Obligation.
    why_jail. 
    exfalso; auto.
  Defined. Next Obligation.
    specific_jail trbool; 
    inversion x0; 
    inversion y0; 
    destruct (H b b0); rewrite H6; rewrite H7; auto.
  Defined.

  (* i guess my next question is how i can go from the prop P \/ Q to
    the type (trunion whateverinp whateverinq)
    but also, x and y could be talking about 2 different varibles so i'm sad *)

Eval compute in 
  or_TR (is_number (giveType (Num 5))) (is_string (giveType (Bool false))).
Eval compute in 
  or_TR (is_number (giveType (Bool false))) (is_string (giveType (Num 5))).

(* and is a little weirder *)
(* same with and *)
Program Definition and_TR {P Q : Prop} {A B : TRTypes} 
    (x : {t : TRValues | (HasType t trbool) /\
                         (t <> Bool false -> P) /\
                         (t = Bool false -> ~P)}) 
    (y : {t : TRValues | (HasType t trbool) /\
                         (t <> Bool false -> Q) /\
                         (t = Bool false -> ~Q)}) : 
    {t | (HasType t trbool) /\
         (t <> Bool false -> P /\ Q) /\
         (t = Bool false -> ~(P /\ Q))} :=
  match x, y with 
  | (Bool true),(Bool true) => (Bool true)
  | (Bool _p), (Bool _q) => (Bool false)
  | _n, _m => False_rec _ _
  end. 
  Next Obligation.
    why_jail; inversion H.
  Defined. Next Obligation.
    why_jail; try (apply H3 in H; destruct H; auto).
    + apply H1 in H; destruct H; auto. 
  Defined. Next Obligation.
    specific_jail trbool; 
    inversion x0; 
    inversion y0; 
    destruct (H b b0); rewrite H6; rewrite H7; auto.
  Defined.

Eval compute in 
  and_TR (is_number (giveType (Num 5))) (is_bool (giveType (Bool false))).
Eval compute in 
  and_TR (is_number (giveType (Bool false))) (is_string (giveType (Str "hello"))).

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

Program Definition strlen (s : {v | HasType v trstr}) : {v | HasType v trnum} :=
  match s with
  | Str s => giveType (Num (length s))
  | _ => False_rec _ _
  end.
  Next Obligation. jail. Defined. (*i'm glad jail works here LOL*)


(* IT LIVES *)
Program Definition ex1 {t : TRTypes} (x : {v | HasType v t}) : {v | HasType v trnum}:=
  if_TR (is_number x) 
        (fun _ => (add1' x)) 
        (fun _ => (giveType (Num 0))).

Print ex1.

Eval compute in ex1 (giveType (Num 5)).
Eval compute in ex1 (giveType (Str "5")).

Program Definition ex2 (x : {v | HasType v (trunion trstr trnum)}) : {v | HasType v trnum} :=
  if_TR (is_number x)
        (fun _ => (add1' x))
        (fun _ => (strlen x)).
  Next Obligation.
  start_jail. destruct_jail.
  - destruct n. constructor.
  - destruct n. inversion h; inversion H1.
  - constructor.
  - destruct n. inversion h; inversion H1.
  Defined.

Eval compute in ex2 (TRUnionL (giveType (Str "hi"))).
Eval compute in ex2 (TRUnionR (giveType (Num 9))).

(* Example 3 uses let and error so i will ignore that *)