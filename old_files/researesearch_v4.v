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

Eval compute in HtPair (Num 5) (Bool true) trnum trbool.

Notation "{ x : A | P }" := 
    (sig A (fun x => P)) (x at level 99).
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

Eval simpl in typeCheck (Num 5).
Eval simpl in typeCheck (Pair (Num 9) (Str "hello")).

Program Definition getType' (v : TRValues) (t : {t | HasType v t}) :=
    match t return {v >> t} with 
    | _ => v
    end.

Eval compute in getType' (Num 5) (typeCheck (Num 5)).
Program Definition giveType (v : TRValues) :=
    getType' v (typeCheck v).

Eval compute in giveType (Num 5).


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

Eval compute in TRUnionR (giveType (Num 5)).

(* automating proof with lots of helpers *)

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
  | H : HasType (Bool ?b) (trpair ?a ?c) |- _ => inversion H
  | H : HasType (Str ?b) (trpair ?a ?c) |- _ => inversion H
  | H : HasType (Num ?b) (trpair ?a ?c) |- _ => inversion H
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

(* a slowly dying attempt at doing a "simple" function *)
Program Definition add1 (n : {t >> trnum}) : {t >> trnum} :=
   match n with
   | Num x => giveType (Num (S x))
   | _r => False_rec _ _
   end.
   Next Obligation.
   jail. Defined.        

Eval compute in add1 (giveType (Num 5)).
Eval compute in add1 (add1 (giveType (Num 5))).

Program Definition add (n : {v >> trnum}) (m : {v >> trnum}) : {v >> trnum} :=
  match n, m with
  | Num x, Num y => giveType (Num (x + y))
  | _r, _q => False_rec _ _
  end.
  Next Obligation. 
  start_jail. destruct (n0 n n4); auto.
  Defined.
  
Eval compute in add (giveType (Num 3)) (giveType (Num 7)).

Program Definition is_number {t : TRTypes} (x : {v >> t}) : 
                  {t >> trbool & (HasType x trnum) & ~(HasType x trnum)} :=
  match x with
  | Num n => Bool true
  | _r => Bool false
  end.
  Next Obligation. 
  start_jail; try constructor; intros; inversion H. 
  Defined. 
  Next Obligation.
  start_jail; 
  intros; 
  try rewrite Heq_x; 
  try constructor; 
  try destruct_forall_jail; 
  destruct H; auto; intro; (*intros doesn't work but intro does?????*) 
  inv_trtype_false.
  Defined.

Eval compute in is_number (giveType (Num 5)).

Program Definition is_string {t : TRTypes} (x : {v >> t}) : 
                  {t >> trbool & (HasType x trstr) & ~(HasType x trstr)} :=
  match x with
  | Str s => Bool true
  | _r => Bool false
  end.
  Next Obligation. 
  start_jail; try constructor; intros; inversion H.
  Defined. 
  Next Obligation. 
  start_jail; 
  intros; 
  try rewrite Heq_x; 
  try constructor; 
  try destruct_forall_jail; 
  destruct H; auto; intro; (*intros doesn't work but intro does?????*) 
  inv_trtype_false.
  Defined.

Program Definition is_bool {t : TRTypes} (x : {v >> t}) : 
                  {t >> trbool & (HasType x trbool) & ~(HasType x trbool)} :=
  match x with
  | Bool b => Bool true
  | _r => Bool false
  end.
  Next Obligation. 
  start_jail; try constructor; intros; inversion H.
  Defined. 
  Next Obligation. 
  start_jail; 
  intros; 
  try rewrite Heq_x; 
  try constructor; 
  try destruct_forall_jail; 
  destruct H; auto; intro; (*intros doesn't work but intro does?????*) 
  inv_trtype_false.
  Defined.

(* making up tactics left and right for absolutely no reason at all*)
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

Eval compute in eq_type_dec trnum trbool.

Check (typeCheck (Num 5)).

Program Definition is_pair {t1 : TRTypes} (x : {v >> t1}) : 
  {t >> trbool & (HasType x (trpair trtop trtop)) & ~(HasType x (trpair trtop trtop))} :=
  match x with
  | Pair a b => Bool true
  | _r => Bool false
  end.

Next Obligation.
intros.
simpl.
repeat split; intros; try constructor; try constructor.
inversion H.
Defined.
Next Obligation.
intros; simpl; repeat split; intros; try constructor; try destruct H; auto.
destruct _r; subst; intro; inversion H.
subst.
specialize n with _r1 _r2.
destruct n. auto.
Defined.


Program Definition or_TR {P Q : Prop} (x : {t >> trbool & P & ~P}) 
                                      (y : {t >> trbool & Q & ~Q}) : 
                              {t >> trbool & (P \/ Q) & ~(P \/ Q)} :=
  match x, y with 
  | (Bool false),(Bool false) => (Bool false)
  | (Bool _p), (Bool _q) => (Bool true)
  | _n, _m => False_rec _ _
  end. 
  Next Obligation.
  why_jail. 
  - apply x2 in Heq_x. auto.
  - apply y2 in Heq_y. auto.
  Defined.
  Next Obligation.
  start_jail; destruct_jail. try constructor.
  - intros. destruct b0, b; try (apply x1 in H ; left; auto). 
    + apply y1 in H ; right; auto.
    + destruct n. rewrite Heq_x; rewrite Heq_y; auto.
  - intros. destruct b0, b; intro; destruct H0; inversion H.
  Defined.
  Next Obligation.
  why_jail; eapply H; eauto.
  Defined.

Program Definition and_TR {P Q : Prop} 
    (x : {t >> trbool & P & ~P}) 
    (y : {t >> trbool & Q & ~Q}) : 
    {t >> trbool & (P /\ Q) & ~(P /\ Q)} :=
  match x, y with 
  | (Bool true),(Bool true) => (Bool true)
  | (Bool _p), (Bool _q) => (Bool false)
  | _n, _m => False_rec _ _
  end. 
  Next Obligation.
    why_jail; inversion H.
  Defined. Next Obligation.
    why_jail; try (apply x2 in H; destruct H; auto).
    + apply y2 in H; destruct H; auto.
  Defined. Next Obligation.
    why_jail;
    eapply H; eauto.
  Defined.

Eval compute in 
  and_TR (is_number (giveType (Num 5))) (is_bool (giveType (Bool false))).
Eval compute in 
  and_TR (is_number (giveType (Bool false))) (is_string (giveType (Str "hello"))).

Definition if_TR {A : TRTypes} {P Q : Prop} 
                          (x : {t >> trbool & P & Q})                        
                          (y : P -> {t >> A}) (* P -> HasType ...*)
                          (z : Q -> {t >> A}) : (* Q -> HasType ... *)
                          {t >> A}.
Proof. 
  destruct x.
  destruct a as [H0 [H1 H2]].
  destruct x; try (apply y; apply H1; discriminate).
  - destruct b.
    * apply y. apply H1. discriminate.
    * apply z. apply H2. auto.
  Defined.

Program Definition strlen (s : {v >> trstr}) : {v >> trnum} :=
  match s with
  | Str s => giveType (Num (length s))
  | _ => False_rec _ _
  end.
  Next Obligation. jail. Defined. (*i'm glad jail works here LOL*)


(* IT LIVES *)
(* Example 1 *)
Program Definition ex1 {t : TRTypes} (x : {v >> t}) : {v >> trnum}:=
  if_TR (is_number x) 
        (fun _ => (add1 x)) 
        (fun _ => (giveType (Num 0))).

Print ex1.

Eval compute in ex1 (giveType (Num 5)).
Eval compute in ex1 (giveType (Str "5")).

(* Example 2 *)
Program Definition ex2 (x : {v >> (trunion trstr trnum)}) : {v >> trnum} :=
  if_TR (is_number x)
        (fun _ => (add1 x))
        (fun _ => (strlen x)).
  Next Obligation.
  start_jail; simpl; try constructor; inversion x0; try inv_trtype_false.
  - destruct n; auto. 
  Defined.

Eval compute in ex2 (TRUnionL (giveType (Str "hi"))).
Eval compute in ex2 (TRUnionR (giveType (Num 9))).

(* Example 3 uses let and error so i will ignore that *)

(* Example 4 *)
Program Definition ex4 {t : TRTypes} (x : {v >> t}) : {v >> trnum} :=
  if_TR (or_TR (is_number x) (is_string x))
        (fun _ => (ex2 x))
        (fun _ => (giveType (Num 0))).
  Next Obligation.
  start_jail; simpl; simpl in o. 
  - apply HtUnion_R. constructor.
  - destruct o; inv_trtype_false.
  - apply HtUnion_L. constructor.
  - destruct o; inv_trtype_false.
  Defined.
  
Eval compute in ex4 (giveType (Num 9)).
Eval compute in ex4 (giveType (Str "hi")).
Eval compute in ex4 (giveType (Bool true)).

(* example 6 is not correct so i'll skip it *)

(* Example 5 *)
Program Definition ex5 {t r : TRTypes} (x : {v >> t}) (y : {w >> r}) : {v >> trnum} :=
  if_TR
        (* HOW CAN I ONLY EXPLICITLY STATE ONE IMPLICIT PARAMETER AHHHH *)
        (@and_TR (HasType x trnum) 
                 (HasType y trstr) 
                 (is_number x) (is_string y))
        (fun _ => add x (strlen y)) (* i need addition *)
        (fun _ => giveType (Num 0)).

Eval compute in ex5 (giveType (Num 5)) (giveType (Str "hi")).
Eval compute in ex5 (giveType (Num 5)) (giveType (Num 8)).
Eval compute in ex5 (giveType (Str "hello")) (giveType (Num 10)).
Eval compute in ex5 (giveType (Bool true)) (giveType (Bool false)).

(* Example 7 *)

Lemma subsume : forall  {A} (P P' Q Q' : Prop),
  (P -> P') -> (Q -> Q') ->
  {t >> (A) & P & Q} -> {t >> (A) & P'  & Q'}.
Proof.
  intros.
  destruct H1 as [x [H2 [H3 H4]]]. 
  econstructor.
  split. eauto.
  split. eauto.
  eauto.  
Defined.

Lemma subsume' : forall  A (P' P'' Q' Q'' : Prop), {t >> (A) & P'' & Q''} -> {t >> (A) & P' \/ P'' & Q' \/ Q''}.
Proof.
  intros. apply subsume with P'' Q''; auto.
Defined.

Lemma subsume_again : forall  {A : TRTypes} {P P' Q Q' : Prop},
  (P -> P') -> (Q -> Q') ->
  {t >> (A) & P & Q} -> {t >> (A) & P'  & Q'}.
Proof.
  intros.
  destruct H1 as [x [H2 [H3 H4]]]. 
  econstructor.
  split. eauto.
  split. eauto.
  eauto.  
Defined.

Definition if_TR' {A : TRTypes} {P P' Q Q' : Prop} 
                          (x : {t >> trbool & P & Q})                        
                          (y : P -> {t >> A & P' & Q'})
                          (z : Q -> {t >> A & P' & Q'}) : 
                          {t >> A & P' & Q'}.
Proof. 
  destruct x.
  destruct a as [H0 [H1 H2]].
  destruct x;
   try (apply subsume with P' Q'; auto; apply y; apply H1; discriminate). 
  - destruct b. 
   + apply subsume with P' Q'; auto; apply y;apply H1; discriminate.
   + apply subsume with P' Q'; auto.
Defined.

Definition if_TR_again {A : TRTypes} {P P' Q Q' : Prop} 
                          (x : {t >> trbool & P & Q})                        
                          (y : P -> {t >> A & P' & Q'})
                          (z : Q -> {t >> A & P' & Q'}) : 
                          {t >> A & P' & Q'}.
Proof. 
  destruct x.
  destruct a as [H0 [H1 H2]].
  destruct x;
   try (eapply subsume_again; eauto; apply y; apply H1; discriminate). 
  - destruct b. 
   + eapply subsume_again ; eauto; apply y;apply H1; discriminate.
   + eapply subsume_again; eauto.
Defined.

(* is there a way to make optional parameters for notations?? *)
Notation " 'ifTR' A B C " := 
  (if_TR' A (fun _ => B) (fun _ => C)) (at level 0, A at next level, B at next level, C at next level). 

Notation " 'ifTR_ah' < P P' Q Q' > A B C " := 
  (@if_TR' _ P P' Q Q' A (fun _ => B) (fun _ => C)) (at level 2, P at next level, P' at next level,
  Q at next level, Q' at next level, A at next level, B at next level, C at next level). 

Program Definition ex7 {t r : TRTypes} (x : {v >> t}) (y : {w >> r}) : {v >> trnum} :=
  (ifTR_ah < (HasType x trnum /\ HasType y trstr) True (~(HasType x trnum /\ HasType y trstr)) True >
    (ifTR_ah < (HasType x trnum)  (HasType x trnum /\ HasType y trstr) (~(HasType x trnum)) (~(HasType x trnum /\ HasType y trstr)) >
      (is_number x)
      (is_string y)
      (Bool false))
    (add x (strlen y))
    (giveType (Num 0))).
Next Obligation.
intros t r x y. simpl. split. 
- destruct y. unfold is_string. simpl. destruct x0. all: constructor.
- split; intros; try split; auto.  destruct y. simpl. destruct x0.
   + unfold is_string;simpl.  all: simpl in H. destruct H. auto.
   + unfold is_string;simpl.  all: simpl in H. destruct H. auto.
   + apply HtStr.
   + unfold is_string;simpl.  all: simpl in H. destruct H. auto.
   + intro. destruct H0. destruct y. simpl in H; destruct x0; unfold is_string;simpl in H.  all: simpl in H1. all: inversion H1. inversion H.
Defined.
Next Obligation.
intros t r x y. simpl. split; try constructor; intros.
  - destruct H; auto.
  - intro. destruct H0. destruct n. auto.
Defined.

Eval compute in ex7 (giveType (Num 6)) (giveType (Str "hello")).

(* Example 8 *)
(* define strnum to then pass to example 2*)

Program Definition ex8 {t : TRTypes} (x : {v >> t}) :=
  (or_TR (is_string x) (is_number x)).

Program Definition ex8_test {t : TRTypes} (x : {v >> t}) : {v >> trnum} :=
  (ifTR (ex8 x) (ex2 x) (giveType (Num 0))).
Next Obligation.
intros. simpl. split.
  - destruct o. apply HtUnion_L; auto. apply HtUnion_R; auto.
  - split; destruct x; auto.
Defined.

Eval compute in (ex8 (giveType (Num 6))).
Eval compute in (ex8_test (giveType (Num 6))).
Eval compute in (ex8 (giveType (Str "potatoes"))).
Eval compute in (ex8_test (giveType (Str "potatoes"))).
Eval compute in (ex8 (giveType (Bool true))).
Eval compute in (ex8_test (giveType (Bool true))).

(* Example 9 *)

Program Definition ex9 {t : TRTypes} (x : {v >> t}) : {v >> trnum} :=
  (ifTR (let p := (is_number x) in 
          (ifTR_ah < (HasType x trnum) 
                     (HasType x trnum \/ HasType x trstr) 
                     (~(HasType x trnum)) 
                     (~(HasType x trnum \/ HasType x trstr)) > 
                    p 
                    p 
                    (is_string x)))
         (ex2 x) 
         (giveType (Num 0))).
Next Obligation.
  start_jail; try constructor; intros; intro; simpl in H; 
  destruct H0; 
  try inversion H; try inversion h; try inversion H0.
Defined.

Next Obligation.
(* this case is ~(HasType x trnum) -> (fun _ => t >> trbool & P' & Q') *)
(* turns out my tactics where creating impossible goals *)
  intros; simpl. destruct_jail.
  - destruct x; simpl. destruct x; try constructor.
  - intro. right. destruct x; destruct x; try constructor; simpl in H; destruct H; auto.
  - intro. intro. destruct H0.
    + destruct x; destruct x; try inversion H0. destruct n; auto.
    + destruct x; destruct x; try inversion H0. simpl in H. inversion H.
Defined.

Next Obligation.
  start_jail.
  - apply HtUnion_R; constructor.
  - destruct o; inversion H.
  - apply HtUnion_L; constructor.
  - destruct o; inversion H.
Defined.

Eval compute in (ex9 (giveType (Num 2))).

(* Example 10 *)

Program Definition car {A B : TRTypes} (l : {v >> (trpair A B)}) : {t >> A} :=
  match l with
  | Pair a b => a
  | _r => False_rec _ _
  end.
  Next Obligation.
  start_jail; try inv_trtype_false. inversion Heq_l. inversion l0; auto.
  Defined.
  Next Obligation.
  start_jail. subst. specialize n with l3 l4. destruct n; auto.
  Defined.

Program Definition cdr {A B : TRTypes} (l : {v >> (trpair A B)}) : {t >> B} :=
  match l with
  | Pair a b => b
  | _r => False_rec _ _
  end.
  Next Obligation.
  start_jail; try inv_trtype_false. inversion Heq_l. inversion l0; auto.
  Defined.
  Next Obligation.
  start_jail. subst. specialize n with l3 l4. destruct n; auto.
  Defined.

Eval compute in (car (giveType (Pair (Num 5) (Str "hi")))).
  
Program Definition ex10 {A B : TRTypes} (p : {v >> (trpair A B)}) : {t >> trnum} :=
  ifTR (is_number (car p)) (add1 (car p)) (giveType (Num 7)).
(* Wowowowow no obligations needed *)

Eval compute in (ex10 (giveType (Pair (Num 5) (Str "bye")))).
Eval compute in (ex10 (giveType (Pair (Bool false) (Num 10)))).
(* Eval compute in (ex10 (giveType (Num 1))). correct error *)

(* Example 11 *)
Program Definition g (p : {v >> trpair trnum trnum}) : {t >> trnum} :=
  (add (car p) (cdr p)).
(* damn "g has type-checked" obligations weren't even generated this time *)

Eval compute in (g (giveType (Pair (Num 4) (Num 5)))).

(* instead of returning 'no, i'll return 0 *)
Program Definition ex11 {A B : TRTypes} (p : {v >> trpair A B}) : {t >> trnum} :=
  ifTR (and_TR (is_number (car p)) (is_number (cdr p))) (g p) (giveType (Num 0)).
Next Obligation.
  start_jail; destruct a; constructor; auto.
  Defined.

Eval compute in (ex11 (giveType (Pair (Num 4) (Num 12)))).
Eval compute in (ex11 (giveType (Pair (Num 3) (Bool false)))).

(* What is g??? *)

(* Example 12 *)
Program Definition ex12 {A B : TRTypes} (p : {v >> trpair A B}) : 
  {t >> trbool & (HasType p (trpair trnum B)) & (~ (HasType p (trpair trnum B)))} :=
  (is_number (car p)).
Next Obligation.
  start_jail; try intros; inversion p0; unfold car in *; simpl in *.
  - destruct p3; simpl; constructor.
  - destruct p3; simpl in H; constructor; auto; try constructor; try destruct H; auto.
  - intro. destruct p3; simpl in H; inversion H6; try inv_trtype_false. discriminate.
Defined.

Program Definition ex12_again {A B : TRTypes} (p : {v >> trpair A B}) : 
{t >> trbool & (HasType (car p) trnum) & (~ (HasType (car p) trnum))} :=
  (is_number (car p)).

Eval compute in (ex12 (giveType (Pair (Num 4) (Bool true)))).
Eval compute in (ex12 (giveType (Pair (Str "hi") (Num 1)))).

(* Example 13 is cond *)

(* i guess i'll just make it a set length for this cond notation *)


(* Example 14 puts it all together *)










