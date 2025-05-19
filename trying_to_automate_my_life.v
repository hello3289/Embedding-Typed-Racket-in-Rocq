Require Import String.
Require Import Bool.
Require Import Coq.Program.Tactics.
Require Import JMeq.
#[local] Obligation Tactic := try now program_simpl.

Notation "[ e ]" := (exist _ e _).

Inductive TRValues : nat -> Type := 
  | Num : forall k, nat -> TRValues k
  | Bool : forall k, bool -> TRValues k
  | Str : forall k, string -> TRValues k
  | Fun : forall n, ((TRValues n) -> TRValues n) -> TRValues (S n)
  | Pair : forall n, TRValues n -> TRValues n -> TRValues n.


Inductive TRTypes : Type := 
  | trnum : TRTypes
  | trbool : TRTypes
  | trstr : TRTypes
  | trpair : TRTypes -> TRTypes -> TRTypes
  | trunion : TRTypes -> TRTypes -> TRTypes
  | trtop : TRTypes.


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
                (HasType t1 B) -> HasType t1 (trunion A B)
  | HtTop :forall (v : TRValues), HasType v trtop.

Eval compute in HtPair (Num 5) (Bool true) trnum trbool.

(* so this notation is a little dumb but i'm too smooth brain to figure out the notation levels
to get : to work *)
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


(* automating proof with lots of helpers *)

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
(* a slowly dying attempt at doing a "simple" function *)


Ltac start_jail :=
   intros; subst;
   repeat 
   (match goal with
   | [ H : {v >> (?t)} |- _ ] => destruct H as [H [?H [?H ?H]]]
   | [ H : {v >> (?t) & ?P & ?Q} |- _ ] => destruct H as [H [?H [?H ?H]]]
   | [ H := context[proj1_sig _] |- _ ] => simpl in H
   | [ H : context[proj1_sig _] |- _ ] => simpl in H
   end).

Ltac pls_destruct_correctly := (* add case for filtered_var destruct *)
    repeat
    (match goal with
    | [ x : TRValues |- _ ] => 
      match goal with
      | [ H : HasType x ?t |- _ ] => idtac x H t; destruct x
      end
    end); try inv_trtype_false. 

Ltac equal_trv :=
  match goal with
  | [ H : (Bool true) = (Bool false) |- _ ] => inversion H
  | [ H : (Bool false) = (Bool true) |- _ ] => inversion H
  end.

Ltac hypothesis_jail :=
    repeat
    (match goal with
    | [ H : forall x : ?t, ?P |- _ ] => 
      match goal with
      | [ n : t |- _ ] => idtac H n; specialize (H n) (* i'm not quite sure how to make it specilaize with the correct "t"*)
      end
    | [ H : _ \/ _ |- _ ] => destruct H
    | [ H : _ <> _ |- _ ] => destruct H
    | [ H : ~_ |- _ ] => destruct H
    | [ H : ?b = ?d |- _ ] => equal_trv
    | [ H : HasType ?x ?t |- _ ] => pls_destruct_correctly
    end); auto.

Ltac hypothesis_jail' :=
    repeat
    (match goal with
    | [ H : forall x : ?t, ?P |- _ ] => 
      match goal with
      | [ n : t |- _ ] => idtac H n; specialize (H n) (* i'm not quite sure how to make it specilaize with the correct "t"*)
      end
    | [ H : _ <> _ |- _ ] => destruct H
    | [ H : ~_ |- _ ] => destruct H
    | [ H : ?b = ?d |- _ ] => equal_trv
    end); auto.

Ltac ht_good_hehe :=
  match goal with
  | [ |- HasType (Bool true) trbool ] => constructor
  | [ |- HasType (Bool false) trbool ] => constructor
  | [ b : bool |- _ ] => 
    match goal with
    | [ |- HasType (Bool b) trbool ] => constructor
    end
  | [ n : nat |- _ ] => 
    match goal with
    | [ |- HasType (Num n) trnum ] => constructor
    end
  | [ s : string |- _ ] => 
    match goal with
    | [ |- HasType (Str s) trstr ] => constructor
    end
  | [ |- HasType (Pair ?a ?b) (trpair ?t1 ?t2) ] => constructor
  | [ |- HasType ?a trtop ] => constructor
  | [ a : TRValues, b : TRValues |- _ ] =>
    match goal with
    | [ H : HasType a ?A, H1 : HasType b ?B |- HasType (Pair a b) (trpair ?A ?B) ] => constructor
    end
  end.

Ltac conclusion_jail :=
  repeat 
  (match goal with
  | [ |- _ /\ _ ] => constructor
  | [ |- _ -> _ ] => intro
  | [ |- ~_ ] => intro
  end); try ht_good_hehe.

Ltac pls_jail :=
  start_jail; conclusion_jail; hypothesis_jail.

Program Definition add1 (n : {t >> trnum}) : {t >> trnum} :=
   match n with
   | Num x => giveType (Num (S x))
   | _r => False_rec _ _
   end.
   (* start_jail. pls_destruct_correctly. hypothesis_jail. *)
   Next Obligation. pls_jail. Defined.

Eval compute in add1 (giveType (Num 5)).
Eval compute in add1 (add1 (giveType (Num 5))).
Program Definition add (n : {v >> trnum}) (m : {v >> trnum}) : {v >> trnum} :=
  match n, m with
  | Num x, Num y => giveType (Num (x + y))
  | _r, _q => False_rec _ _
  end.
  Next Obligation. (* the question above is the problem we see with this one *)
  start_jail. repeat pls_destruct_correctly. specialize (n0 n n4). hypothesis_jail. 
  Defined.
  

Program Definition is_number {t : TRTypes} (x : {v >> t}) : 
                  {t >> trbool & (HasType x trnum) & ~(HasType x trnum)} :=
  match x with
  | Num n => Bool true
  | _r => Bool false
  end.
  Next Obligation. pls_jail. Defined.
  Next Obligation. pls_jail. Defined.


Program Definition is_string {t : TRTypes} (x : {v >> t}) : 
                  {t >> trbool & (HasType x trstr) & ~(HasType x trstr)} :=
  match x with
  | Str s => Bool true
  | _r => Bool false
  end.
  Next Obligation. pls_jail. Defined.
  Next Obligation. pls_jail. Defined.

Program Definition is_bool {t : TRTypes} (x : {v >> t}) : 
                  {t >> trbool & (HasType x trbool) & ~(HasType x trbool)} :=
  match x with
  | Bool b => Bool true
  | _r => Bool false
  end.
  Next Obligation. pls_jail. Defined.
  Next Obligation. pls_jail. Defined.

Program Definition is_pair {t1 : TRTypes} (x : {v >> t1}) : 
  {t >> trbool & (HasType x (trpair trtop trtop)) & ~(HasType x (trpair trtop trtop))} :=
  match x with
  | Pair a b => Bool true
  | _r => Bool false
  end.
  Next Obligation. 
  start_jail. conclusion_jail; try constructor. inversion H.
  Defined.
  Next Obligation.
  start_jail. conclusion_jail.
  - try destruct H; auto.
  - pls_destruct_correctly; 
    specialize n with filtered_var1 filtered_var2;
    destruct n; auto.
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
  pls_jail;
  replace (Bool b0) with filtered_var in x2; auto; 
  replace (Bool b) with filtered_var0 in y2; auto;
  symmetry in Heq_x, Heq_y.
  - apply x2 in Heq_x; auto.
  - apply y2 in Heq_y; auto.
  Defined.
  
  Next Obligation.
  pls_jail. split.
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
  -  constructor 6. constructor.
  - destruct o; inv_trtype_false.
  - constructor 5. constructor.
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

(* Program Definition ex7_again {t r : TRTypes} (x : {v >> t}) (y : {w >> r}) : {v >> trnum} :=
  (@if_TR_again _ _ _ _ True
    (@if_TR_again _ _ _ _ (~(HasType x trnum /\ HasType y trstr))
      (is_number x)
      (fun _ => (is_string y))
      (fun _ => (Bool false)))
    (fun _ => (add x (strlen y)))
    (fun _ => (giveType (Num 0)))).
Next Obligation. (*ahhhhh*) *)


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
  - destruct o. constructor 5; auto. constructor 6; auto.
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
          (* i think these props are wrong. or my proofs are wrong *)
                    p 
                    p 
                    (is_string x)))
         (ex2 x) 
         (giveType (Num 0))).
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.

(* Example 10 & 11 & 12 uses pair, so maybe later *) (* :( i can't get is_pair to work i sad *)

(* Example 13 is cond *)

(* Example 14 puts it all together *)










