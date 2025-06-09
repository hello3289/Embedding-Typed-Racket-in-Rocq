From research Require Import Tactic_jail.
From research Require Import Definitions.
Require Import String.
Require Import Bool.
Require Import Coq.Program.Tactics.
Require Import JMeq.
#[local] Obligation Tactic := try (program_simpl; easy); try (pls_jail; easy).

Program Definition add1 (n : {t >> trnum}) : {t >> trnum} :=
   match n with
   | Num x => giveType (Num (S x))
   | _r => False_rec _ _
   end.

Program Definition add (n : {v >> trnum}) (m : {v >> trnum}) : {v >> trnum} :=
  match n, m with
  | Num x, Num y => giveType (Num (x + y))
  | _r, _q => False_rec _ _
  end.

Program Definition is_number {P Q} {t : TRTypes} (x : {v >> t & P & Q}) : 
                  {t >> trbool & (HasType x trnum) & ~(HasType x trnum)} :=
  match x with
  | Num n => Bool true
  | _r => Bool false
  end.
  

Program Definition is_string {t : TRTypes} (x : {v >> t}) : 
                  {t >> trbool & (HasType x trstr) & ~(HasType x trstr)} :=
  match x with
  | Str s => Bool true
  | _r => Bool false
  end.
  
Program Definition is_bool {t : TRTypes} (x : {v >> t}) : 
                  {t >> trbool & (HasType x trbool) & ~(HasType x trbool)} :=
  match x with
  | Bool b => Bool true
  | _r => Bool false
  end.
  
Program Definition is_pair {t1 : TRTypes} (x : {v >> t1}) : 
  {t >> trbool & (HasType x (trpair trtop trtop)) & ~(HasType x (trpair trtop trtop))} :=
  match x with
  | Pair a b => Bool true
  | _r => Bool false
  end.
  
Program Definition strlen (s : {v >> trstr}) : {v >> trnum} :=
  match s with
  | Str s => giveType (Num (length s))
  | _ => False_rec _ _
  end.
  
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

(************************************************************************)
(************************ IF AND OR WHAT SUBSUME ************************)

Lemma subsume' : forall  A (P' P'' Q' Q'' : Prop), {t >> (A) & P'' & Q''} -> {t >> (A) & P' \/ P'' & Q' \/ Q''}.
Proof.
  intros. apply subsume with P'' Q''; auto.
Defined.

Definition if_TR' {A : TRTypes} {P P' Q Q' : Prop} 
                          (x : {t >> trbool & P & Q})                        
                          (y : P -> {t >> A & P' & Q'})
                          (z : Q -> {t >> A & P' & Q'}) : 
                          {t >> A & P' & Q'}.
Proof. 
  start_jail.
  destruct x; 
  try destruct b;
  try (apply subsume with P' Q'; auto); 
  try (apply y; apply x1; discriminate). 
Defined.

(************************************************************************)
(********************** MORE NOTATIONS FOR IF AHHH **********************)
Notation " 'ifTR' A B C " := 
  (if_TR' A (fun _ => B) (fun _ => C)) 
  (at level 0, A at next level, B at next level, C at next level). 

Notation " 'ifTR' < P P' Q Q' > A B C " := 
  (@if_TR' _ P P' Q Q' A (fun _ => B) (fun _ => C)) 
  (at level 2, P at next level, P' at next level,
  Q at next level, Q' at next level, A at next level, 
  B at next level, C at next level). 

Notation " 'ifTR' < P P' > A B C " := 
  (@if_TR' _ P P' (~P) (~P') A (fun _ => B) (fun _ => C)) 
  (at level 2, P at next level, P' at next level, A at next level, 
  B at next level, C at next level).
  
Notation " 'condTR' [ A B ] [ C D ] [ 'else' E ]" :=
  (ifTR A B (ifTR C D E)) (A at level 0, C at next level, E at next level).

Notation " 'orTR' < P Q > A B " :=
  (ifTR < P (P \/ Q) > A A B) (at level 10, P at next level, Q at next level, A at next level, B at next level).

Notation " 'andTR' < P Q > A B " :=
  (ifTR < P (P /\ Q) > A B A) (at level 10, P at next level, Q at next level, A at next level, B at next level).


(************************************************************************)
(********************** I HAVE FAILED AHHHHHHHHHHH **********************)

Program Definition orTest {A : TRTypes} (x : {t >> A}) : 
    {t >> trbool & ((HasType x trnum) \/ (HasType x trstr)) & ~((HasType x trnum) \/ (HasType x trstr))} :=
    orTR < (HasType x trnum) (HasType x trstr) > (is_number x) (is_string x).


Program Definition andTest {A B : TRTypes} (x : {t >> A}) (y : {t >> B}) :
  {t >> trbool & ((HasType x trnum)  /\ (HasType y trstr)) & ~((HasType x trnum)  /\ (HasType y trstr))} :=
  andTR < (HasType x trnum) (HasType y trstr) > (is_number x) (is_string y).
  

Program Definition condTest {A B : TRTypes}
    (x : {v >> A})
    (y : {v >> B}) :
    {t >> trnum} :=
  condTR [ (is_number x) (add1 x) ]
         [ (is_string y) (strlen y) ]
         [ else (giveType (Num 0))].

Eval compute in condTest <[(Num 14)]> <[(Num 4)]>.
Eval compute in condTest <[(Str "hi")]> <[(Str "four")]>.
Eval compute in condTest <[(Bool true)]> <[(Bool true)]>.
    

(************************************************************************)
(********************** PAIRS AHHHHHHHHHHHHHHHHHHH **********************)

Program Definition car {X Y : Prop} {A B : TRTypes} (l : {v >> (trpair A B) & X & Y}) : {t >> A} :=
  match l with
  | Pair a b => a
  | _r => False_rec _ _
  end.

  Print car.

Program Definition cdr {X Y : Prop} {A B : TRTypes} (l : {v >> (trpair A B) & X & Y}) : {t >> B} :=
  match l with
  | Pair a b => b
  | _r => False_rec _ _
  end.
