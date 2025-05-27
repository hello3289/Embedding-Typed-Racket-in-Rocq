From research Require Import Tactic_jail.
From research Require Import Definitions.
Require Import String.
Require Import Bool.
Require Import Coq.Program.Tactics.
Require Import JMeq.
#[local] Obligation Tactic := try now program_simpl.

Program Definition add1 (n : {t >> trnum}) : {t >> trnum} :=
   match n with
   | Num x => giveType (Num (S x))
   | _r => False_rec _ _
   end.
   Next Obligation.
   jail. Defined.
   
Program Definition add (n : {v >> trnum}) (m : {v >> trnum}) : {v >> trnum} :=
  match n, m with
  | Num x, Num y => giveType (Num (x + y))
  | _r, _q => False_rec _ _
  end.
  Next Obligation. 
  start_jail. destruct (n0 n n4); auto.
  Defined.

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

Program Definition strlen (s : {v >> trstr}) : {v >> trnum} :=
  match s with
  | Str s => giveType (Num (length s))
  | _ => False_rec _ _
  end.
  Next Obligation. jail. Defined.

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
  destruct x.
  destruct a as [H0 [H1 H2]].
  destruct x;
   try (apply subsume with P' Q'; auto; apply y; apply H1; discriminate). 
  - destruct b. 
   + apply subsume with P' Q'; auto; apply y;apply H1; discriminate.
   + apply subsume with P' Q'; auto.
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
  Next Obligation.
  start_jail; simpl in *; try intro; try constructor.
  all : intro; destruct H0; try discriminate; try inversion H0.
  inversion h.
  Defined. Next Obligation.
  start_jail; simpl in *; try intro; try intro.
  - constructor.
  - left; constructor. (* doing constructor normally can lead to it choosing the wrong side *)
  - destruct n; constructor.
  - constructor.
  - destruct H; auto.
  - destruct H0; inversion H0.
  - constructor.
  - right; constructor.
  - discriminate.
  - constructor.
  - destruct H; auto.
  - destruct H0; inversion H0.
  Defined.

Program Definition andTest {A B : TRTypes} (x : {t >> A}) (y : {t >> B}) :
  {t >> trbool & ((HasType x trnum)  /\ (HasType y trstr)) & ~((HasType x trnum)  /\ (HasType y trstr))} :=
  andTR < (HasType x trnum) (HasType y trstr) > (is_number x) (is_string y).
  Next Obligation.
  intros; simpl in *. split; try intros; destruct y as [?H [?H [?H ?H]]].
  - destruct H; simpl; constructor.
  - split; intro. 
    + split; auto.
      destruct H; simpl in *; try constructor; try destruct H3; auto.
    + intro. destruct H4. destruct H; simpl in *; try inversion H5.
      discriminate.
  Defined. Next Obligation.
  intros; simpl in *. split; destruct x as [?H [?H [?H ?H]]].
  - destruct H; simpl; constructor.
  - split; intro.
    + destruct n. destruct H; simpl in *; try constructor; try destruct H3; auto.
    + intro. destruct H4. destruct n; destruct H; simpl in *; try constructor; auto.
  Defined.
(*
Program Definition orTR {P Q : Prop} (x : {t >> trbool & P & ~P}) 
                                      (y : {t >> trbool & Q & ~Q}) : 
                              {t >> trbool & (P \/ Q) & ~(P \/ Q)} :=
  ifTR < P (P \/ Q) > x x y.
  Next Obligation.
  start_jail. simpl; intro. intro. rewrite H in *. destruct H0;
  specialize (x2 eq_refl); destruct x2; auto.
  Defined.
  Next Obligation.
  start_jail. simpl; intro. intro. rewrite H in *. destruct H0; 
  specialize (y2 eq_refl); destruct y2; auto.
  Defined.
*)
(* Program Definition andTR {P Q : Prop} 
    (x : {t >> trbool & P & ~P}) 
    (y : {t >> trbool & Q & ~Q}) : 
    {t >> trbool & (P /\ Q) & ~(P /\ Q)} :=
    ifTR < P (P /\ Q) > x y x.
  Next Obligation.
  start_jail; simpl; intro; intro. rewrite H in *; destruct H0; 
  specialize (y3 eq_refl); destruct y3; auto.
  Defined.
  Next Obligation.
  start_jail; simpl; intro; intro. rewrite H in *; destruct H0. 
  specialize (x2 eq_refl); destruct x2; auto.
  Defined.
  *)

Program Definition condTest {A B : TRTypes}
    (x : {v >> A})
    (y : {v >> B}) :
    {t >> trnum} :=
  condTR [ (is_number x) (add1 x) ]
         [ (is_string y) (strlen y) ]
         [ else (giveType (Num 0))].

Eval compute in <[<[condTest (Num 14)]> (Num 4)]>.
Eval compute in <[<[condTest (Str "hi")]> (Str "four")]>.
Eval compute in <[<[condTest (Bool true)]> (Bool true)]>.
    

(************************************************************************)
(********************** PAIRS AHHHHHHHHHHHHHHHHHHH **********************)

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
