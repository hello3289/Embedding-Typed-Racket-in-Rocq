From research Require Import Functions.
From research Require Import Tactic_jail.
From research Require Import Definitions.
Require Import String.
Require Import Bool.
Require Import Coq.Program.Tactics.
Require Import JMeq.
#[local] Obligation Tactic := try now program_simpl.

(* IT LIVES *)

(************************************************************************)
(********************** EXAMPLE 1 AHHHHHHHHHHHHHHH **********************)
Program Definition ex1 {t : TRTypes} (x : {v >> t}) : {v >> trnum}:=
  ifTR (is_number x) (add1 x) (giveType (Num 0)).

Eval compute in <[ ex1 (Num 5) ]>.
Eval compute in <[ ex1 (Str "5") ]>.

(************************************************************************)
(********************** EXAMPLE 2 AHHHHHHHHHHHHHHH **********************)

Program Definition ex2 (x : {v >> (trunion trstr trnum)}) : {v >> trnum} :=
  ifTR (is_number x) (add1 x) (strlen x).
  Next Obligation.
  start_jail; simpl; try constructor; inversion x0; try inv_trtype_false.
  - destruct n; auto. 
  Defined.

Eval compute in ex2 <[TRUnionL (Str "hi")]>.
Eval compute in ex2 <[TRUnionR (Num 9)]>.

(************************************************************************)
(********************** EXAMPLE 4 AHHHHHHHHHHHHHHH **********************)

Program Definition ex4 {t : TRTypes} (x : {v >> t}) : {v >> trnum} :=
  ifTR (orTR (is_number x) (is_string x))
        (ex2 x)
        (Num 0).
  Next Obligation.
  start_jail; simpl; simpl in o. 
  - apply HtUnion_R. constructor.
  - destruct o; inv_trtype_false.
  - apply HtUnion_L. constructor.
  - destruct o; inv_trtype_false.
  Defined.
  Next Obligation.
  start_jail; simpl; constructor. (* the strangest obligation what *)
  Defined.
  
Eval compute in <[ex4 (Num 9)]>.
Eval compute in <[ex4 (Str "hi")]>.
Eval compute in <[ex4 (Bool true)]>.

(************************************************************************)
(********************** EXAMPLE 5 AHHHHHHHHHHHHHHH **********************)

Program Definition ex5 {t r : TRTypes} (x : {v >> t}) (y : {w >> r}) : {v >> trnum} :=
  ifTR  (andTR (is_number x) (is_string y))
        (add x (strlen y)) (* i need addition *)
        (Num 0).
   Next Obligation.
   start_jail; simpl; constructor. (* another strange obligation.... *)
   Defined.

Eval compute in <[<[ex5 (Num 5)]> (Str "hi")]>.
Eval compute in <[<[ex5 (Num 5)]> (Num 8)]>.
Eval compute in <[<[ex5 (Str "hello")]> (Num 10)]>.
Eval compute in <[<[ex5 (Bool true)]> (Bool false)]>.

(************************************************************************)
(********************** EXAMPLE 7 AHHHHHHHHHHHHHHH **********************)

Program Definition ex7 {t r : TRTypes} (x : {v >> t}) (y : {w >> r}) : {v >> trnum} :=
  (ifTR < (HasType x trnum /\ HasType y trstr) True (~(HasType x trnum /\ HasType y trstr)) True >
    (ifTR < (HasType x trnum)  (HasType x trnum /\ HasType y trstr)>
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

Eval compute in <[<[ex7 (Num 6)]> (Str "hello")]>.

(************************************************************************)
(********************** EXAMPLE 8 AHHHHHHHHHHHHHHH **********************)

Program Definition ex8 {t : TRTypes} (x : {v >> t}) :=
  (orTR (is_string x) (is_number x)).

Program Definition ex8_test {t : TRTypes} (x : {v >> t}) : {v >> trnum} :=
  (ifTR (ex8 x) (ex2 x) (giveType (Num 0))).
Next Obligation.
intros. simpl. split.
  - destruct o. apply HtUnion_L; auto. apply HtUnion_R; auto.
  - split; destruct x; auto.
Defined.

Eval compute in <[ex8 (Num 6)]>.
Eval compute in <[ex8_test (Num 6)]>.
Eval compute in <[ex8 (Str "potatoes")]>.
Eval compute in <[ex8_test (Str "potatoes")]>.
Eval compute in <[ex8 (Bool true)]>.
Eval compute in <[ex8_test (Bool true)]>.

(************************************************************************)
(********************** EXAMPLE 9 AHHHHHHHHHHHHHHH **********************)

Program Definition ex9 {t : TRTypes} (x : {v >> t}) : {v >> trnum} :=
  (ifTR (let p := (is_number x) in 
          (ifTR < (HasType x trnum) 
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

Eval compute in <[ex9 (Num 2)]>.

(************************************************************************)
(********************** EXAMPLE 10 AHHHHHHHHHHHHHH **********************)

Program Definition ex10 {A B : TRTypes} (p : {v >> (trpair A B)}) : {t >> trnum} :=
  ifTR (is_number (car p)) (add1 (car p)) (giveType (Num 7)).

Eval compute in <[ex10 (Pair (Num 5) (Str "bye"))]>.
Eval compute in <[ex10 (Pair (Bool false) (Num 10))]>.

(************************************************************************)
(********************** EXAMPLE 11 AHHHHHHHHHHHHHH **********************)

Program Definition g (p : {v >> trpair trnum trnum}) : {t >> trnum} :=
  (add (car p) (cdr p)).

Eval compute in <[g (Pair (Num 4) (Num 5))]>.

(* instead of returning 'no, i'll return 0 *)
Program Definition ex11 {A B : TRTypes} (p : {v >> trpair A B}) : {t >> trnum} :=
  ifTR (andTR (is_number (car p)) (is_number (cdr p))) (g p) (giveType (Num 0)).
Next Obligation.
  start_jail; destruct a; constructor; auto.
  Defined.

Eval compute in <[ex11 (Pair (Num 4) (Num 12))]>.
Eval compute in <[ex11 (Pair (Num 3) (Bool false))]>.

(************************************************************************)
(********************** EXAMPLE 12 AHHHHHHHHHHHHHH **********************)

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

Eval compute in <[ex12 (Pair (Num 4) (Bool true))]>.
Eval compute in <[ex12 (Pair (Str "hi") (Num 1))]>.