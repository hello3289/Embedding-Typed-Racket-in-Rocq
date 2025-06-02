From research Require Import Functions.
From research Require Import Tactic_jail.
From research Require Import Definitions.
Require Import String.
Require Import Bool.
Require Import Coq.Program.Tactics.
Require Import JMeq.
#[local] Obligation Tactic := try now program_simpl.
#[local] Obligation Tactic := try (program_simpl; easy); try (pls_jail; easy).


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

Eval compute in ex2 <[TRUnionL (Str "hi")]>.
Eval compute in ex2 <[TRUnionR (Num 9)]>.

(************************************************************************)
(********************** EXAMPLE 4 AHHHHHHHHHHHHHHH **********************)

Program Definition ex4 {t : TRTypes} (x : {v >> t}) : {v >> trnum} :=
  ifTR (orTR < (HasType x trnum) (HasType x trstr) > 
          (is_number x) (is_string x))
        (ex2 x)
        (Num 0).
  
Eval compute in <[ex4 (Num 9)]>.
Eval compute in <[ex4 (Str "hi")]>.
Eval compute in <[ex4 (Bool true)]>.

(************************************************************************)
(********************** EXAMPLE 5 AHHHHHHHHHHHHHHH **********************)

Program Definition ex5 {t r : TRTypes} (x : {v >> t}) (y : {w >> r}) : {v >> trnum} :=
  ifTR  (andTR < (HasType x trnum) (HasType y trstr) > (is_number x) (is_string y))
        (add x (strlen y)) (* i need addition *)
        (Num 0).

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

Eval compute in <[<[ex7 (Num 6)]> (Str "hello")]>.

(************************************************************************)
(********************** EXAMPLE 8 AHHHHHHHHHHHHHHH **********************)

Program Definition ex8 {t : TRTypes} (x : {v >> t}) :=
  orTest x.

Program Definition ex8_test {t : TRTypes} (x : {v >> t}) : {v >> trnum} :=
  (ifTR (ex8 x) (ex2 x) (giveType (Num 0))).

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
  ifTR (andTR < (HasType (car p) trnum) (HasType (cdr p) trnum) > (is_number (car p)) (is_number (cdr p))) (g p) (giveType (Num 0)).
  
Eval compute in <[ex11 (Pair (Num 4) (Num 12))]>.
Eval compute in <[ex11 (Pair (Num 3) (Bool false))]>.

(************************************************************************)
(********************** EXAMPLE 12 AHHHHHHHHHHHHHH **********************)

Lemma ok : True.
Proof. auto. Qed.

Lemma wtf2 : HasType (Num 5) trnum.
Proof. constructor. Qed.

Program Definition what {p3 p4 : TRValues} {A B : TRTypes} : HasType (Pair p3 p4) (trpair A B) /\ ((Pair p3 p4) <> Bool false -> True) /\
  ((Pair p3 p4) = Bool false -> True).
Proof. repeat split; auto. Admitted. (* i don't think we can prove this? *)

Program Definition what2 {t1 : TRValues} {A : TRTypes} : HasType t1 A /\ (t1 <> Bool false -> True) /\
  (t1 = Bool false -> True).
Proof. repeat split; auto. Admitted. (* same with this *)

Check what.

(* Disable Notation "[ e ]" := (exist _ e _). *)

Program Definition ex12 {A B : TRTypes} (p : {v >> trpair A B}) : 
  {t >> trbool & (HasType p (trpair trnum B)) & (~ (HasType p (trpair trnum B)))} :=
  (is_number (car p)).
  (* start_jail; conclusion_jail.
  - destruct p; try inversion p0. subst *. Search exist.
  assert (proj1_sig (exist (fun _ => True) p3 ok) = p3).
    + simpl; auto.
    + assert 
    (proj1_sig (car (exist 
          (fun x => (HasType x (trpair A B)) /\ 
                    (x <> Bool false -> True) /\
                    (x = Bool false -> True)) 
          (Pair p3 p4) 
          what)) = 
          p3).
      ++ unfold car; simpl; auto. (* this does work, but i don't know if it's useful *)
          (* but this doesn't work when we don't have proj1_sig like [p3] = [p3] 
          bc they have different proofs that can't compute to the same thing*)
      ++ assert 
        ((car (exist 
          (fun v => (HasType v (trpair A B)) /\ 
                    (v <> Bool false -> True) /\
                    (v = Bool false -> True)) 
          (Pair p3 p4) 
          what)) = 
          (exist (fun x => (HasType x A) /\ (x <> Bool false -> True) /\ (x = Bool false -> True))
                 p3
                 what2)).
          +++ give_up.
          +++ Check what. (* i think the implicit parameters of what are causing a problem, which is not surprising i guess *)
*)
  

Program Definition ex12_again {A B : TRTypes} (p : {v >> trpair A B}) : 
{t >> trbool & (HasType (car p) trnum) & (~ (HasType (car p) trnum))} :=
  (is_number (car p)).

Eval compute in <[ex12 (Pair (Num 4) (Bool true))]>.
Eval compute in <[ex12 (Pair (Str "hi") (Num 1))]>.

(************************************************************************)
(********************** EXAMPLE 13/14 AHHHHHHHHHHH **********************)

Program Definition ex13_14 {A B : TRTypes} 
    (x : {v >> trunion trnum trstr}) 
    (y : {v >> trpair trtop trtop}) :
    {t >> trnum} :=
  condTR [ (andTR < (HasType x trnum) (HasType (car y) trnum) > (is_number x) (is_number (car y))) (add x (car y)) ] 
         [ (is_number (car y)) (add (strlen x) (car y)) ] 
         [ else (giveType (Num 0))].
  
  