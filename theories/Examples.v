From research Require Import Functions.
From research Require Import Tactic_jail.
From research Require Import Definitions.
Require Import String.
Require Import Bool.
Require Import Coq.Program.Tactics.
Require Import JMeq.
#[local] Obligation Tactic := try now program_simpl.
#[local] Obligation Tactic := try (program_simpl; easy); try (pls_jail; easy).


Coercion Num : nat >-> TRValues.
Coercion Str : string >-> TRValues.
Coercion Bool : bool >-> TRValues.
(* not sure if you want a coercion to pair, it seems a little weird to do so *)

Open Scope string_scope.

(* IT LIVES *)

(************************************************************************)
(********************** EXAMPLE 1 AHHHHHHHHHHHHHHH **********************)
Program Definition ex1 {t : TRTypes} (x : {v >> t}) : {v >> trnum}:=
  ifTR (is_number x) (add1 x) <[0]>.
  (* Num 0 is required as ifTR needs type {v >> t} so the coercion will not work *)
  (* since it only does so when it see the specific type TRVales, not the subtype *)
  (* maybe another coercion? *)
  (* so <[0]> works since <[]> is expecting a TRValue, but this doesn't seem like what we want *)

Eval compute in ex1 <[ 5 ]>.
Eval compute in ex1 <[ "5" ]>.

(************************************************************************)
(********************** EXAMPLE 2 AHHHHHHHHHHHHHHH **********************)

Program Definition ex2 (x : {v >> (trunion trstr trnum)}) : {v >> trnum} :=
  ifTR (is_number x) (add1 x) (strlen x).

Program Definition ex2_test1 := ex2 <["hi"]>.
Program Definition ex2_test2 := ex2 <[9]>.

Eval compute in ex2_test1.
Eval compute in ex2_test2.

(************************************************************************)
(********************** EXAMPLE 4 AHHHHHHHHHHHHHHH **********************)

Program Definition ex4 {t : TRTypes} (x : {v >> t}) : {v >> trnum} :=
  ifTR (orTR (is_number x) (is_string x))
        (ex2 x)
        <[0]>.
  
Eval compute in ex4 <[9]>.
Eval compute in ex4 <["hi"]>.
Eval compute in ex4 <[true]>.

(************************************************************************)
(********************** EXAMPLE 5 AHHHHHHHHHHHHHHH **********************)

Program Definition ex5 {t r : TRTypes} (x : {v >> t}) (y : {w >> r}) : {v >> trnum} :=
  ifTR  (andTR (is_number x) (is_string y))
        (add x (strlen y)) (* i need addition *)
        <[0]>.

Eval compute in ex5 <[5]> <["hi"]>.
Eval compute in ex5 <[5]> <[8]>.
Eval compute in ex5 <["hello"]> <[10]>.
Eval compute in ex5 <[true]> <[false]>.

(************************************************************************)
(********************** EXAMPLE 7 AHHHHHHHHHHHHHHH **********************)

Program Definition ex7 {t r : TRTypes} (x : {v >> t}) (y : {w >> r}) : {v >> trnum} :=
  (ifTR < (HasType x trnum /\ HasType y trstr) True (~(HasType x trnum /\ HasType y trstr)) True >
    (ifTR < (HasType x trnum)  (HasType x trnum /\ HasType y trstr)>
      (is_number x)
      (is_string y)
      (Bool false))
    (add x (strlen y))
    <[0]>).

Eval compute in ex7 <[6]> <["hello"]>.

(************************************************************************)
(********************** EXAMPLE 8 AHHHHHHHHHHHHHHH **********************)

Program Definition ex8 {t : TRTypes} (x : {v >> t}) :=
  orTest x.

Program Definition ex8_test {t : TRTypes} (x : {v >> t}) : {v >> trnum} :=
  (ifTR (ex8 x) (ex2 x) <[0]>).

Eval compute in ex8 <[6]>.
Eval compute in ex8_test <[6]>.
Eval compute in ex8 <["potatoes"]>.
Eval compute in ex8_test <["potatoes"]>.
Eval compute in ex8 <[true]>.
Eval compute in ex8_test <[true]>.

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
         <[0]>).

Eval compute in ex9 <[2]>.

(************************************************************************)
(********************** EXAMPLE 10 AHHHHHHHHHHHHHH **********************)

Program Definition ex10 {A B : TRTypes} (p : {v >> (trpair A B)}) : {t >> trnum} :=
  ifTR (is_number (car p)) (add1 (car p)) <[7]>.

Eval compute in ex10 <[(Pair 5 "bye")]>.
Eval compute in ex10 <[(Pair false 10)]>.

(************************************************************************)
(********************** EXAMPLE 11 AHHHHHHHHHHHHHH **********************)

Program Definition g (p : {v >> trpair trnum trnum}) : {t >> trnum} :=
  (add (car p) (cdr p)).

Eval compute in g <[(Pair 4 5)]>. 

(* instead of returning 'no, i'll return 0 *)
Program Definition ex11 {A B : TRTypes} (p : {v >> trpair A B}) : {t >> trnum} :=
  ifTR (andTR (is_number (car p)) (is_number (cdr p))) (g p) <[0]>.
  
Eval compute in ex11 <[(Pair 4 12)]>.
Eval compute in ex11 <[(Pair 3 false)]>.

(************************************************************************)
(********************** EXAMPLE 12 AHHHHHHHHHHHHHH **********************)

(* back to the scheduled programming *)
Program Definition ex12 {A B : TRTypes} (p : {v >> trpair A B}) : 
  {t >> trbool & (HasType p (trpair trnum B)) & (~ (HasType p (trpair trnum B)))} :=
  (is_number (car p)).
  
  

Program Definition ex12_again {A B : TRTypes} (p : {v >> trpair A B}) : 
{t >> trbool & (HasType (car p) trnum) & (~ (HasType (car p) trnum))} :=
  (is_number (car p)).

Eval compute in ex12 <[(Pair 4 true)]>.
Eval compute in ex12 <[(Pair "hi" 1)]>.

(************************************************************************)
(********************** EXAMPLE 13/14 AHHHHHHHHHHH **********************)

Program Definition ex13_14 
    (x : {v >> trunion trnum trstr}) 
    (y : {v >> trpair trtop trtop}) :
    {t >> trnum} :=
  condTR [ (andTR (is_number x) (is_number (car y))) (add x (car y)) ] 
         [ (is_number (car y)) (add (strlen x) (car y)) ] 
         [ else <[0]>].

Check Num.

Program Definition ex_13_14_use := ex13_14 <[14]> <[Pair 14 "hello"]>.

Eval compute in ex_13_14_use.


(* though I don't know if this is the best solution for trpair trtop trtop, it probably isn't lol *)
 
(************************************************************************)
(******************* RANDOM STUFF WE HAVE TRIED TO DO *******************)

(* trying to do something but failing spectacularly *)
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


(* Disable Notation "[ e ]" := (exist _ e _). *)
Check what.

Lemma trying_prequel : forall (p3 : TRValues), 
  proj1_sig (exist (fun _ => True) p3 ok) = p3.
  Proof. intros; simpl; auto. Defined.

Lemma trying : forall (p1 p2 : TRValues) (A B : TRTypes), 
  HasType p1 A -> HasType p2 B -> 
  proj1_sig (car (exist (fun x => (HasType x (trpair A B)) /\ 
                    (x <> Bool false -> True) /\
                    (x = Bool false -> True)) 
          (Pair p1 p2) 
          what)) = 
          p1.
  Proof. intros. simpl; auto. Defined.
(* this does work, but i don't know if it's useful *)
(* but this doesn't work when we don't have proj1_sig like [p3] = [p3] 
bc they have different proofs that can't compute to the same thing*)

Check car.

Lemma trying_pt2 : forall (P Q : Prop) (p1 p2 : TRValues) (A B : TRTypes) Z W, 
  HasType p1 A -> HasType p2 B -> 
 proj1_sig (car (exist (fun x => (HasType x (trpair A B)) /\ (x <> Bool false -> P) /\ (x = Bool false -> Q)) 
          (Pair p1 p2) 
             Z)) = 
      proj1_sig (exist (fun x => (HasType x A /\(x <> Bool false -> True) /\ (x = Bool false -> True)) )
          p1
             W).
  Proof. intros. unfold car. destruct p1; simpl; auto. Qed.

    (*
Lemma trying_pt3 : forall  (p1 p2 : TRValues) (A B : TRTypes), 
  HasType p1 A -> HasType p2 B -> 
 proj1_sig (car (giveType(Pair p1 p2))) = proj1_sig [p1].
  Proof. intros. unfold car. destruct p1; simpl; auto. Qed.

    unfold car. simpl.
  
  Admitted.
  (* i think the implicit parameters of what are causing a problem, which is not surprising i guess *)
*)

Lemma want : forall T A B  (p  q : T) P Q, p = q ->
 proj1_sig (exist A p P) = proj1_sig (exist B q Q).
 Proof. 
  intros.
 simpl.
 auto.
Qed.

(* i forgot what we wanted to do with this *)

Lemma is_num_type: (forall T P Q (W : {v >> T & P & Q}), HasType (@proj1_sig TRValues (fun t : TRValues =>
HasType t trbool /\
(t <> Bool false -> (HasType (proj1_sig W) trnum)) /\
(t = Bool false -> ~(HasType (proj1_sig W) trnum))) (@is_number _ _ _  W)) trbool).
Proof. intros. destruct W; destruct x; simpl; constructor. Qed.

Lemma test : forall T P Q (x : { v >> T & P & Q }), HasType (proj1_sig (is_number x)) trbool.
Proof. apply is_num_type. Defined.

(* hehe *)