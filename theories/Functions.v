Set Warnings "-meta-collision".
Set Warnings "-uniform-inheritance".
Set Warnings "-ambiguous-paths".

From TRresearch Require Import Tactic_jail.
From TRresearch Require Import Definitions.
From TRresearch Require Import StandardFunctions.
From Stdlib.Strings Require Import String.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From Corelib Require Import Program.Tactics.
#[local] Obligation Tactic := try small_jail; try discriminate.

Declare Scope TR_scope.

(* i'm going to try and see if I can solve these with smaller tactics first before the big boy jail *)
#[local] Obligation Tactic := try new_jail; try discriminates.
Program Definition add1 (n : {trnum}) : {trnum} :=
   match n with
   | Num x => S x
   | _r => False_rec _ _
   end.

Eval compute in add1 5.

Program Definition sum (n : {trnum}) (m : {trnum}) : {trnum} :=
  match n with 
  | Num n' => 
    match m with 
    | Num m' => n' + m' 
    | _r2 => False_rec _ _ 
    end
  | _r1 => False_rec _ _ 
  end.
  
Program Definition mult (n : {trnum}) (m : {trnum}) : {trnum} :=
  match n with 
  | Num n' => 
    match m with 
    | Num m' => n' * m' 
    | _r2 => False_rec _ _ 
    end
  | _r1 => False_rec _ _ 
  end.
  


Program Definition sub (n : {trnum}) (m : {trnum}) : {trnum} :=
  match n with 
  | Num n' => 
    match m with 
    | Num m' => n' - m' 
    | _r2 => False_rec _ _ 
    end
  | _r1 => False_rec _ _ 
  end.

Notation " 'add' A B " := (sum A B) (at level 0, A at next level, B at next level) : TR_scope.
Notation " 'mul' A B " := (mult A B) (at level 0, A at next level, B at next level) : TR_scope.
Notation " 'sub' A B " := (sub A B) (at level 0, A at next level, B at next level) : TR_scope.

Program Definition is_number {t : TRTypes} (x : {t}) : 
                  {>> trbool & (HasType x trnum)} :=
  match x with
  | Num n => Bool true
  | _r => Bool false
  end.




Eval compute in is_number 5.
Program Definition is_string {t : TRTypes} (x : {t}) : 
                  {>> trbool & (HasType x trstr)} :=
  match x with
  | Str s => Bool true
  | _r => Bool false
  end.
  
Program Definition is_bool {t : TRTypes} (x : {t}) : 
                  {>> trbool & (HasType x trbool)} :=
  match x with
  | Bool b => Bool true
  | _r => Bool false
  end.
  
Program Definition is_pair {t : TRTypes} (x : {t}) : 
  {>> trbool & (HasType x (trpair trtop trtop))} :=
  match x with
  | Pair a b => Bool true
  | _r => Bool false
  end.

        
Program Definition strlen (s : {trstr}) : {trnum} :=
  match s with
  | Str s => length s
  | _r => False_rec _ _
  end.


Lemma subsume : forall  {A} (P P' Q Q' : Prop),
  (P -> P') -> (Q -> Q') ->
  {>> (A) & P & Q} -> {>> (A) & P'  & Q'}.
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

Lemma subsume' : forall  A (P' P'' Q' Q'' : Prop), {>> (A) & P'' & Q''} -> {>> (A) & P' \/ P'' & Q' \/ Q''}.
Proof.
  intros. apply subsume with P'' Q''; auto.
Defined.

Definition if_TR {A : TRTypes} {P P' Q Q' : Prop} 
                          (x : {t >> trbool & P & Q})                        
                          (y : P -> {t >> A & P' & Q'})
                          (z : Q -> {t >> A & P' & Q'}) : 
                          {t >> A & P' & Q'}. (* A union B *)
Proof. 
  start_jail.
  destruct x;
  try destruct b; 
  try (apply y; apply x1; split; try (auto; discriminate); fail).
  apply z; apply x2; split; auto.
Defined.


Lemma unionL : forall A B (P Q : Prop), {>> A & P & Q} -> {>> (U A B) & P & Q}.
Proof.
  intros.
  destruct H.
  assert (HasType x (trunion A B) /\ (HasType x (trunion A B) /\ x <> Bool false -> P) /\ (HasType x (trunion A B) /\ x = Bool false -> Q)).
  -  destruct a as [?H [?H ?H]]; repeat split; auto.
    + apply HtUnion_L; auto.
    + intros. destruct H2. apply H0; split; auto.
    + intros. destruct H2. apply H1; split; auto.
  - exact (exist (fun t : TRValues => 
                    HasType t (trunion A B) /\ 
                    (HasType t (trunion A B) /\ t <> Bool false -> P) /\ 
                    (HasType t (trunion A B) /\ t = Bool false -> Q))
                 x
                 H).
Defined.

Lemma unionR : forall A B (P Q : Prop), {>> B & P & Q} -> {>> (U A B) & P & Q}.
Proof.
  intros.
  destruct H.
  assert (HasType x (trunion A B) /\ (HasType x (trunion A B) /\ x <> Bool false -> P) /\ (HasType x (trunion A B) /\ x = Bool false -> Q)).
  - destruct a as [?H [?H ?H]]; repeat split; auto.
    + apply HtUnion_R; auto.
    + intros. destruct H2. apply H0; split; auto.
    + intros. destruct H2. apply H1; split; auto.
  - exact (exist (fun t : TRValues => 
                    HasType t (trunion A B) /\ 
                    (HasType t (trunion A B) /\ t <> Bool false -> P) /\ 
                    (HasType t (trunion A B) /\ t = Bool false -> Q))
                 x
                 H).
Defined.

Definition if_TR_union {A B : TRTypes} {P P' P'' Q Q' Q'' : Prop} 
                          (x : {>> trbool & P & Q})                        
                          (y : P -> {>> A & P' & Q'})
                          (z : Q -> {>> B & P'' & Q''}) : 
                          {>> (U A B) & (P' \/ P'') & (Q' \/ Q'')}.
Proof.
  start_jail.
  destruct x. 
    - apply unionL; 
      assert (H : HasType n trbool /\ (Num n) <> (Bool false)) by (split; auto; intro; inversion H); 
      specialize (x1 H); specialize (y x1); destruct y; destruct2 a;
      exists x; repeat split; auto.
    - destruct b. 
      apply unionL; 
      assert (H : HasType true trbool /\ (Bool true) <> (Bool false)) by (split; auto; intro; inversion H); 
      specialize (x1 H); specialize (y x1); destruct y; destruct2 a;
      exists x; repeat split; auto.
      apply unionR; 
      assert (H : HasType false trbool /\ (Bool false) = (Bool false)) by (split; auto; intro; inversion H); 
      specialize (x2 H); specialize (z x2); destruct z; destruct2 a;
      exists x; repeat split; auto.
    - apply unionL; 
      assert (H : HasType s trbool /\ (Str s) <> (Bool false)) by (split; auto; intro; inversion H); 
      specialize (x1 H); specialize (y x1); destruct y; destruct2 a;
      exists x; repeat split; auto.
    - apply unionL;
      assert (H : HasType (x3, x4) trbool /\ (x3, x4) <> (Bool false)) by (split; auto; intro; inversion H); 
      specialize (x1 H); specialize (y x1); destruct y; destruct2 a; 
      exists x; repeat split; auto.
    - apply unionL; 
      assert (H : HasType (List l) trbool /\ (List l) <> (Bool false)) by (split; auto; intro; inversion H); 
      specialize (x1 H); specialize (y x1); destruct y; destruct2 a;
      exists x; repeat split; auto.
    - apply unionL; 
      assert (H : HasType (Vec n n0) trbool /\ (Vec n n0) <> (Bool false)) by (split; auto; intro; inversion H); 
      specialize (x1 H); specialize (y x1); destruct y; destruct2 a;
      exists x; repeat split; auto.
    - apply unionL; 
      assert (H : HasType (Void v) trbool /\ (Void v) <> (Bool false)) by (split; auto; intro; inversion H); 
      specialize (x1 H); specialize (y x1); destruct y; destruct2 a;
      exists x; repeat split; auto.
  Defined.

Open Scope string_scope.
Eval compute in is_string "hi".

Program Definition notTR {P Q : Prop} (x : {>> trbool & P & Q}) : {>> trbool & Q & P} :=
  match x with
  | Bool false => Bool true
  | _r => Bool false
  end.

Eval compute in (notTR (is_string "hi")).



(************************************************************************)
(********************** MORE NOTATIONS FOR IF AHHH **********************)

(* these (and or/and) are defined with a more restricted ifTR (where the output type is not union)
   because of performance : having union requires more intensive automation, which dramatically
   slows down the automation. Also, these notation are always used when both branches are bool/the same
   type, so it's not worth the slowdown to use the union ifTR *)
  
Notation " 'ifTR' < 'second' > A B C " := 
  (let P := (get_true_prop A) in
    (let P' := (get_true_prop B) in
      (@if_TR _ P 
              (P /\ P') 
              (~P) 
              (~(P /\ P')) 
              A (fun _ => B) (fun _ => giveType C)))) 
  (at level 0, A at next level, 
  B at next level, C at next level).

Notation " 'ifTR' < 'third' > A B C " := 
  (let P := (get_true_prop A) in
    (let P' := (get_true_prop C) in 
      (@if_TR _ P 
             (P \/ P') 
             (~P) 
             (~(P \/ P')) 
             A (fun _ => B) (fun _ => C)))) 
  (at level 0, A at next level, 
  B at next level, C at next level).

Notation " 'ifTR' < 'all' > A B C " := 
  (let P := (get_true_prop A) in
    (let Q := (get_true_prop B) in
      (let R := (get_true_prop C) in 
        (@if_TR trbool P (* hmm *)
              ((P /\ Q) \/ R) 
              (~P) 
              (~((P /\ Q) \/ R)) 
              A (fun _ => B) (fun _ => C))))) 
  (at level 0, A at next level, B at next level, C at next level).  

Notation " 'ifTR' A B C " := 
  (if_TR_union A (fun _ => B) (fun _ => C))
  (at level 0, A at next level, B at next level, C at next level). 
 

Notation " 'condTR' [ A B ] [ C D ] [ 'else' E ]" :=
  (ifTR A B (ifTR C D E)) (A at level 0, C at next level, E at next level).

Notation " 'orTR' A B " :=
  (ifTR < third > A A B)
  (at level 10, A at next level, B at next level).

Notation " 'andTR' A B " :=
  (ifTR < second > A B A) 
  (at level 10, A at next level, B at next level).


Notation " 'orTR_2' A B " :=
  (ifTR A A B)
  (at level 10, A at next level, B at next level).

Notation " 'andTR_2' A B " :=
  (ifTR A B A)
  (at level 10, A at next level, B at next level).



(************************************************************************)
(********************************* TESTS ********************************)
Create HintDb TRHints.
Hint Unfold get_true_prop : TRHints.
Hint Constructors HasType : TRHints.

Program Definition orTest {A : TRTypes} (x : {A}) : 
    {>> trbool & ((HasType x trnum) \/ (HasType x trstr))} :=
    orTR (is_number x) (is_string x).

Program Definition andTest {A B : TRTypes} (x : {A}) (y : {B}) :
  {>> trbool & ((HasType x trnum)  /\ (HasType y trstr))} :=
  andTR (is_number x) (is_string y).

Eval compute in andTest 5 "hi".


Eval compute in (add1 5).

(* this is the exact program why we changed to trunion instead of directly following if's rule *)
Program Definition ifTest_1 {t : TRTypes} (x : {t}) : {trnum} :=
  ifTR (is_number x) x 0. 

Program Definition condTest {A B : TRTypes}
    (x : {A})
    (y : {B}) :
    {trnum} :=
  condTR [ (is_number x) (add1 x) ] 
         [ (is_string y) (strlen y) ]
         [ else 0].

Eval compute in condTest 14 4.
Eval compute in condTest "hi" "four".
Eval compute in condTest true true.

Program Definition orTest2 {A : TRTypes} (x : {A}) : 
    {>> trbool & ((HasType x trnum) \/ (HasType x trstr))} :=
    orTR_2 (is_number x) (is_string x).
Eval compute in orTest2 5.

Program Definition andTest2 {A B : TRTypes} (x : {A}) (y : {B}) :
  {>> trbool & ((HasType x trnum)  /\ (HasType y trstr))} :=
  andTR_2 (is_number x) (is_string y).
Print andTest2.

Eval compute in andTest2 5 "hi".

(************************************************************************)
(********************** PAIRS AHHHHHHHHHHHHHHHHHHH **********************)


Program Definition car {X Y} {A B : TRTypes} (l : {>> (trpair A B) & X & Y}) : {A} :=
  match l with
  | Pair a b => a
  | _r => False_rec _ _
  end.

Program Definition cdr {X Y : Prop} {A B : TRTypes} (l : {>> (trpair A B) & X & Y}) : {B} :=
  match l with
  | Pair a b => b
  | _r => False_rec _ _
  end.

(************************************************************************)
(********************** NUM EQUALITIES AHHHHHHHHHH **********************)

#[local] Obligation Tactic := try (intros; intro; simplify_hypothesis; discriminate).
Program Definition leTR (x : { trnum }) (y : { trnum }) : Prop :=
  match x, y with
  | Num n, Num m => n <= m
  | _r, _r2 => False
  end.

Inductive less_than_equal : TRValues -> TRValues -> Prop :=
  | valid_le : forall (n m : nat), leTR (Num n) (Num m) -> less_than_equal (Num n) (Num m).

Program Definition ltTR (x : { trnum }) (y : { trnum }) : Prop :=
  match x, y with
  | Num n, Num m => n < m
  | _r, _r2 => False
  end.

Inductive less_than : TRValues -> TRValues -> Prop :=
  | valid_lt : forall (n m : nat), ltTR (Num n) (Num m) -> less_than (Num n) (Num m).

Close Scope string_scope.
#[local] Obligation Tactic := try small_jail; try discriminate; try new_jail.
Program Definition ltTR_B (x : { trnum }) (y : { trnum }) : {trbool} :=
  match x, y with
  | Num n, Num m => Nat.ltb n m
  | _r, _r2 => False_rec _ _
  end.

(************************************************************************)
(************* NUM EQUALITIES LEMMAS AND WELL FOUNDEDNESS ***************)

Lemma less_than_0 :forall (n : nat), less_than_equal (Num 0) (Num n).
  Proof. intros. constructor; unfold leTR; simpl. apply le_0_n. Defined.

Lemma what_again : forall i n, (Nat.ltb i n) = true -> i < n.
  intros. apply PeanoNat.Nat.ltb_lt; auto. Defined.

Lemma strictly_lessthan : forall (n : nat) (i : nat) (step : nat), 
    i < n + S step -> i < n -> n + S step - (i + S step) < n + S step - i.
Proof. intros. lia. Defined.

Lemma what_again_TR : forall i n, (Bool true) = (proj1_sig (ltTR_B (Num i) (Num n))) -> i < n.
Proof. intros. simpl in H. apply what_again. inversion H. rewrite H1; auto. Defined.

Lemma what_again_again_TR : forall i n, (Bool true) = (proj1_sig (ltTR_B (Num i) (Num n))) -> less_than (Num i) (Num n).
Proof. intros. simpl in H. constructor. unfold ltTR; simpl. apply what_again. inversion H. rewrite H1; auto. Qed.

Lemma what_again_again_again_TR : forall i n, (Bool true) = (proj1_sig (ltTR_B (Num i) (Num n))) -> ltTR (Num i) (Num n).
Proof. intros. apply what_again_again_TR in H. inversion H; auto. Qed.

#[local] Obligation Tactic := try small_jail; try discriminate; try new_jail.
  Program Definition wf_id (n : {trnum}) : nat := 
    match n with 
    | Num n' => n'
    | _r => False_rec _ _
    end.

Lemma wf_ltTR : well_founded ltTR.
Proof. 
  eapply (Wf_nat.well_founded_lt_compat _ wf_id). 
  intros; destruct2 x; destruct2 y.
  destruct x; try inv_trtype_false_faster_2. destruct y; try inv_trtype_false_faster_2. 
  unfold ltTR in H; simpl in H. unfold wf_id; simpl. auto.
Defined.


(************************************************************************)
(********************** VECTOR FUNCTIONS AHHHHHHHH **********************)

(* these notation were just to test if we could get rid of the match, which we couldn't *)
Notation " {{ f { res } a1 a2 }} " :=
  match a1, a2 with 
  | Vec a v1, Vec b v2 => (Vec res (f v1 v2))
  | _r1, _r2 => False_rec _ _
  end 
(at level 0, f at next level, res at next level, a1 at next level, a2 at next level).

Notation " {{ f n x }} " :=
  match x with 
  | Vec a v => f n v
  | _r => False_rec _ _
  end 
(at level 0, f at next level, n at next level, x at next level).

#[local] Obligation Tactic := try vec_inv; try small_jail; try discriminate; try new_jail.
Program Definition append_tr {n m} (x : { (trvec n) }) (y : { (trvec m) }) : { (trvec (n + m)) } :=
  match x, y with 
  | Vec a v1, Vec b v2 => (Vec (n + m) (append_vec v1 v2))
  | _r1, _r2 => False_rec _ _
  end.
Next Obligation. all : inversion Heq_x; inversion x0; subst *; inversion y0; auto. Defined. 
Next Obligation. specialize (n0 n3 n4 n1 n2). destruct n0; auto. Defined.

Eval compute in append_tr (cons 4 (cons 5 nil)) (cons 9 nil).
Eval compute in append_tr (cons 4 (cons 5 nil)) (append_vec (cons 9 nil) (cons 8 (cons 3 nil))).
(* Eval compute in append (cons 4 (cons 5 nil)) 6. *)

#[local] Obligation Tactic := try vec_inv; try small_jail; try discriminate; try new_jail; try unify_vec; auto.
Program Definition head_tr {n} (x : { (trvec (S n)) }) : { trnum } :=
  match x with 
  | Vec a v => head_vec n v
  | _r => False_rec _ _
  end.

Eval compute in (head_tr (cons 5 (cons 9 nil))).
(* Eval compute in (head nil). fails as expected *)

Program Definition tail_tr {n} (x : {(trvec (S n))}) : {(trvec n)} :=
  match x with 
  | Vec a v => tail_vec n v
  | _r => False_rec _ _
  end.

(* Eval compute in tail nil. *)
Eval compute in tail_tr (cons 9 (cons 5 (cons 4 nil))).

Program Definition tr_length {n} (x : { (trvec n) }) : { trnum } := n.
Eval compute in tr_length (cons 1 (cons 5 nil)).

Close Scope string_scope.
Open Scope nat_scope.
Check Nat.eqb.
(* lmaoooo the output will not hold any information *)
Program Definition eq_numTR (i : {trnum}) (j : {trnum}) : {trbool} :=
  match i, j with 
  | Num n, Num m => Nat.eqb n m  (* i have no idea why the string scope won't close *)
  | _r1, _r2 => False_rec _ _ 
  end.

Eval compute in eq_numTR 5 5.

(* lol i guess this is actually unit *)
Program Definition vec_setTR {n} 
  (x : {(trvec n)}) 
  (i : {t >> trnum & ((less_than_equal 0 t) /\ (less_than t n)) & True}) : {trvoid} := 
  void.



