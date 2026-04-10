Set Warnings "-uniform-inheritance".
Set Warnings "-ambiguous-paths".
Set Warnings "-meta-collision".
From TRresearch.Tactics Require Import Tactic_jail.
From TRresearch Require Import Definitions.
From TRresearch Require Import StandardFunctions.
From Stdlib Require Import Strings.String.
From Stdlib Require Bool.
From Stdlib Require Import Lia.
From Corelib Require Import Program.Tactics.
#[local] Obligation Tactic := try fail.

(* "organized from here to" *)
Ltac rewrite_jail' := 
  match goal with 
  | [ H : ?r = ?x |- _ ] => (rewrite H in *) + (rewrite <- H in *) ; clear H
  | _ => fail "rewrite_jail' match fail"
  end.

Create HintDb TRHints.

Hint Extern 0 => discriminates : TRHints.
Hint Extern 0 => subst_filtered_var : TRHints.
Hint Extern 0 => simpl_func : TRHints.
Hint Extern 0 => rewrite_jail' : TRHints.
Hint Constructors HasType : TRHints.

(* from crush *)
Definition done (T : Type) (x : T) := True.

Ltac instantiate' T e trace := 
  match goal with 
  | [ H : T |- _ ] =>
    match trace with 
    | 1 => 
      match goal with 
      | [ H2 : done T H |- _ ] => fail 2
      end
    | _ => 
      let S := fresh "S" in 
      let C := fresh "C" in 
        specialize (e H) as S; 
        assert (done T H) as C by constructor;
        instantiate' T e 1 
    end
  | _ => match trace with | 0 => fail 1 | _ => clear e end
  end.

Ltac undone := 
  match goal with 
  | [ H : done _ _ |- _ ] => clear H 
  end.

Ltac spec := 
  match goal with 
  | [ H : forall x : ?T, _ |- _ ] => idtac "spec" H T; instantiate' T H 0
  end.

Ltac specify := 
  repeat spec; repeat undone.

Ltac subst_definition' := 
  match goal with 
  | [ def := _ |- _ ] =>
    match goal with 
    | [ H : context [ def ] |- _ ] => simpl in def; subst def
    | |- context [ def ] => simpl in def; subst def
    | _ => fail "no hypothesis uses " def
    end 
  | _ => fail "no definition"
  end.

Ltac match_union_type x y type := 
  tryif (constr_eq_strict x type) 
  then idtac type "is in union" 
  else (constr_eq_strict y type).

Ltac inv_trtype_choice t := 
  match t with 
  | trnum => inv_trnum_fast
  | trbool => inv_trbool_fast
  | trstr => inv_trstr_fast
  | trvec => inv_trvec_fast
  | trvoid => inv_trvoid_fast
  | trpair => inv_trpair_fast
  | trlist => inv_trlist_fast
  end.

Ltac inv_trtype_union H t1 t2 := 
  inversion H; try inv_trtype_choice t1; inv_trtype_choice t2.



Ltac check_union := 
  match goal with
  | H : HasType (Bool ?b) (trunion ?x ?y) |- _ =>  idtac "first" x "second" y; 
    tryif match_union_type x y trbool 
    then idtac "union is a match"
    else inv_trtype_union H x y
  | H : HasType (Str ?b) (trunion ?x ?y) |- _ => idtac "first" x "second" y; 
    tryif match_union_type x y trstr 
    then idtac "union is a match"
    else inv_trtype_union H x y
  | H : HasType (Num ?b) (trunion ?x ?y) |- _ => idtac "first" x "second" y; 
    tryif match_union_type x y trnum 
    then idtac "union is a match"
    else inv_trtype_union H x y
  | H : HasType (Vec _ ?b) (trunion ?x ?y) |- _ => idtac "first" x "second" y; 
    tryif match_union_type x y trvec 
    then idtac "union is a match"
    else inv_trtype_union H x y
  | H : HasType (List ?l) (trunion ?x ?y) |- _ => idtac "first" x "second" y; 
    tryif match_union_type x y trlist 
    then idtac "union is a match"
    else inv_trtype_union H x y
  | H : HasType (Void ?v) (trunion ?x ?y) |- _ =>  idtac "first" x "second" y; 
    tryif match_union_type x y trvoid 
    then idtac "union is a match"
    else inv_trtype_union H x y
  | H : HasType (Pair ?a ?b) (trunion ?x ?y) |- _ => idtac "first" x "second" y; 
    tryif match_union_type x y trpair 
    then idtac "union is a match"
    else inv_trtype_union H x y
  end. 

Ltac check_union_false := 
  match goal with 
  | [H : HasType ?x (trunion ?t1 ?t2) |- _ ] => 
    tryif (constr_eq_strict t1 trtop)
    then fail "union is top"
    else tryif (constr_eq_strict t2 trtop)
         then fail "union is top"
         else check_union
  end.

Ltac solve_union := 
  match goal with 
  | [ H : ~  ?Maybe |- _ ] => destruct H; trivial with TRHints; fail
  | [ H : HasType ?x (trunion ?T1 ?T2) |- _ ] => repeat (progress check_union)

  end.

Ltac destructTR_if_needed' := 
  match goal with 
  | [ x : TRValues |- _ ] => 
    match goal with 
    | [ H : HasType x _ |- _ ] => 
      match goal with 
      | |- False => idtac "goal is False" x; destruct x; try inv_trtype_false_faster; repeat (progress check_union)
      | |- context [ x ] => idtac "goal has " x; destruct x; try inv_trtype_false_faster; repeat (progress check_union) 
      end 
    | _ => fail "no HasType for " x " in destruct_TR"
    end
  end.

Definition hide (T : Type) (x : T) := True.

Ltac hide_definitions :=
  match goal with 
  | [ H := ?a : _ |- _ ] =>
    match goal with 
    | |- context [ H ] => idtac "didn't hide" H "as it's used in the goal"
    | [ H1 : context [ H ] |- _ ] => idtac "didn't hide" H "as it's used in" H1 
    | _ => 
      match type of H with 
      | ?A => let i := fresh "i" in (pose (i := a)); assert (hide A i) by constructor; subst i; clear H 
      end 
    end 
  end.

Ltac unfold_definitions H := 
  try unfold get_true_prop in H.

Ltac unfold_definitions_goal := 
  try unfold get_true_prop.

Ltac simpl_function_calls_hypothesis := 
  match goal with 
  | [ H : context[ [?x] ] |- _ ] => unfold_definitions H; simpl in H
  end.

Ltac simpl_function_calls_goal := 
  match goal with 
  | |- context[ [?x] ] => unfold_definitions_goal; simpl
  end.

Ltac rewrite_vec trace :=
  match goal with 
  | [ v1 : nat_vec ?n1 |- _ ] => idtac v1 "first";
    match goal with 
    | [ H : HasType (Vec _ v1) (trvec ?n2) |- _ ] => idtac H; 
      match goal with 
      | |- context [ n1 ] => 
        match goal with 
        | |- context [ n2 ] => 
          match trace with 
          | 0 => inversion H; 
                 let S := fresh "S" in 
                 assert (done (nat_vec n1) v1) by constructor; 
                 idtac v1 H "inverted"; rewrite_vec 1 
          | _ => 
            match goal with 
            | [ P : done (nat_vec n1) v1 |- _ ] => fail 3
            | _ => inversion H; 
                    let S := fresh "S" in 
                    assert (done (nat_vec n1) v1) by constructor; 
                    idtac v1 H "inverted"; rewrite_vec 1 
            end
          end
        end
      end 
    end 
  | _ => idtac trace
  end.

Ltac vec_inversion := 
  rewrite_vec 0.

Lemma false_is_trbool : HasType false trbool /\ (Bool false) = (Bool false).
Proof. repeat constructor. Qed.

Lemma true_is_trbool : HasType true trbool /\ (Bool true) <> (Bool false).
Proof. repeat constructor. intro. discriminates. Qed.

Ltac specialize_booleans := 
  match goal with 
  | [ H : HasType (Bool false) trbool /\ (Bool false) = (Bool false) -> _ |- _ ] => specialize (H false_is_trbool)
  | [ H : HasType (Bool true) trbool /\ (Bool true) <> (Bool false) -> _ |- _ ] => specialize (H true_is_trbool)
  end.

Ltac really_simple_start := 
  try intros; simpl;
  repeat subst_definition';
  repeat rewrite_jail';
  conclusion_jail;
  simplify_hypothesis; 
  auto with TRHints.

Ltac test_jail := 
  try (really_simple_start; fail);
  start_jail; 
  repeat (match goal with 
  | |- ~ _ => intro 
  | |- _ <> _ => intro
  end);
  repeat subst_definition';
  try (match goal with 
  | [ H : context [ trvec ] |- _ ] => repeat rewrite_jail'; vec_inversion
  end );
  try (match goal with 
  | |- (HasType _ _) /\ _ /\ _ => make_constructor
  end); auto with TRHints; 
  repeat (match goal with 
  | |- _ /\ _ => split 
  end); auto with TRHints; 
  repeat (match goal with 
  | [ H : _ /\ _ |- _ ] => destruct H 
  end);
  repeat (progress simpl_function_calls_hypothesis);
  repeat (progress destructTR_if_needed'); auto with TRHints;
  repeat hide_definitions;
  repeat (match goal with 
  | [ H : (HasType _ _) /\ _ -> True |- _ ] => clear H
  end);
  repeat (progress simpl_function_calls_hypothesis);
  repeat (progress simpl_function_calls_goal);
  try match goal with 
  | [ H : (HasType _ _) /\ _ -> True |- _ ] => fail 1
  | [ H : forall _:_, _ |- _ ] => specify 
  end; auto with TRHints;
  try match goal with 
  | [ H : (HasType _ _) \/ (HasType _ _) |- _ ] => destruct H; try inv_trtype_false_faster
  end;
  try rewrite_jail';
  try specialize_booleans;
  try solve_union; 
  auto with TRHints.
(* "organized until here" *)


(* "organized" *)  
#[local] Obligation Tactic := try test_jail.
Program Definition add1 (n : {trnum}) : {trnum} :=
   match n with
   | Num x => S x
   | _r => False_rec _ _
   end.

(* "organized" *)  
Program Definition sum (n : {trnum}) (m : {trnum}) : {trnum} :=
  match n, m with 
  | Num n', Num m' => n' + m' 
  | _r1, _r2 => False_rec _ _ 
  end.


(* "organized" *)  
Program Definition mult (n : {trnum}) (m : {trnum}) : {trnum} :=
  match n, m with 
  | Num n', Num m' => n' * m' 
  | _r1, _r2 => False_rec _ _ 
  end.


(* "organized" *)  
Program Definition sub (n : {trnum}) (m : {trnum}) : {trnum} :=
  match n, m with 
  | Num n', Num m' => n' - m' 
  | _r1, _r2 => False_rec _ _ 
  end.

(* "organized" *)  
#[local] Obligation Tactic := try fail.
Program Definition is_number {t : TRTypes} (x : {t}) : 
                  {>> trbool & (HasType x trnum)} :=
  match x with
  | Num n => Bool true
  | _r => Bool false
  end.
Solve All Obligations with test_jail.

(* "organized" *)
Program Definition is_string {t : TRTypes} (x : {t}) : 
                  {>> trbool & (HasType x trstr)} :=
  match x with
  | Str s => Bool true
  | _r => Bool false
  end.
Solve All Obligations with test_jail.
  
(* "organized" *)
Program Definition is_bool {t : TRTypes} (x : {t}) : 
                  {>> trbool & (HasType x trbool)} :=
  match x with
  | Bool b => Bool true
  | _r => Bool false
  end.
Solve All Obligations with test_jail.

(* "organized" *)
Lemma is_top : forall (x : TRValues), HasType x trtop.
Proof. intros; constructor. Qed.

(* "organized" *)
Lemma is_top_pair : forall (x y : TRValues), HasType (x , y) (U trtop trtop).
Proof. intros; repeat constructor. Qed.


Hint Immediate is_top : TRHints.
Hint Immediate is_top_pair : TRHints.

(* "organized" *)
Program Definition is_pair {t : TRTypes} (x : {t}) : 
  {>> trbool & (HasType x (trpair trtop trtop))} :=
  match x with
  | Pair a b => Bool true
  | _r => Bool false
  end.
Solve All Obligations with test_jail.



Hint Unfold get_true_prop : TRHints.

(* "organized" *)
Lemma pair_left : forall {A B : TRTypes} {l : TRValues} {a b :TRValues}, 
  (a, b) = l ->  HasType l (trpair A B) -> 
  HasType a A.
Proof. 
  intros. rewrite <- H in H0. inversion H0. 
  auto.
Defined.

(* "organized" *)
Lemma pair_right : forall {A B : TRTypes} {l : TRValues} {a b :TRValues}, 
  (a, b) = l ->  HasType l (trpair A B) -> 
  HasType b B.
Proof. 
  intros. rewrite <- H in H0. inversion H0. 
  auto.
Defined.

(* "organized" *)
Program Definition strlen (s : {trstr}) : {trnum} :=
  match s with
  | Str s => length s
  | _r => False_rec _ _
  end.
Solve All Obligations with test_jail.

(* "organized" *)
Lemma subsume : forall  {A} (P P' Q Q' : Prop),
  (P -> P') -> (Q -> Q') ->
  {>> A & P & Q} -> {>> (A) & P'  & Q'}.
Proof.
  intros.
  destruct H1 as [x [H2 [H3 H4]]].
  econstructor. 
  make_constructor; eauto.
Defined.

(************************************************************************)
(************************ IF AND OR WHAT SUBSUME ************************)

(* "organized" *)
Lemma subsume' : forall  A (P' P'' Q' Q'' : Prop), {>> (A) & P'' & Q''} -> {>> (A) & P' \/ P'' & Q' \/ Q''}.
Proof.
  intros. apply subsume with P'' Q''; auto.
Defined.

(* "organized" *)
Definition if_TR {A : TRTypes} {P P' Q Q' : Prop} 
                          (x : {t >> trbool & P & Q})                        
                          (y : P -> {t >> A & P' & Q'})
                          (z : Q -> {t >> A & P' & Q'}) : 
                          {t >> A & P' & Q'}. (* A union B *)
Proof. 
  destructTR x;
  destruct x;
  try destruct b; 
  try (apply y; apply x1; split; try (auto; discriminate); fail).
  apply z; apply x2; split; auto.
Defined.
(* "organized" *)
Lemma unionL : forall A B (P Q : Prop), {>> A & P & Q} -> {>> (U A B) & P & Q}.
Proof.
  intros.
  destructTR H.
  assert (HasType H (trunion A B) /\ (HasType H (trunion A B) /\ H <> Bool false -> P) /\ (HasType H (trunion A B) /\ H = Bool false -> Q)).
  -  repeat split; eauto with TRHints; intros; destruct H3; smarter_apply; split; auto.
  - exact (exist (fun t : TRValues => 
                    HasType t (trunion A B) /\ 
                    (HasType t (trunion A B) /\ t <> Bool false -> P) /\ 
                    (HasType t (trunion A B) /\ t = Bool false -> Q))
                 H
                 H3).
Defined.
(* "organized" *)
Lemma unionR : forall A B (P Q : Prop), {>> B & P & Q} -> {>> (U A B) & P & Q}.
Proof.
  intros.
  destructTR H.
  assert (HasType H (trunion A B) /\ (HasType H (trunion A B) /\ H <> Bool false -> P) /\ (HasType H (trunion A B) /\ H = Bool false -> Q)).
  -  repeat split; eauto with TRHints; intros; destruct H3; smarter_apply; split; auto.
  - exact (exist (fun t : TRValues => 
                    HasType t (trunion A B) /\ 
                    (HasType t (trunion A B) /\ t <> Bool false -> P) /\ 
                    (HasType t (trunion A B) /\ t = Bool false -> Q))
                 H
                 H3).
Defined.

Ltac idk_man := 
  match goal with 
  | [ b : bool |- _ ] => destruct b; (apply unionL; idk_man_part2 false; fail) + (apply unionR; idk_man_part2 true)
  | [ n : ?type |- _ ] =>  
      apply unionL; idk_man_part2 false
  end.
(* "organized" *)
Definition if_TR_union {A B : TRTypes} {P P' P'' Q Q' Q'' : Prop} 
                          (x : {>> trbool & P & Q})                        
                          (y : P -> {>> A & P' & Q'})
                          (z : Q -> {>> B & P'' & Q''}) : 
                          {>> (U A B) & (P' \/ P'') & (Q' \/ Q'')}.
Proof.
  destructTR x.
  destruct x; try idk_man.
  Defined.

Open Scope string_scope.
Eval compute in is_string "hi".
(* "organized" *)
Program Definition notTR {P Q : Prop} (x : {>> trbool & P & Q}) : {>> trbool & Q & P} :=
  match x with
  | Bool false => Bool true
  | _r => Bool false
  end.
Solve All Obligations with test_jail.


Hint Immediate pair_left : TRHints.
Hint Immediate pair_right : TRHints.

(* "organized" *)
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



Hint Unfold is_number : TRHints.
Print HintDb TRHints.
(* "organized" *)
Lemma is_number_returns_bool : forall {A : TRTypes} (x : {A}), 
  (proj1_sig (is_number x)) = Bool true \/ (proj1_sig (is_number x)) = Bool false.
Proof. intros. destructTR x. destruct x; eauto with TRHints. Qed.

(* "organized" *)
Lemma is_number_trbool : forall {A : TRTypes} {x : {A}},
  HasType (proj1_sig (is_number x)) trbool.
Proof. 
  intros. 
  assert (H : (proj1_sig (is_number x)) = Bool true \/ (proj1_sig (is_number x)) = Bool false) by (apply is_number_returns_bool).
  destruct H; rewrite_jail; auto with TRHints.
Qed. 
(* "organized" *)
Lemma is_string_returns_bool : forall {A : TRTypes} (x : {A}), 
  (proj1_sig (is_string x)) = Bool true \/ (proj1_sig (is_string x)) = Bool false.
Proof. intros. destructTR x. destruct x; eauto with TRHints. Qed.

(* "organized" *)
Lemma is_string_trbool : forall {A : TRTypes} {x : {A}},
  HasType (proj1_sig (is_string x)) trbool.
Proof. 
  intros. 
  assert (H : (proj1_sig (is_string x)) = Bool true \/ (proj1_sig (is_string x)) = Bool false) by (apply is_string_returns_bool).
  destruct H; rewrite_jail; auto with TRHints.
Qed. 


Hint Immediate is_number_trbool : TRHints.
Hint Immediate is_string_trbool : TRHints.

(* "organized" *)
Program Definition orTest {A : TRTypes} (x : {A}) : 
    {>> trbool & ((HasType x trnum) \/ (HasType x trstr))} :=
    orTR (is_number x) (is_string x).
Solve All Obligations with test_jail.

Hint Immediate is_number_trbool : TRHints.
Hint Immediate is_string_trbool : TRHints.


Print HintDb TRHints.

(* "organized" *)
Lemma is_string_trbool' : forall (x : TRValues) {A : TRTypes} 
  (J : (HasType x A) /\ ((HasType x A) /\ x <> Bool false -> True) /\ ((HasType x A) /\ x = Bool false -> True)),
  HasType (proj1_sig (is_string (exist (fun t : TRValues => (HasType t A) /\ 
                                        ((HasType t A) /\ t <> Bool false -> True) /\ 
                                        ((HasType t A) /\ t = Bool false -> True))
                                       x 
                                       J))) trbool.
Proof. intros. apply is_string_trbool. Qed.

Hint Immediate is_string_trbool' : TRHints.

(* "organized" *)
Lemma proj1_sig_is_string_true : forall  {A : TRTypes} (x : {A}),
  proj1_sig (is_string x) <> Bool false -> 
  HasType (proj1_sig x) trstr.
Proof. intros. test_jail. Qed.

(* "organized" *)  
Ltac apply_proj1_sig_is_string_true := 
  match goal with 
  | [ H : proj1_sig (is_string ?x) <> Bool false |- HasType (proj1_sig _) trstr] => apply proj1_sig_is_string_true; auto with TRHints 
  end.

Hint Extern 1 => apply_proj1_sig_is_string_true : TRHints.

(* "organized" *)
Lemma proj1_sig_is_string_false : forall  {A : TRTypes} (x : {A}),
  proj1_sig (is_string x) = Bool false -> 
  HasType (proj1_sig x) trstr -> 
  False.
Proof. intros. test_jail. Qed.

(* "organized" *)
Ltac apply_proj1_sig_is_string_false := 
  match goal with 
  | [ H : proj1_sig (is_string ?x) = Bool false |- False] => 
    match goal with 
    | [ H : HasType (proj1_sig x) trstr |- False ] => apply (proj1_sig_is_string_false x); auto with TRHints 
    end 
  end.

Hint Extern 1 => apply_proj1_sig_is_string_false : TRHints.

(* "organized" *)
Ltac unfold_get_true_prop_hypothesis :=
  match goal with 
  | [ H : context[ get_true_prop ] |- _ ] => unfold get_true_prop in H 
  end.

Hint Extern 0 => repeat (progress unfold_get_true_prop_hypothesis) : TRHints.

(* "organized" *)
Lemma proj1_sig_is_number_true : forall  {A : TRTypes} (x : {A}),
  proj1_sig (is_number x) <> Bool false -> 
  HasType (proj1_sig x) trnum.
Proof. intros. test_jail. Qed.

(* "organized" *)
Ltac apply_proj1_sig_is_number_true := 
  match goal with 
  | [ H : proj1_sig (is_number ?x) <> Bool false |- HasType (proj1_sig _) trnum] => apply proj1_sig_is_number_true; auto with TRHints 
  | [ H : ~ HasType (proj1_sig ?x) trnum |- _ ] => 
    match goal with 
    | [ H1 : proj1_sig (is_number x) <> Bool false |- _ ] => destruct H; apply proj1_sig_is_number_true; auto with TRHints 
    end
  end.

Hint Extern 1 => apply_proj1_sig_is_number_true : TRHints.

(* "organized" *)
Program Definition andTest {A B : TRTypes} (x : {A}) (y : {B}) :
  {>> trbool & ((HasType x trnum)  /\ (HasType y trstr))} :=
  andTR (is_number x) (is_string y).
Solve All Obligations with test_jail; new_jail.


(* "organized" *)
Lemma i_hate_my_life : forall (P P' P'' Q Q' Q'' : Prop) (t : TRTypes) (x : {>> trbool & P & Q } )
  (y : P -> {>> t & P' & Q'})
  (z : Q -> {>> t & P'' & Q''}),
  HasType (proj1_sig (if_TR_union x y z))
          t.
Proof. intros. destructTR x. destruct x; try inv_trtype_false_faster.
  simpl. destruct b; simpl.
  - destructTR y; simpl. apply y1.
  - destructTR z; simpl. apply z1.
Qed.

(* "organized" *)
Lemma i_hate_my_life_2 : forall (P P' P'' Q Q' Q'' : Prop) (t : TRTypes) 
  (x : {>> trbool & P & Q } )
  (y : P -> {>> t & P' & Q'})
  (z : Q -> {>> t & P'' & Q''}),
  HasType (proj1_sig (if_TR_union x y z))
          t.
Proof. intros. destructTR x. destruct x; try inv_trtype_false_faster.
  simpl. destruct b; simpl.
  - destructTR y; simpl. apply y1.
  - destructTR z; simpl. apply z1.
Qed.

(* "organized" *)
Program Definition ifTest_1 {t : TRTypes} (x : {t}) : {trnum} :=
  ifTR (is_number x) x 0.
Solve All Obligations with test_jail; new_jail.

(* "organized" *)
Lemma an_incredibly_specific_i_hate_my_life : forall {P P' P'' Q Q' Q'' : Prop} (x : {>> trbool & P & Q } )
  (y : {>> trnum & P' & Q'})
  (z : {>> trnum & P'' & Q''}), 
  (exists (n : nat), 
    (proj1_sig 
      (if_TR_union x 
                   (fun _ => y)
                   (fun _ => z))) 
      = 
      (Num n)).
Proof.
  intros. destructTR x. destruct x; try inv_trtype_false_faster.
  destruct b.
  - destructTR y; destruct y; try inv_trtype_false_faster. simpl. exists n; reflexivity.
  - destructTR z; destruct z; try inv_trtype_false_faster. simpl. exists n; reflexivity.
Qed.
(* "organized" *)
Lemma why_has_my_life_come_to_this : forall {A : TRTypes} (x : {A}),
  HasType (proj1_sig x) trnum -> 
  exists n : nat, proj1_sig x = Num n.
Proof. intros. destructTR x; destruct x; simpl in H; try inv_trtype_false_faster. exists n; reflexivity. Qed.

(* "organized" *)
Ltac destructTR_fresh x := 
  let a := fresh "x" in destruct x as [?a [?a [?a ?a]]].
(* "organized" *)
Ltac autoTR := 
  auto with TRHints.
(* "organized" *)
Ltac prove_if_TR_branches := 
  let rec solve_branch := idtac "solve-branch";
    match goal with 
    | [ x : {?A} |- context[ (if_TR_union _ _ _) ] ] => prove_if_TR_branches
    | [ x : {?A} |- HasType (proj1_sig _) ?type ] => idtac type "first";
      match goal with 
    | |- context [ x ] => idtac x;
        match goal with 
        | |- context[ let (_, _) := ?func ?op1 ?op2 in _] => idtac "new 1" func op1 op2;
          match type of (func op1 op2) with 
          | {type} => destruct (func op1 op2);
            match goal with 
            | [ x1 : _ /\ _ /\ _ |- _ ] => idtac x1; destruct x1 as [?x1 [?x1 ?x1]]; try autoTR; idtac "complete"
            end
          end
        | |- context[ let (_, _) := ?func ?op in _ ] => idtac "new 2" func op;
          match type of (func op) with 
          | {type} => destruct (func op);
            match goal with 
            | [ x1 : _ /\ _ /\ _ |- _ ] => idtac x1; destruct x1 as [?x1 [?x1 ?x1]]; try autoTR; idtac "complete"
            end
          end
        | |- context[ let (_, _) := x in _ ] => idtac x; destruct x;
          match goal with 
          | [ x1 : _ /\ _ /\ _ |- _ ] => idtac x1; destruct x1 as [?x1 [?x1 ?x1]]; try autoTR; idtac "complete"
          end
        end
      end
    end 
  in 
  match goal with 
  | [ x : {?A} |- context[ if_TR_union ?pred ?true_branch ?false_branch ] ] => idtac "matched";
    destructTR_fresh pred; (* destructs the predicate to get to the boolean *)
    match goal with 
    | [ H3 : HasType ?x1 trbool |- _ ] => idtac "boolean"; destruct x1; try inv_trtype_false_faster; (* actually gets the boolean *)
      match goal with 
      | [ b : bool |- _ ] => idtac "destruct boolean"; destruct b; simpl; (* destruct the boolean to get to the cases *)
        match goal with 
        | |- context[ true ] => idtac true_branch ; try solve_branch
        | |- context[ false ] => idtac false_branch; try solve_branch
        | |- HasType _ _ => autoTR
        end
      end
    end
  end.


Hint Extern 1 => prove_if_TR_branches : TRHints.

(* "organized" *)
Program Definition condTest {A B : TRTypes}
    (x : {A})
    (y : {B}) :
    {trnum} :=
  condTR [ (is_number x) (add1 x) ] 
         [ (is_string y) (strlen y) ]
         [ else 0 ].
Solve All Obligations with test_jail. (* on the edge *)


(* "organized" *)
Program Definition orTest2 {A : TRTypes} (x : {A}) : 
    {>> trbool & ((HasType x trnum) \/ (HasType x trstr))} :=
    orTR_2 (is_number x) (is_string x).
Solve All Obligations with test_jail. (* there's one obligation in here that's slow, but i'm tired *)
Eval compute in orTest2 5.

(* "organized" *)
Lemma eventually_i_will_make_this_better : forall {A B : TRTypes} {P Q : Prop} (x : {A}) (y : {B})
  (pred1 : (forall x : {A}, {>> trbool & P}))
  (pred2 : (forall x : {B}, {>> trbool & Q})),
  proj1_sig (andTR_2 (pred1 x) (pred2 y)) <> Bool false -> 
  P.
Proof. intros.
  destructTR_fresh (pred1 x). destruct x0; try inv_trtype_false_faster.
  destructTR_fresh (pred2 y). destruct x0; try inv_trtype_false_faster.
  destruct b; destruct b0; simpl in H; try (apply x2); try (apply x5); split; auto.
Qed.

(* "organized" *)
Program Definition andTest2 {A B : TRTypes} (x : {A}) (y : {B}) :
  {>> trbool & ((HasType x trnum)  /\ (HasType y trstr))} :=
  andTR_2 (is_number x) (is_string y).
  (* really_simple_start. eapply eventually_i_will_make_this_better. eapply H0. (* well another interesting problem indeed *) *)
  
Solve All Obligations with test_jail; new_jail. (* on the edge *)


Hint Immediate pair_left : TRHints.
Hint Immediate pair_right : TRHints.

(* "organized" *)
Lemma trpair_left : forall {a : TRValues} {A :TRTypes} (b : TRValues) (B : TRTypes), 
  HasType (a, b) (trpair A B) -> 
  HasType a A.
Proof.
  intros. inversion H; auto.
Qed.

(* "organized" *)
Lemma trpair_right : forall {b : TRValues} {B :TRTypes} (a : TRValues) (A : TRTypes), 
  HasType (a, b) (trpair A B) -> 
  HasType b B.
Proof.
  intros. inversion H; auto.
Qed.

(* "organized" *)
Ltac apply_trpair := 
  match goal with 
  | [ H : HasType (?a, ?b) (trpair ?A ?B) |- _ ] => idtac a b;
    match goal with 
    | |- HasType a A => apply (trpair_left b B); autoTR 
    | |- HasType b B => apply (trpair_right a A); autoTR 
    end 
  end.

Hint Extern 1 => apply_trpair : TRHints.

(* "organized" *)
Program Definition car {A B : TRTypes} (l : {(trpair A B)}) : {A} :=
  match l with
  | Pair a b => a
  | _r => False_rec _ _
  end.  
Solve All Obligations with test_jail.

(* "organized" *)
Program Definition cdr {X Y : Prop} {A B : TRTypes} (l : {>> (trpair A B) & X & Y}) : {B} :=
  match l with
  | Pair a b => b
  | _r => False_rec _ _
  end.
Solve All Obligations with test_jail.




(* "organized up to" *)
Program Definition leTR (x : { trnum }) (y : { trnum }) : Prop :=
  match x, y with
  | Num n, Num m => n <= m
  | _r, _r2 => False
  end.
Solve All Obligations with test_jail; new_jail.

Inductive less_than_equal : TRValues -> TRValues -> Prop :=
  | valid_le : forall (n m : nat), leTR (Num n) (Num m) -> less_than_equal (Num n) (Num m).

Program Definition ltTR (x : { trnum }) (y : { trnum }) : Prop :=
  match x, y with
  | Num n, Num m => n < m
  | _r, _r2 => False
  end.
Solve All Obligations with test_jail; new_jail.

Inductive less_than : TRValues -> TRValues -> Prop :=
  | valid_lt : forall (n m : nat), ltTR (Num n) (Num m) -> less_than (Num n) (Num m).

(* this one too *)
Close Scope string_scope.
Program Definition ltTR_B (x : { trnum }) (y : { trnum }) : {trbool} :=
  match x, y with
  | Num n, Num m => Nat.ltb n m
  | _r, _r2 => False_rec _ _
  end.
Solve All Obligations with test_jail; new_jail.

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
(* "organized here" *)

(* "organized" *)
Program Definition wf_id (n : {trnum}) : nat := 
  match n with 
  | Num n' => n'
  | _r => False_rec _ _
  end.
Solve All Obligations with test_jail; new_jail.

(* "organized" *)
Lemma wf_ltTR : well_founded ltTR.
Proof. 
  eapply (Wf_nat.well_founded_lt_compat _ wf_id). 
  intros; destruct2 x; destruct2 y.
  destruct x; try inv_trtype_false_faster_2. destruct y; try inv_trtype_false_faster_2. 
  unfold ltTR in H; simpl in H. unfold wf_id; simpl. auto.
Defined.


(* "organized all below " *)
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



Program Definition append_tr {n m} (x : { (trvec n) }) (y : { (trvec m) }) : { (trvec (n + m)) } :=
  match x, y with 
  | Vec a v1, Vec b v2  => (Vec (n + m) (append_vec v1 v2))
  | _r1, _r2 => False_rec _ _
  end.
Solve All Obligations with test_jail; new_jail.

Program Definition head_tr {n} (x : { (trvec (S n)) }) : { trnum } :=
  match x with 
  | Vec a v => head_vec n v
  | _r => False_rec _ _
  end.
Solve All Obligations with test_jail; new_jail.

Program Definition tail_tr {n} (x : {(trvec (S n))}) : {(trvec n)} :=
  match x with 
  | Vec a v => tail_vec n v
  | _r => False_rec _ _
  end.
Solve All Obligations with test_jail; new_jail.

Program Definition tr_length {n} (x : { (trvec n) }) : { trnum } := n.

(* "organized" *)
Program Definition eq_numTR (i : {trnum}) (j : {trnum}) : {trbool} :=
  match i, j with 
  | Num n, Num m => Nat.eqb n m  (* i have no idea why the string scope won't close *)
  | _r1, _r2 => False_rec _ _ 
  end.
Solve All Obligations with test_jail; new_jail.

(* lol i guess this is actually unit *)
(* "organized" *)
Program Definition vec_setTR {n} 
  (x : {(trvec n)}) 
  (i : {t >> trnum & ((less_than_equal 0 t) /\ (less_than t n)) & True}) : {trvoid} := 
  void.




(* "organized" *)
Program Definition if_ex1 {t : TRTypes} (x : {t}) : {trnum}:=
  ifTR (is_number x) (add1 x) 0.
Solve All Obligations with test_jail; new_jail. 


(* "organized" *)
Ltac union_input := 
  match goal with 
  | [ H : HasType ?val (trunion ?t1 ?t2) |- _ ] =>
    match goal with 
    | [ H1 : ~(HasType (proj1_sig [val]) t1) |- (HasType (proj1_sig [val]) t2) ] => inversion H; auto; destruct H1; trivial with TRHints
    | [ H1 : ~(HasType (proj1_sig [val]) t2) |- (HasType (proj1_sig [val]) t1) ] => inversion H; auto; destruct H1; trivial with TRHints
    end
  end.

Hint Extern 1 => union_input : TRHints.


(* "organized" *)
Program Definition if_ex2 (x : {(U trstr trnum)}) : {trnum} :=
  ifTR (is_number x) (add1 x) (strlen x).
Solve All Obligations with test_jail; new_jail.
(* "organized" *)
Program Definition if_exWhat (x : {(U trstr trnum)}) : {trnum} :=
  ifTR (is_number x) (add1 x) 4.
Solve All Obligations with test_jail; new_jail.

(* i already proved these above lol
Lemma if_string_then_trstr : forall {A : TRTypes} (x : {A}), 
  (proj1_sig (is_string x)) <> Bool false -> HasType (proj1_sig x) trstr.
Proof.
  small_jail. destruct x; simpl in H; try discriminates. constructor. 
Qed.

Lemma if_not_string_then_not_trstr : forall {A : TRTypes} (x : {A}), 
  (proj1_sig (is_string x)) = Bool false -> ~ (HasType (proj1_sig x) trstr).
Proof.
small_jail. destruct x; simpl in H0; try inv_trtype_false_faster_2.
simpl in H; discriminates.
Qed.

*)

(* "do i actually need this?" *)
Ltac prove_if_TR_not_union_branches := 
  match goal with 
  | [ x : {?t} |- HasType (proj1_sig (if_TR ?pred ?true_branch ?false_branch)) ?type ] => 
    match goal with 
    | |- context [ x ] (* ensures x is actually used in the goal *) => 
      destructTR x; destruct x; simpl; autoTR
    end 
  end.

Hint Extern 1 => prove_if_TR_not_union_branches : TRHints.

(* already did this
Program Definition if_orTest2 {t : TRTypes} (x : {t}) : {trbool} :=
  orTR (is_number x) (is_string x).
Next Obligation. intros. exact trbool. Defined.
Solve All Obligations with test_jail.
*)

(* "organized" *)
Program Definition if_ex4 {t : TRTypes} (x : {t}) : {trnum} :=
  ifTR
       (orTR (is_number x) (is_string x))
       (if_exWhat x)
       0.
Solve All Obligations with test_jail.

(* Hint Immediate if_string_then_trstr : TRHints.

Lemma if_num_then_trnum : forall {A : TRTypes} (x : {A}), 
  (proj1_sig (is_number x)) <> Bool false -> (HasType (proj1_sig x) trnum).
Proof.
small_jail. destruct x; simpl in H; try discriminates. constructor. 
Qed.

Lemma if_not_num_then_not_trnum : forall {A : TRTypes} (x : {A}), 
  (proj1_sig (is_number x)) = Bool false -> ~ (HasType (proj1_sig x) trnum).
Proof.
small_jail. destruct x; simpl in H0; try inv_trtype_false_faster_2.
simpl in H; discriminates.
Qed.

Hint Immediate if_num_then_trnum : TRHints.
Hint Immediate if_not_num_then_not_trnum : TRHints.
*)

Lemma is_num_not_trnum : forall {t} (x : {t}), 
  proj1_sig (is_number x) <> Bool false -> 
  get_true_prop (is_number x). 
Proof. 
  test_jail.
Qed.

Lemma if_branches_num : forall (x : bool) {P Q : Prop}
  (J : (HasType (Bool x) trbool) /\ ((HasType (Bool x) trbool) /\ (Bool x) <> Bool false -> P) /\ ((HasType (Bool x) trbool) /\ (Bool x) = Bool false -> Q))                     
  (y : P -> {>> trnum & True & True})
  (z : Q -> {>> trnum & True & True}),
  HasType (proj1_sig (if_TR_union 
                            (exist (fun t : TRValues => (HasType t trbool) /\ 
                                        ((HasType t trbool) /\ t <> Bool false -> P) /\ 
                                        ((HasType t trbool) /\ t = Bool false -> Q))
                                       (Bool x) 
                                       J)
                            y 
                            z)) 
            trnum.
Proof. start_jail. destruct x; destruct2 J.
  - simpl. destruct y. destruct2 a. simpl. auto.
  - simpl. destruct z; destruct2 a; simpl; auto.
Qed.

Ltac apply_if_branches_num :=
  match goal with 
  | |- HasType (proj1_sig (if_TR_union _ _ _)) trnum => idtac "Hello"; try apply if_branches_num
  end.
    
Ltac apply_is_num_not_trnum :=
  match goal with 
  | [ H : proj1_sig (is_number ?x) <> Bool false |- get_true_prop (is_number ?x) ] => apply is_num_not_trnum; auto with TRHints
  | [ H : ~ get_true_prop (is_number ?x) , H1 : proj1_sig (is_number ?x) <> Bool false |- _ ] => destruct H; apply is_num_not_trnum; auto with TRHints
  end.

Hint Extern 1 => apply_is_num_not_trnum : TRHints.

Lemma andTR_eval' : forall{P P'}
  (x : {>> trbool & P})
  (y : {>> trbool & P'}),
  {>> trbool & (P /\ P')}.
Proof. intros.
  assert (
    J : HasType (proj1_sig (ifTR x y x)) trbool /\
        (HasType (proj1_sig (ifTR x y x)) trbool /\ (proj1_sig (ifTR x y x)) <> Bool false -> P /\ P') /\
        (HasType (proj1_sig (ifTR x y x)) trbool /\ (proj1_sig (ifTR x y x)) = Bool false -> ~(P /\ P'))
  ).
  - repeat split.
    + test_jail; destruct b0; simpl; auto with TRHints.
    + destructTR x. apply x1. split; auto with TRHints.
      destruct H.
      destruct x; try inv_trtype_false_faster. 
      simpl in H0; destruct b; try discriminates. simpl in H0; auto.
    + destructTR y; apply y1; split; auto.
      destruct H.
      destruct y; try inv_trtype_false_faster.
      destructTR x; destruct x; try inv_trtype_false_faster.
      simpl in H. destruct b0; simpl in H0; try discriminates. auto.
    + intro. intro. destruct H0.
      test_jail.
      destruct b0; simpl in H2; simpl in H.
      apply y2; try split; auto with TRHints.
      apply x2; try split; auto with TRHints.
  - exact (
      exist (fun t => HasType t trbool /\
                     (HasType t trbool /\ t <> false -> P /\ P') /\ 
                     (HasType t trbool /\ t = false -> ~ (P /\ P')))
            (proj1_sig (ifTR x y x))
            J
  ).
Qed.


Notation " 'andTR_2_again' A B " :=
  (let P := get_true_prop A in
   let P2 := get_true_prop B in
   let P' := P /\ P2 in 
    (@if_TR_union trbool trbool P P' P' (~ P) (~ P') (~ P') A (fun _ => B) (fun _ => A)))
  (at level 10, A at next level, B at next level).

Notation " 'ifTR_again' A B C " := 
  (let P := get_true_prop A in 
   let Q := get_false_prop A in 
  (@if_TR_union _ _ P _ _ Q _ _ A (fun _ => B) (fun _ => C)))
  (at level 0, A at next level, B at next level, C at next level). 


Lemma trying_to_test : forall {t t2 P Q} (x : {>> trbool & P & Q}) (y : {t}) (z : {t2}), 
  HasType (proj1_sig (if_TR_union x (fun H : P => y) (fun _ => z))) trnum -> HasType (proj1_sig (if_TR_union x (fun _ => y) (fun _ => z))) trnum.
Proof. auto. Qed.

(* not fine *)
(* "organized" *)
Program Definition if_ex5 {t r : TRTypes} (x : {t}) (y : {r}) : {trnum} :=
  ifTR (andTR (is_number x) (is_string y))
           (sum x (strlen y)) 
           0.
Solve All Obligations with test_jail.

(* "organized" *)
Program Definition if_ex10 {A B : TRTypes} (p : {(trpair A B)}) : {trnum} :=
  ifTR (is_number (car p)) (add1 (car p)) 7.
Solve All Obligations with test_jail.

(* "organized" *)
Program Definition if_more_ex3_1 {t : TRTypes} (x : {t}) : {trnum} :=
  ifTR (is_number x) x 54.
Solve All Obligations with test_jail.

(* lmao quite bad now *)
(* "organized" *)
Program Definition if_more_ex1 {t r : TRTypes} (x : {t}) (y : {r}) 
         : {t >> trbool & 
                 ((HasType x trnum) /\ (HasType y trstr) \/ (HasType x trstr))} :=
  (ifTR < all > (is_number x) (is_string y) (is_string x)).
Solve All Obligations with test_jail; new_jail.

(* "organized" *)
Ltac P_and_not_P :=
  match goal with 
  | [ H1 : ~ ?P |- _ ] => 
    match goal with 
    | [ H : ?P |- _ ] => destruct H1; auto 
    end
  | [ H1 : ~ (?P1 /\ ?P2) |- _ ] => 
    match goal with 
    | [ H : P1 , H2 : P2 |- _ ] => destruct H1; split; auto
    end
  end.

Hint Extern 1 => P_and_not_P : TRHints.

(* not fine *)
Program Definition if_more_ex3 {t r : TRTypes} (x : {t}) (y : {r}) : {trnum} :=
(ifTR (if_more_ex1 x y) 
  (ifTR (is_string x) (strlen x) (sum x (strlen y)))
  (ifTR (is_number x) x 54)).
Solve All Obligations with test_jail.





Program Definition ex1 {t : TRTypes} (x : {t}) : {trnum}:=
  ifTR (is_number x) (add1 x) 0.
Solve All Obligations with test_jail.

(************************************************************************)
(********************** EXAMPLE 2 AHHHHHHHHHHHHHHH **********************)
Open Scope string.

Program Definition ex2 (x : {(U trstr trnum)}) : {trnum} :=
  ifTR (is_number x) (add1 x) (strlen x). 
Solve All Obligations with test_jail.

Program Definition ex2_test1 := ex2 <[ "hi" ]>.
Solve All Obligations with test_jail; new_jail.
Program Definition ex2_test2 := ex2 <[ 9 ]>. 
Solve All Obligations with test_jail; new_jail.

Eval compute in ex2_test1.
Eval compute in ex2_test2.

(************************************************************************)
(********************** EXAMPLE 4 AHHHHHHHHHHHHHHH **********************)

(* on the edge *)
Program Definition ex4 {t : TRTypes} (x : {t}) : {trnum} :=
  ifTR (orTR (is_number x) (is_string x))
       (ex2 x)
       0.
Solve All Obligations with test_jail.

Eval compute in ex4 9.
Eval compute in ex4 "hi".
Eval compute in ex4 true.

(************************************************************************)
(********************** EXAMPLE 5 AHHHHHHHHHHHHHHH **********************)

(* not fine *)
Program Definition ex5 {t r : TRTypes} (x : {t}) (y : {r}) : {trnum} :=
  ifTR  (andTR (is_number x) (is_string y))
           (sum x (strlen y))
           0.
Solve All Obligations with test_jail.


Eval compute in ex5 5 "hi".
Eval compute in ex5 5 8.
Eval compute in ex5 "hello" 10.
Eval compute in ex5 true false.

(************************************************************************)
(********************** EXAMPLE 7 AHHHHHHHHHHHHHHH **********************)

(* on the edge *)
Program Definition ex7 {t r : TRTypes} (x : {t}) (y : {r}) : {trnum} :=
  (ifTR 
    (ifTR < second > (is_number x) (is_string y) false)
    (sum x (strlen y))
    0).
Solve All Obligations with test_jail.

Eval compute in ex7 6 "hello".

(************************************************************************)
(********************** EXAMPLE 8 AHHHHHHHHHHHHHHH **********************)

Program Definition ex8 {t : TRTypes} (x : {t}) :=
  orTest x.

Program Definition ex8_test {t : TRTypes} (x : {t}) : {trnum} :=
  (ifTR (ex8 x) (ex2 x) 0).
Solve All Obligations with test_jail.

Eval compute in ex8 6.
Eval compute in ex8_test 6.
Eval compute in ex8 "potatoes".
Eval compute in ex8_test "potatoes".
Eval compute in ex8 true.
Eval compute in ex8_test true.

(************************************************************************)
(********************** EXAMPLE 9 AHHHHHHHHHHHHHHH **********************)

Program Definition ex9 {t : TRTypes} (x : {t}) : {trnum} :=
  (ifTR 
    (let p := (is_number x) in 
      (ifTR < third > p p (is_string x)))
    (ex2 x) 
    0).
Solve All Obligations with test_jail.

Eval compute in ex9 2.

(************************************************************************)
(********************** EXAMPLE 10 AHHHHHHHHHHHHHH **********************)

Program Definition ex10 {A B : TRTypes} (p : {(trpair A B)}) : {trnum} :=
  ifTR (is_number (car p)) (add1 (car p)) 7.
Solve All Obligations with test_jail.

Eval compute in ex10 (5, "bye").
Eval compute in ex10 (false, 10).

(************************************************************************)
(********************** EXAMPLE 11 AHHHHHHHHHHHHHH **********************)

Program Definition g (p : {trpair trnum trnum}) : {trnum} :=
  (sum (car p) (cdr p)).
Solve All Obligations with test_jail.

Eval compute in g (4, 5). 

Lemma is_number_trbool' : forall (x : TRValues) {A : TRTypes} 
  (J : (HasType x A) /\ ((HasType x A) /\ x <> Bool false -> True) /\ ((HasType x A) /\ x = Bool false -> True)),
  HasType (proj1_sig (is_number (exist (fun t : TRValues => (HasType t A) /\ 
                                        ((HasType t A) /\ t <> Bool false -> True) /\ 
                                        ((HasType t A) /\ t = Bool false -> True))
                                       x 
                                       J))) trbool.
Proof. intros. apply is_number_trbool. Qed.

Hint Immediate is_number_trbool' : TRHints.

Print HintDb TRHints.

Ltac apply_is_number_lemmas :=
  match goal with 
  | |- HasType (proj1_sig (is_number _)) trbool => idtac "Hi"; try apply is_number_trbool; try apply is_number_trbool' 
  end.

Hint Extern 3 => apply_is_number_lemmas : TRHints.
Hint Extern 0 => progress simpl : TRHints.

Lemma is_num_false_trnum : forall {t} (x : {t}),
  proj1_sig (is_number x) = Bool false -> 
  get_true_prop (is_number x) -> 
  False.
Proof. test_jail. Qed.

Ltac apply_is_num_false_trnum := 
  match goal with 
  | [ H : proj1_sig (is_number ?x) = Bool false, H1 : get_true_prop (is_number ?x) |- _ ] => 
      try (exfalso; eapply is_num_false_trnum; eauto with TRHints; fail)
  end.

Hint Extern 1 => apply_is_num_false_trnum : TRHints.
(* oof this takes a while *)
(* not fine *)
Program Definition ex11 {A B : TRTypes} (p : {trpair A B}) : {trnum} :=
  ifTR (andTR (is_number (car p)) (is_number (cdr p))) (g p) 0.
Solve All Obligations with test_jail.



Eval compute in ex11 (4, 12).
Eval compute in ex11 (3, false).

(************************************************************************)
(********************** EXAMPLE 12 AHHHHHHHHHHHHHH **********************)

Ltac car_pred_true_type := 
  match goal with 
  | [ H : proj1_sig (?pred (car ?val)) <> Bool false |- _ ] => idtac pred val;
    match type of pred with 
    | (forall x : ?A, { t : TRValues | _ /\ (_ /\ _ -> HasType ?v ?type ) /\ _ }) => idtac type; destructTR_fresh (pred (car val));
      match goal with 
      | [ H1 : {trpair ?A ?B} |- HasType (proj1_sig val) (trpair type ?B) ] => idtac val type; 
        destructTR H1; 
          match goal with 
          | [ H2 : HasType ?a (trpair A B) |- _ ] => destruct a; try inv_trtype_false_faster; constructor; autoTR
          end
      end
    end
  end.

Ltac car_pred_false_False := 
  match goal with 
  | [ H : proj1_sig (?pred (car ?val)) = Bool false |- _ ] => idtac "step 1" pred val;
    match type of pred with 
    | (forall x : ?A, { t : TRValues | _ /\ (_ /\ _ -> HasType ?v ?type ) /\ _ }) => idtac "step 2" type;
      match goal with 
      | [ H1 : HasType (proj1_sig val) (trpair type ?B) |- False ] => idtac "step 3" val; destruct (pred (car val)); idtac "done";
        match goal with 
        | [ H2 : _ /\ _ /\ _ |- _ ] => destruct2 H2; idtac val "here"; destructTR val; destruct val;  try inv_trtype_false_faster;
          inversion H1; subst *; idtac val;
          match goal with 
          | [ H3 : _ -> ~ (HasType (proj1_sig (car ?l)) type) |- _ ] => apply H3; autoTR
          end 
        end
      end 
    end
  end.

Hint Extern 1 => car_pred_true_type : TRHints.
Hint Extern 1 => car_pred_false_False : TRHints.

(* back to the scheduled programming *)
Program Definition ex12 {A B : TRTypes} (p : {trpair A B}) : 
  {t >> trbool & (HasType p (trpair trnum B))} :=
  (is_number (car p)).
Solve All Obligations with test_jail.
  
  
Program Definition ex12_again {A B : TRTypes} (p : {trpair A B}) : 
{t >> trbool & (HasType (car p) trnum)} :=
  (is_number (car p)).

Eval compute in ex12 (4, true).
Eval compute in ex12 ("hi", 1).

(* some extra programs to test my tactics *)
Program Definition ex12_string {A B : TRTypes} (p : {trpair A B}) : 
  {t >> trbool & (HasType p (trpair trstr B))} :=
  (is_string (car p)).
Solve All Obligations with test_jail.

Check is_bool.

Lemma pred_returns_bool : forall {A : TRTypes} (type :TRTypes)
  (x : {A}) (pred : forall x : {A}, {>> trbool & (HasType (proj1_sig x) type)})
  , HasType (proj1_sig (pred x)) trbool.
Proof. intros. destructTR_fresh (pred x). auto. Qed.



Program Definition ex12_boolean {A B : TRTypes} (p : {trpair A B}) : 
  {t >> trbool & (HasType p (trpair trbool B))} :=
  (is_bool (car p)).
Next Obligation.
  intros; simpl; repeat split. apply pred_returns_bool.
  really_simple_start.
  really_simple_start.
  
Solve All Obligations with test_jail. 

(************************************************************************)
(********************** MORE EXAMPLES AHHHHHHHHHHH **********************)

(*
(* on the edge , same thing as above? *)
Program Definition more_ex1 {t r : TRTypes} (x : {t}) (y : {r}) 
         : {t >> trbool & ((HasType x trnum) /\ (HasType y trstr) \/ (HasType x trstr))} :=
  (ifTR < all > (is_number x) (is_string y) (is_string x)).
Next Obligation.
  test_jail.
Solve All Obligations with test_jail; new_jail. 

Program Definition more_ex1_use := more_ex1 5 "hello".
Solve All Obligations with test_jail; new_jail.
Eval compute in more_ex1_use.  *)

(* on the edge *)
Program Definition more_ex2 {t r : TRTypes} (x : {t}) (y : {r}) : {trnum} :=
  (ifTR (if_more_ex1 x y) 
    (ifTR (is_string x) (strlen x) (sum x (strlen y)))
    42).
Solve All Obligations with test_jail.

(* not fine, but individually it solves all the goals fast? *)
Program Definition more_ex3 {t r : TRTypes} (x : {t}) (y : {r}) : {trnum} :=
  (ifTR (if_more_ex1 x y) 
    (ifTR (is_string x) (strlen x) (sum x (strlen y)))
    (ifTR (is_number x) (add1 x) 54)). 
Solve All Obligations with test_jail.


(************************************************************************)
(********************** EXAMPLES NOT AHHHHHHHHHHHHHHH *******************)
Program Definition not_ex1 {t : TRTypes} (x : {t}) : {trnum} :=
  (ifTR (notTR (notTR (is_number x))) (add1 x) 42).
Solve All Obligations with test_jail.

Eval compute in (not_ex1 5).
Eval compute in (not_ex1 "hi").

Program Definition not_ex2 {t : TRTypes} (x : {t}) : {trnum} :=
  (ifTR (notTR (is_number x)) 
      (ifTR (is_string x) (strlen x) 13)
      42).
Solve All Obligations with test_jail.

Eval compute in (not_ex2 5).
Eval compute in (not_ex2 "hi").
Eval compute in (not_ex2 true).

(************************************************************************)
(****************** LET EXAMPLES???????????????? AHHHHHHHH **************)

Hint Extern 3 => apply_if_branches_num : TRHints.

Program Definition let_ex1 {t : TRTypes} (x : {t}) : {trnum} :=
  let p := (is_number x) in
    (ifTR p (add1 x) 0).
Solve All Obligations with test_jail.

Program Definition car_add {t r : TRTypes} (p : {(trpair t r)}) : {trnum} :=
(ifTR (is_number (car p)) (add1 (car p)) 0).
Solve All Obligations with test_jail.

Eval compute in (car_add ("hi", 9)).
Eval compute in (car_add (18, 4)).

(* just write your own lol *)
Program Definition pos_success {t : TRTypes} (x : {t}) : {trtop} :=
  (ifTR (is_string x) (strlen x) x).
Solve All Obligations with test_jail.
Eval compute in (pos_success "potatoes").
Eval compute in (pos_success 8).
Eval compute in (pos_success true).
Eval compute in (pos_success ("hi", false)).

Program Definition neg_success (x : {U trstr trnum}) : {trnum} :=
  (ifTR (is_string x) (strlen x) (add1 x)).
Solve All Obligations with test_jail.

Program Definition neg_succ_test1 := (neg_success <["hi"]>).
Solve All Obligations with test_jail; new_jail.
Program Definition neg_succ_test2 := (neg_success <[7]>).
Solve All Obligations with test_jail; new_jail.

Eval compute in neg_succ_test1.
Eval compute in neg_succ_test2.

Program Definition is_strnum {t : TRTypes} (x : {t}) : 
                  {t >> trbool & ((HasType x trstr) \/ (HasType x trnum))} :=
  (orTR (is_string x) (is_number x)).
Solve All Obligations with test_jail.

Program Definition f (x : {U trstr trnum}) : {trnum} :=
  ifTR (is_number x) (add1 x) (strlen x).
Solve All Obligations with test_jail.

Program Definition g2 (x : {trtop}) : {trnum} :=
  ifTR (is_strnum x)
       (f x)
       0.
Solve All Obligations with test_jail.

Program Definition g2_test1 := g2 <[5]>.
Solve All Obligations with test_jail; new_jail.
Program Definition g2_test2 := g2 <["potatoes"]>.
Solve All Obligations with test_jail; new_jail.
Program Definition g2_test3 := g2 <[false]>.
Solve All Obligations with test_jail; new_jail.

Lemma notTR_is_bool : forall {P Q} (x : {>> trbool & P & Q}), 
  HasType (proj1_sig (notTR x)) trbool.
Proof. test_jail. unfold notTR; simpl. destruct b; auto with TRHints. Qed.

Lemma notTR_bool_true_is_false : forall {t} (x : {t}),
  proj1_sig (notTR (is_bool x)) <> Bool false -> 
  HasType (proj1_sig x) trbool -> 
  False.
Proof. test_jail. Qed.

Lemma notTR_num_true_is_false : forall {t} (x : {t}),
  proj1_sig (notTR (is_number x)) <> Bool false -> 
  HasType (proj1_sig x) trnum -> 
  False.
Proof. test_jail. Qed.

Lemma notTR_bool_false_is_true : forall {t} (x : {t}),
  proj1_sig (notTR (is_bool x)) = Bool false -> 
  HasType (proj1_sig x) trbool.
Proof. test_jail. Qed.

Lemma notTR_num_false_is_true : forall {t} (x : {t}),
  proj1_sig (notTR (is_number x)) = Bool false -> 
  HasType (proj1_sig x) trnum.
Proof. test_jail. Qed.

Ltac apply_notTR_is_bool :=
  match goal with 
  | |- HasType (proj1_sig (notTR ?x)) trbool => apply notTR_is_bool
  end.

Ltac apply_notTR_bool_true_is_false := 
  match goal with 
  | [ H : proj1_sig (notTR (is_bool ?x)) <> Bool false |- _ ] => 
    match goal with 
    | |- get_true_prop (notTR (is_bool x)) => unfold get_true_prop; intro; eapply notTR_bool_true_is_false; eauto with TRHints 
    end 
  | [ H : proj1_sig (notTR (is_number ?x)) <> Bool false |- _ ] => 
    match goal with 
    | |- get_true_prop (notTR (is_number x)) => unfold get_true_prop; intro; eapply notTR_num_true_is_false; eauto with TRHints 
    end 
  end.

Ltac apply_notTR_bool_false_is_true := 
  match goal with 
  | [ H : proj1_sig (notTR (is_bool ?x)) = Bool false |- False ] => 
    match goal with 
    | [ H1 : get_true_prop (notTR (is_bool x)) |- _ ] => unfold get_true_prop in H1; destruct H1; eapply notTR_bool_false_is_true; eauto with TRHints
    end
  | [ H : proj1_sig (notTR (is_number ?x)) = Bool false |- False ] => 
    match goal with 
    | [ H1 : get_true_prop (notTR (is_number x)) |- _ ] => unfold get_true_prop in H1; destruct H1; eapply notTR_num_false_is_true; eauto with TRHints
    end
  end.

Hint Extern 1 => apply_notTR_is_bool : TRHints.
Hint Extern 1 => apply_notTR_bool_true_is_false : TRHints. 
Hint Extern 1 => apply_notTR_bool_false_is_true : TRHints.
Hint Unfold get_true_prop : TRHints.


(* "RESUME HERE!" *)


Lemma union_not_left : forall {A B} (x : {trunion A B}),
  ~ HasType (proj1_sig x) A -> 
  HasType (proj1_sig x) B.
Proof. test_jail. Qed.

Lemma union_not_right : forall {A B} (x : {trunion A B}),
  ~ HasType (proj1_sig x) B -> 
  HasType (proj1_sig x) A.
Proof. test_jail. Qed.
  
Lemma not_either_union : forall {t} {A B} (x : {t}),
  ~ HasType (proj1_sig x) A -> 
  ~ HasType (proj1_sig x) B -> 
  ~ HasType (proj1_sig x) U A B.
Proof. really_simple_start. inversion H1; 
  try (destruct H; auto; fail); try (destruct H0; auto).
Qed.

Ltac apply_not_either_union := 
  match goal with 
  | |- ~ HasType (proj1_sig ?x) U ?A ?B => try (eapply not_either_union; eauto with TRHints)
  end.

Ltac apply_union_not :=
  match goal with 
  | [ x : {trunion ?A ?B} |- _ ] => 
    match goal with 
    | |- HasType (proj1_sig x) A => eapply union_not_right; eauto with TRHints
    end 
  end.

Hint Extern 1 => apply_union_not : TRHints.
Hint Extern 1 => apply_not_either_union : TRHints.

(* not fine *)
(* "completed" *)
Program Definition h (x : {U trstr (U trnum trbool)}) : {trnum} :=
  ifTR (andTR (notTR (is_bool x)) (notTR (is_number x)))
          (strlen x)
          0.
Solve All Obligations with test_jail.


Lemma if_branches_num_not : forall {P Q : Prop}
  (x : {>> trbool & P & Q})
  (y : Q -> {>> trnum & True & True})
  (z : P -> {>> trnum & True & True}),
  HasType (proj1_sig (if_TR_union 
                            (notTR x)
                            y 
                            z)) 
            trnum.
Proof. start_jail. destruct x; try inv_trtype_false_faster. destruct b.
  - simpl. destruct z. destruct2 a. simpl. auto.
  - simpl. destruct y; destruct2 a; simpl; auto.
Qed.

Ltac apply_if_branches_num_not :=
  match goal with 
  | |- HasType (proj1_sig (if_TR_union (notTR _) _ _)) trnum => idtac "Good morning"; try apply if_branches_num_not
  end.


Ltac one_of_union_type :=
  let find_type x type := 
    match goal with 
    | [ H : HasType x (trunion ?type1 ?type2) |- HasType (proj1_sig [x]) type ] => 
      match goal with 
      | [ H2 : (done (HasType x (trunion type1 type2)) H) |- _ ] => fail 1 
      | _ => 
        inversion H; subst *;
        let J := fresh "J" in 
          assert (done (HasType x (trunion type1 type2)) H) as J by constructor
      end
    | [ H : ~ (HasType (proj1_sig [x]) ?type1) |- _ ] => simpl in H;
      match goal with 
      | [ H2 : HasType x type1 |- _ ] => P_and_not_P
      end
    | [ H : HasType x type |- _ ] => autoTR
    end
  in
  match goal with 
  | [ x : {trunion ?type1 ?type2} |- HasType ?val ?type ] =>
    destructTR x; repeat (progress find_type x type)
  end.

Hint Extern 1 => one_of_union_type : TRHints.

(* not fine *)
Program Definition f2 (x : {U trstr (U trnum trbool)}) : {trnum} :=
  ifTR (notTR (is_string x))
          (ifTR (notTR (is_bool x))
                   (add1 x)
                   0)
          0.
Solve All Obligations with test_jail.

(* todo : 
  - lemma for unions (aka go through the slow examples and see if you can write 
    lemmas for them
  - finish vector examples
  - reorganize
)*)


(* not fine *)
Program Definition ex13_14 
    (x : {U trnum trstr}) 
    (y : {trpair trtop trtop}) :
    {trnum} :=
  condTR [ (andTR (is_number x) (is_number (car y))) (sum x (car y)) ] 
         [ (is_number (car y)) (sum (strlen x) (car y)) ] 
         [ else 0].
Solve All Obligations with test_jail.


Program Definition make_ltTR (n1 : {trnum}) (n2 : {trnum}) (H : (ltTR n1 n2)) 
    : {t >> trnum & (ltTR n1 n2) & True} :=
  n1.
Solve All Obligations with test_jail.










(* "completed until here" *)

(* "organized" *)
Program Definition trvec_unsafe_ref_tr {n} (x : { (trvec n) }) (m : {trnum}) : option {trnum} :=
  match x with 
  | Vec a v => match m with 
                | Num m' => match vec_unsafe_ref v m' with 
                           | None => None 
                           | Some p => Some p 
                           end
                | _r2 => False_rec _ _
                end
  | _r1 => False_rec _ _
  end.
Solve All Obligations with test_jail.




(* "organized" *)
Ltac invert_equality := 
    match goal with 
    | [H : less_than _ _ |- _ ] =>
        let K1 := fresh "K" in 
        inversion H as [?n ?n K1]; unfold ltTR in K1; simpl in K1; subst *; clear H
    | [H : less_than_equal _ _ |- _ ] =>
        let K1 := fresh "K" in 
        inversion H as [?n ?n K1]; unfold leTR in K1; simpl in K1; subst *; clear H
    | [ H : leTR _ _ |- _ ] => unfold leTR in H; simpl in H
    | [ H : ltTR _ _ |- _ ] => unfold ltTR in H; simpl in H
    | _ => idtac "nothing else in invert_equality"
    end.


(* "organized" *)
Ltac get_props := 
match goal with 
| [H : HasType ?n ?type /\ ?n <> (Bool false) -> ?P |- _ ] => idtac H;
  match goal with 
  | [ H1 : done _ H |- _ ] => fail 1 
  | _ => 
    match goal with 
    | [ H : context [ less_than_equal ] |- _ ] => idtac "2";
    make_hypothesis_not_bool n type; 
        match goal with 
        | [H2 : HasType n type /\ n <> (Bool false) |- _ ] => idtac "3";
            let K := fresh "K" in 
            let C := fresh "C" in 
            specialize (H H2) as K; idtac "yes"; inversion K; idtac "here"; clear K;
            assert (done (HasType n type /\ n <> (Bool false) -> P) H) by constructor;
            repeat (progress invert_equality)
        end
    end
  end
end.

(* "organized" *)
Ltac unify_n_trvec := 
  match goal with 
  | [ v : nat_vec ?m |- _ ] => 
    match goal with 
    | [ H : HasType (Vec _ v) (trvec ?n) |- _ ] => 
      inversion H; subst *;
      match goal with 
      | [ H2 : existT _ _ _ = existT _ _ _ |- _ ] => clear H2
      end
    end 
  end.

  
Lemma nat_is_num : forall (n0 : nat), 
  HasType (Num n0) trnum /\
  (HasType (Num n0) trnum /\ (Num n0) <> Bool false -> True) /\
  (HasType (Num n0) trnum /\ (Num n0) = Bool false -> True).
Proof. auto with TRHints. Qed.


Lemma vec_unsafe_ref_none_false : 
  forall {n} 
  (x : { (trvec n) })
  (n0 : nat), 
  n0 < n -> 
  0 <= n0 -> 
  None = trvec_unsafe_ref_tr x (exist 
                                  (fun p => HasType p trnum /\ 
                                            ((HasType p trnum) /\ p <> Bool false -> True) /\
                                            ((HasType p trnum) /\ p = Bool false -> True)) 
                                  (Num n0) (nat_is_num n0)) 
  -> False.
Proof. intros.
  test_jail.
  unify_n_trvec.
  generalize dependent n0. 
  induction n2.
    - lia.
    - intros; induction n1. inversion H1. unfold trvec_unsafe_ref_tr in H1; simpl in *.
      assert (J2 : n1 < n) by lia. (* we need this bc the eapply/eauto will fill in the hole with the wrong thing *)
      eapply IHn2; eauto.  
      unfold leTR; simpl; lia.
      Unshelve. all : eauto; constructor.
Qed.

(* requires the trvec to not be destructed!! *)
Ltac apply_vec_unsafe_ref_none_false := 
  match goal with 
  | [ H : None = trvec_unsafe_ref_tr ?v ?x |- _ ] =>
    match x with 
    | [ Num ?n ] => apply (vec_unsafe_ref_none_false v n); auto;
                    destructTR v; destruct v; try inv_trtype_false_faster_2; auto
    end
  end. 

Ltac deal_with_none_trvec := 
  match goal with 
  | [ n : {_ : TRValues | _ /\ (_ /\ _ -> less_than_equal _ _ /\ _ ) /\ _} |- _ ] => 
      destructTR n; destruct n; try inv_trtype_false_faster_2; get_props;
      match goal with 
      | [ H : context[ [?n] ] |- _ ] => simpl in H; apply_vec_unsafe_ref_none_false
      end 
  end.

Ltac sometimes_things_need_to_be_fast_tracked := 
  match goal with 
  | |- context[ let filtered_var := trvec_unsafe_ref_tr _ _ in None = filtered_var -> _ ] => idtac "trvec_unsafe_ref_tr in goal";
      intros; subst_filtered_var; deal_with_none_trvec
  end.

Hint Extern 0 => sometimes_things_need_to_be_fast_tracked : TRHints.

Program Definition trvec_ref_tr {n} (x : { (trvec n) }) (m : {t >> trnum & ((less_than_equal 0 t) /\ (less_than t n)) & True}) : { trnum } :=
  match (trvec_unsafe_ref_tr x m) with 
  | Some p => p 
  | None => False_rec _ _
  end.
Solve All Obligations with auto with TRHints; test_jail.

Notation " 'trvec_ref' v n " := 
  (trvec_ref_tr v (make_ltTR n (tr_length v) _)) (at level 0, v at next level, n at next level).


From Corelib Require Import Program.Wf.


Hint Unfold leTR : TRHints.
Hint Unfold ltTR : TRHints.
Hint Constructors less_than_equal : TRHints.
Hint Constructors less_than : TRHints.
Hint Unfold tr_length : TRHints.
Hint Extern 1 (ltTR _ _) => repeat (progress get_props) : TRHints.
Hint Extern 1 (less_than_equal _ _) => repeat (progress get_props) : TRHints.
Hint Extern 2 => lia : TRHints.

Ltac destruct_nat := 
  match goal with 
  | [ H : forall n : nat, _ <> (Num ?m) |- False ] => idtac m;
    match goal with 
    | [ H2 : (Num 0) <> (Num m) |- False ] =>  idtac "there";
      destruct m; try spec; try discriminates
    end 
  end.

Hint Extern 2 => destruct_nat : TRHints.


(* "HERE" *)
Program Fixpoint vec_prod_TR {n} 
  (res : {trnum}) 
  (i : {t >> trnum & (less_than_equal t (Num n)) & True}) 
  (x : {trvec n}) 
  {measure (proj1_sig i) ltTR}
  : {trnum} :=
  match i with 
  | Num 0 => res 
  | Num (S i') => vec_prod_TR (mult res (trvec_ref x i')) (Num i') x
  | _r => False_rec _ _ 
  end.
Next Obligation.
  test_jail.
Defined. Next Obligation.
  test_jail. (* kinda bad *)
Defined. Next Obligation.
  test_jail. (* pretty bad *)
Defined. Next Obligation.
  test_jail. (* kinda bad *)
Defined. Next Obligation.
  test_jail.
Defined. Next Obligation.
  test_jail.
Defined. Next Obligation.
  test_jail.
Defined. Next Obligation.
  test_jail.
Defined. Next Obligation.
  test_jail.
Defined. Next Obligation.
  test_jail.
Defined. Next Obligation.
  test_jail.
Defined. Next Obligation.
  test_jail.
Defined.   (* one obligation here is the problem lmao *)
Next Obligation.
  apply measure_wf; apply wf_ltTR.
Defined.
  


Program Definition vec_product_tr_loop {n} 
  (x : {(trvec n)})
  (len : {t >> trnum & (less_than_equal t (Num n)) & ~(less_than_equal t (Num n))})
  (res : { trnum }) : {trnum} :=
  vec_prod_TR res len x.
Next Obligation. test_jail. Defined.

Program Definition vec_product_tr_new {n} (x : {(trvec n)}) : {trnum} :=
  match x with 
  | Vec m1 nv1 => 
    let loop := vec_product_tr_loop x in 
      let i := (tr_length x) in 
        let res := 1 in 
          loop i res
  | _r1 => False_rec _ _
  end.
Solve All Obligations with simpl; test_jail. 

Ltac destructB := 
  match goal with 
  | |- context[ Nat.eqb ?n1 ?n2 ] => destruct (Nat.eqb n1 n2)
  end.

Hint Extern 2 => destructB : TRHints.

Program Definition vec_swap_tr {n} 
  (x : {(trvec n)}) 
  (i : {t >> trnum & ((less_than_equal 0 t) /\ (less_than t n)) & True})
  (j : {t >> trnum & ((less_than_equal 0 t) /\ (less_than t n)) & True}) : {trvoid} :=
  ifTR (eq_numTR i j)
       void 
       (let i_val := (trvec_ref x i) in 
          let j_val := (trvec_ref x j) in 
            let swap1 := (vec_setTR x i) in 
              vec_setTR x j).
Solve All Obligations with test_jail.


Ltac solve_ltB := 
  match goal with 
  | [H : (Bool true) = (proj1_sig (ltTR_B _ _)) |- _ ] => 
    let P1 := fresh H in 
    let P2 := fresh H in 
    let P3 := fresh H in
    let P4 := fresh H in
      apply what_again_again_TR in H as P1; apply what_again_TR in H as P2; apply what_again_again_again_TR in H as P3; 
      try clear H
  end.

Ltac less_than_equal_0 :=
  match goal with 
  | |- less_than_equal (Num 0) (Num ?n) => apply (less_than_0 n)
  end.

Ltac immediate_TR := 
  match goal with 
  | [ x : {t : _ | HasType t ?type /\ _ /\ _} |- _ ] => 
    match goal with 
    | |- HasType (proj1_sig x) trnum => destructTR x; autoTR 
    end 
  | [ x : HasType ?v ?type /\ _ /\ _ |- _ ] => 
    match goal with 
    | |- HasType (proj1_sig [v]) type => destruct2 x; autoTR
    end
  end.

Ltac destruct_application :=
  match goal with 
  | |- HasType (proj1_sig (?func ?op1)) ?type => destruct (func op1)
  | |- HasType (proj1_sig (?func ?op1 ?op2)) ?type => destruct (func op1 op2)
  end.

Hint Extern 1 => destruct_application : TRHints.

Hint Extern 1 => immediate_TR : TRHints.

Hint Unfold tr_length : TRHints.
Hint Unfold ltTR : TRHints.


Ltac ltTR_goal := 
  match goal with 
  | [ H : Bool true = proj1_sig (ltTR_B [proj1_sig ?x] ?n) |- ltTR [proj1_sig ?x] ?n] => 
    match goal with 
    | [ x : {t : TRValues | ?P} |- _ ] => destructTR x; destruct x; try inv_trtype_false_faster
    end
  end.
  
Hint Extern 1 => ltTR_goal : TRHints.
Hint Extern 0 => solve_ltB : TRHints.

Close Scope string_scope.

Hint Constructors less_than : TRHints.

Ltac normalize_to_less_than_equal_0 :=
  repeat (progress 
  match goal with 
  | |- less_than_equal (Num 0) ?n => 
    match goal with
    | [ n : { _ : TRValues | _ } |- context[ n ] ] => idtac n; destructTR n; destruct n; try inv_trtype_false_faster
    | _ => idtac n;
      match type of n with 
      | TRValues => simpl
      | nat => idtac
      end 
    end
  end); less_than_equal_0.

Ltac solve_less_than :=
  match goal with 
  | |- less_than ?n ?m => 
    match goal with 
    | |- context[ proj1_sig ?n0 ] => destructTR n0; destruct n0; try inv_trtype_false_faster
    end;
    match goal with 
    | |- context[ proj1_sig ?m0 ] => destructTR m0; destruct m0; try inv_trtype_false_faster
    end; constructor
  | |- ltTR ?n ?m => 
    match goal with 
    | |- context[ proj1_sig ?n0 ] => destructTR n0; destruct n0; try inv_trtype_false_faster; simpl
    end;
    match goal with 
    | |- context[ proj1_sig ?m0 ] => destructTR m0; destruct m0; try inv_trtype_false_faster; simpl
    end
  end; unfold ltTR; simpl; solve_ltB; auto; try lia.

Ltac solve_specific_thing :=
  match goal with 
  |  [ H : _ /\ _ -> less_than (Num 0) (Num ?m) |- _ ] => idtac H;
    match goal with 
    | |- ?n + m - (?o + m) < ?n + m - ?o => destruct m; idtac m;
      match goal with 
      | |- n + 0 - (o + 0) < n + 0 - o => 
        make_hypothesis_not_bool (Num 0) trnum;
        let J := fresh "J" in 
        match goal with 
        | [ J1 : HasType (Num 0) trnum /\ (Num 0) <> (Bool false) |- _ ] => idtac J1; try apply H in J1;
          inversion J1; subst *;
          match goal with 
          | [ H1 : ltTR (?func (Num 0)) (?func (Num 0)) |- _ ] => idtac func; unfold ltTR in H1; simpl in H1; lia
          end
        end
      | |- _ => apply strictly_lessthan; lia
      end
    end
  end.

Ltac bool_not_true_or_false :=
  match goal with 
  | [ H : (Bool false) <> proj1_sig (ltTR_B ?n ?m) |- False ] => 
    match goal with 
    | [ H1 : (Bool true) <> proj1_sig (ltTR_B n m) |- False ] => 
      destruct (ltTR_B n m); 
      match goal with 
      | [ a : _ /\ _ /\ _ , H1_new : (Bool false) <> proj1_sig [ ?x ] |- _ ] => 
        destruct2 a; destruct x; try inv_trtype_false_faster; simpl in H; simpl in H1;
        match goal with 
        | [ H_new' : (Bool false) <> (Bool ?b) |- _ ] => destruct b; discriminates
        end
      end
    end 
  end.

Hint Extern 1 => solve_specific_thing : TRHints.
Hint Extern 1 => bool_not_true_or_false : TRHints.


Hint Extern 1 => normalize_to_less_than_equal_0 : TRHints.
Hint Extern 1 => solve_less_than : TRHints.

Program Fixpoint dot_prod_what_tr_3 {n : nat} 
  (len : { trnum }) 
  (step : {t >> trnum & (less_than 0 t) & ~(less_than 0 t)}) 
  (x : { (trvec n) }) 
  (y : { (trvec n) })  
  (acc : { trnum }) 
  (i : {t >> trnum & (less_than t (sum (Num n) step)) & True}) {measure (proj1_sig (sub (sum n step) i)) ltTR}
   : { trnum } :=
  match (ltTR_B i n) as M with
  | Bool true => @dot_prod_what_tr_3 n len step x y (sum acc (mult (trvec_ref x i) (trvec_ref y i))) (sum i step) _
  | Bool false => acc
  | _r => False_rec _ _
  end.
(* oof already up to a bad start lmao *)
Next Obligation. 
  really_simple_start.
Defined. Next Obligation. 
  really_simple_start.
Defined. Next Obligation. 
  really_simple_start.
Defined. Next Obligation. 
  really_simple_start.
Defined. Next Obligation. 
  really_simple_start.
Defined. Next Obligation. 
  really_simple_start.
Defined. Next Obligation. 
  really_simple_start.
Defined. Next Obligation. 
  really_simple_start.
Defined. Next Obligation. 
  really_simple_start.
Defined. Next Obligation. 
  really_simple_start.
Defined. Next Obligation. 
  really_simple_start.
Defined. Next Obligation. 
  really_simple_start.
Defined. Next Obligation. 
  really_simple_start.
Defined. Next Obligation. 
  really_simple_start.
Defined. Next Obligation. 
  really_simple_start.
Defined. Next Obligation. 
  really_simple_start.
Defined. Next Obligation. 
  really_simple_start.
Defined. Next Obligation. 
  really_simple_start.
Defined. Next Obligation. 
  really_simple_start.
Defined. Next Obligation. 
  really_simple_start.
Defined. Next Obligation. 
  really_simple_start.
Defined.  Next Obligation. 
  really_simple_start.
Defined.

Next Obligation.
  apply measure_wf. apply wf_ltTR.
Defined.
