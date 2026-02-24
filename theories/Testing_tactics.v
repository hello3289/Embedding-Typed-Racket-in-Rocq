From TRresearch.Tactics Require Import Tactic_jail.
From TRresearch Require Import Definitions.
From TRresearch Require Import StandardFunctions.
From Stdlib Require Import Strings.String.
From Stdlib Require Bool.
From Corelib Require Import Program.Tactics.

(* Coercion Num : nat >-> TRValues.
  Coercion Str : string >-> TRValues.
  Coercion Bool : bool >-> TRValues.
  Coercion Vec : nat_vec >-> TRValues.
  Coercion Void : Void_ >-> TRValues.
  Coercion giveTypeWat (p : TRValues) := giveType p.
  Set Warnings "-uniform-inheritance".
  Set Warnings "-ambiguous-paths".
  Coercion simplifyUnion {t : TRTypes} (p : {(trunion t t)}) := union_same p.
  Set Warnings "uniform-inheritance".
  Set Warnings "ambiguous-paths". *)
Set Warnings "-meta-collision".

#[global] Obligation Tactic := try simpl.

(* Notes of the kinds of obligations generated (and for what kinds of definitions) and what order is best for 
   solving them : 

   - single input "operation" definitions (aka. add1 where one of the branches is False_rec _ _) : 
      + for the False_rec branch : 
        * intro all, then rewrite (since _r = proj1_sig n)
*)

(* Ltac rewrite_jail := 
  match goal with 
  | [ H : ?r = ?x |- _ ] => rewrite H in *; clear H
  end.

Program Definition add1 (n : {trnum}) : {trnum} :=
   match n with
   | Num x => S x
   | _r => False_rec _ _
   end.
Next Obligation.
  intros. rewrite_jail. 
  match goal with 
  | [ H : {t : TRValues | (HasType ?val ?type) /\ ?T /\ ?F } |- _ ] => 
    match goal with 
    | 
    end
  end.
*)


Ltac false_inversion := 
  match goal with 
  | [H : {t : TRValues | (HasType ?val ?type) /\ ?T /\ ?F } |- _ ] => 
    match goal with 
    | |- False => idtac H; let name := H in let val := fresh name in destruct H as [val [?name [?name ?name]]]; destruct val;
          match type with 
          | trnum => try inv_trnum_fast
          | trbool => try inv_trbool_fast
          | trstr => try inv_trstr_fast
          | trlist => try inv_trlist_fast
          | trpair ?x ?y => try inv_trpair_fast
          | trvec ?n => try inv_trvec_fast
          end; simpl
    end
  end.

Ltac subst_filtered_var := 
  match goal with 
  | [ filtered_var := _ |- _ ] => subst filtered_var
  end.

Ltac specialize_specific H k := 
  match k with 
  | proj1_sig [?v] => idtac v;
    match v with 
    | Num ?v1 => specialize (H v1) as H; simpl in H
    | Bool ?v1 => specialize (H v1) as H; simpl in H
    | Str ?v1 => specialize (H v1) as H; simpl in H
    | Void ?v1 => specialize (H v1) as H; simpl in H
    | List ?v1 => specialize (H v1) as H; simpl in H
    | Vec ?n ?v1 => specialize (H v1) as H; simpl in H
    end
  end.

Ltac false_specialize_one := 
  match goal with 
  | |- False => idtac "yes";
      match goal with 
      | H : forall r : ?type, ?tr_r <> ?k |- _  => idtac H k;
        specialize_specific H k 
      end
  end.

Ltac rewrite_jail := 
  match goal with 
  | [ H : ?r = ?x |- _ ] => rewrite H in *; clear H
  end.

Ltac false_jail := 
  try false_inversion; try rewrite_jail; try subst_filtered_var; try false_specialize_one; try discriminates.

#[local] Obligation Tactic := try intros; false_jail; try discriminates.
Program Definition add1 (n : {trnum}) : {trnum} :=
   match n with
   | Num x => S x
   | _r => False_rec _ _
   end.

Eval compute in add1 5.

Ltac tiny_start_jail := 
  intros; 
  try repeat (
    match goal with 
    | |- ~(?n) => intro 
    end
  );
  try repeat (
    match goal with 
    | [ H : ?a /\ ?b |- _ ] => destruct H
    end
  ).

Ltac false_specialize_two := 
  match goal with 
  | |- False => 
      match goal with 
      | H : forall r q : ?type, ~( ?tr_r = ?k /\ ?tr_q = ?j ) |- _  => idtac k j;
        specialize_specific H k; specialize_specific H j
      end
  end.

Ltac false_jail_fix_this := 
  intros; do 2 false_inversion; do 2 rewrite_jail; do 2 subst_filtered_var; 
  false_specialize_two.

Ltac very_stupid_intros_false :=
  repeat (
    match goal with 
    | |- ?p -> False => idtac p
    | |- _ => intro
    end).

Ltac false_inversion_what := 
  match goal with 
  | [H : {t : TRValues | (HasType ?val ?type) /\ ?T /\ ?F } |- _ ] => 
    match goal with 
    | |- context [ H ] => 
        let name := H in let val := fresh name in destruct H as [val [?name [?name ?name]]]; destruct val;
          match type with 
          | trnum => try inv_trnum_fast
          | trbool => try inv_trbool_fast
          | trstr => try inv_trstr_fast
          | trlist => try inv_trlist_fast
          | trpair ?x ?y => try inv_trpair_fast
          | trvec ?n => try inv_trvec_fast
          end; simpl
    end
  end.

Ltac specialize_specific_what H k := 
  match k with 
    | Num ?v1 => specialize (H v1) as H; simpl in H
    | Bool ?v1 => specialize (H v1) as H; simpl in H
    | Str ?v1 => specialize (H v1) as H; simpl in H
    | Void ?v1 => specialize (H v1) as H; simpl in H
    | List ?v1 => specialize (H v1) as H; simpl in H
    | Vec ?n ?v1 => specialize (H v1) as H; simpl in H
    | ?v => idtac v; specialize (H v) as H; simpl in H (* generic case *)
    end.

Ltac false_specialize_one_what := 
  match goal with 
  | |- False =>
      match goal with 
      | H : forall r : ?type, ?tr_r <> ?k |- _  => 
        specialize_specific_what H k 
      | H : forall r e : ?type, ?tr_r <> ?k |- _ => match k with 
                                                    | (?a , ?b) => specialize_specific_what H a; specialize_specific_what H b
                                                    end                                                    
      end
  end.

Ltac false_jail_what := 
  try very_stupid_intros_false;
  try subst_filtered_var;
  try false_inversion_what;
  intro;
  try rewrite_jail;
  try false_specialize_one_what;
  try discriminates;
  fail.


#[local] Obligation Tactic := try false_jail_what; try (tiny_start_jail; discriminates).
Program Definition sum (n : {trnum}) (m : {trnum}) : {trnum} :=
  match m with 
  | Num m' => 
    match n with 
    | Num n' => m' + n' 
    | _r2 => False_rec _ _ 
    end
  | _r1 => False_rec _ _ 
  end.
  
#[local] Obligation Tactic := try false_jail_what; try (tiny_start_jail; discriminates).
Program Definition mult (n : {trnum}) (m : {trnum}) : {trnum} :=
  match m with 
  | Num m' => 
    match n with 
    | Num n' => m' * n' 
    | _r2 => False_rec _ _ 
    end
  | _r1 => False_rec _ _ 
  end.
  


#[local] Obligation Tactic := try false_jail_what; try (tiny_start_jail; discriminates).  
Program Definition sub (n : {trnum}) (m : {trnum}) : {trnum} :=
  match m with 
  | Num m' => 
    match n with 
    | Num n' => m' - n' 
    | _r2 => False_rec _ _ 
    end
  | _r1 => False_rec _ _ 
  end.

Notation " 'add' A B " := (sum A B) (at level 0, A at next level, B at next level) : TR_scope.
Notation " 'mul' A B " := (mult A B) (at level 0, A at next level, B at next level) : TR_scope.
Notation " 'sub' A B " := (sub A B) (at level 0, A at next level, B at next level) : TR_scope.

Create HintDb TRHints.
Hint Constructors HasType : TRHints. 

Ltac simpl_func := 
  match goal with 
  | |- (fun t : ?type => ?body ) ?val => simpl 
  end.

Ltac simple_destruct := 
  match goal with 
    | [H : {t : TRValues | (HasType ?val ?type) /\ ?T /\ ?F } |- _ ] => 
      match goal with 
      | |- context [ H ] => 
            let name := H in let val := fresh name in destruct H as [val [?name [?name ?name]]]; destruct val; simpl
      end
    end.

Ltac simpl_proj := 
  repeat (
    match goal with 
  | [ H : context[ proj1_sig ?p ] |- _ ] => simpl in H 
  end).

Ltac very_small_start_jail := 
  try (
    match goal with 
  | |- ?r /\ ?p => split; very_small_start_jail
    end); 
  try auto with TRHints.

Ltac forall_intro := 
  repeat (
    match goal with 
    | |- forall _, _ => intro
    end
  ).

  (* once and exactly_once may help here with the + *)
#[local] Obligation Tactic := 
  tryif simpl 
    then (try very_stupid_intros_false; try discriminates) 
    else forall_intro; very_small_start_jail; rewrite_jail;
        (simple_destruct; very_stupid_intros_false; try inv_trtype_false_faster; try simpl_proj; try false_specialize_one_what)
        +
        (match goal with | |- ?P /\ ?Q -> _ => let H := fresh "H" in intro H; destruct H end); discriminates.
Program Definition is_number {t : TRTypes} (x : {t}) : 
                  {>> trbool & (HasType x trnum)} :=
  match x with
  | Num n => Bool true
  | _r => Bool false
  end.




Eval compute in is_number 5.
#[local] Obligation Tactic := 
  tryif simpl 
    then (try very_stupid_intros_false; try discriminates) 
    else forall_intro; very_small_start_jail; rewrite_jail;
        (simple_destruct; very_stupid_intros_false; try inv_trtype_false_faster; try simpl_proj; try false_specialize_one_what)
        +
        (match goal with | |- ?P /\ ?Q -> _ => let H := fresh "H" in intro H; destruct H end); discriminates.
Program Definition is_string {t : TRTypes} (x : {t}) : 
                  {>> trbool & (HasType x trstr)} :=
  match x with
  | Str s => Bool true
  | _r => Bool false
  end.
  
#[local] Obligation Tactic := 
  tryif simpl 
    then (try very_stupid_intros_false; try discriminates) 
    else forall_intro; very_small_start_jail; rewrite_jail;
        (simple_destruct; very_stupid_intros_false; try inv_trtype_false_faster; try simpl_proj; try false_specialize_one_what)
        +
        (match goal with | |- ?P /\ ?Q -> _ => let H := fresh "H" in intro H; destruct H end); discriminates.
Program Definition is_bool {t : TRTypes} (x : {t}) : 
                  {>> trbool & (HasType x trbool)} :=
  match x with
  | Bool b => Bool true
  | _r => Bool false
  end.
  
#[local] Obligation Tactic := 
  tryif simpl 
    then (try very_stupid_intros_false; try discriminates) 
    else forall_intro; very_small_start_jail; rewrite_jail;
        (simple_destruct; very_stupid_intros_false; try inv_trtype_false_faster; try simpl_proj; try false_specialize_one_what)
        +
        (match goal with | |- ?P /\ ?Q -> _ => let H := fresh "H" in intro H; destruct H end); discriminates.
Program Definition is_pair {t : TRTypes} (x : {t}) : 
  {>> trbool & (HasType x (trpair trtop trtop))} :=
  match x with
  | Pair a b => Bool true
  | _r => Bool false
  end.

        
#[local] Obligation Tactic := 
  try false_jail_what; try (tiny_start_jail; discriminates).
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

Ltac goal_inside_type := 
  match goal with 
    | [ H : { >> ?type & ?P & ?Q } |- _ ] => match goal with 
                                           | |- Q => destruct H as [?H [?H [?H ?H]]]
                                           end
    | [ H : { >> ?type & ?P & ?Q } |- _ ] => match goal with 
                                           | |- P => destruct H as [?H [?H [?H ?H]]]
                                           end
    end.

Ltac find_apply := 
  match goal with 
    | |- ?Q => match goal with 
              | [H : _ -> Q |- _ ] => apply H 
              end 
  end.

Ltac reflexivity_swap := 
  match goal with 
      | [ H : ?a <> ?b |- _ ] => match goal with 
                                 | |- context [ b <> a ] => let A := fresh H in assert (b <> a) as A by eauto; clear H
                                 end 
  end.

#[local] Obligation Tactic := 
  tryif simpl 
    then (try very_stupid_intros_false; try discriminates) 
    else forall_intro; very_small_start_jail; intros; goal_inside_type; find_apply; 
         tiny_start_jail 
          + 
        (try rewrite_jail; try simpl_proj; try reflexivity_swap); 
          auto; discriminates.
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

Ltac intro_false_premise := 
  match goal with 
    | |- ?a -> _ => let H := fresh "H" in intro H;
                    match a with 
                    | context [ Bool true = Bool false ] => match a with 
                                                            | ?b /\ ?c => destruct H; discriminates
                                                            end
                    | _ => intro H; intro_false_premise
                    end
    | _ => idtac
    end.

#[local] Obligation Tactic := try simpl_func; autounfold with TRHints; forall_intro; very_small_jail.
Program Definition orTest {A : TRTypes} (x : {A}) : 
    {>> trbool & ((HasType x trnum) \/ (HasType x trstr))} :=
    orTR (is_number x) (is_string x).
  Next Obligation.
    all : simple_destruct; auto with TRHints; simpl_proj; try inv_trtype_false_faster; intro_false_premise.
  Defined.
  Next Obligation.
      - simple_destruct; auto with TRHints.
      - right.
        simple_destruct; 
        match goal with 
        | [ H : context[ [?a] ] |- _ ] => simpl in H 
        end; auto with TRHints;
        match goal with 
        | [ H : context[ Bool false <> Bool false ] |- _ ] => try destruct H; discriminates (* this doesn't generalize well exactly *)
        | |- ?a => idtac a
        end.
      - intro; intro. 
        match goal with 
        | [H : ?a \/ ?b |- _ ] => destruct H 
        end.
        match goal with 
        | [ H : ~ ?a |- _ ] => match goal with  
                               | [ J : a |- _ ] => destruct H; auto 
                               end 
        end.
        match goal with 
        | [ H : ~ ?a |- False ] => destruct H 
        end.
        simple_destruct; 
        match goal with 
        | [ H : context[ [?a] ] |- _ ] => simpl in H 
        end; try inv_trtype_false_faster.
        match goal with 
        | [ H : context[ [?a] ] |- _ ] => simpl in H 
        end.
        match goal with 
        | [ H : context[ Bool true = Bool false ] |- _ ] => try destruct H; discriminates (* this doesn't generalize well exactly *)
        | |- ?a => idtac a
        end.
  Defined.
