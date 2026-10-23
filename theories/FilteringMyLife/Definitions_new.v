From Stdlib Require Import Strings.String Bool.
From Corelib Require Import Lists.ListDef.
Require Import Program.Tactics.
#[local] Obligation Tactic := try now program_simpl.

(************************************************************************)
(**************** OUR VALUE AND TYPE DEFINITIONS AHHHHHH ****************)

Inductive Void_ := void.

Inductive nat_vec : nat -> Type :=
  | vec_nil : nat_vec O
  | vec_cons : forall {n : nat} , nat -> (nat_vec n) -> nat_vec (S n).

  Inductive TRValues : Type := 
  | Num (n : nat)
  | Bool (b : bool)
  | Str (s : string)
  | Pair  (a : TRValues) (b : TRValues)
  | List (l : list TRValues)
  | Vec : forall (n : nat),  (nat_vec n) -> TRValues
  | Void (v : Void_).

Check List (Num 5 :: Str "hi" :: nil).

Inductive TRTypes : Type := 
  | trnum : TRTypes
  | trbool : TRTypes
  | trstr : TRTypes
  | trvoid : TRTypes
  | trpair : TRTypes -> TRTypes -> TRTypes
  | trvec : nat -> TRTypes
  | trlist : TRTypes -> TRTypes
  | trunion : TRTypes -> TRTypes -> TRTypes
  | trtop : TRTypes.

  Inductive HasType : TRValues -> TRTypes -> Prop :=
  | HtTop     : forall (v : TRValues), HasType v trtop
  | HtNum     : forall (n : nat), HasType (Num n) trnum
  | HtBool    : forall (b : bool), HasType (Bool b) trbool
  | HtStr     : forall (s : string), HasType (Str s) trstr
  | HtVoid    : forall (v : Void_), HasType (Void v) trvoid
  | HtPair    : forall (t1 t2 : TRValues) (A B : TRTypes) ,  
                  HasType t1 A -> 
                  HasType t2 B -> 
                  HasType (Pair t1 t2) (trpair A B)
  | HtList    : forall (l : list TRValues) (A : TRTypes),
                Forall (fun x => (HasType x A)) l -> 
                HasType (List l) (trlist A)
  | HtVec     : forall (n : nat) (nv : nat_vec n), HasType (Vec n nv) (trvec n)
  | HtUnion_L : forall (t1 : TRValues) (A B : TRTypes),
                (HasType t1 A) -> HasType t1 (trunion A B)
  | HtUnion_R : forall (t1 : TRValues) (A B : TRTypes),
                (HasType t1 B) -> HasType t1 (trunion A B).

(************************************************************************)
(**************************** NOTATIONS AHHH ****************************)

Notation "[ e ]" := (exist _ e _).

Notation "{ t >> T & P & Q }" := 
    (sig (fun t : TRValues => (HasType t T) /\ 
                              ((HasType t T) /\ t <> Bool false -> P) /\ 
                               ((HasType t T) /\ t = Bool false -> Q)))
    (at level 0, t at level 99, T at next level, P at next level, Q at next level).

Notation "{ t >> T & P  }" := 
    { t >> T & P & (~P)}
    (at level 0, t at level 99, T at next level, P at next level).

Notation "{ >> T & P  }" := 
    { t >> T & P & (~P)}
    (at level 0, T at next level, P at next level).

Notation "{ >> T & P & Q  }" := 
    { t >> T & P & Q }
    (at level 0, T at next level, P at next level).

Notation "{ T }" := 
    { t >> T & True & True }
    (at level 0, T at level 99).

Notation " 'U' A B " :=
  (trunion A B) (at level 0, A at next level, B at next level). 
  

(************************************************************************)
(*************************** GIVE THOSE TYPES ***************************)

Fixpoint eqb (a b : TRTypes) : bool := 
  match a , b with 
  | trnum , trnum => true 
  | trbool , trbool => true 
  | trstr , trstr => true 
  | trvoid , trvoid => true 
  | (trpair A B) , (trpair A' B') => andb (eqb A A') (eqb B B')
  | (trvec n) , (trvec n') => (Nat.eqb n n')
  | (trlist A), (trlist A') => eqb A A'
  | (trunion A B) , (trunion A' B') => andb (eqb A A') (eqb B B')
  | trtop , trtop => true 
  | _ , _ => false 
  end.

Definition tr_union (a b : TRTypes) : TRTypes :=
  if (eqb a b) then a else (trunion a b).

Lemma eqb_true : forall (A B : TRTypes), 
  true = eqb A B -> eq A B.
Proof. intros. generalize dependent B.
  induction A; intros.
  induction B; simpl in H; try inversion H; auto.
  induction B; simpl in H; try inversion H; auto.
  induction B; simpl in H; try inversion H; auto.
  induction B; simpl in H; try inversion H; auto.
  destruct B; simpl in H; try inversion H; auto.
    specialize (IHA1 B1).
    specialize (IHA2 B2).
    symmetry in H.
    apply (Bool.andb_true_iff _ _) in H.
    destruct H; symmetry in H; symmetry in H0.
    specialize (IHA1 H).
    specialize (IHA2 H0).
    rewrite IHA1. rewrite IHA2. auto.
  destruct B; simpl in H; try inversion H; auto.
  symmetry in H. apply (PeanoNat.Nat.eqb_eq _ _) in H. rewrite H; auto.
  destruct B; simpl in H; try inversion H; auto. 
  specialize (IHA B). specialize (IHA H). rewrite IHA. auto.
  destruct B; simpl in H; try inversion H; auto.
    specialize (IHA1 B1).
    specialize (IHA2 B2).
    symmetry in H.
    apply (Bool.andb_true_iff _ _) in H.
    destruct H; symmetry in H; symmetry in H0.
    specialize (IHA1 H).
    specialize (IHA2 H0).
    rewrite IHA1. rewrite IHA2. auto.
  destruct B; simpl in H; try inversion H; auto.
Qed.

Program Fixpoint typeCheck (v : TRValues) : {t : TRTypes | HasType v t} := 
  match v return {t | HasType v t} with 
  | Void v => trvoid 
  | Num n => trnum 
  | Bool b => trbool 
  | Str s => trstr 
  | Vec n v => trvec n 
  | Pair a b => 
    match (typeCheck a) with 
    | A => match (typeCheck b) with 
           | B => trpair A B 
           end 
    end 
  | List l => let fix typeCheckList (xs : list TRValues) (init : TRTypes)
              : { t : TRTypes | Forall (fun x => HasType x t) xs } :=
              match xs with
              | nil => init
              | cons x l' =>
                  match (typeCheck x) with
                  | A => match (typeCheckList l' A) with 
                         | B => (tr_union A B) 
                         end 
                  end
              end
            in match (typeCheckList l trtop) with 
               | T => trlist T 
               end
  end. 
Next Obligation. 
   intros. simpl. constructor.
  Defined. Next Obligation. 
   intros. simpl. constructor.
  Defined. Next Obligation. 
   intros. simpl. constructor.
  Defined. Next Obligation. 
   intros.  subst *. repeat destruct typeCheck. simpl in *. 
   subst filtered_var0. subst filtered_var.
   constructor; auto. 
  Defined. Next Obligation.
  intros. simpl. constructor.
  - subst *. subst filtered_var0. subst filtered_var.
    unfold tr_union. 
    destruct (eqb (proj1_sig (typeCheck x)) (proj1_sig (typeCheckList l' (proj1_sig (typeCheck x))))).
    destruct typeCheck. simpl; auto.
    apply HtUnion_L. destruct typeCheck. simpl; auto.
  - subst *. subst filtered_var0. subst filtered_var.
    unfold tr_union. 
    remember (eqb (proj1_sig (typeCheck x)) (proj1_sig (typeCheckList l' (proj1_sig (typeCheck x))))).
    destruct b.
    + specialize (eqb_true _ _ Heqb). intros. rewrite H.
      destruct (typeCheckList l').
      simpl. auto.
    + destruct (typeCheckList l'). simpl.
      assert (H : forall (l : list TRValues) (A B : TRTypes),
               Forall (fun x : TRValues => HasType x B) l -> 
               Forall (fun x : TRValues => HasType x (trunion A B)) l).
      ++ intros. induction l0.
         constructor. 
         inversion H. specialize (IHl0 H3). 
         subst *. constructor.
         apply HtUnion_R. auto.
         auto.
      ++ apply H. auto.
  Defined. Next Obligation.
   intros. simpl. destruct typeCheckList. 
   constructor. subst *. subst filtered_var. simpl. auto.
  Defined. Next Obligation.
   intros. simpl. constructor.
  Defined. Next Obligation.
   intros; simpl; constructor.
  Defined.
      

Eval compute in typeCheck (Num 5).
Eval compute in typeCheck (List (Num 5 :: Str "hi" :: nil)).
Eval compute in typeCheck (List (Num 5 :: Num 19 :: nil)).

Program Definition getType' (v : TRValues) (t : {t | HasType v t}) :=
    match t return { t } with 
    | _ => v
    end.

Program Definition giveType (v : TRValues) :=
    getType' v (typeCheck v).

Program Definition TRUnionL {t1 t2 : TRTypes} (x : { t1 }) : { (U t1 t2) } :=
  x.
  Next Obligation. 
    simpl. 
    intros. 
    destruct x; simpl. 
    destruct a as [?a ?a];
    split; try apply HtUnion_L; auto. Defined.

Program Definition TRUnionR {t1 t2 : TRTypes} (x : { t2 }) : { (U t1 t2) } :=
  x.
  Next Obligation. 
    simpl. 
    intros. 
    destruct x; simpl. 
    destruct a as [?a ?a];
    split; try apply HtUnion_R; auto. Defined.

    
Definition get_true_prop {T : TRTypes} {P Q : Prop} (v : { t >> T & P & Q }) : Prop.
Proof.
  exact P.
Defined.

Definition get_false_prop {T} {P Q : Prop} (v : { t >> T & P & Q }) : Prop.
Proof. 
  exact Q.
Defined.

Definition get_type {T} {P Q : Prop} (v : { t >> T & P & Q }) : TRTypes.
Proof. 
    exact T.
Defined.

(************************************************************************)
(*********************** TWO MORE NOTATIONS AHHH ************************)

Program Definition top_pair { S T : TRTypes } (v : { (trpair S T) }) : { (trpair trtop trtop) } :=
  v.
  Next Obligation.
  intros; simpl.
  repeat split. destruct v. destruct a. destruct a.
  destruct x; try inversion h.
  constructor; constructor.
  Defined. 

Program Definition union_same {t : TRTypes} (x : { (U t t) }) : { t } :=
  x.
  Next Obligation.
  intros; simpl in *; repeat split. destruct x as [?x ?x]. destruct x0 as [?x ?x].
  inversion x0; auto.
  Defined.

Notation " <[ e ]> " :=
    (giveType e) (e at level 0).
Notation "( a , b )" := (Pair a b).
 

(************************************************************************)
(*********************** COERCIONS **************************************)



Coercion Num : nat >-> TRValues.
Coercion Str : string >-> TRValues.
Coercion Bool : bool >-> TRValues.
Coercion Vec : nat_vec >-> TRValues.
Coercion Void : Void_ >-> TRValues.
Coercion giveTypeWat (p : TRValues) := giveType p.
Set Warnings "-uniform-inheritance".
Set Warnings "-ambiguous-paths".
Coercion simplifyUnion {t : TRTypes} (p : {(trunion t t)}) := union_same p.
Set Warnings "uniform-inheritance".
Set Warnings "ambiguous-paths".


