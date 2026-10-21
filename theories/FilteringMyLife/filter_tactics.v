Set Warnings "-ambiguous-paths".
From TRresearch Require Import Definitions_new.
From TRresearch Require Import Basic_stuff.
Require Import Program.Tactics.
From TRresearch Require Import Lemmas_new.
From Corelib Require Import Lists.ListDef.
Require Import Program.Tactics.
From Corelib Require Import Program.Wf.

Lemma tr_union_right_list : forall (l : list TRValues) (A B : TRTypes),
               Forall (fun x : TRValues => HasType x B) l -> 
               Forall (fun x : TRValues => HasType x (tr_union A B)) l.
Proof. 
    intros. unfold tr_union.
    remember (eqb A B).
    destruct b.
    apply eqb_true in Heqb. rewrite Heqb. auto.
    assert (H1 : forall (l : list TRValues) (A B : TRTypes),
               Forall (fun x : TRValues => HasType x B) l -> 
               Forall (fun x : TRValues => HasType x (trunion A B)) l).
      ++ intros. induction l0.
         constructor. 
         inversion H0. specialize (IHl0 H4). 
         subst *. constructor.
         apply HtUnion_R. auto.
         auto.
      ++ apply H1. auto.
Qed.

Lemma tr_union_left_list : forall (l : list TRValues) (A B : TRTypes),
               Forall (fun x : TRValues => HasType x A) l -> 
               Forall (fun x : TRValues => HasType x (tr_union A B)) l.
Proof. 
    intros. unfold tr_union.
    remember (eqb A B).
    destruct b. auto.
    assert (H1 : forall (l : list TRValues) (A B : TRTypes),
               Forall (fun x : TRValues => HasType x A) l -> 
               Forall (fun x : TRValues => HasType x (trunion A B)) l).
      ++ intros. induction l0.
         constructor. 
         inversion H0. specialize (IHl0 H4). 
         subst *. constructor.
         apply HtUnion_L. auto.
         auto.
      ++ apply H1. auto.
Qed.

Ltac false_list := 
    match goal with 
    | [H : forall l : list TRValues, List l <> ?tail |- _] => 
        destruct tail; try inv_trtype_false_faster_2;
        match goal with 
        | [ H1 : HasType (List ?l) _ |- _ ] => 
            let J := fresh "J" in
            specialize (H l) as J; destruct J; auto 
        end
    end.

Ltac HasType_list := 
    match goal with 
    | |- HasType (List ?l) (trlist _) => repeat constructor
    end.

Ltac deal_tr_union := 
    let eqb_trunion P := 
        unfold tr_union; destruct (eqb _ _); auto; apply P; auto in
    match goal with 
    | [H : HasType ?a ?A |- _ ] => 
        match goal with 
        | |- HasType a (tr_union A ?B) => eqb_trunion HtUnion_L
        end
    | [H : HasType ?a ?B |- _ ] => 
        match goal with 
        | |- HasType a (tr_union ?A B) => eqb_trunion HtUnion_R
        end
    end.

Ltac apply_tr_union_right_list := 
    match goal with 
    | |- Forall (fun x : TRValues => HasType x (tr_union ?A ?B)) ?l => 
        match goal with 
        | [ H : HasType (List l) (trlist A) |- _ ] => inversion h
        | [ H : HasType (List l) (trlist B) |- _ ] => inversion h
        end; try (apply tr_union_right_list); try (apply tr_union_left_list)
    end; auto.

Ltac give_true := 
    match goal with 
    | |- Prop => exact True
    end.

Ltac exists_list := 
    match goal with 
    | |- exists _ _, _ = _ => 
        match goal with 
        | [ H : HasType (List ?l) ?A |- _ ] => 
            match goal with 
            | |- context[ l ] => destruct l 
            end
        end
    end; 
    try match goal with 
    | [ H : ~ (proj1_sig [List nil] = List nil /\ _ ) |- _ ] => 
        destruct H; repeat constructor
    end;
    try match goal with 
    | [ H : HasType (List (?h :: ?t)) ?A |- _ ] => idtac "HI"; 
        exists h; exists t ;auto 
    end.

Ltac destruct_specific := 
    match goal with 
    | [ H : {?A} |- _ ] => idtac A;
        match goal with 
        | |- context[ H ] => idtac H; destructTR H;
            match goal with 
            | [ J : HasType ?x A |- _ ] => destruct x; try inv_trtype_false_faster_2
            end
        end 
    end.


      Ltac falsities := 
        match goal with 
        | [ H : _ = Bool false |- False ] => try inversion H 
        end.
      Ltac simpl_goals := 
        match goal with 
        | [ H : _ /\ _ |- _ ] => destruct H 
        end.
      Ltac negation_intro := 
        match goal with 
        | |- ~ ?n => intro 
        end.

Ltac trtop_all := 
        match goal with 
        | |- HasType _ trtop => constructor 
        end.

Ltac cdr_length := 
    match goal with 
    | [ l : {trlist ?A} |- _ ] => 
        match goal with 
        | |- lengthTR (TRcdr [proj1_sig l]) < lengthTR l => 
            destruct_specific; destruct l
        end 
    | [ l : list TRValues |- _ ] => 
        match goal with 
        | |- lengthTR (TRcdr [proj1_sig [List l]]) < lengthTR [List l]=> idtac "HI";
            destruct l
        end
    end; 
    try match goal with 
    | [ H : ~(proj1_sig [List nil] = List nil /\ _ ) |- _ ] => 
      destruct H; repeat constructor
    end; 
    try (unfold TRcdr; simpl; unfold lengthTR; simpl; eapply PeanoNat.Nat.lt_succ_diag_r).

Lemma reflexive_types : forall (B0 : TRTypes), true = eqb B0 B0.
Proof.
    intro. induction B0; simpl; auto. 
      rewrite <- IHB0_1. rewrite <- IHB0_2. simpl. auto.
      symmetry. apply PeanoNat.Nat.eqb_refl.
      rewrite <- IHB0_1. rewrite <- IHB0_2. simpl. auto.
Qed.
Lemma tr_union_type : forall B, tr_union B B = B.
Proof. intro. unfold tr_union. rewrite <- (reflexive_types B). auto.
Qed.

Ltac car_is_type := 
    match goal with 
    | [ H : HasType (proj1_sig [proj1_sig (TRcar [proj1_sig [List ?l]])]) ?B |- _ ] => 
        match goal with 
        | |- HasType (proj1_sig (TRcar [proj1_sig [List l]])) _ => 
            destruct l
        end 
    end;
    try match goal with 
    | [ H : ~ (proj1_sig [List nil] = List nil /\ _ ) |- _ ] => 
        destruct H; repeat constructor
    end; 
    simpl; auto.

Ltac tr_union_union := 
    simpl;
    match goal with 
    | [ H : HasType ?x (trlist (tr_union _ ?B)) |- _ ] =>
        match goal with 
        | |- HasType x (trlist B) => 
            let J := fresh "J" in 
            let J2 := fresh "J" in
            specialize (tr_union_type B) as J;
            assert (J2 : HasType x (trlist B)) by (rewrite <- J; auto);
            auto
        end 
    end.

Ltac destruct_inside_hastype := 
    match goal with 
    | |- HasType (proj1_sig (?func _ _ _)) ?type => 
        destruct (func _ _ _)
    end; simpl_goals.

Ltac autoTR := auto with TRHints.
Ltac start := intros; simpl.

Ltac give_B := 
    intros;
    match goal with 
    | [ H : HasType (proj1_sig [proj1_sig (TRcar [proj1_sig ?l])]) ?B |- TRTypes ] => exact B 
    end.

Ltac trtactic := 
    match goal with 
    | |- TRTypes => give_B 
    | |- _ => idtac 
    end;
    try start; try destruct_specific; 
    try match goal with 
    | |- _ /\ _ /\ _ => repeat split
    end; 
    autoTR.
