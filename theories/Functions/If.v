Set Warnings "-uniform-inheritance".
Set Warnings "-ambiguous-paths".
Set Warnings "-meta-collision".
From TRresearch.Tactics Require Import tactics_all.
From TRresearch Require Import Definitions.
From TRresearch.Lemmas Require Import Lemmas Union_Lemmas.
#[local] Obligation Tactic := try (timeout 1 test_jail).


Create HintDb TRHints.
Hint Immediate pair_left : TRHints.
Hint Immediate pair_right : TRHints.

Lemma subsume : forall  {A} (P P' Q Q' : Prop),
  (P -> P') -> (Q -> Q') ->
  {>> A & P & Q} -> {>> (A) & P'  & Q'}.
Proof.
  intros.
  destruct H1 as [x [H2 [H3 H4]]].
  econstructor. 
  make_constructor; eauto.
Defined.

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
  destructTR x;
  destruct x;
  try destruct b; 
  try (apply y; apply x1; split; try (auto; discriminate); fail).
  apply z; apply x2; split; auto.
Defined.

Ltac idk_man := 
  match goal with 
  | [ b : bool |- _ ] => destruct b; (apply unionL; idk_man_part2 false; fail) + (apply unionR; idk_man_part2 true)
  | [ n : ?type |- _ ] =>  
      apply unionL; idk_man_part2 false
  end.

Definition if_TR_union {A B : TRTypes} {P P' P'' Q Q' Q'' : Prop} 
                          (x : {>> trbool & P & Q})                        
                          (y : P -> {>> A & P' & Q'})
                          (z : Q -> {>> B & P'' & Q''}) : 
                          {>> (U A B) & (P' \/ P'') & (Q' \/ Q'')}.
Proof.
  destructTR x.
  destruct x; try idk_man.
  Defined.

Program Definition notTR {P Q : Prop} (x : {>> trbool & P & Q}) : {>> trbool & Q & P} :=
  match x with
  | Bool false => Bool true
  | _r => Bool false
  end.

(* "Notations" *)
(* one day i will make these notations into one... *)
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