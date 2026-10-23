Set Warnings "-uniform-inheritance".
Set Warnings "-ambiguous-paths".
Set Warnings "-meta-collision".
From TRresearch Require Import Definitions_new.

(* "trivial lemmas that make solving obligations faster" real annoying *)
(* trnum *)
Lemma bool_not_trnum : forall b, HasType (Bool b) trnum -> False.
Proof. intros b H; inversion H. Qed.
Lemma str_not_trnum : forall b, HasType (Str b) trnum -> False.
Proof. intros b H; inversion H. Qed.
Lemma pair_not_trnum : forall b p, HasType (Pair b p) trnum -> False.
Proof. intros b p H; inversion H. Qed.
Lemma list_not_trnum : forall b, HasType (List b) trnum -> False.
Proof. intros b H; inversion H. Qed.
Lemma vec_not_trnum : forall {n} (b : nat_vec n), HasType (Vec n b) trnum -> False.
Proof. intros n b H; inversion H. Qed.
Lemma void_not_trnum : forall b, HasType (Void b) trnum -> False.
Proof. intros b H; inversion H. Qed.

(* trbool *)
Lemma num_not_trbool : forall b, HasType (Num b) trbool -> False.
Proof. intros b H; inversion H. Qed.
Lemma str_not_trbool : forall b, HasType (Str b) trbool -> False.
Proof. intros b H; inversion H. Qed.
Lemma pair_not_trbool : forall b p, HasType (Pair b p) trbool -> False.
Proof. intros b p H; inversion H. Qed.
Lemma list_not_trbool : forall b, HasType (List b) trbool -> False.
Proof. intros b H; inversion H. Qed.
Lemma vec_not_trbool : forall {n} (b : nat_vec n), HasType (Vec n b) trbool -> False.
Proof. intros n b H; inversion H. Qed.
Lemma void_not_trbool : forall b, HasType (Void b) trbool -> False.
Proof. intros b H; inversion H. Qed.

(* trstr *)
Lemma bool_not_trstr : forall b, HasType (Bool b) trstr -> False.
Proof. intros b H; inversion H. Qed.
Lemma num_not_trstr : forall b, HasType (Num b) trstr -> False.
Proof. intros b H; inversion H. Qed.
Lemma pair_not_trstr : forall b p, HasType (Pair b p) trstr -> False.
Proof. intros b p H; inversion H. Qed.
Lemma list_not_trstr : forall b, HasType (List b) trstr -> False.
Proof. intros b H; inversion H. Qed.
Lemma vec_not_trstr : forall {n} (b : nat_vec n), HasType (Vec n b) trstr -> False.
Proof. intros n b H; inversion H. Qed.
Lemma void_not_trstr : forall b, HasType (Void b) trstr -> False.
Proof. intros b H; inversion H. Qed.

(* trpair *)
Lemma bool_not_trpair : forall b {x y}, HasType (Bool b) (trpair x y) -> False.
Proof. intros b x y H; inversion H. Qed.
Lemma str_not_trpair : forall b {x y}, HasType (Str b) (trpair x y) -> False.
Proof. intros b x y H; inversion H. Qed.
Lemma num_not_trpair : forall b {x y}, HasType (Num b) (trpair x y) -> False.
Proof. intros b x y H; inversion H. Qed.
Lemma list_not_trpair : forall b {x y}, HasType (List b) (trpair x y) -> False.
Proof. intros b x y H; inversion H. Qed.
Lemma vec_not_trpair : forall {n} {x y} (b : nat_vec n), HasType (Vec n b) (trpair x y) -> False.
Proof. intros n b x y H; inversion H. Qed.
Lemma void_not_trpair : forall b {x y}, HasType (Void b) (trpair x y) -> False.
Proof. intros b x y H; inversion H. Qed.

(* trlist *)
Lemma bool_not_trlist : forall b A, HasType (Bool b) (trlist A) -> False.
Proof. intros b A H; inversion H. Qed.
Lemma num_not_trlist : forall b A, HasType (Num b) (trlist A) -> False.
Proof. intros b A H; inversion H. Qed.
Lemma pair_not_trlist : forall b p A, HasType (Pair b p) (trlist A) -> False.
Proof. intros b p A H; inversion H. Qed.
Lemma str_not_trlist : forall b A, HasType (Str b) (trlist A) -> False.
Proof. intros b A H; inversion H. Qed.
Lemma vec_not_trlist : forall {n} (b : nat_vec n) A, HasType (Vec n b) (trlist A) -> False.
Proof. intros n b A H; inversion H. Qed.
Lemma void_not_trlist : forall b A, HasType (Void b) (trlist A) -> False.
Proof. intros b A H; inversion H. Qed.

(* trvec *)
Lemma bool_not_trvec : forall b {n}, HasType (Bool b) (trvec n) -> False.
Proof. intros b n H; inversion H. Qed.
Lemma num_not_trvec : forall b {n}, HasType (Num b) (trvec n) -> False.
Proof. intros b n H; inversion H. Qed.
Lemma pair_not_trvec : forall b p {n}, HasType (Pair b p) (trvec n) -> False.
Proof. intros b p n H; inversion H. Qed.
Lemma list_not_trvec : forall b {n}, HasType (List b) (trvec n) -> False.
Proof. intros b n H; inversion H. Qed.
Lemma str_not_trvec : forall {n} b, HasType (Str b) (trvec n) -> False.
Proof. intros n b H; inversion H. Qed.
Lemma void_not_trvec : forall b {n}, HasType (Void b) (trvec n) -> False.
Proof. intros b n H; inversion H. Qed.

(* trvoid *)
Lemma bool_not_trvoid : forall b, HasType (Bool b) trvoid -> False.
Proof. intros b H; inversion H. Qed.
Lemma num_not_trvoid : forall b, HasType (Num b) trvoid -> False.
Proof. intros b H; inversion H. Qed.
Lemma pair_not_trvoid : forall b p, HasType (Pair b p) trvoid -> False.
Proof. intros b p H; inversion H. Qed.
Lemma list_not_trvoid : forall b, HasType (List b) trvoid -> False.
Proof. intros b H; inversion H. Qed.
Lemma vec_not_trvoid : forall {n} (b : nat_vec n), HasType (Vec n b) trvoid -> False.
Proof. intros n b H; inversion H. Qed.
Lemma str_not_trvoid : forall b, HasType (Str b) trvoid -> False.
Proof. intros b H; inversion H. Qed.

(************************)  
(* "lemmas about trtop" *)  
Lemma is_top : forall (x : TRValues), HasType x trtop.
Proof. intros; constructor. Qed.

Lemma is_top_pair : forall (x y : TRValues), HasType (x , y) (U trtop trtop).
Proof. intros; repeat constructor. Qed.


(************************)  
(* "lemmas about pairs" *)
Lemma pair_left : forall {A B : TRTypes} {l : TRValues} {a b :TRValues}, 
  (a, b) = l ->  HasType l (trpair A B) -> 
  HasType a A.
Proof. 
  intros. rewrite <- H in H0. inversion H0. 
  auto.
Defined.

Lemma pair_right : forall {A B : TRTypes} {l : TRValues} {a b :TRValues}, 
  (a, b) = l ->  HasType l (trpair A B) -> 
  HasType b B.
Proof. 
  intros. rewrite <- H in H0. inversion H0. 
  auto.
Defined.

(************************************************************************)
(********************** HasType FALSE INVERSIONS AH *********************)
(* looks at hypothesis for a false "HasType" to invert *)

Ltac inv_trnum_fast_2 :=
  match goal with
  | H : HasType (Bool ?b) trnum |- _ => apply (bool_not_trnum b H)
  | H : HasType (Str ?b) trnum |- _ => apply (str_not_trnum b H)
  | H : HasType (Pair ?b ?p) trnum |- _ => apply (pair_not_trnum b p H)
  | H : HasType (Vec _ ?b) trnum |- _ => apply (vec_not_trnum b H)
  | H : HasType (List ?l) trnum |- _ => apply (list_not_trnum l H)
  | H : HasType (Void ?v) trnum |- _ => apply (void_not_trnum v H)
  end.

Ltac inv_trbool_fast_2 :=
  match goal with
  | H : HasType (Num ?b) trbool |- _ => apply (num_not_trbool b H)
  | H : HasType (Str ?b) trbool |- _ => apply (str_not_trbool b H)
  | H : HasType (Pair ?b ?p) trbool |- _ => apply (pair_not_trbool b p H)
  | H : HasType (Vec _ ?b) trbool |- _ => apply (vec_not_trbool b H)
  | H : HasType (List ?l) trbool |- _ => apply (list_not_trbool l H)
  | H : HasType (Void ?v) trbool |- _ => apply (void_not_trbool v H)
  end.

Ltac inv_trstr_fast_2 :=
  match goal with
  | H : HasType (Bool ?b) trstr |- _ => apply (bool_not_trstr b H)
  | H : HasType (Num ?b) trstr |- _ => apply (num_not_trstr b H)
  | H : HasType (Pair ?b ?p) trstr |- _ => apply (pair_not_trstr b p H)
  | H : HasType (Vec _ ?b) trstr |- _ => apply (vec_not_trstr b H)
  | H : HasType (List ?l) trstr |- _ => apply (list_not_trstr l H)
  | H : HasType (Void ?v) trstr |- _ => apply (void_not_trstr v H)
  end.

Ltac inv_trpair_fast_2 :=
  match goal with
  | H : HasType (Bool ?b) (trpair ?x ?y) |- _ => apply (bool_not_trpair b H)
  | H : HasType (Str ?b) (trpair ?x ?y) |- _ => apply (str_not_trpair b H)
  | H : HasType (Num ?b) (trpair ?x ?y) |- _ => apply (num_not_trpair b H)
  | H : HasType (Vec _ ?b) (trpair ?x ?y) |- _ => apply (vec_not_trpair b H)
  | H : HasType (List ?l) (trpair ?x ?y) |- _ => apply (list_not_trpair l H)
  | H : HasType (Void ?v) (trpair ?x ?y) |- _ => apply (void_not_trpair v H)
  end.

Ltac inv_trlist_fast_2 :=
  match goal with
  | H : HasType (Bool ?b) (trlist ?A) |- _ => apply (bool_not_trlist b A H)
  | H : HasType (Str ?b) (trlist ?A) |- _ => apply (str_not_trlist b A H)
  | H : HasType (Pair ?b ?p) (trlist ?A) |- _ => apply (pair_not_trlist b p A H)
  | H : HasType (Vec _ ?b) (trlist ?A) |- _ => apply (vec_not_trlist b A H)
  | H : HasType (Num ?l) (trlist ?A) |- _ => apply (num_not_trlist l A H)
  | H : HasType (Void ?v) (trlist ?A) |- _ => apply (void_not_trlist v A H)
  end.

Ltac inv_trvec_fast_2 :=
  match goal with
  | H : HasType (Bool ?b) (trvec _) |- _ => apply (bool_not_trvec b H)
  | H : HasType (Str ?b) (trvec _) |- _ => apply (str_not_trvec b H)
  | H : HasType (Pair ?b ?p) (trvec _) |- _ => apply (pair_not_trvec b p H)
  | H : HasType (Num ?b) (trvec _) |- _ => apply (num_not_trvec b H)
  | H : HasType (List ?l) (trvec _) |- _ => apply (list_not_trvec l H)
  | H : HasType (Void ?v) (trvec _) |- _ => apply (void_not_trvec v H)
  end.

Ltac inv_trvoid_fast_2 :=
  match goal with
  | H : HasType (Bool ?b) trvoid |- _ => apply (bool_not_trvoid b H)
  | H : HasType (Str ?b) trvoid |- _ => apply (str_not_trvoid b H)
  | H : HasType (Pair ?b ?p) trvoid |- _ => apply (pair_not_trvoid b p H)
  | H : HasType (Vec _ ?b) trvoid |- _ => apply (vec_not_trvoid b H)
  | H : HasType (List ?l) trvoid |- _ => apply (list_not_trvoid l H)
  | H : HasType (Num ?v) trvoid |- _ => apply (num_not_trvoid v H)
  end.

Ltac inv_trtype_false_faster_2  :=
  exfalso; try inv_trnum_fast_2; try inv_trbool_fast_2; try inv_trstr_fast_2; 
  try inv_trpair_fast_2; try inv_trvec_fast_2; try inv_trlist_fast_2; fail.

Ltac destructTR x := 
  destruct x as [?x [?x [?x ?x]]].