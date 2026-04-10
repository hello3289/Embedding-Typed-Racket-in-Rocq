Set Warnings "-uniform-inheritance".
Set Warnings "-ambiguous-paths".
Set Warnings "-meta-collision".
From TRresearch Require Import Definitions.

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
Lemma bool_not_trlist : forall b, HasType (Bool b) trlist -> False.
Proof. intros b H; inversion H. Qed.
Lemma num_not_trlist : forall b, HasType (Num b) trlist -> False.
Proof. intros b H; inversion H. Qed.
Lemma pair_not_trlist : forall b p, HasType (Pair b p) trlist -> False.
Proof. intros b p H; inversion H. Qed.
Lemma str_not_trlist : forall b, HasType (Str b) trlist -> False.
Proof. intros b H; inversion H. Qed.
Lemma vec_not_trlist : forall {n} (b : nat_vec n), HasType (Vec n b) trlist -> False.
Proof. intros n b H; inversion H. Qed.
Lemma void_not_trlist : forall b, HasType (Void b) trlist -> False.
Proof. intros b H; inversion H. Qed.

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