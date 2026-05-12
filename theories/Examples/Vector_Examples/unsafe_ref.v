Set Warnings "-uniform-inheritance".
Set Warnings "-ambiguous-paths".
Set Warnings "-meta-collision".
From TRresearch.Tactics Require Import tactics_all.
From TRresearch Require Import Definitions.
From TRresearch.Functions Require Import Basics Vectors.
From TRresearch.Non_TR_Functions Require Import Vectors.
From Stdlib Require Import Strings.String.
#[local] Obligation Tactic := try ((timeout 1 (time really_simple_start)); (timeout 1 (time new_jail))).


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