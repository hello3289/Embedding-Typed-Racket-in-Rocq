Set Warnings "-uniform-inheritance".
Set Warnings "-ambiguous-paths".
Set Warnings "-meta-collision".
From TRresearch Require Import Wf_Lemma.
From Corelib Require Import Program.Wf.


Ltac well_founded_tactic := 
  match goal with 
  | |- well_founded _ => try (apply measure_wf; apply wf_ltTR)
  end.