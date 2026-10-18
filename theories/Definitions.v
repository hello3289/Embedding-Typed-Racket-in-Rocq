From TRresearch Require Export Definitions_base.
From TRresearch Require Import tactics_all.

Create HintDb TRHints.

  Hint Extern 0 => discriminates : TRHints.
  Hint Extern 0 => subst_filtered_var : TRHints.
  Hint Extern 0 => simpl_func : TRHints.
  Hint Extern 0 => rewrite_jail' : TRHints.
  Hint Constructors HasType : TRHints. 