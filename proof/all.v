From Stdlib Require Import Bool.
Require Import Monoid.
Module AllMonoid.
Definition all : MonoidalOps bool bool :=
  {| m_summary := bool; m_ne := true; m_op := andb;
     m_gen := fun x => x; m_obs := fun x => Some x |}.
Theorem all_is_monoid : IsMonoid all.
Proof.
  split.
  - intros [] [] []; reflexivity.
  - split; intros []; reflexivity.
Qed.
End AllMonoid.
