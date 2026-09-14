From Stdlib Require Import Bool.
Require Import Monoid.
Module ExistsMonoid.
(** Capitalisation/suffix avoid Rocq's exists keyword. *)
Definition exists_monoid : MonoidalOps bool bool :=
  {| m_summary := bool; m_ne := false; m_op := orb;
     m_gen := fun x => x; m_obs := fun x => Some x |}.
Theorem exists_is_monoid : IsMonoid exists_monoid.
Proof.
  split.
  - intros [] [] []; reflexivity.
  - split; intros []; reflexivity.
Qed.
End ExistsMonoid.
