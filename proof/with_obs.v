Require Import Monoid.
Set Implicit Arguments.
Set Universe Polymorphism.
Module WithObsMonoid.
(** Partial observation composition; None propagates as failure. *)
Definition with_obs_try {I O R} (M : MonoidalOps I O) (f : O -> option R) :
    MonoidalOps I R :=
  {| m_summary := m_summary M; m_ne := m_ne M; m_op := m_op M;
     m_gen := m_gen M;
     m_obs := fun x => match m_obs M x with
                      | Some y => f y | None => None end |}.
(** Futhark's total observation callback. *)
Definition with_obs {I O R} (M : MonoidalOps I O) (f : O -> R) :=
  with_obs_try M (fun x => Some (f x)).
Theorem with_obs_try_is_monoid {I O R} (M : MonoidalOps I O) (f : O -> option R) :
  IsMonoid M -> IsMonoid (with_obs_try M f).
Proof. intro H; exact H. Qed.
Theorem with_obs_is_monoid {I O R} (M : MonoidalOps I O) (f : O -> R) :
  IsMonoid M -> IsMonoid (with_obs M f).
Proof. intro H; exact H. Qed.
Lemma failure_propagates {I O R} (M : MonoidalOps I O) (f : O -> option R) x :
  m_obs M x = None -> m_obs (with_obs_try M f) x = None.
Proof. intro H; cbn; now rewrite H. Qed.
End WithObsMonoid.
