Require Import Monoid with_obs.
Set Implicit Arguments.
Set Universe Polymorphism.
Module FilterMonoid.
(** Rejection observes the neutral element; that observation may fail. *)
Definition filter {I O} (M : MonoidalOps I O) (pred : O -> bool) :=
  WithObsMonoid.with_obs_try M
    (fun x => if pred x then Some x else m_obs M (m_ne M)).
Theorem filter_is_monoid {I O} (M : MonoidalOps I O) pred :
  IsMonoid M -> IsMonoid (filter M pred).
Proof. intro H; exact H. Qed.
Lemma accepts {I O} (M : MonoidalOps I O) pred x v :
  m_obs M x = Some v -> pred v = true ->
  m_obs (filter M pred) x = Some v.
Proof. intros H P; cbn; now rewrite H, P. Qed.
Lemma rejects {I O} (M : MonoidalOps I O) pred x v :
  m_obs M x = Some v -> pred v = false ->
  m_obs (filter M pred) x = m_obs M (m_ne M).
Proof. intros H P; cbn; now rewrite H, P. Qed.
Lemma failure_propagates {I O} (M : MonoidalOps I O) pred x :
  m_obs M x = None -> m_obs (filter M pred) x = None.
Proof. intro H; cbn; now rewrite H. Qed.
End FilterMonoid.
