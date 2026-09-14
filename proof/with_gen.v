Require Import Monoid.
Set Implicit Arguments.
Set Universe Polymorphism.
Module WithGenMonoid.
Definition with_gen {I O J} (M : MonoidalOps I O) (f : J -> I) :
    MonoidalOps J O :=
  {| m_summary := m_summary M; m_ne := m_ne M; m_op := m_op M;
     m_gen := fun x => m_gen M (f x); m_obs := m_obs M |}.
Theorem with_gen_is_monoid {I O J} (M : MonoidalOps I O) (f : J -> I) :
  IsMonoid M -> IsMonoid (with_gen M f).
Proof. intro H; exact H. Qed.
End WithGenMonoid.
