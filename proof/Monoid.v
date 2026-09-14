Set Implicit Arguments.
Set Universe Polymorphism.

(** Generated/observable monoids, corresponding to the Futhark [monoid]
    module type.  Observation is option-valued so assertion failure is
    represented explicitly. *)
Record MonoidalOps (I O : Type) := {
  m_summary : Type;
  m_ne : m_summary;
  m_op : m_summary -> m_summary -> m_summary;
  m_gen : I -> m_summary;
  m_obs : m_summary -> option O
}.

Arguments m_summary {_ _} _.
Arguments m_ne {_ _} _.
Arguments m_op {_ _} _ _ _.
Arguments m_gen {_ _} _ _.
Arguments m_obs {_ _} _ _.

(** The proof obligation that is implicit in the Futhark module interface.
    Generators and observations do not occur in the algebraic laws. *)
Definition IsMonoid {I O} (M : MonoidalOps I O) : Prop :=
  (forall x y z : m_summary M,
      m_op M (m_op M x y) z = m_op M x (m_op M y z)) /\
  (forall x : m_summary M, m_op M (m_ne M) x = x) /\
  (forall x : m_summary M, m_op M x (m_ne M) = x).
