Require Import Monoid prod.

Set Implicit Arguments.
Set Universe Polymorphism.

(** [dup] changes only generation: each input is sent to the underlying
    monoid as a pair of identical inputs.  Summaries, operation, neutral
    element, and observation are unchanged. *)
Module DupMonoid.
Section Construction.
  Context {I O : Type}.
  Context (M : MonoidalOps (I * I) O).

  Definition t : Type := m_summary M.
  Definition ne : t := m_ne M.
  Definition op : t -> t -> t := m_op M.
  Definition gen (input : I) : t := m_gen M (input, input).
  Definition obs : t -> option O := m_obs M.

  Definition dup : MonoidalOps I O :=
    {| m_summary := t; m_ne := ne; m_op := op;
       m_gen := gen; m_obs := obs |}.

  Theorem op_assoc : IsMonoid M ->
    forall a b c, op (op a b) c = op a (op b c).
  Proof. intros [H _]; exact H. Qed.

  Theorem ne_left_neutral : IsMonoid M -> forall x, op ne x = x.
  Proof. intros [_ [H _]]; exact H. Qed.

  Theorem ne_right_neutral : IsMonoid M -> forall x, op x ne = x.
  Proof. intros [_ [_ H]]; exact H. Qed.

  Theorem dup_is_monoid : IsMonoid M -> IsMonoid dup.
  Proof. intro H; exact H. Qed.

  (** The algebraic laws are definitionally identical, not merely implied. *)
  Theorem dup_is_monoid_iff : IsMonoid dup <-> IsMonoid M.
  Proof. split; intro H; exact H. Qed.
End Construction.

Section DuplicatedProduct.
  Context {I O R : Type}.
  Context (M1 : MonoidalOps I O) (M2 : MonoidalOps I R).

  Corollary dup_prod_is_monoid :
    IsMonoid M1 -> IsMonoid M2 ->
    IsMonoid (dup (ProdMonoid.prod M1 M2)).
  Proof.
    intros H1 H2; apply dup_is_monoid, ProdMonoid.prod_is_monoid; assumption.
  Qed.

  Lemma dup_prod_gen (x : I) :
    m_gen (dup (ProdMonoid.prod M1 M2)) x = (m_gen M1 x, m_gen M2 x).
  Proof. reflexivity. Qed.
End DuplicatedProduct.
End DupMonoid.
