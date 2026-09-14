Require Import Monoid.

Set Implicit Arguments.
Set Universe Polymorphism.

(** Componentwise product, following [prod] in monoidal.fut.  In the
    option-valued observation model, either component's failure propagates
    to the product observation.  This does not affect the summary algebra. *)
Module ProdMonoid.
Section Construction.
  Context {I O J R : Type}.
  Context (M1 : MonoidalOps I O) (M2 : MonoidalOps J R).

  Definition t : Type := (m_summary M1 * m_summary M2)%type.
  Definition ne : t := (m_ne M1, m_ne M2).
  Definition op (a b : t) : t :=
    (m_op M1 (fst a) (fst b), m_op M2 (snd a) (snd b)).
  Definition gen (input : I * J) : t :=
    (m_gen M1 (fst input), m_gen M2 (snd input)).
  Definition obs (x : t) : option (O * R) :=
    match m_obs M1 (fst x), m_obs M2 (snd x) with
    | Some a, Some b => Some (a, b)
    | _, _ => None
    end.

  Definition prod : MonoidalOps (I * J) (O * R) :=
    {| m_summary := t; m_ne := ne; m_op := op;
       m_gen := gen; m_obs := obs |}.

  Theorem op_assoc : IsMonoid M1 -> IsMonoid M2 ->
    forall a b c, op (op a b) c = op a (op b c).
  Proof.
    intros [H1 _] [H2 _] [a1 a2] [b1 b2] [c1 c2].
    unfold op; simpl; rewrite H1, H2; reflexivity.
  Qed.

  Theorem ne_left_neutral : IsMonoid M1 -> IsMonoid M2 ->
    forall x, op ne x = x.
  Proof.
    intros [_ [H1 _]] [_ [H2 _]] [x1 x2].
    unfold op, ne; simpl; rewrite H1, H2; reflexivity.
  Qed.

  Theorem ne_right_neutral : IsMonoid M1 -> IsMonoid M2 ->
    forall x, op x ne = x.
  Proof.
    intros [_ [_ H1]] [_ [_ H2]] [x1 x2].
    unfold op, ne; simpl; rewrite H1, H2; reflexivity.
  Qed.

  Theorem prod_is_monoid : IsMonoid M1 -> IsMonoid M2 -> IsMonoid prod.
  Proof.
    intros H1 H2; split; [exact (op_assoc H1 H2)|].
    split; [exact (ne_left_neutral H1 H2)|exact (ne_right_neutral H1 H2)].
  Qed.

  Lemma obs_success (x : t) a b :
    obs x = Some (a, b) <->
    m_obs M1 (fst x) = Some a /\ m_obs M2 (snd x) = Some b.
  Proof.
    unfold obs; destruct (m_obs M1 (fst x)), (m_obs M2 (snd x));
      split; intros H; try discriminate;
      inversion H; subst; intuition congruence.
  Qed.
End Construction.
End ProdMonoid.
