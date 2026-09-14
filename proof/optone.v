Require Import Monoid.
Set Implicit Arguments.
Set Universe Polymorphism.

Module OptOneMonoid.
Inductive del (I D : Type) := E : I -> del I D | Del : D -> del I D.
Arguments E {_ _} _.
Arguments Del {_ _} _.

Section Construction.
  Context {I D : Type}.
  (** The inner option is the first-present summary of Futhark's one.
      The outer option represents assertion failure, including invalid
      delimiter input. Some None is neutral; None is absorbing failure. *)
  Definition t := option (option I).
  Definition ne : t := Some None.
  Definition op (x y : t) : t :=
    match x, y with
    | Some (Some v), Some _ => Some (Some v)
    | Some None, Some w => Some w
    | _, _ => None
    end.
  Definition gen (x : del I D) : t :=
    match x with E v => Some (Some v) | Del _ => None end.
  Definition obs (x : t) : option I :=
    match x with Some v => v | None => None end.
  Definition optone : MonoidalOps (del I D) I :=
    {| m_summary := t; m_ne := ne; m_op := op; m_gen := gen; m_obs := obs |}.

  Theorem op_assoc : forall x y z, op (op x y) z = op x (op y z).
  Proof. intros [[x|]|] [[y|]|] [[z|]|]; reflexivity. Qed.
  Theorem ne_left_neutral : forall x, op ne x = x.
  Proof. intros [[x|]|]; reflexivity. Qed.
  Theorem ne_right_neutral : forall x, op x ne = x.
  Proof. intros [[x|]|]; reflexivity. Qed.
  Theorem optone_is_monoid : IsMonoid optone.
  Proof.
    split; [exact op_assoc|].
    split; [exact ne_left_neutral|exact ne_right_neutral].
  Qed.
  Lemma empty_observation : obs ne = None.
  Proof. reflexivity. Qed.
  Lemma first_element x y : obs (op (gen (E x)) (gen (E y))) = Some x.
  Proof. reflexivity. Qed.
  Lemma delimiter_fails d : gen (Del d) = None.
  Proof. reflexivity. Qed.
  Lemma delimiter_after_value_fails x d : op (gen (E x)) (gen (Del d)) = None.
  Proof. reflexivity. Qed.
  Lemma none_left x : op None x = None.
  Proof. reflexivity. Qed.
  Lemma none_right x : op x None = None.
  Proof. intros; destruct x as [[v|]|]; reflexivity. Qed.
End Construction.
End OptOneMonoid.
