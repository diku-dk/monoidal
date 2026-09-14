Require Import Monoid Parens.
Set Implicit Arguments.
Set Universe Polymorphism.

(** Uses the shared Nest input type already used by parens and parens_n. *)
Module NestableMonoid.
Section Construction.
  Context {I O : Type}.
  Context (Base : MonoidalOps I O).
  Inductive raw_t :=
  | NE
  | M : m_summary Base -> raw_t
  | V : O -> raw_t.
  Definition t := option raw_t.
  Definition ne : t := Some NE.
  Definition raw_op (x y : raw_t) : t :=
    match x, y with
    | NE, _ => Some y
    | _, NE => Some x
    | M a, M b => Some (M (m_op Base a b))
    | _, _ => None
    end.
  Definition op (x y : t) : t :=
    match x, y with Some x, Some y => raw_op x y | _, _ => None end.
  Definition gen (x : Nest I O) : t :=
    match x with raw v => Some (M (m_gen Base v)) | nested v => Some (V v) end.
  Definition obs (x : t) : option O :=
    match x with
    | Some NE => m_obs Base (m_ne Base)
    | Some (M s) => m_obs Base s
    | Some (V v) => Some v
    | None => None
    end.
  Definition nestable : MonoidalOps (Nest I O) O :=
    {| m_summary := t; m_ne := ne; m_op := op; m_gen := gen; m_obs := obs |}.

  Theorem op_assoc : IsMonoid Base ->
    forall x y z, op (op x y) z = op x (op y z).
  Proof.
    intros [H _] [[|x|x]|] [[|y|y]|] [[|z|z]|];
      cbn [op raw_op]; rewrite ?H; reflexivity.
  Qed.
  Theorem ne_left_neutral : forall x, op ne x = x.
  Proof. intros [[|x|x]|]; reflexivity. Qed.
  Theorem ne_right_neutral : forall x, op x ne = x.
  Proof. intros [[|x|x]|]; reflexivity. Qed.
  Theorem nestable_is_monoid : IsMonoid Base -> IsMonoid nestable.
  Proof.
    intro H; split; [exact (op_assoc H)|].
    split; [exact ne_left_neutral|exact ne_right_neutral].
  Qed.

  (** M Base.ne is not NE: keeping that distinction is necessary because a
      raw fragment is not allowed to combine with an already-observed value. *)
  Lemma raw_ne_not_ne : Some (M (m_ne Base)) <> ne.
  Proof. discriminate. Qed.
  Lemma nested_observation v : obs (gen (nested v)) = Some v.
  Proof. reflexivity. Qed.
  Lemma empty_observation : obs ne = m_obs Base (m_ne Base).
  Proof. reflexivity. Qed.
  Lemma nested_with_raw_fails v x : op (gen (nested v)) (gen (raw x)) = None.
  Proof. reflexivity. Qed.
  Lemma raw_with_nested_fails x v : op (gen (raw x)) (gen (nested v)) = None.
  Proof. reflexivity. Qed.
  Lemma nested_with_nested_fails v w : op (gen (nested v)) (gen (nested w)) = None.
  Proof. reflexivity. Qed.
  Lemma observation_failure s : m_obs Base s = None -> obs (Some (M s)) = None.
  Proof. exact (fun H => H). Qed.
  Lemma none_left x : op None x = None.
  Proof. reflexivity. Qed.
  Lemma none_right x : op x None = None.
  Proof. destruct x; reflexivity. Qed.
End Construction.
End NestableMonoid.
