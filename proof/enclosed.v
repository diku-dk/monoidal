From Stdlib Require Import List Bool.
Require Import Monoid.
Import ListNotations.
Set Implicit Arguments.
Set Universe Polymorphism.

(** Direct model of [enclosed]. Bytes are abstract; instantiate [eqb] with
    byte equality. Option-valued observation models parser rejection/failure. *)
Module EnclosedMonoid.
Section Construction.
  Context {B O : Type} (M : MonoidalOps B O).
  Context (eqb : B -> B -> bool) (left right : B).
  Inductive t := Empty | Single : B -> t | Ends : B -> m_summary M -> B -> t.
  Definition ne := Empty.
  Definition gen := Single.

  (** [pieces] lists precisely the nx+ny operands of the Futhark loop.
      A Single contributes no middle operand on either side. *)
  Definition pieces (x y : t) : list (m_summary M) :=
    (match x with Ends _ _ b => [m_gen M b] | _ => [] end) ++
    (match y with Ends a s _ => [m_gen M a; s] | _ => [] end).
  Definition op (x y : t) : t :=
    match x, y with
    | Empty, _ => y | _, Empty => x
    | Single a, Single b => Ends a (m_ne M) b
    | Single a, Ends c s b =>
        Ends a (fold_left (m_op M) (pieces x y) (m_ne M)) b
    | Ends a s c, Single b =>
        Ends a (fold_left (m_op M) (pieces x y) s) b
    | Ends a s c, Ends d u b =>
        Ends a (fold_left (m_op M) (pieces x y) s) b
    end.
  Lemma append_single a s b c :
    op (Ends a s b) (Single c) = Ends a (m_op M s (m_gen M b)) c.
  Proof. reflexivity. Qed.
  Lemma two_singletons a b : op (Single a) (Single b) = Ends a (m_ne M) b.
  Proof. reflexivity. Qed.

  Definition obs (x : t) : option O :=
    match x with
    | Ends a s b => if eqb a left && eqb b right then m_obs M s else None
    | _ => None
    end.
  Definition enclosed : MonoidalOps B O :=
    {| m_summary := t; m_ne := ne; m_op := op; m_gen := gen; m_obs := obs |}.

  (** Original operation: three inner calls, including neutral operands. *)
  Definition reference_op (x y : t) : t :=
    match x, y with
    | Empty, _ => y | _, Empty => x
    | Single a, Single b =>
        Ends a (m_op M (m_op M (m_op M (m_ne M) (m_ne M)) (m_ne M)) (m_ne M)) b
    | Single a, Ends c s b =>
        Ends a (m_op M (m_op M (m_op M (m_ne M) (m_ne M)) (m_gen M c)) s) b
    | Ends a s c, Single b =>
        Ends a (m_op M (m_op M (m_op M s (m_gen M c)) (m_ne M)) (m_ne M)) b
    | Ends a s c, Ends d u b =>
        Ends a (m_op M (m_op M (m_op M s (m_gen M c)) (m_gen M d)) u) b
    end.
  Theorem op_reference_equivalent : IsMonoid M ->
    forall x y, op x y = reference_op x y.
  Proof.
    intros [_ [Hl Hr]] [|a|a s b] [|c|c u d];
      cbn [op reference_op pieces app fold_left]; rewrite ?Hl, ?Hr; reflexivity.
  Qed.
  Theorem op_assoc : IsMonoid M ->
    forall x y z, op (op x y) z = op x (op y z).
  Proof.
    intros [Ha [Hl Hr]] [|a|a s b] [|c|c u d] [|e|e v f];
      cbn [op pieces app fold_left]; rewrite ?Hl, ?Hr; repeat rewrite Ha; reflexivity.
  Qed.
  Theorem ne_left_neutral : forall x, op ne x = x.
  Proof. destruct x; reflexivity. Qed.
  Theorem ne_right_neutral : forall x, op x ne = x.
  Proof. destruct x; reflexivity. Qed.
  Theorem enclosed_is_monoid : IsMonoid M -> IsMonoid enclosed.
  Proof. intro H; split; [exact (op_assoc H)|].
    split; [exact ne_left_neutral|exact ne_right_neutral]. Qed.

  Definition fold (xs : list B) := fold_left (fun s c => op s (gen c)) xs ne.
  Definition reference_fold (xs : list B) :=
    fold_left (fun s c => reference_op s (gen c)) xs ne.
  Theorem fold_reference_equivalent : IsMonoid M ->
    forall xs, fold xs = reference_fold xs.
  Proof.
    intros H xs; unfold fold, reference_fold; generalize ne.
    induction xs as [|x xs IH]; intro s; cbn; [reflexivity|].
    rewrite (op_reference_equivalent H); apply IH.
  Qed.
  Corollary observation_unchanged : IsMonoid M -> forall xs,
    obs (fold xs) = obs (reference_fold xs).
  Proof. intros H xs; now rewrite (fold_reference_equivalent H). Qed.
End Construction.
End EnclosedMonoid.
