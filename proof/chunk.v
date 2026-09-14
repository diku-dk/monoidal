Require Import Monoid.

Set Implicit Arguments.
Set Universe Polymorphism.

(** Direct model of [chunk] in monoidal.fut.  Delimiters are polymorphic
    (instantiate [D] with eight-bit characters for Futhark). *)
Module ChunkMonoid.
Inductive del (I D : Type) :=
| E : I -> del I D
| Del : D -> del I D.
Arguments E {_ _} _.
Arguments Del {_ _} _.

Section Construction.
  Context {I O R D : Type}.
  Context (M1 : MonoidalOps I O) (M2 : MonoidalOps (del O D) R).
  Context (del_ign : D -> bool).

  (** [A] has no chunk boundary; [C] retains the unfinished left and right
      chunks and the already-combined outer summary between them. *)
  Inductive form :=
  | A : m_summary M1 -> form
  | C : m_summary M1 -> m_summary M2 -> m_summary M1 -> form.

  (** Failure of inner observation can occur during combination, so it is
      represented in the summary, not only in the final observation. *)
  Definition t : Type := option form.
  Definition ne : t := Some (A (m_ne M1)).

  Definition m1_to_m2 (x : m_summary M1) : option (m_summary M2) :=
    match m_obs M1 x with
    | Some v => Some (m_gen M2 (E v))
    | None => None
    end.

  Definition op (x y : t) : t :=
    match x, y with
    | Some (A lx), Some (A ly) => Some (A (m_op M1 lx ly))
    | Some (A lx), Some (C l c r) => Some (C (m_op M1 lx l) c r)
    | Some (C lx cx rx), Some (A ly) => Some (C lx cx (m_op M1 rx ly))
    | Some (C lx cx rx), Some (C ly cy ry) =>
        match m1_to_m2 (m_op M1 rx ly) with
        | Some middle => Some (C lx (m_op M2 cx (m_op M2 middle cy)) ry)
        | None => None
        end
    | _, _ => None
    end.

  Definition gen (input : del I D) : t :=
    match input with
    | E x => Some (A (m_gen M1 x))
    | Del c => if del_ign c then ne
               else Some (C (m_ne M1) (m_gen M2 (Del c)) (m_ne M1))
    end.

  Definition obs (x : t) : option R :=
    match x with
    | Some (A a) =>
        match m1_to_m2 a with
        | Some v => m_obs M2 v
        | None => None
        end
    | Some (C l c r) =>
        match m1_to_m2 l, m1_to_m2 r with
        | Some vl, Some vr => m_obs M2 (m_op M2 vl (m_op M2 c vr))
        | _, _ => None
        end
    | None => None
    end.

  Definition chunk : MonoidalOps (del I D) R :=
    {| m_summary := t; m_ne := ne; m_op := op;
       m_gen := gen; m_obs := obs |}.

  Lemma none_left x : op None x = None.
  Proof. destruct x as [[a|l c r]|]; reflexivity. Qed.

  Lemma none_right x : op x None = None.
  Proof. destruct x as [[a|l c r]|]; reflexivity. Qed.

  Theorem op_assoc : IsMonoid M1 -> IsMonoid M2 ->
    forall x y z, op (op x y) z = op x (op y z).
  Proof.
    intros [H1 _] [H2 _] [[xa|xl xc xr]|]
      [[ya|yl yc yr]|] [[za|zl zc zr]|];
      simpl; rewrite ?H1;
      repeat match goal with
      | |- context [m1_to_m2 ?s] => destruct (m1_to_m2 s) eqn:?;
          simpl; repeat match goal with
          | H : m1_to_m2 ?s = _ |- context [m1_to_m2 ?s] => rewrite H
          end
      end;
      simpl; rewrite ?H2; reflexivity.
  Qed.

  Theorem ne_left_neutral : IsMonoid M1 -> forall x, op ne x = x.
  Proof.
    intros [_ [H _]] [[a|l c r]|]; unfold ne; simpl;
      rewrite ?H; reflexivity.
  Qed.

  Theorem ne_right_neutral : IsMonoid M1 -> forall x, op x ne = x.
  Proof.
    intros [_ [_ H]] [[a|l c r]|]; unfold ne; simpl;
      rewrite ?H; reflexivity.
  Qed.

  (** No reachability invariant or laws for [m_obs]/[m_gen] are required.
      In particular, observations are not assumed total or homomorphic. *)
  Theorem chunk_is_monoid : IsMonoid M1 -> IsMonoid M2 -> IsMonoid chunk.
  Proof.
    intros H1 H2; split; [exact (op_assoc H1 H2)|].
    split; [exact (ne_left_neutral H1)|exact (ne_right_neutral H1)].
  Qed.

  Lemma ignored_delimiter c : del_ign c = true -> gen (Del c) = ne.
  Proof. intro H; unfold gen; rewrite H; reflexivity. Qed.

  Lemma retained_delimiter c : del_ign c = false ->
    gen (Del c) = Some (C (m_ne M1) (m_gen M2 (Del c)) (m_ne M1)).
  Proof. intro H; unfold gen; rewrite H; reflexivity. Qed.

  Lemma boundary_observation_failure lx cx rx ly cy ry :
    m_obs M1 (m_op M1 rx ly) = None ->
    op (Some (C lx cx rx)) (Some (C ly cy ry)) = None.
  Proof. intro H; unfold op, m1_to_m2; rewrite H; reflexivity. Qed.
End Construction.
End ChunkMonoid.
