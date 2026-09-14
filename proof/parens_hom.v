Require Import Monoid Parens.
Set Implicit Arguments.
Set Universe Polymorphism.

Module ParensHom.
Section DirectParens.
  Context {I O : Type}.
  Context (M : MonoidalOps (Nest I O) O).

  Definition close (x : m_summary M) : option (m_summary M) :=
    match m_obs M x with
    | Some v => Some (m_gen M (nested v))
    | None => None
    end.

  Inductive ParensForm :=
  | Failure : ParensForm
  | A : m_summary M -> ParensForm
  | Closed : m_summary M -> ParensForm
  | L : m_summary M -> m_summary M -> ParensForm
  | R : m_summary M -> m_summary M -> ParensForm
  | B : m_summary M -> m_summary M -> m_summary M -> ParensForm.

  Definition combine_forms (x y : ParensForm) : ParensForm :=
    match x, y with
    | A x, A y => A (m_op M x y)
    | A xo, Closed yo => Closed (m_op M xo yo)
    | Closed xo, A yo => Closed (m_op M xo yo)
    | Closed xo, Closed yo => Closed (m_op M xo yo)
    | Closed xo, L yo yi => L (m_op M xo yo) yi
    | R xi xo, Closed yo => R xi (m_op M xo yo)
    | A xo, L yo yi => L (m_op M xo yo) yi
    | L xo xi, A yi => L xo (m_op M xi yi)
    | A xi, R yi yo => R (m_op M xi yi) yo
    | R xi xo, A yo => R xi (m_op M xo yo)
    | A xi, B yl yo yr => B (m_op M xi yl) yo yr
    | B xl xo xr, A yi => B xl xo (m_op M xr yi)
    | L xo xi, R yi yo =>
        match close (m_op M xi yi) with
        | Some c => Closed (m_op M xo (m_op M c yo))
        | None => Failure
        end
    | R xi xo, L yo yi => B xi (m_op M xo yo) yi
    | L xo xi, B yi yo yr =>
        match close (m_op M xi yi) with
        | Some c => L (m_op M xo (m_op M c yo)) yr
        | None => Failure
        end
    | B xl xo xr, R yi yo =>
        match close (m_op M xr yi) with
        | Some c => R xl (m_op M xo (m_op M c yo))
        | None => Failure
        end
    | B xl xo xr, B yl yo yr =>
        match close (m_op M xr yl) with
        | Some c => B xl (m_op M xo (m_op M c yo)) yr
        | None => Failure
        end
    | _, _ => Failure
    end.

  Definition parens_ne : ParensForm :=
    A (m_ne M).

  Definition parens_op (x y : ParensForm) : ParensForm :=
    combine_forms x y.

  Lemma parens_op_failure_left x : parens_op Failure x = Failure.
  Proof. destruct x; reflexivity. Qed.
  Lemma parens_op_failure_right x : parens_op x Failure = Failure.
  Proof. destruct x; reflexivity. Qed.

  (** Every summary is now structurally admissible: there is no separate
      consistency invariant or canonicalisation premise. *)
  Theorem parens_ne_left_neutral :
    IsMonoid M -> forall x, parens_op parens_ne x = x.
  Proof.
    intros [_ [H1 _]] [|a|a|a b|a b|a b c];
      cbn [parens_op parens_ne combine_forms];
      rewrite ?H1; reflexivity.
  Qed.

  Theorem parens_ne_right_neutral :
    IsMonoid M -> forall x, parens_op x parens_ne = x.
  Proof.
    intros [_ [_ H1]] [|a|a|a b|a b|a b c];
      cbn [parens_op parens_ne combine_forms];
      rewrite ?H1; reflexivity.
  Qed.

  Theorem parens_op_assoc :
    IsMonoid M -> forall x y z,
    parens_op (parens_op x y) z = parens_op x (parens_op y z).
  Proof.
    intros [H1 _] x y z;
      destruct x; destruct y; destruct z;
      cbv [parens_op combine_forms]; cbn;
      rewrite ?H1;
      repeat match goal with
      | |- context [close ?s] =>
          destruct (close s) eqn:?;
          cbv [parens_op combine_forms]; cbn;
          repeat match goal with
          | H : close ?s = _ |- context [close ?s] => rewrite H
          end
      end;
      rewrite ?H1; reflexivity.
  Qed.

  Definition parens_gen (x : Token I) : ParensForm :=
    match x with
    | atom v => A (m_gen M (raw v))
    | left => L (m_ne M) (m_ne M)
    | right => R (m_ne M) (m_ne M)
    end.

  Definition parens_obs (x : ParensForm) : option O :=
    match x with
    | A outer | Closed outer => m_obs M outer
    | _ => None
    end.

  Definition parens_hom : MonoidalOps (Token I) O :=
    {| m_summary := ParensForm;
       m_ne := parens_ne; m_op := parens_op;
       m_gen := parens_gen; m_obs := parens_obs |}.

  Theorem parens_hom_is_monoid :
    IsMonoid M -> IsMonoid parens_hom.
  Proof.
    intro H1; split; [exact (parens_op_assoc H1)|].
    split; [exact (parens_ne_left_neutral H1)|
            exact (parens_ne_right_neutral H1)].
  Qed.

  (** Futhark's del input and configurable delimiter predicates.  The sum
      uses inl for #E and inr for #Del; a delimiter matching neither
      predicate is ignored.  Left takes precedence, as in Futhark. *)
  Definition parens_gen_del {D : Type} (is_left is_right : D -> bool)
      (x : (I + D)%type) : ParensForm :=
    match x with
    | inl v => parens_gen (atom v)
    | inr d => if is_left d then parens_gen left
               else if is_right d then parens_gen right
               else parens_ne
    end.

  Definition parens_del {D : Type} (is_left is_right : D -> bool)
      : MonoidalOps (I + D) O :=
    {| m_summary := ParensForm;
       m_ne := parens_ne; m_op := parens_op;
       m_gen := parens_gen_del is_left is_right; m_obs := parens_obs |}.

  Theorem parens_del_is_monoid {D : Type} (is_left is_right : D -> bool) :
    IsMonoid M -> IsMonoid (parens_del is_left is_right).
  Proof. exact parens_hom_is_monoid. Qed.
  (** The existing heterogeneous combinator with a raw-only view of M is
      the semantic reference. Embedding duplicates only the A payload. *)
  Definition raw_view : MonoidalOps I O :=
    {| m_summary := m_summary M; m_ne := m_ne M; m_op := m_op M;
       m_gen := fun x => m_gen M (raw x); m_obs := m_obs M |}.

  Definition embed (x:ParensForm) : Parens.ParensForm raw_view M :=
    match x with
    | Failure => Parens.Failure raw_view M
    | A a => Parens.A raw_view M a a
    | Closed a => Parens.Closed raw_view M a
    | L a b => Parens.L raw_view M a b
    | R a b => Parens.R raw_view M a b
    | B a b c => Parens.B raw_view M a b c
    end.

  Lemma embed_injective x y : embed x = embed y -> x = y.
  Proof. destruct x, y; cbn [embed]; congruence. Qed.

  Theorem operation_correspondence x y :
    embed (parens_op x y) = Parens.parens_op (embed x) (embed y).
  Proof.
    destruct x, y;
      cbv [parens_op combine_forms embed Parens.parens_op Parens.combine_forms
           close Parens.close raw_view]; cbn;
      repeat match goal with
      | |- context [m_obs M ?s] => destruct (m_obs M s) eqn:?
      end; reflexivity.
  Qed.
  Lemma neutral_correspondence : embed parens_ne = Parens.parens_ne raw_view M.
  Proof. reflexivity. Qed.
  Lemma generation_correspondence x : embed (parens_gen x) = Parens.parens_gen raw_view M x.
  Proof. destruct x; reflexivity. Qed.
  Lemma observation_correspondence x : parens_obs x = Parens.parens_obs (embed x).
  Proof. destruct x; reflexivity. Qed.
End DirectParens.
End ParensHom.
