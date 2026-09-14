From Stdlib Require Import List ZArith Lia.
Require Export Monoid.

Import ListNotations.
Open Scope Z_scope.
Set Implicit Arguments.
Set Universe Polymorphism.

(** Inputs to homogeneous nesting.  [nested x] is the result injected after
    a balanced parenthesised region has been observed. *)
Inductive Nest (I O : Type) :=
| raw : I -> Nest I O
| nested : O -> Nest I O.

Arguments raw {_ _} _.
Arguments nested {_ _} _.


Inductive Token (I : Type) :=
| atom : I -> Token I
| left : Token I
| right : Token I.

Arguments atom {_} _.
Arguments left {_}.
Arguments right {_}.

(** Exact depth metadata used by the Futhark implementation.  [lo] and [hi]
    are the minimum and maximum relative prefix depths of a fragment; [net]
    is its final relative depth. *)
Record Depth := depth {
  lo : Z;
  hi : Z;
  net : Z
}.

Definition zmin : Z -> Z -> Z := Z.min.
Definition zmax : Z -> Z -> Z := Z.max.

Definition depth_ne : Depth := depth 0 0 0.

(** If [y] follows [x], the prefix depths of [y] are shifted by [net x]. *)
Definition depth_op (x y : Depth) : Depth :=
  depth (zmin (lo x) (net x + lo y))
        (zmax (hi x) (net x + hi y))
        (net x + net y).

Lemma depth_ext (x y : Depth) :
  lo x = lo y -> hi x = hi y -> net x = net y -> x = y.
Proof.
  destruct x, y; simpl; intros; subst; reflexivity.
Qed.

Lemma depth_op_assoc (x y z : Depth) :
  depth_op (depth_op x y) z = depth_op x (depth_op y z).
Proof.
  apply depth_ext; destruct x, y, z; simpl; unfold zmin, zmax.
  - rewrite <- Z.add_min_distr_l.
    repeat rewrite Z.add_assoc.
    rewrite Z.min_assoc; reflexivity.
  - rewrite <- Z.add_max_distr_l.
    repeat rewrite Z.add_assoc.
    rewrite Z.max_assoc; reflexivity.
  - lia.
Qed.

Lemma depth_ne_l (x : Depth) :
  lo x <= 0 -> 0 <= hi x -> depth_op depth_ne x = x.
Proof.
  intros Hlo Hhi; apply depth_ext; destruct x as [xl xh xn];
    simpl in *; unfold zmin, zmax.
  - rewrite Z.min_r; lia.
  - rewrite Z.max_r; lia.
  - lia.
Qed.

Lemma depth_ne_r (x : Depth) :
  lo x <= net x -> net x <= hi x -> depth_op x depth_ne = x.
Proof.
  intros Hlo Hhi; apply depth_ext; destruct x as [xl xh xn];
    simpl in *; unfold zmin, zmax.
  - rewrite Z.min_l; lia.
  - rewrite Z.max_l; lia.
  - lia.
Qed.

Definition depth_span (d : Depth) : Z := hi d - lo d.
Definition supported (d : Depth) : bool := Z.leb (depth_span d) 1.

Lemma depth_span_op_ge_l (x y : Depth) :
  depth_span x <= depth_span (depth_op x y).
Proof.
  destruct x as [xl xh xn], y as [yl yh yn].
  unfold depth_span, depth_op, zmin, zmax; simpl.
  pose proof (Z.le_min_l xl (xn + yl)).
  pose proof (Z.le_max_l xh (xn + yh)).
  lia.
Qed.

Lemma depth_span_op_ge_r (x y : Depth) :
  depth_span y <= depth_span (depth_op x y).
Proof.
  destruct x as [xl xh xn], y as [yl yh yn].
  unfold depth_span, depth_op, zmin, zmax; simpl.
  pose proof (Z.le_min_r xl (xn + yl)).
  pose proof (Z.le_max_r xh (xn + yh)).
  lia.
Qed.

Definition atom_depth : Depth := depth 0 0 0.
Definition left_depth : Depth := depth 0 1 1.
Definition right_depth : Depth := depth (-1) 0 (-1).

Definition token_depth {I} (t : Token I) : Depth :=
  match t with
  | atom _ => atom_depth
  | left => left_depth
  | right => right_depth
  end.

Definition encode_depth {I} (w : list (Token I)) : Depth :=
  fold_right (fun t d => depth_op (token_depth t) d) depth_ne w.

Lemma depth_op_bounds (x y : Depth) :
  lo x <= 0 -> 0 <= hi x ->
  lo y <= net y -> net y <= hi y ->
  lo (depth_op x y) <= 0 /\
  0 <= hi (depth_op x y) /\
  lo (depth_op x y) <= net (depth_op x y) /\
  net (depth_op x y) <= hi (depth_op x y).
Proof.
  intros Hxlo Hxhi Hylon Hynhi.
  destruct x as [xl xh xn], y as [yl yh yn];
    unfold depth_op, zmin, zmax; simpl in *.
  repeat split.
  - eapply Z.le_trans; [apply Z.le_min_l | exact Hxlo].
  - eapply Z.le_trans; [exact Hxhi | apply Z.le_max_l].
  - eapply Z.le_trans; [apply Z.le_min_r |]; lia.
  - eapply Z.le_trans; [| apply Z.le_max_r]; lia.
Qed.

Lemma encode_depth_bounds {I} (w : list (Token I)) :
  lo (encode_depth w) <= 0 /\
  0 <= hi (encode_depth w) /\
  lo (encode_depth w) <= net (encode_depth w) /\
  net (encode_depth w) <= hi (encode_depth w).
Proof.
  induction w as [|t w [Hlo [Hhi [Hlon Hnhi]]]]; simpl.
  - repeat split; lia.
  - apply depth_op_bounds; destruct t; simpl; lia.
Qed.

Lemma encode_depth_append {I} (u v : list (Token I)) :
  encode_depth (u ++ v) = depth_op (encode_depth u) (encode_depth v).
Proof.
  induction u as [|t u IH]; simpl.
  - symmetry; apply depth_ne_l;
      pose proof (encode_depth_bounds v) as [Hlo [Hhi _]]; assumption.
  - rewrite IH, depth_op_assoc; reflexivity.
Qed.

(** Compact counterpart of Futhark's parens: the constructors encode depth
    metadata, and Closed has only an outer summary. Failure is an absorbing
    constructor in the summary itself. Observations still return options;
    an observation failure encountered by close produces Failure. *)
Section DirectParens.
  Context {I O R0 : Type}.
  Context (M1 : MonoidalOps I O).
  Context (M2 : MonoidalOps (Nest I O) R0).

  Definition close (x : m_summary M1) : option (m_summary M2) :=
    match m_obs M1 x with
    | Some v => Some (m_gen M2 (nested v))
    | None => None
    end.

  Inductive ParensForm :=
  | Failure : ParensForm
  | A : m_summary M1 -> m_summary M2 -> ParensForm
  | Closed : m_summary M2 -> ParensForm
  | L : m_summary M2 -> m_summary M1 -> ParensForm
  | R : m_summary M1 -> m_summary M2 -> ParensForm
  | B : m_summary M1 -> m_summary M2 -> m_summary M1 -> ParensForm.

  Definition form_depth (x : ParensForm) : Depth :=
    match x with
    | Failure => depth 0 0 0 (* Shape metadata is irrelevant for failure. *)
    | A _ _ => depth 0 0 0
    | Closed _ => depth 0 1 0
    | L _ _ => depth 0 1 1
    | R _ _ => depth (-1) 0 (-1)
    | B _ _ _ => depth (-1) 0 0
    end.

  Definition combine_forms (x y : ParensForm) : ParensForm :=
    match x, y with
    | A xi xo, A yi yo => A (m_op M1 xi yi) (m_op M2 xo yo)
    | A _ xo, Closed yo => Closed (m_op M2 xo yo)
    | Closed xo, A _ yo => Closed (m_op M2 xo yo)
    | Closed xo, Closed yo => Closed (m_op M2 xo yo)
    | Closed xo, L yo yi => L (m_op M2 xo yo) yi
    | R xi xo, Closed yo => R xi (m_op M2 xo yo)
    | A _ xo, L yo yi => L (m_op M2 xo yo) yi
    | L xo xi, A yi _ => L xo (m_op M1 xi yi)
    | A xi _, R yi yo => R (m_op M1 xi yi) yo
    | R xi xo, A _ yo => R xi (m_op M2 xo yo)
    | A xi _, B yl yo yr => B (m_op M1 xi yl) yo yr
    | B xl xo xr, A yi _ => B xl xo (m_op M1 xr yi)
    | L xo xi, R yi yo =>
        match close (m_op M1 xi yi) with
        | Some c => Closed (m_op M2 xo (m_op M2 c yo))
        | None => Failure
        end
    | R xi xo, L yo yi => B xi (m_op M2 xo yo) yi
    | L xo xi, B yi yo yr =>
        match close (m_op M1 xi yi) with
        | Some c => L (m_op M2 xo (m_op M2 c yo)) yr
        | None => Failure
        end
    | B xl xo xr, R yi yo =>
        match close (m_op M1 xr yi) with
        | Some c => R xl (m_op M2 xo (m_op M2 c yo))
        | None => Failure
        end
    | B xl xo xr, B yl yo yr =>
        match close (m_op M1 xr yl) with
        | Some c => B xl (m_op M2 xo (m_op M2 c yo)) yr
        | None => Failure
        end
    | _, _ => Failure
    end.

  Definition parens_ne : ParensForm :=
    A (m_ne M1) (m_ne M2).

  Definition parens_op (x y : ParensForm) : ParensForm :=
    combine_forms x y.

  (** Constructor dispatch handles invalid shapes and the absorbing failure
      constructor directly, without an option wrapper or depth arithmetic. *)
  Lemma combine_forms_depth_guard_redundant x y :
    (if supported (depth_op (form_depth x) (form_depth y))
     then combine_forms x y else Failure) = combine_forms x y.
  Proof.
    destruct x; destruct y;
      cbv [form_depth depth_op supported depth_span zmin zmax lo hi net];
      reflexivity.
  Qed.

  Theorem parens_op_guarded_equivalent x y :
    parens_op x y =
    (if supported (depth_op (form_depth x) (form_depth y))
     then combine_forms x y else Failure).
  Proof. symmetry; apply combine_forms_depth_guard_redundant. Qed.

  Lemma parens_op_failure_left x : parens_op Failure x = Failure.
  Proof. destruct x; reflexivity. Qed.
  Lemma parens_op_failure_right x : parens_op x Failure = Failure.
  Proof. destruct x; reflexivity. Qed.

  (** Every summary is now structurally admissible: there is no separate
      consistency invariant or canonicalisation premise. *)
  Theorem parens_ne_left_neutral :
    IsMonoid M1 -> IsMonoid M2 -> forall x, parens_op parens_ne x = x.
  Proof.
    intros [_ [H1 _]] [_ [H2 _]] [|a b|a|a b|a b|a b c];
      cbn [parens_op parens_ne combine_forms];
      rewrite ?H1, ?H2; reflexivity.
  Qed.

  Theorem parens_ne_right_neutral :
    IsMonoid M1 -> IsMonoid M2 -> forall x, parens_op x parens_ne = x.
  Proof.
    intros [_ [_ H1]] [_ [_ H2]] [|a b|a|a b|a b|a b c];
      cbn [parens_op parens_ne combine_forms];
      rewrite ?H1, ?H2; reflexivity.
  Qed.

  Theorem parens_op_assoc :
    IsMonoid M1 -> IsMonoid M2 -> forall x y z,
    parens_op (parens_op x y) z = parens_op x (parens_op y z).
  Proof.
    intros [H1 _] [H2 _] x y z;
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
      rewrite ?H2; reflexivity.
  Qed.

  Definition parens_gen (x : Token I) : ParensForm :=
    match x with
    | atom v => A (m_gen M1 v) (m_gen M2 (raw v))
    | left => L (m_ne M2) (m_ne M1)
    | right => R (m_ne M1) (m_ne M2)
    end.

  Definition parens_obs (x : ParensForm) : option R0 :=
    match x with
    | A _ outer | Closed outer => m_obs M2 outer
    | _ => None
    end.

  Definition parens : MonoidalOps (Token I) R0 :=
    {| m_summary := ParensForm;
       m_ne := parens_ne; m_op := parens_op;
       m_gen := parens_gen; m_obs := parens_obs |}.

  Theorem parens_is_monoid :
    IsMonoid M1 -> IsMonoid M2 -> IsMonoid parens.
  Proof.
    intros H1 H2; split; [exact (parens_op_assoc H1 H2)|].
    split; [exact (parens_ne_left_neutral H1 H2)|
            exact (parens_ne_right_neutral H1 H2)].
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
      : MonoidalOps (I + D) R0 :=
    {| m_summary := ParensForm;
       m_ne := parens_ne; m_op := parens_op;
       m_gen := parens_gen_del is_left is_right; m_obs := parens_obs |}.

  Theorem parens_del_is_monoid {D : Type} (is_left is_right : D -> bool) :
    IsMonoid M1 -> IsMonoid M2 -> IsMonoid (parens_del is_left is_right).
  Proof. exact parens_is_monoid. Qed.
End DirectParens.

Module ParensRegression.
  Definition inner : MonoidalOps unit Z :=
    {| m_summary := Z; m_ne := 0; m_op := Z.add;
       m_gen := fun _ => 7; m_obs := fun x => Some x |}.
  Definition outer : MonoidalOps (Nest unit Z) Z :=
    {| m_summary := Z; m_ne := 0; m_op := Z.add;
       m_gen := fun x => match x with raw _ => 7 | nested v => v end;
       m_obs := fun x => Some x |}.
  Definition x := parens_gen inner outer (atom tt).
  Definition l := parens_gen inner outer left.
  Definition r := parens_gen inner outer right.

  Example grouping_summaries_equal :
    parens_op (parens_op x l) r = parens_op x (parens_op l r).
  Proof. reflexivity. Qed.
  Example closed_has_only_outer :
    parens_op (parens_op x l) r = Closed inner outer 7.
  Proof. reflexivity. Qed.
  Example observed_value : parens_obs (parens_op (parens_op x l) r) = Some 7.
  Proof. reflexivity. Qed.
  Example nested_parentheses_fail :
    parens_op l (parens_op l (parens_op r r)) = Failure _ _.
  Proof. reflexivity. Qed.
  Example nested_closed_fail : parens_op l (parens_op l r) = Failure _ _.
  Proof. reflexivity. Qed.
  Example ignored_delimiter :
    parens_gen_del inner outer (fun _ : unit => false) (fun _ => false)
      (inr tt) = parens_ne inner outer.
  Proof. reflexivity. Qed.

  Definition failing_inner : MonoidalOps unit Z :=
    {| m_summary := Z; m_ne := 0; m_op := Z.add;
       m_gen := fun _ => 7; m_obs := fun _ => None |}.
  Example inner_observation_failure :
    parens_op (parens_gen failing_inner outer left)
              (parens_gen failing_inner outer right) = Failure _ _.
  Proof. reflexivity. Qed.
End ParensRegression.
