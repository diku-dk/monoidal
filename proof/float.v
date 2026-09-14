From Stdlib Require Import QArith Qcanon Ascii Field Eqdep_dec Bool.
Require Import Monoid.

Open Scope Qc_scope.

(** Exact-arithmetic model of the corrected float0 case table.
    Canonical rationals isolate structural errors from IEEE rounding.
    Failures use option, as in float0 instantiated with option_failure.
    This is not a model of finite-precision arithmetic. *)
Module FloatMonoid.
Local Notation "10" := (Q2Qc (inject_Z 10%Z)) : Qc_scope.
Local Notation "100" := (Q2Qc (inject_Z 100%Z)) : Qc_scope.
Local Notation "123" := (Q2Qc (inject_Z 123%Z)) : Qc_scope.
Inductive raw_t :=
| I : bool -> Qc -> Qc -> raw_t
| F : bool -> Qc -> Qc -> Qc -> raw_t
| P | M | NE.

Definition t := option raw_t.
Definition ne : t := Some NE.

Definition raw_op (a b : raw_t) : t :=
  match a, b with
  | NE, _ => Some b
  | _, NE => Some a
  | I s1 x b1, I s2 y b2 =>
      if s2 then None else Some (I s1 (x * b2 + y) (b1 * b2))
  | I s1 x b1, F s2 y b2 f2 =>
      if s2 then None else Some (F s1 (x * b2 + y) (b1 * b2) f2)
  | F s1 x b1 f1, I s2 y b2 =>
      if s2 then None else Some (F s1 (x + y * (f1 / b2)) b1 (f1 / b2))
  | I s x b, P => Some (F s x b 1)
  | P, I s x b =>
      if s then None else Some (F false (x / b) 1 (1 / b))
  | M, I s x b => if s then None else Some (I true x b)
  | M, F s x b f => if s then None else Some (F true x b f)
  | M, P => Some (F true 0 1 1)
  | _, _ => None
  end.

Definition op (a b : t) : t :=
  match a, b with Some x, Some y => raw_op x y | _, _ => None end.

Definition raw_obs (x : raw_t) : option Qc :=
  match x with
  | I s x _ | F s x _ _ => Some (if s then -x else x)
  | _ => None
  end.
Definition obs (x : t) : option Qc :=
  match x with Some x => raw_obs x | None => None end.

Definition gen (x : ascii) : t :=
  let c := nat_of_ascii x in
  if Nat.eqb c 46 then Some P
  else if Nat.eqb c 45 then Some M
  else if andb (Nat.leb 48 c) (Nat.leb c 57)
       then Some (I false (Q2Qc (inject_Z (Z.of_nat (c - 48)))) 10)
       else None.

Definition float : MonoidalOps ascii Qc :=
  {| m_summary := t; m_ne := ne; m_op := op; m_gen := gen; m_obs := obs |}.

Theorem ne_left_neutral : forall x, op ne x = x.
Proof. intros [x|]; [destruct x|]; reflexivity. Qed.

Theorem ne_right_neutral : forall x, op x ne = x.
Proof. intros [x|]; [destruct x|]; reflexivity. Qed.

Lemma none_left x : op None x = None.
Proof. reflexivity. Qed.

Lemma none_right x : op x None = None.
Proof. destruct x; reflexivity. Qed.

(** Decimal scales in generated summaries are nonzero.  No restriction on
    values, signs, or fractional scale is needed for the algebraic proof. *)
Definition Consistent (x : raw_t) : Prop :=
  match x with I _ _ b | F _ _ b _ => b <> 0 | _ => True end.
Definition ConsistentOpt (x : t) : Prop :=
  match x with Some x => Consistent x | None => True end.

Theorem op_assoc : forall x y z,
  ConsistentOpt x -> ConsistentOpt y -> ConsistentOpt z ->
  op (op x y) z = op x (op y z).
Proof.
  intros [x|] [y|] [z|]; try (destruct x); try (destruct y);
    try (destruct z); unfold ConsistentOpt, Consistent; intros;
    repeat match goal with b : bool |- _ => destruct b end;
    cbn [op raw_op]; try reflexivity;
    f_equal; f_equal; try (field; auto).
Qed.

Theorem ne_consistent : ConsistentOpt ne.
Proof. exact Logic.I. Qed.

Theorem op_preserves_consistency : forall x y,
  ConsistentOpt x -> ConsistentOpt y -> ConsistentOpt (op x y).
Proof.
  intros [x|] [y|]; try (destruct x); try (destruct y);
    repeat match goal with b : bool |- _ => destruct b end;
    cbn [op raw_op ConsistentOpt Consistent]; intros; try assumption;
    try exact Logic.I; try discriminate.
  all: intro Hzero; apply Qcmult_integral in Hzero; intuition.
Qed.

Theorem gen_consistent : forall c, ConsistentOpt (gen c).
Proof.
  intro c; unfold gen.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end;
    cbn [ConsistentOpt Consistent]; try exact Logic.I; discriminate.
Qed.

(** A decidable invariant lets us package the actual operation on a closed
    carrier without assuming proof irrelevance.  Equality proofs over bool
    are unique by [UIP_dec]. *)
Definition consistentb (x : t) : bool :=
  match x with
  | Some (I _ _ b) | Some (F _ _ b _) =>
      if Qc_eq_dec b 0 then false else true
  | _ => true
  end.

Lemma consistentb_spec x : consistentb x = true <-> ConsistentOpt x.
Proof.
  destruct x as [[s x b|s x b f| | |]|];
    cbn [consistentb ConsistentOpt Consistent]; try tauto;
    destruct (Qc_eq_dec b 0); intuition discriminate.
Qed.

Definition consistent_t := { x : t | consistentb x = true }.

Lemma consistent_ext (x y : consistent_t) :
  proj1_sig x = proj1_sig y -> x = y.
Proof.
  destruct x as [x Hx], y as [y Hy]; cbn; intro H; subst y.
  assert (Hx = Hy) by (apply UIP_dec; decide equality).
  subst Hy; reflexivity.
Qed.

Definition consistent_ne : consistent_t :=
  exist _ ne (proj2 (consistentb_spec ne) ne_consistent).

Definition consistent_op (x y : consistent_t) : consistent_t :=
  exist _ (op (proj1_sig x) (proj1_sig y))
    (proj2 (consistentb_spec _) (op_preserves_consistency _ _
      (proj1 (consistentb_spec _) (proj2_sig x))
      (proj1 (consistentb_spec _) (proj2_sig y)))).

Definition consistent_gen (c : ascii) : consistent_t :=
  exist _ (gen c) (proj2 (consistentb_spec _) (gen_consistent c)).

Definition consistent_float : MonoidalOps ascii Qc :=
  {| m_summary := consistent_t;
     m_ne := consistent_ne;
     m_op := consistent_op;
     m_gen := consistent_gen;
     m_obs := fun x => obs (proj1_sig x) |}.

Theorem float_is_monoid : IsMonoid consistent_float.
Proof.
  split.
  - intros [x Hx] [y Hy] [z Hz]; apply consistent_ext; cbn.
    apply op_assoc; apply consistentb_spec; assumption.
  - split; intros [x Hx]; apply consistent_ext; cbn.
    + apply ne_left_neutral.
    + apply ne_right_neutral.
Qed.

(** Regression for the fractional-scale fix, using generated fragments. *)
Definition one := gen "1"%char.
Definition point := gen "."%char.
Definition twenty_three := op (gen "2"%char) (gen "3"%char).

Example left_grouping :
  obs (op (op one point) twenty_three) = Some (123 / 100).
Proof. vm_compute; reflexivity. Qed.

Example right_grouping :
  obs (op one (op point twenty_three)) = Some (123 / 100).
Proof. vm_compute; reflexivity. Qed.

Example grouping_summaries_equal :
  op (op one point) twenty_three = op one (op point twenty_three).
Proof. vm_compute; reflexivity. Qed.

Definition forty_five := op (gen "4"%char) (gen "5"%char).

Example appended_fractional_digits :
  obs (op (op (op one point) twenty_three) forty_five) =
    Some (Q2Qc (12345 # 10000)).
Proof. vm_compute; apply f_equal, Qc_is_canon; reflexivity. Qed.

Example negative_fraction :
  obs (op (op (gen "-"%char) point) twenty_three) =
    Some (Q2Qc (-23 # 100)).
Proof. vm_compute; apply f_equal, Qc_is_canon; reflexivity. Qed.

Example misplaced_minus : op one (gen "-"%char) = None.
Proof. reflexivity. Qed.

Example invalid_character : gen "x"%char = None.
Proof. reflexivity. Qed.

Example repeated_point : op point point = None.
Proof. reflexivity. Qed.

Example empty_observation : obs ne = None.
Proof. reflexivity. Qed.
End FloatMonoid.
