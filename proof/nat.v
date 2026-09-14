From Stdlib Require Import ZArith Ascii List Lia.
Require Import Monoid.

Set Implicit Arguments.
Set Universe Polymorphism.

(** Horner summaries for Futhark's [nat (Y:numeric)].  The arithmetic
    operations are abstract: the numeric interface alone does not guarantee
    exact algebraic laws (in particular, floating-point addition is not
    associative).  No digit-validity invariant is needed for the monoid laws.
    [ascii] is an eight-bit input, corresponding to [u8]. *)
Module NatMonoid.

Record NumericOps := {
  number : Type;
  of_Z : Z -> number;
  add : number -> number -> number;
  mul : number -> number -> number;
  sub : number -> number -> number
}.

Section Construction.
  Context (Y : NumericOps).

  Definition t : Type := (number Y * number Y)%type.
  Definition ne : t := (of_Z Y 0, of_Z Y 1).
  Definition op (a b : t) : t :=
    let '(x, b1) := a in
    let '(y, b2) := b in
    (add Y (mul Y x b2) y, mul Y b1 b2).
  Definition gen (x : ascii) : t :=
    (sub Y (of_Z Y (Z.of_nat (nat_of_ascii x))) (of_Z Y 48), of_Z Y 10).
  Definition obs (x : t) : option (number Y) := Some (fst x).

  Definition nat : MonoidalOps ascii (number Y) :=
    {| m_summary := t; m_ne := ne; m_op := op;
       m_gen := gen; m_obs := obs |}.

  (** These are precisely the arithmetic identities used below.  There is
      no assumption about subtraction or digit conversion: they affect
      generation, not the summary algebra. *)
  Record ArithmeticLaws : Prop := {
    add_assoc : forall x y z, add Y (add Y x y) z = add Y x (add Y y z);
    add_zero_l : forall x, add Y (of_Z Y 0) x = x;
    add_zero_r : forall x, add Y x (of_Z Y 0) = x;
    mul_assoc : forall x y z, mul Y (mul Y x y) z = mul Y x (mul Y y z);
    mul_one_l : forall x, mul Y (of_Z Y 1) x = x;
    mul_one_r : forall x, mul Y x (of_Z Y 1) = x;
    mul_zero_l : forall x, mul Y (of_Z Y 0) x = of_Z Y 0;
    mul_add_r : forall x y z,
      mul Y (add Y x y) z = add Y (mul Y x z) (mul Y y z)
  }.

  Theorem op_assoc : ArithmeticLaws ->
    forall a b c, op (op a b) c = op a (op b c).
  Proof.
    intros H [x b1] [y b2] [z b3]; unfold op; simpl.
    rewrite (mul_add_r H), !(mul_assoc H), (add_assoc H).
    reflexivity.
  Qed.

  Theorem ne_left_neutral : ArithmeticLaws -> forall x, op ne x = x.
  Proof.
    intros H [x b]; unfold op, ne; simpl.
    rewrite (mul_zero_l H), (add_zero_l H), (mul_one_l H).
    reflexivity.
  Qed.

  Theorem ne_right_neutral : ArithmeticLaws -> forall x, op x ne = x.
  Proof.
    intros H [x b]; unfold op, ne; simpl.
    rewrite !(mul_one_r H), (add_zero_r H); reflexivity.
  Qed.

  Theorem nat_is_monoid : ArithmeticLaws -> IsMonoid nat.
  Proof.
    intro H; split; [exact (op_assoc H)|].
    split; [exact (ne_left_neutral H)|exact (ne_right_neutral H)].
  Qed.
End Construction.

(** Exact-integer instance.  Machine-integer instances require their own
    arithmetic-law proof; this instance does not model fixed-width overflow.
    Just like the Futhark code, [gen] subtracts '0' without rejecting input
    outside '0'..'9'. *)
Definition integers : NumericOps :=
  {| number := Z; of_Z := fun z => z;
     add := Z.add; mul := Z.mul; sub := Z.sub |}.

Theorem integer_arithmetic_laws : ArithmeticLaws integers.
Proof.
  constructor; cbn -[Z.add Z.mul]; intros; ring.
Qed.

Corollary integer_nat_is_monoid : IsMonoid (nat integers).
Proof. apply nat_is_monoid, integer_arithmetic_laws. Qed.

Definition run (input : list ascii) : option Z :=
  obs (List.fold_right (fun c acc => op (gen integers c) acc)
    (ne integers) input).

Example empty_input : run nil = Some 0%Z.
Proof. reflexivity. Qed.

Example multi_digit :
  run ("1"%char :: "2"%char :: "3"%char :: "4"%char :: nil) = Some 1234%Z.
Proof. reflexivity. Qed.

Example leading_zeros :
  run ("0"%char :: "0"%char :: "4"%char :: "2"%char :: nil) = Some 42%Z.
Proof. reflexivity. Qed.

Example combine_fragments :
  @op integers (12%Z, 100%Z) (345%Z, 1000%Z) = (12345%Z, 100000%Z).
Proof. reflexivity. Qed.

End NatMonoid.
