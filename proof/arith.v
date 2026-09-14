From Stdlib Require Import ZArith Lia.
Require Import Monoid.
Open Scope Z_scope.
Module ArithMonoid.
Definition simple {T : Type} (ne : T) (op : T -> T -> T) : MonoidalOps T T :=
  {| m_summary := T; m_ne := ne; m_op := op;
     m_gen := fun x => x; m_obs := fun x => Some x |}.
Lemma simple_is_monoid {T} (ne : T) op :
  (forall x y z, op (op x y) z = op x (op y z)) ->
  (forall x, op ne x = x) -> (forall x, op x ne = x) ->
  IsMonoid (simple ne op).
Proof. intros; repeat split; assumption. Qed.

(** Exact integers: no finite-width overflow or IEEE rounding is modelled. *)
Definition sum := simple 0 Z.add.
Definition mul := simple 1 Z.mul.
Theorem sum_is_monoid : IsMonoid sum.
Proof. apply simple_is_monoid; intros; lia. Qed.
Theorem mul_is_monoid : IsMonoid mul.
Proof. apply simple_is_monoid; intros; ring. Qed.

(** Unbounded integers have no lowest/highest element. Explicit sentinels
    model the bounds required by Futhark's max/min neutral elements. *)
Inductive bounded := Lowest | Finite : Z -> bounded | Highest.
Definition max_op (x y : bounded) : bounded :=
  match x,y with
  | Highest,_ | _,Highest => Highest
  | Lowest,_ => y | _,Lowest => x
  | Finite a,Finite b => Finite (Z.max a b)
  end.
Definition min_op (x y : bounded) : bounded :=
  match x,y with
  | Lowest,_ | _,Lowest => Lowest
  | Highest,_ => y | _,Highest => x
  | Finite a,Finite b => Finite (Z.min a b)
  end.
Definition max := simple Lowest max_op.
Definition min := simple Highest min_op.
Theorem max_is_monoid : IsMonoid max.
Proof.
  apply simple_is_monoid.
  - intros [|x|] [|y|] [|z|]; cbn; try reflexivity.
    now rewrite Z.max_assoc.
  - intros [|x|]; reflexivity.
  - intros [|x|]; reflexivity.
Qed.
Theorem min_is_monoid : IsMonoid min.
Proof.
  apply simple_is_monoid.
  - intros [|x|] [|y|] [|z|]; cbn; try reflexivity.
    now rewrite Z.min_assoc.
  - intros [|x|]; reflexivity.
  - intros [|x|]; reflexivity.
Qed.
Example max_negative : max_op (Finite (-12)) (Finite (-3)) = Finite (-3).
Proof. reflexivity. Qed.
Example min_positive : min_op (Finite 12) (Finite 34) = Finite 12.
Proof. reflexivity. Qed.
End ArithMonoid.
