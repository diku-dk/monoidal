From Stdlib Require Import ZArith List Lia.
Require Import Monoid arith.
Module CountMonoid.
(** Exact-integer abstraction of the i64 counter; overflow is not modelled. *)
Definition count (I : Type) : MonoidalOps I Z :=
  {| m_summary := Z; m_ne := 0%Z; m_op := Z.add;
     m_gen := fun _ => 1%Z; m_obs := fun x => Some x |}.
Theorem count_is_monoid I : IsMonoid (count I).
Proof. exact ArithMonoid.sum_is_monoid. Qed.
Theorem count_length {I} (xs : list I) :
  fold_right (fun x acc => m_op (count I) (m_gen (count I) x) acc)
    (m_ne (count I)) xs = Z.of_nat (length xs).
Proof.
  induction xs as [|x xs IH]; [reflexivity|].
  change (1 + fold_right (fun _ acc => (1 + acc)%Z) 0%Z xs =
    Z.of_nat (S (length xs)))%Z.
  change (fold_right (fun _ acc => (1 + acc)%Z) 0%Z xs =
    Z.of_nat (length xs)) in IH.
  rewrite IH, Nat2Z.inj_succ; lia.
Qed.
End CountMonoid.
