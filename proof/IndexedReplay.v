From Stdlib Require Import Arith Lia.

(** Algebra of indexed iteration.  A concrete loop is supplied together with
    its zero/step equations; no change to its implementation is required.
    The state may itself be an option, with failure handled by the step. *)
Section Iteration.
  Context {State : Type}.
  Variable run : nat -> nat -> State -> State.
  Hypothesis run_zero : forall j s, run 0 j s = s.
  Hypothesis run_step : forall n j s,
    run (S n) j s = run n (S j) (run 1 j s).

  Theorem plus : forall p q j s,
    run (p + q) j s = run q (j + p) (run p j s).
  Proof.
    induction p as [|p IH]; intros q j s.
    - rewrite Nat.add_0_r, !run_zero; reflexivity.
    - change (run (S (p + q)) j s = run q (j + S p) (run (S p) j s)).
      rewrite (run_step (p + q) j s), (run_step p j s), IH.
      replace (S j + p) with (j + S p) by lia; reflexivity.
  Qed.

End Iteration.

Section LastStep.
  Context {State : Type}.
  Variable run : nat -> nat -> State -> State.
  Hypothesis run_plus : forall p q j s,
    run (p + q) j s = run q (j + p) (run p j s).
  Corollary snoc : forall p j s,
    run (S p) j s = run 1 (j + p) (run p j s).
  Proof.
    intros p j s; replace (S p) with (p + 1) by lia; apply run_plus.
  Qed.
End LastStep.
