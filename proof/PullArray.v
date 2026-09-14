From Stdlib Require Import Arith Bool FunctionalExtensionality Lia.

(** A small proof-oriented model of a pull array.  Values outside [size] are
    still represented by the function, but [get] exposes only valid indices
    and [put] ignores out-of-bounds updates. *)
  Record t (A : Type) := mk {
    size : nat;
    index : nat -> A
  }.

  Arguments mk {_} _ _.
  Arguments size {_} _.
  Arguments index {_} _ _.

  Definition replicate {A} (n : nat) (x : A) : t A :=
    mk n (fun _ => x).

  Definition get {A} (xs : t A) (i : nat) : option A :=
    if Nat.ltb i (size xs) then Some (index xs i) else None.

  Definition put {A} (xs : t A) (i : nat) (x : A) : t A :=
    if Nat.ltb i (size xs) then
      mk (size xs) (fun j => if Nat.eqb i j then x else index xs j)
    else xs.

  Lemma size_replicate {A} n (x : A) :
    size (replicate n x) = n.
  Proof. reflexivity. Qed.

  Lemma size_put {A} (xs : t A) i x :
    size (put xs i x) = size xs.
  Proof.
    unfold put; destruct (Nat.ltb i (size xs)); reflexivity.
  Qed.

  Lemma index_replicate {A} n (x : A) i :
    index (replicate n x) i = x.
  Proof. reflexivity. Qed.

  Lemma index_put_same {A} (xs : t A) i x :
    i < size xs -> index (put xs i x) i = x.
  Proof.
    intro Hi; unfold put.
    destruct (Nat.ltb i (size xs)) eqn:Htest.
    2:{ apply Nat.ltb_ge in Htest; lia. }
    simpl.
    now rewrite Nat.eqb_refl.
  Qed.

  Lemma index_put_other {A} (xs : t A) i j x :
    i <> j -> index (put xs i x) j = index xs j.
  Proof.
    intro Hneq; unfold put.
    destruct (Nat.ltb i (size xs)); simpl; [|reflexivity].
    apply Nat.eqb_neq in Hneq; now rewrite Hneq.
  Qed.

  Lemma put_out_of_bounds {A} (xs : t A) i x :
    size xs <= i -> put xs i x = xs.
  Proof.
    intro Hi; unfold put.
    destruct (Nat.ltb i (size xs)) eqn:Htest; [|reflexivity].
    apply Nat.ltb_lt in Htest; lia.
  Qed.

  Lemma ext {A} (xs ys : t A) :
    size xs = size ys ->
    (forall i, index xs i = index ys i) ->
    xs = ys.
  Proof.
    destruct xs as [nx fx], ys as [ny fy]; simpl.
    intros Hsize Hindex; subst ny.
    f_equal; apply functional_extensionality; exact Hindex.
  Qed.

  Lemma get_put_same {A} (xs : t A) i x :
    i < size xs -> get (put xs i x) i = Some x.
  Proof.
    intro Hi; unfold get.
    rewrite size_put.
    destruct (Nat.ltb i (size xs)) eqn:Htest.
    2:{ apply Nat.ltb_ge in Htest; lia. }
    now rewrite index_put_same.
  Qed.

  Lemma put_same {A} (xs : t A) i :
    i < size xs -> put xs i (index xs i) = xs.
  Proof.
    intro Hi; apply ext.
    - apply size_put.
    - intro j; destruct (Nat.eq_dec i j) as [->|Hneq].
      + now rewrite index_put_same.
      + now rewrite index_put_other.
  Qed.

  Lemma put_put_same_index {A} (xs : t A) i (x y : A) :
    put (put xs i x) i y = put xs i y.
  Proof.
    destruct (lt_dec i (size xs)) as [Hi|Hi].
    - apply ext.
      + now rewrite !size_put.
      + intro j; destruct (Nat.eq_dec i j) as [->|Hneq].
        * rewrite index_put_same by (now rewrite size_put).
          now rewrite index_put_same.
        * rewrite index_put_other by exact Hneq.
          rewrite index_put_other by exact Hneq.
          now rewrite index_put_other.
    - assert (Hout : size xs <= i) by lia.
      rewrite put_out_of_bounds by (now rewrite size_put).
      now rewrite !put_out_of_bounds.
  Qed.

  Lemma put_put_other_index {A} (xs : t A) i j (x y : A) :
    i <> j ->
    put (put xs i x) j y = put (put xs j y) i x.
  Proof.
    intro Hneq.
    unfold put.
    destruct (Nat.ltb i (size xs)) eqn:Hi,
      (Nat.ltb j (size xs)) eqn:Hj; simpl;
      rewrite ?Hi, ?Hj; try reflexivity.
    f_equal; apply functional_extensionality; intro k.
    destruct (Nat.eqb i k) eqn:Hik, (Nat.eqb j k) eqn:Hjk;
      try reflexivity.
    apply Nat.eqb_eq in Hik; apply Nat.eqb_eq in Hjk; congruence.
  Qed.
