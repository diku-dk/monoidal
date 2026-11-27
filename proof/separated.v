From Stdlib Require Import List Bool.
Require Import Monoid Parens.
Import ListNotations.
Set Implicit Arguments.
Set Universe Polymorphism.

(** Direct [separated] representation. None is Futhark's #Fail; the two
    booleans mark whether the first/last token is an element (true) or a
    delimiter (false). Observation uses option to model rejection/failure. *)
Module SeparatedMonoid.
Section Construction.
  Context {B I O : Type} (A : MonoidalOps I O).
  Context (is_delimiter : B -> bool).
  Inductive form := Empty | Seq : bool -> m_summary A -> bool -> form.
  Definition t := option form.
  Definition ne : t := Some Empty.
  Definition op (x y : t) : t :=
    match x, y with
    | Some Empty, _ => y | _, Some Empty => x
    | Some (Seq a s b), Some (Seq c u d) =>
        if Bool.eqb b c then None else Some (Seq a (m_op A s u) d)
    | _, _ => None
    end.
  Definition classify (x : Nest B (option I)) : option (bool * m_summary A) :=
    match x with
    | nested (Some v) => Some (true, m_gen A v)
    | raw c => if is_delimiter c then Some (false, m_ne A) else None
    | _ => None
    end.
  Definition gen (x : Nest B (option I)) : t :=
    match classify x with Some (k,s) => Some (Seq k s k) | None => None end.
  Definition obs (x : t) : option O :=
    match x with
    | Some Empty => m_obs A (m_ne A)
    | Some (Seq true s true) => m_obs A s
    | _ => None
    end.
  Definition separated : MonoidalOps (Nest B (option I)) O :=
    {| m_summary := t; m_ne := ne; m_op := op; m_gen := gen; m_obs := obs |}.

  Theorem op_assoc : IsMonoid A -> forall x y z,
    op (op x y) z = op x (op y z).
  Proof.
    intros [Ha _] [[|a s b]|] [[|c u d]|] [[|e v f]|];
      repeat match goal with k : bool |- _ => destruct k end;
      cbn [op Bool.eqb]; rewrite ?Ha; reflexivity.
  Qed.
  Theorem ne_left_neutral : forall x, op ne x = x.
  Proof. destruct x as [[|a s b]|]; reflexivity. Qed.
  Theorem ne_right_neutral : forall x, op x ne = x.
  Proof. destruct x as [[|a s b]|]; reflexivity. Qed.
  Theorem separated_is_monoid : IsMonoid A -> IsMonoid separated.
  Proof. intro H; split; [exact (op_assoc H)|].
    split; [exact ne_left_neutral|exact ne_right_neutral]. Qed.
  Lemma fail_left x : op None x = None.
  Proof. destruct x as [[|a s b]|]; reflexivity. Qed.
  Lemma fail_right x : op x None = None.
  Proof. destruct x as [[|a s b]|]; reflexivity. Qed.

  Definition fold (xs : list (Nest B (option I))) : t :=
    fold_right (fun x s => op (gen x) s) ne xs.
  Theorem fold_app : IsMonoid A -> forall xs ys,
    fold (xs ++ ys) = op (fold xs) (fold ys).
  Proof.
    intros H xs; induction xs as [|x xs IH]; intro ys; cbn [fold fold_right app].
    - symmetry; apply ne_left_neutral.
    - rewrite IH; symmetry; apply (op_assoc H).
  Qed.

  (** Independent grammar for a nonempty sequence of alternating token kinds.
      It also specifies the ordered aggregate. Delimiters contribute A.ne. *)
  Inductive Parses : list (Nest B (option I)) -> bool -> m_summary A -> bool -> Prop :=
  | Parses_one : forall x k s, classify x = Some (k,s) -> Parses [x] k s k
  | Parses_cons : forall x xs k a first s last,
      classify x = Some (k,a) -> Parses xs first s last ->
      k <> first -> Parses (x::xs) k (m_op A a s) last.

  Lemma fold_empty_iff xs : fold xs = ne <-> xs = [].
  Proof.
    destruct xs as [|x xs]; [split; reflexivity|].
    split; [|discriminate].
    intro H; change (op (gen x) (fold xs) = Some Empty) in H.
    unfold gen in H; destruct (classify x) as [[k a]|];
      destruct (fold xs) as [[|f s l]|];
      repeat match goal with b : bool |- _ => destruct b end;
      cbn [op Bool.eqb] in H; discriminate.
  Qed.
  Theorem parses_sound : forall xs first s last,
    Parses xs first s last -> fold xs = Some (Seq first s last).
  Proof.
    intros xs first s last H; induction H.
    - change (op (gen x) ne = Some (Seq k s k)).
      unfold gen; rewrite H; reflexivity.
    - change (op (gen x) (fold xs) = Some (Seq k (m_op A a s) last)).
      unfold gen; rewrite H, IHParses.
      cbn [op Bool.eqb]; destruct k, first; cbn; try reflexivity; contradiction.
  Qed.
  Theorem parses_complete : forall xs first s last,
    fold xs = Some (Seq first s last) -> Parses xs first s last.
  Proof.
    induction xs as [|x xs IH]; intros first s last H; [discriminate|].
    destruct xs as [|y ys].
    - change (op (gen x) ne = Some (Seq first s last)) in H.
      unfold gen, ne in H.
      destruct (classify x) as [[k a]|] eqn:C; cbn [op Bool.eqb] in H; try discriminate.
      inversion H; subst; now apply Parses_one.
    - change (op (gen x) (fold (y::ys)) = Some (Seq first s last)) in H.
      destruct (fold (y::ys)) as [[|f u l]|] eqn:F.
      + exfalso; apply fold_empty_iff in F; discriminate.
      + unfold gen in H; destruct (classify x) as [[k a]|] eqn:C;
          cbn [op Bool.eqb] in H; try discriminate.
        destruct (Bool.eqb k f) eqn:E; try discriminate.
        inversion H; subst.
        eapply Parses_cons; [exact C|apply IH; reflexivity|].
        intro Eq; subst; rewrite Bool.eqb_reflx in E; discriminate.
      + rewrite fail_right in H; discriminate.
  Qed.
  Theorem fold_characterisation xs first s last :
    fold xs = Some (Seq first s last) <-> Parses xs first s last.
  Proof. split; [apply parses_complete|apply parses_sound]. Qed.

  Definition contribution (x : Nest B (option I)) : m_summary A :=
    match x with nested (Some v) => m_gen A v | _ => m_ne A end.
  Lemma classify_contribution x k s : classify x = Some (k,s) -> contribution x = s.
  Proof.
    destruct x as [c|[v|]]; cbn [classify contribution]; try discriminate.
    - destruct (is_delimiter c); intro H; inversion H; reflexivity.
    - intro H; inversion H; reflexivity.
  Qed.
  Theorem parses_aggregate : IsMonoid A -> forall xs first s last,
    Parses xs first s last ->
    s = fold_right (m_op A) (m_ne A) (map contribution xs).
  Proof.
    intros [_ [_ Hr]] xs first s last H; induction H; cbn.
    - rewrite (classify_contribution x H), Hr; reflexivity.
    - rewrite (classify_contribution x H), <- IHParses; reflexivity.
  Qed.
  Corollary accepted_observation : IsMonoid A -> forall xs s,
    Parses xs true s true -> obs (fold xs) =
      m_obs A (fold_right (m_op A) (m_ne A) (map contribution xs)).
  Proof.
    intros H xs s P; rewrite (parses_sound P); cbn [obs].
    now rewrite (parses_aggregate H P).
  Qed.
  Theorem rejected_observation xs : xs <> [] ->
    (forall s, ~ Parses xs true s true) -> obs (fold xs) = None.
  Proof.
    intros N P; destruct (fold xs) as [[|first s last]|] eqn:F; cbn [obs].
    - apply fold_empty_iff in F; contradiction.
    - destruct first, last; cbn; try reflexivity.
      exfalso; apply (P s); now apply parses_complete.
    - reflexivity.
  Qed.
  Lemma empty_observation : obs (fold []) = m_obs A (m_ne A).
  Proof. reflexivity. Qed.
  Lemma invalid_value_rejected : gen (nested None) = None.
  Proof. reflexivity. Qed.
  Lemma adjacent_elements_rejected v w :
    op (gen (nested (Some v))) (gen (nested (Some w))) = None.
  Proof. reflexivity. Qed.
  Lemma neutral_value_still_present v : m_gen A v = m_ne A ->
    gen (nested (Some v)) = Some (Seq true (m_ne A) true).
  Proof. intro H; unfold gen, classify; now rewrite H. Qed.
  Lemma invalid_raw_rejected c : is_delimiter c = false -> gen (raw c) = None.
  Proof. intro H; unfold gen, classify; now rewrite H. Qed.
  Lemma adjacent_delimiters_rejected c d :
    is_delimiter c = true -> is_delimiter d = true ->
    op (gen (raw c)) (gen (raw d)) = None.
  Proof. intros Hc Hd; unfold gen, classify; rewrite Hc, Hd; reflexivity. Qed.
  Lemma delimiter_only_rejected c : obs (fold [raw c]) = None.
  Proof. unfold fold; cbn [fold_right]; unfold gen, classify.
    destruct (is_delimiter c); reflexivity. Qed.
End Construction.
End SeparatedMonoid.
