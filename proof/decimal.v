From Stdlib Require Import ZArith Arith Ascii Bool Lia List String QArith Qcanon Eqdep_dec.
Require Import Monoid.
Open Scope nat_scope.

(** Model of decimal_try/decimal.  None represents #Fail; Minus represents
    #Minus.  NE names the canonical empty #D payload.  D contains every
    nonempty payload, with frac=None encoding -1 and Some f encoding f.
    Counts use naturals and mantissas use exact integers.  Observation is
    parameterised: floating-point rounding is not part of the monoid laws. *)
Module DecimalMonoid.
Inductive raw_t :=
| NE | Minus
| D (negative : bool) (digits : Z) (ndigits : nat) (frac : option nat).
Definition t := option raw_t.
Definition ne : t := Some NE.
Definition pow10 (n : nat) : Z := 10 ^ Z.of_nat n.
Definition raw_op (a b : raw_t) : t :=
  match a,b with
  | NE,_ => Some b
  | _,NE => Some a
  | D s x n f, D r y m g =>
      if r || (18 <? n+m) then None else
      match f,g with
      | Some _,Some _ => None
      | _,_ => Some (D s (x * pow10 m + y)%Z (n+m)
                         (match f with Some k => Some (k+m) | None => g end))
      end
  | Minus,D s x n f => if s then None else Some (D true x n f)
  | _,_ => None
  end.
Definition op (a b : t) : t :=
  match a,b with Some a,Some b => raw_op a b | _,_ => None end.

Lemma pow10_add n m : pow10 (n+m) = (pow10 n * pow10 m)%Z.
Proof. unfold pow10; rewrite Nat2Z.inj_add, Z.pow_add_r; auto; lia. Qed.

Theorem ne_left_neutral x : op ne x = x.
Proof. destruct x as [[]|]; reflexivity. Qed.
Theorem ne_right_neutral x : op x ne = x.
Proof. destruct x as [[]|]; reflexivity. Qed.

Theorem op_assoc a b c : op (op a b) c = op a (op b c).
Proof.
  destruct a as [a|], b as [b|], c as [c|];
    try destruct a; try destruct b; try destruct c;
    repeat match goal with s : bool |- _ => destruct s end;
    repeat match goal with f : option nat |- _ => destruct f end;
    cbn [op raw_op]; try reflexivity;
    repeat match goal with
    | |- context [if ?b then _ else _] => destruct b eqn:?
    end; cbn [op raw_op]; try reflexivity;
    repeat match goal with
    | |- context [if ?b then _ else _] => destruct b eqn:?
    end; cbn [op raw_op]; try reflexivity;
    repeat match goal with
    | H : false || _ = _ |- _ => cbn [orb] in H
    | H : Nat.ltb _ _ = true |- _ => apply Nat.ltb_lt in H
    | H : Nat.ltb _ _ = false |- _ => apply Nat.ltb_ge in H
    end; try lia.
  all: rewrite ?pow10_add, ?Nat.add_assoc; f_equal; f_equal; try ring.
Qed.

Definition gen (c : ascii) : t :=
  let k := nat_of_ascii c in
  if Nat.eqb k 45 then Some Minus
  else if Nat.eqb k 46 then Some (D false 0 0 (Some 0))
  else if (48 <=? k) && (k <=? 57)
       then Some (D false (Z.of_nat (k-48)) 1 None)
       else None.

(** Representation invariant for summaries produced by the parser. *)
Definition Consistent (x : raw_t) : Prop :=
  match x with
  | D _ v n f =>
      (0 <= v < pow10 n)%Z /\ n <= 18 /\
      (match f with Some k => k <= n | None => 0 < n end)
  | _ => True
  end.
Definition ConsistentOpt (x : t) : Prop :=
  match x with Some x => Consistent x | None => True end.

Lemma pow10_positive n : (0 < pow10 n)%Z.
Proof. unfold pow10; apply Z.pow_pos_nonneg; lia. Qed.

Lemma digits_append x y n m :
  (0 <= x < pow10 n)%Z -> (0 <= y < pow10 m)%Z ->
  (0 <= x * pow10 m + y < pow10 (n+m))%Z.
Proof.
  intros Hx Hy; rewrite pow10_add.
  pose proof (pow10_positive n); pose proof (pow10_positive m); nia.
Qed.

Theorem ne_consistent : ConsistentOpt ne.
Proof. exact I. Qed.

Theorem op_preserves_consistency a b :
  ConsistentOpt a -> ConsistentOpt b -> ConsistentOpt (op a b).
Proof.
  destruct a as [a|], b as [b|]; try destruct a; try destruct b;
    repeat match goal with s : bool |- _ => destruct s end;
    repeat match goal with f : option nat |- _ => destruct f end;
    cbn [op raw_op ConsistentOpt Consistent]; intros Ha Hb;
    try assumption; try exact I;
    repeat match goal with |- context [if ?b then _ else _] => destruct b eqn:? end;
    cbn [ConsistentOpt Consistent]; try exact I.
  all: repeat match goal with
    | H : false || _ = _ |- _ => cbn [orb] in H
    | H : Nat.ltb _ _ = false |- _ => apply Nat.ltb_ge in H
    end.
  all: destruct Ha as [Ha [Hn Hf]], Hb as [Hb [Hm Hg]];
    split; [apply digits_append; assumption|split; lia].
Qed.

Theorem gen_consistent c : ConsistentOpt (gen c).
Proof.
  unfold gen; destruct (Nat.eqb (nat_of_ascii c) 45); [exact I|].
  destruct (Nat.eqb (nat_of_ascii c) 46).
  - cbn [ConsistentOpt Consistent pow10]; repeat split; lia.
  - destruct ((48 <=? nat_of_ascii c) && (nat_of_ascii c <=? 57)) eqn:H;
      [|exact I].
    apply andb_true_iff in H; destruct H as [Hl Hr].
    apply Nat.leb_le in Hl, Hr.
    change ((0 <= Z.of_nat (nat_of_ascii c - 48) < 10)%Z /\
      1 <= 18 /\ 0 < 1).
    repeat split; lia.
Qed.

(** Futhark-shaped representation.  Only the signed frac=-1 sentinel is
    re-encoded as None; Some k denotes a nonnegative fractional count. *)
Record payload := Payload {
  negative : bool; digits : Z; ndigits : nat; frac : option nat
}.
Inductive form := FMinus | FD (d : payload).
Definition futhark_t := option form.
Definition empty := Payload false 0 0 None.
Definition is_empty (d : payload) : bool :=
  Nat.eqb (ndigits d) 0 &&
  (match frac d with None => true | Some _ => false end) &&
  negb (negative d).
Definition encode (x : t) : futhark_t :=
  match x with
  | None => None
  | Some NE => Some (FD empty)
  | Some Minus => Some FMinus
  | Some (D s v n f) => Some (FD (Payload s v n f))
  end.
Definition futhark_op (a b : futhark_t) : futhark_t :=
  match a,b with
  | Some (FD x),Some (FD y) =>
      if is_empty x then b else if is_empty y then a else
      if negative y || (18 <? ndigits x + ndigits y) then None else
      match frac x,frac y with
      | Some _,Some _ => None
      | _,_ => Some (FD (Payload (negative x)
          (digits x * pow10 (ndigits y) + digits y)%Z
          (ndigits x + ndigits y)
          (match frac x with Some k => Some (k + ndigits y) | None => frac y end)))
      end
  | Some FMinus,Some (FD y) =>
      if is_empty y then a else if negative y then None else
      Some (FD (Payload true (digits y) (ndigits y) (frac y)))
  | Some (FD x),Some FMinus => if is_empty x then b else None
  | _,_ => None
  end.

Lemma nonempty_payload s v n f :
  Consistent (D s v n f) -> is_empty (Payload s v n f) = false.
Proof.
  destruct f; unfold Consistent, is_empty; cbn [ndigits frac negative];
    intros H; destruct (Nat.eqb n 0) eqn:E; destruct s;
    cbn; try reflexivity.
  apply Nat.eqb_eq in E; intuition lia.
Qed.

Theorem encode_op a b :
  ConsistentOpt a -> ConsistentOpt b ->
  encode (op a b) = futhark_op (encode a) (encode b).
Proof.
  destruct a as [a|], b as [b|]; try destruct a; try destruct b;
    cbn [ConsistentOpt]; intros Ha Hb;
    cbn [op raw_op encode futhark_op]; try reflexivity.
  all: try rewrite (nonempty_payload _ _ _ _ Ha);
    try rewrite (nonempty_payload _ _ _ _ Hb);
    cbn [negative digits ndigits frac]; try reflexivity.
  all: repeat match goal with
    | s : bool |- _ => destruct s
    | f : option nat |- _ => destruct f
    end; cbn [encode];
    repeat match goal with |- context [if ?b then _ else _] => destruct b end;
    reflexivity.
Qed.

Definition FutharkConsistent (x : futhark_t) : Prop :=
  exists a, ConsistentOpt a /\ encode a = x.

Theorem futhark_op_preserves_consistency a b :
  FutharkConsistent a -> FutharkConsistent b ->
  FutharkConsistent (futhark_op a b).
Proof.
  intros [x [Hx <-]] [y [Hy <-]].
  exists (op x y); split; [now apply op_preserves_consistency|].
  now apply encode_op.
Qed.

Theorem futhark_op_assoc a b c :
  FutharkConsistent a -> FutharkConsistent b -> FutharkConsistent c ->
  futhark_op (futhark_op a b) c = futhark_op a (futhark_op b c).
Proof.
  intros [x [Hx <-]] [y [Hy <-]] [z [Hz <-]].
  rewrite <- !encode_op by (auto using op_preserves_consistency).
  now rewrite op_assoc.
Qed.

Theorem futhark_ne_left_neutral x :
  futhark_op (encode ne) x = x.
Proof. destruct x as [[|d]|]; reflexivity. Qed.
Theorem futhark_ne_right_neutral x :
  FutharkConsistent x -> futhark_op x (encode ne) = x.
Proof.
  intros [a [Ha <-]]. rewrite <- encode_op by auto using ne_consistent.
  now rewrite ne_right_neutral.
Qed.

(** Bounds justify mathematical counts and mantissas on consistent inputs.
    Even before the guard, the sum of two digit counts fits in u8.
    Successful mantissa arithmetic stays below 10^18, hence within u64. *)
Theorem payload_machine_bounds s v n f : Consistent (D s v n f) ->
  n <= 18 /\ (0 <= v < 18446744073709551616)%Z /\
  match f with Some k => k <= 18 | None => True end.
Proof.
  intros [Hv [Hn Hf]]; split; [exact Hn|]; split.
  - assert (pow10 n <= pow10 18)%Z.
    { unfold pow10; apply Z.pow_le_mono_r; lia. }
    assert (pow10 18 = 1000000000000000000)%Z by reflexivity.
    lia.
  - destruct f; simpl in *; auto; lia.
Qed.

Theorem count_add_no_overflow n m : n <= 18 -> m <= 18 -> n+m < 256.
Proof. lia. Qed.
Theorem fractional_add_no_overflow k m : k <= 18 -> m <= 18 -> k+m < 128.
Proof. lia. Qed.

Definition consistentb (x : t) : bool :=
  match x with
  | Some (D _ v n f) =>
      Z.leb 0 v && Z.ltb v (pow10 n) && (n <=? 18) &&
      match f with Some k => k <=? n | None => 0 <? n end
  | _ => true
  end.
Lemma consistentb_spec x : consistentb x = true <-> ConsistentOpt x.
Proof.
  destruct x as [[| |s v n f]|]; cbn [consistentb ConsistentOpt Consistent];
    try tauto.
  destruct f; rewrite !andb_true_iff, Z.leb_le, Z.ltb_lt, Nat.leb_le;
    [rewrite Nat.leb_le|rewrite Nat.ltb_lt]; tauto.
Qed.

Definition decode (x : futhark_t) : t :=
  match x with
  | None => None
  | Some FMinus => Some Minus
  | Some (FD d) => if is_empty d then ne else
      Some (D (negative d) (digits d) (ndigits d) (frac d))
  end.
Definition fconsistentb (x : futhark_t) : bool :=
  match x with
  | Some (FD d) => if is_empty d then Z.eqb (digits d) 0 else
      consistentb (Some (D (negative d) (digits d) (ndigits d) (frac d)))
  | _ => true
  end.
Lemma decode_consistent x : fconsistentb x = true -> ConsistentOpt (decode x).
Proof.
  destruct x as [[|d]|]; cbn [fconsistentb decode]; try (intros; exact I).
  destruct (is_empty d); [intros; exact I|apply consistentb_spec].
Qed.
Lemma encode_decode x : fconsistentb x = true -> encode (decode x) = x.
Proof.
  destruct x as [[|[s v n f]]|]; cbn [decode fconsistentb]; try reflexivity.
  destruct (is_empty (Payload s v n f)) eqn:E; [|reflexivity].
  cbn [digits]; intro V; apply Z.eqb_eq in V; subst v.
  unfold is_empty in E; cbn [ndigits frac negative] in E.
  apply andb_true_iff in E; destruct E as [E S].
  apply andb_true_iff in E; destruct E as [N F].
  apply Nat.eqb_eq in N; subst n.
  destruct s, f; cbn in *; try discriminate; reflexivity.
Qed.
Lemma fconsistentb_encode x : ConsistentOpt x -> fconsistentb (encode x) = true.
Proof.
  destruct x as [[| |s v n f]|]; cbn [ConsistentOpt encode fconsistentb];
    try reflexivity; intro H.
  rewrite (nonempty_payload _ _ _ _ H).
  apply consistentb_spec; exact H.
Qed.
Lemma fconsistentb_spec x : fconsistentb x = true <-> FutharkConsistent x.
Proof.
  split.
  - intro H; exists (decode x); split; auto using decode_consistent, encode_decode.
  - intros [a [Ha <-]]; now apply fconsistentb_encode.
Qed.

(** The packaged carrier retains the Futhark-shaped payload.  Boolean
    consistency proofs are erased and need no proof-irrelevance axiom. *)
Definition consistent_t := {x : futhark_t | fconsistentb x = true}.
Lemma consistent_ext (x y : consistent_t) :
  proj1_sig x = proj1_sig y -> x = y.
Proof.
  destruct x as [x Hx], y as [y Hy]; cbn; intro E; subst y.
  assert (Hx = Hy) by (apply UIP_dec; decide equality).
  now subst Hy.
Qed.
Definition consistent_ne : consistent_t := exist _ (encode ne) eq_refl.
Definition consistent_op (x y : consistent_t) : consistent_t :=
  exist _ (futhark_op (proj1_sig x) (proj1_sig y))
    (proj2 (fconsistentb_spec _)
      (futhark_op_preserves_consistency _ _
        (proj1 (fconsistentb_spec _) (proj2_sig x))
        (proj1 (fconsistentb_spec _) (proj2_sig y)))).
Definition consistent_gen (c : ascii) : consistent_t :=
  exist _ (encode (gen c)) (fconsistentb_encode _ (gen_consistent c)).

Section Observation.
Context {Y : Type} (convert : bool -> Z -> Z -> Y).
Definition obs (x : t) : option Y :=
  match x with
  | Some (D s x n f) =>
      if Nat.eqb n 0 then None else
      match f with
      | Some k => if Nat.eqb k 0 || Nat.eqb k n then None
                  else Some (convert s x (pow10 k))
      | None => Some (convert s x 1%Z)
      end
  | _ => None
  end.
Definition decimal : MonoidalOps ascii Y :=
  {| m_summary := t; m_ne := ne; m_op := op; m_gen := gen; m_obs := obs |}.
Theorem decimal_is_monoid : IsMonoid decimal.
Proof. split; [exact op_assoc|split; [exact ne_left_neutral|exact ne_right_neutral]]. Qed.
Definition decimal_try : MonoidalOps ascii (option Y) :=
  {| m_summary := t; m_ne := ne; m_op := op; m_gen := gen;
     m_obs := fun x => Some (obs x) |}.
Theorem decimal_try_is_monoid : IsMonoid decimal_try.
Proof. split; [exact op_assoc|split; [exact ne_left_neutral|exact ne_right_neutral]]. Qed.

Definition futhark_decimal : MonoidalOps ascii Y :=
  {| m_summary := consistent_t; m_ne := consistent_ne;
     m_op := consistent_op; m_gen := consistent_gen;
     m_obs := fun x => obs (decode (proj1_sig x)) |}.
Theorem futhark_decimal_is_monoid : IsMonoid futhark_decimal.
Proof.
  split.
  - intros [x Hx] [y Hy] [z Hz]; apply consistent_ext; cbn.
    apply futhark_op_assoc; now apply fconsistentb_spec.
  - split; intros [x Hx]; apply consistent_ext; cbn.
    + apply futhark_ne_left_neutral.
    + apply futhark_ne_right_neutral; now apply fconsistentb_spec.
Qed.
Definition futhark_decimal_try : MonoidalOps ascii (option Y) :=
  {| m_summary := consistent_t; m_ne := consistent_ne;
     m_op := consistent_op; m_gen := consistent_gen;
     m_obs := fun x => Some (obs (decode (proj1_sig x))) |}.
Theorem futhark_decimal_try_is_monoid : IsMonoid futhark_decimal_try.
Proof. exact futhark_decimal_is_monoid. Qed.
End Observation.

Definition exact_value (s : bool) (v scale : Z) : Qc :=
  Q2Qc ((if s then -v else v) # Z.to_pos scale).
Fixpoint summary (s : string) : t :=
  match s with EmptyString => ne | String c cs => op (gen c) (summary cs) end.
Definition run (s : string) := obs exact_value (summary s).

Theorem summary_consistent s : ConsistentOpt (summary s).
Proof.
  induction s; cbn [summary]; auto using ne_consistent,
    op_preserves_consistency, gen_consistent.
Qed.

Theorem summary_append a b :
  summary (String.append a b) = op (summary a) (summary b).
Proof.
  induction a; cbn [String.append summary].
  - now rewrite ne_left_neutral.
  - now rewrite IHa, op_assoc.
Qed.

Example multidigit : run "12345.067"%string = Some (Q2Qc (12345067 # 1000)).
Proof. vm_compute; reflexivity. Qed.
Example signed_decimal : run "-12.034"%string = Some (Q2Qc (-12034 # 1000)).
Proof. vm_compute; reflexivity. Qed.
Example eighteen_digits :
  run "999999999999999999"%string = Some (Q2Qc (999999999999999999 # 1)).
Proof. vm_compute; reflexivity. Qed.
Example nineteen_digits : summary "1000000000000000000"%string = None.
Proof. vm_compute; reflexivity. Qed.
Example leading_zeros_count_towards_limit : summary "0000000000000000000"%string = None.
Proof. vm_compute; reflexivity. Qed.
Example split_point_left :
  obs exact_value (op (op (summary "1") (summary ".")) (summary "23")) =
  Some (Q2Qc (123 # 100)).
Proof. vm_compute; reflexivity. Qed.
Example split_point_right :
  obs exact_value (op (summary "1") (op (summary ".") (summary "23"))) =
  Some (Q2Qc (123 # 100)).
Proof. vm_compute; reflexivity. Qed.
Example incomplete_fraction : run "12."%string = None.
Proof. reflexivity. Qed.
Example missing_integer : run ".23"%string = None.
Proof. reflexivity. Qed.
Example empty_input : run ""%string = None.
Proof. reflexivity. Qed.
Example bare_minus : run "-"%string = None.
Proof. reflexivity. Qed.
Example plus_unsupported : summary "+12"%string = None.
Proof. reflexivity. Qed.
Example exponent_unsupported : summary "1e2"%string = None.
Proof. reflexivity. Qed.
Example repeated_point : summary "1.2.3"%string = None.
Proof. reflexivity. Qed.
Example misplaced_minus : summary "1-2"%string = None.
Proof. reflexivity. Qed.
Example minus_point_fragment : summary "-."%string = Some (D true 0 0 (Some 0)).
Proof. reflexivity. Qed.
Example nonempty_does_not_mean_observable :
  run "-."%string = None /\ run "-.23"%string = None.
Proof. split; reflexivity. Qed.

End DecimalMonoid.
