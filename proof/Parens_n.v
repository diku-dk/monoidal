From Stdlib Require Import ZArith Lia.
Require Import Monoid Parens PullArray IndexedReplay.
Require Export Delimiter.

Open Scope nat_scope.
Set Implicit Arguments.
Set Universe Polymorphism.

(** Futhark's [del a] input, made polymorphic in the delimiter type. *)

(** A direct Rocq model of the array-based Futhark [parens_n]
    implementation.  Array indices and boundary counts are natural numbers;
    relative parenthesis depths remain integers. *)
Module ParensN.
Section ParensNDefinition.
  Context {Raw Value : Type}.
  Context {Delimiter : Type}.
  Context (N : nat).
  Context (M : MonoidalOps (Nest Raw Value) Value).
  Context (is_left is_right : Delimiter -> bool).

  Definition regions : Type := PullArray.t (m_summary M).

  Definition empty_regions : regions :=
    PullArray.replicate (2 * N + 1) (m_ne M).

  Definition region (rs : regions) (i : nat) : m_summary M :=
    PullArray.index rs i.

  Definition put_region
      (rs : regions) (i : nat) (x : m_summary M) : regions :=
    PullArray.put rs i x.

  Record t := mk {
    lo : Z;
    hi : Z;
    net : Z;
    regions_of : regions
  }.

  Definition base (x : m_summary M) : t :=
    mk 0 0 0 (put_region empty_regions 0 x).

  Definition invalid : option t := None.

  Definition ne : option t := Some (base (m_ne M)).

  Definition closes (s : t) : nat := Z.to_nat (Z.opp (lo s)).

  Definition opens (s : t) : nat := Z.to_nat (Z.sub (net s) (lo s)).

  Definition active (s : t) : nat := closes s + opens s.

  Definition close (x : m_summary M) : option (m_summary M) :=
    match m_obs M x with
    | Some value => Some (m_gen M (nested value))
    | None => None
    end.

  Definition append_region (s : t) (x : m_summary M) : t :=
    let i := active s in
    let old := region (regions_of s) i in
    mk (lo s) (hi s) (net s)
       (put_region (regions_of s) i (m_op M old x)).

  Definition append_open (s : t) : t :=
    let i := active s + 1 in
    mk (Z.min (lo s) (net s))
       (Z.max (hi s) (Z.add (net s) 1))
       (Z.add (net s) 1)
       (put_region (regions_of s) i (m_ne M)).

  Definition append_close (s : t) : option t :=
    if Nat.ltb 0 (opens s) then
        let i := active s in
        let inner := region (regions_of s) i in
        let outer := region (regions_of s) (i - 1) in
        match close inner with
        | Some nested_summary =>
            let rs0 := put_region (regions_of s) (i - 1)
                         (m_op M outer nested_summary) in
            let rs := put_region rs0 i (m_ne M) in
            Some (mk (Z.min (lo s) (Z.sub (net s) 1))
                     (Z.max (hi s) (net s))
                     (Z.sub (net s) 1) rs)
        | None => None
        end
    else
        let i := closes s + 1 in
        Some (mk (Z.min (lo s) (Z.sub (net s) 1))
                 (Z.max (hi s) (net s))
                 (Z.sub (net s) 1)
                 (put_region (regions_of s) i (m_ne M)))
    .

  Fixpoint replay_closes
      (remaining j : nat) (source : t) (state : option t) : option t :=
    match remaining, state with
    | 0, _ => state
    | S remaining', Some s =>
        match append_close s with
        | Some s' =>
            replay_closes remaining' (S j) source
              (Some (append_region s'
                       (region (regions_of source) (S j))))
        | None => None
        end
    | _, None => None
    end.

  Fixpoint replay_opens
      (remaining j : nat) (source : t) (state : option t) : option t :=
    match remaining, state with
    | 0, _ => state
    | S remaining', Some s =>
        let s' := append_open s in
        replay_opens remaining' (S j) source
          (Some (append_region s'
                   (region (regions_of source)
                     (closes source + S j))))
    | _, None => None
    end.

  Definition replay_summary (state source : t) : option t :=
    let seeded := append_region state (region (regions_of source) 0) in
    match replay_closes (closes source) 0 source (Some seeded) with
    | None => None
    | Some after_closes =>
        replay_opens (opens source) 0 source (Some after_closes)
    end.

  Lemma replay_closes_none (remaining j : nat) (source : t) :
    replay_closes remaining j source None = None.
  Proof. destruct remaining; reflexivity. Qed.

  Lemma replay_opens_none (remaining j : nat) (source : t) :
    replay_opens remaining j source None = None.
  Proof. destruct remaining; reflexivity. Qed.

  Lemma replay_opens_none_iff (remaining j : nat) (source : t)
      (state : option t) :
    replay_opens remaining j source state = None <-> state = None.
  Proof.
    revert j state.
    induction remaining as [|k IH]; intros j [s|]; simpl; try tauto.
    rewrite IH; split; discriminate.
  Qed.

  (** Replaying a prefix and then the remaining suffix is the same as
      replaying the concatenated number of boundaries.  The offset [j]
      records how many source regions have already been consumed. *)
  Lemma replay_closes_plus
      (p q j : nat) (source : t) (state : option t) :
    replay_closes (p + q) j source state =
    replay_closes q (j + p) source
      (replay_closes p j source state).
  Proof.
    apply (@IndexedReplay.plus (option t)
      (fun n j s => replay_closes n j source s)).
    - reflexivity.
    - intros n k [s|]; simpl.
      + destruct (append_close s); simpl; [reflexivity|].
        symmetry; apply replay_closes_none.
      + symmetry; apply replay_closes_none.
  Qed.

  Lemma replay_opens_plus
      (p q j : nat) (source : t) (state : option t) :
    replay_opens (p + q) j source state =
    replay_opens q (j + p) source
      (replay_opens p j source state).
  Proof.
    apply (@IndexedReplay.plus (option t)
      (fun n j s => replay_opens n j source s)).
    - reflexivity.
    - intros n k [s|]; simpl.
      + reflexivity.
      + symmetry; apply replay_opens_none.
  Qed.

  Lemma replay_closes_snoc
      (p j : nat) (source : t) (state : option t) :
    replay_closes (S p) j source state =
    replay_closes 1 (j + p) source
      (replay_closes p j source state).
  Proof.
    apply (@IndexedReplay.snoc (option t)
      (fun n j s => replay_closes n j source s)).
    intros; apply replay_closes_plus.
  Qed.

  Lemma replay_opens_snoc
      (p j : nat) (source : t) (state : option t) :
    replay_opens (S p) j source state =
    replay_opens 1 (j + p) source
      (replay_opens p j source state).
  Proof.
    apply (@IndexedReplay.snoc (option t)
      (fun n j s => replay_opens n j source s)).
    intros; apply replay_opens_plus.
  Qed.

  Lemma replay_closes_last
      (p j : nat) (source : t) (state : option t) :
    replay_closes (S p) j source state =
    match replay_closes p j source state with
    | None => None
    | Some before_last =>
        match append_close before_last with
        | None => None
        | Some after_close =>
            Some (append_region after_close
              (region (regions_of source) (S (j + p))))
        end
    end.
  Proof.
    rewrite replay_closes_snoc.
    destruct (replay_closes p j source state) as [before_last|];
      simpl; [|reflexivity].
    destruct (append_close before_last); reflexivity.
  Qed.

  Lemma replay_opens_last
      (p j : nat) (source : t) (state : option t) :
    replay_opens (S p) j source state =
    match replay_opens p j source state with
    | None => None
    | Some before_last =>
        Some (append_region (append_open before_last)
          (region (regions_of source)
            (closes source + S (j + p))))
    end.
  Proof.
    rewrite replay_opens_snoc.
    destruct (replay_opens p j source state); reflexivity.
  Qed.

  (** Replay ignores the historical maximum [hi].  This is the equality
      notion used by the fusion argument; [parens_n_op] installs the final
      depth triple separately. *)
  Definition ReplayEq (x y : t) : Prop :=
    lo x = lo y /\
    net x = net y /\
    regions_of x = regions_of y.

  Definition ReplayEqOpt (x y : option t) : Prop :=
    match x, y with
    | Some x', Some y' => ReplayEq x' y'
    | None, None => True
    | _, _ => False
    end.

  Definition option_bind {A B : Type}
      (x : option A) (f : A -> option B) : option B :=
    match x with
    | Some value => f value
    | None => None
    end.

  Lemma ReplayEq_refl (x : t) : ReplayEq x x.
  Proof. repeat split; reflexivity. Qed.

  Lemma ReplayEq_sym (x y : t) : ReplayEq x y -> ReplayEq y x.
  Proof. intros [Hlo [Hnet Hregions]]; repeat split; symmetry; assumption. Qed.

  Lemma ReplayEq_trans (x y z : t) :
    ReplayEq x y -> ReplayEq y z -> ReplayEq x z.
  Proof.
    intros [Hlo1 [Hnet1 Hregions1]] [Hlo2 [Hnet2 Hregions2]].
    repeat split; etransitivity; eassumption.
  Qed.

  Lemma ReplayEqOpt_refl (x : option t) : ReplayEqOpt x x.
  Proof. destruct x; simpl; [apply ReplayEq_refl|exact I]. Qed.

  Lemma ReplayEqOpt_sym (x y : option t) :
    ReplayEqOpt x y -> ReplayEqOpt y x.
  Proof.
    destruct x as [x|], y as [y|]; simpl; try contradiction;
      [apply ReplayEq_sym|exact id].
  Qed.

  Lemma ReplayEqOpt_trans (x y z : option t) :
    ReplayEqOpt x y -> ReplayEqOpt y z -> ReplayEqOpt x z.
  Proof.
    destruct x as [x|], y as [y|], z as [z|]; simpl;
      intros Hxy Hyz; try contradiction; try exact I.
    eapply ReplayEq_trans; eassumption.
  Qed.

  Lemma ReplayEqOpt_bind
      (x y : option t) (f g : t -> option t) :
    ReplayEqOpt x y ->
    (forall x' y', ReplayEq x' y' -> ReplayEqOpt (f x') (g y')) ->
    ReplayEqOpt (option_bind x f) (option_bind y g).
  Proof.
    destruct x as [x|], y as [y|]; simpl; try contradiction.
    - intros Hxy Hfg; now apply Hfg.
    - intros _ _; exact I.
  Qed.

  Lemma ReplayEq_active (x y : t) :
    ReplayEq x y -> active x = active y.
  Proof.
    intros [Hlo [Hnet _]].
    unfold active, closes, opens; now rewrite Hlo, Hnet.
  Qed.

  Lemma append_region_replay_eq
      (x y : t) (value : m_summary M) :
    ReplayEq x y ->
    ReplayEq (append_region x value) (append_region y value).
  Proof.
    intros Heq.
    pose proof (ReplayEq_active Heq) as Hactive.
    destruct Heq as [Hlo [Hnet Hregions]].
    unfold ReplayEq, append_region; simpl.
    repeat split; try assumption.
    now rewrite Hactive, Hregions.
  Qed.

  Lemma append_open_replay_eq (x y : t) :
    ReplayEq x y -> ReplayEq (append_open x) (append_open y).
  Proof.
    intros Heq.
    pose proof (ReplayEq_active Heq) as Hactive.
    destruct Heq as [Hlo [Hnet Hregions]].
    unfold ReplayEq, append_open; simpl.
    repeat split; rewrite ?Hlo, ?Hnet, ?Hactive, ?Hregions; reflexivity.
  Qed.

  Lemma append_close_replay_eq (x y : t) :
    ReplayEq x y -> ReplayEqOpt (append_close x) (append_close y).
  Proof.
    intros Heq.
    pose proof (ReplayEq_active Heq) as Hactive.
    destruct Heq as [Hlo [Hnet Hregions]].
    assert (Hopens : opens x = opens y).
    { unfold opens; now rewrite Hlo, Hnet. }
    assert (Hcloses : closes x = closes y).
    { unfold closes; now rewrite Hlo. }
    unfold append_close.
    rewrite Hopens.
    destruct (Nat.ltb 0 (opens y)) eqn:Hhas_open.
    - rewrite Hactive, Hregions.
      destruct (close (region (regions_of y) (active y)))
        as [nested_summary|] eqn:Hclose; simpl; [|exact I].
      unfold ReplayEq; simpl.
      repeat split; rewrite ?Hlo, ?Hnet, ?Hregions; reflexivity.
    - rewrite Hcloses, Hregions; simpl.
      unfold ReplayEq; simpl.
      repeat split; rewrite ?Hlo, ?Hnet, ?Hregions; reflexivity.
  Qed.

  Lemma replay_closes_replay_eq
      (remaining j : nat) (source_x source_y : t)
      (state_x state_y : option t) :
    ReplayEq source_x source_y ->
    ReplayEqOpt state_x state_y ->
    ReplayEqOpt
      (replay_closes remaining j source_x state_x)
      (replay_closes remaining j source_y state_y).
  Proof.
    revert j state_x state_y.
    induction remaining as [|remaining IH];
      intros j state_x state_y Hsource Hstate.
    - exact Hstate.
    - destruct state_x as [state_x|], state_y as [state_y|];
        simpl in Hstate; try contradiction.
      2:{ simpl; exact I. }
      simpl.
      pose proof (append_close_replay_eq Hstate) as Hclose.
      destruct (append_close state_x) as [next_x|] eqn:Hx,
        (append_close state_y) as [next_y|] eqn:Hy;
        simpl in Hclose; try contradiction.
      2:{ exact I. }
      apply IH; [exact Hsource|].
      destruct Hsource as [Hsource_lo [Hsource_net Hsource_regions]].
      rewrite Hsource_regions.
      apply append_region_replay_eq; exact Hclose.
  Qed.

  Lemma replay_closes_extensional
      (remaining jx jy : nat) (source_x source_y : t)
      (state_x state_y : option t) :
    ReplayEqOpt state_x state_y ->
    (forall r, r < remaining ->
      region (regions_of source_x) (S (jx + r)) =
      region (regions_of source_y) (S (jy + r))) ->
    ReplayEqOpt
      (replay_closes remaining jx source_x state_x)
      (replay_closes remaining jy source_y state_y).
  Proof.
    revert jx jy state_x state_y.
    induction remaining as [|remaining IH];
      intros jx jy state_x state_y Hstate Hregions.
    - exact Hstate.
    - destruct state_x as [state_x|], state_y as [state_y|];
        simpl in Hstate; try contradiction.
      2:{ simpl; exact I. }
      simpl.
      pose proof (append_close_replay_eq Hstate) as Hclose.
      destruct (append_close state_x) as [next_x|] eqn:Hx,
        (append_close state_y) as [next_y|] eqn:Hy;
        simpl in Hclose; try contradiction.
      2:{ exact I. }
      apply IH.
      + specialize (Hregions 0 ltac:(lia)).
        replace (jx + 0) with jx in Hregions by lia.
        replace (jy + 0) with jy in Hregions by lia.
        rewrite Hregions.
        apply append_region_replay_eq; exact Hclose.
      + intros r Hr.
        specialize (Hregions (S r) ltac:(lia)).
        replace (S jx + r) with (jx + S r) by lia.
        replace (S jy + r) with (jy + S r) by lia.
        exact Hregions.
  Qed.

  Lemma replay_opens_replay_eq
      (remaining j : nat) (source_x source_y : t)
      (state_x state_y : option t) :
    ReplayEq source_x source_y ->
    ReplayEqOpt state_x state_y ->
    ReplayEqOpt
      (replay_opens remaining j source_x state_x)
      (replay_opens remaining j source_y state_y).
  Proof.
    revert j state_x state_y.
    induction remaining as [|remaining IH];
      intros j state_x state_y Hsource Hstate.
    - exact Hstate.
    - destruct state_x as [state_x|], state_y as [state_y|];
        simpl in Hstate; try contradiction.
      2:{ simpl; exact I. }
      simpl.
      apply IH; [exact Hsource|].
      pose proof (ReplayEq_active Hsource) as Hsource_active.
      destruct Hsource as [Hsource_lo [Hsource_net Hsource_regions]].
      assert (Hsource_closes : closes source_x = closes source_y).
      { unfold closes; now rewrite Hsource_lo. }
      rewrite Hsource_closes, Hsource_regions.
      apply append_region_replay_eq.
      apply append_open_replay_eq; exact Hstate.
  Qed.

  Lemma replay_opens_extensional
      (remaining jx jy : nat) (source_x source_y : t)
      (state_x state_y : option t) :
    ReplayEqOpt state_x state_y ->
    (forall r, r < remaining ->
      region (regions_of source_x) (closes source_x + S (jx + r)) =
      region (regions_of source_y) (closes source_y + S (jy + r))) ->
    ReplayEqOpt
      (replay_opens remaining jx source_x state_x)
      (replay_opens remaining jy source_y state_y).
  Proof.
    revert jx jy state_x state_y.
    induction remaining as [|remaining IH];
      intros jx jy state_x state_y Hstate Hregions.
    - exact Hstate.
    - destruct state_x as [state_x|], state_y as [state_y|];
        simpl in Hstate; try contradiction.
      2:{ simpl; exact I. }
      simpl.
      apply IH.
      + specialize (Hregions 0 ltac:(lia)).
        replace (jx + 0) with jx in Hregions by lia.
        replace (jy + 0) with jy in Hregions by lia.
        rewrite Hregions.
        apply append_region_replay_eq.
        apply append_open_replay_eq.
        exact Hstate.
      + intros r Hr.
        specialize (Hregions (S r) ltac:(lia)).
        replace (S jx + r) with (jx + S r) by lia.
        replace (S jy + r) with (jy + S r) by lia.
        exact Hregions.
  Qed.

  Lemma replay_summary_replay_eq
      (state_x state_y source_x source_y : t) :
    ReplayEq state_x state_y ->
    ReplayEq source_x source_y ->
    ReplayEqOpt
      (replay_summary state_x source_x)
      (replay_summary state_y source_y).
  Proof.
    intros Hstate Hsource.
    pose proof (ReplayEq_active Hsource) as Hsource_active.
    destruct Hsource as [Hsource_lo [Hsource_net Hsource_regions]].
    assert (Hsource_closes : closes source_x = closes source_y).
    { unfold closes; now rewrite Hsource_lo. }
    assert (Hsource_opens : opens source_x = opens source_y).
    { unfold opens; now rewrite Hsource_lo, Hsource_net. }
    unfold replay_summary.
    rewrite Hsource_closes, Hsource_opens, Hsource_regions.
    assert (Hsource' : ReplayEq source_x source_y).
    { repeat split; assumption. }
    assert (Hseed :
      ReplayEq
        (append_region state_x (region (regions_of source_y) 0))
        (append_region state_y (region (regions_of source_y) 0))).
    { apply append_region_replay_eq; exact Hstate. }
    pose proof
      (replay_closes_replay_eq (closes source_y) 0
        (Some (append_region state_x (region (regions_of source_y) 0)))
        (Some (append_region state_y (region (regions_of source_y) 0)))
        Hsource' Hseed) as Hcloses.
    destruct (replay_closes (closes source_y) 0 source_x
                (Some (append_region state_x
                  (region (regions_of source_y) 0)))) as [after_x|],
      (replay_closes (closes source_y) 0 source_y
                (Some (append_region state_y
                  (region (regions_of source_y) 0)))) as [after_y|];
      simpl in Hcloses |- *; try contradiction.
    - apply replay_opens_replay_eq; assumption.
    - exact I.
  Qed.

  Lemma append_region_assoc
      (s : t) (x y : m_summary M) :
    IsMonoid M ->
    active s < PullArray.size (regions_of s) ->
    append_region (append_region s x) y =
    append_region s (m_op M x y).
  Proof.
    intros [HM_assoc _] Hbound.
    destruct s as [sl sh sn rs].
    unfold append_region in *; simpl in *.
    unfold region, put_region in *.
    rewrite PullArray.index_put_same by exact Hbound.
    rewrite PullArray.put_put_same_index.
    rewrite HM_assoc.
    reflexivity.
  Qed.

  Definition parens_n_op (a b : option t) : option t :=
    match a, b with
    | Some a', Some b' =>
        let new_lo := Z.min (lo a') (Z.add (net a') (lo b')) in
        let new_hi := Z.max (hi a') (Z.add (net a') (hi b')) in
        let new_net := Z.add (net a') (net b') in
        if Z.ltb (Z.of_nat N) (Z.sub new_hi new_lo)
        then invalid
        else
          let s0 := append_region a' (region (regions_of b') 0) in
          match replay_closes (closes b') 0 b' (Some s0) with
          | None => None
          | Some s1 =>
              match replay_opens (opens b') 0 b' (Some s1) with
              | None => None
              | Some s2 =>
                  Some (mk new_lo new_hi new_net (regions_of s2))
              end
          end
    | _, _ => None
    end.

  Definition parens_n_gen (x : del Raw Delimiter) : option t :=
    match x with
    | E value => Some (base (m_gen M (raw value)))
    | Del delimiter =>
        if is_left delimiter then
          match N with
          | 0 => invalid
          | S _ =>
              let s := append_open (base (m_ne M)) in
              Some s
          end
        else if is_right delimiter then
          match N with
          | 0 => invalid
          | S _ =>
              match append_close (base (m_ne M)) with
              | None => None
              | Some s => Some s
              end
          end
        else ne
    end.

  Definition parens_n_obs (s : option t) : option Value :=
    match s with
    | Some s' =>
        if (Z.leb 0 (lo s') && Z.leb (hi s') (Z.of_nat N) &&
            Z.eqb (net s') 0)%bool
        then m_obs M (region (regions_of s') 0)
        else None
    | None => None
    end.

  Definition regions_well_sized (s : t) : Prop :=
    PullArray.size (regions_of s) = 2 * N + 1.

  Definition counters_in_bounds (s : t) : Prop :=
    active s <= 2 * N.

  Definition Sized (s : t) : Prop :=
    regions_well_sized s.

  Definition SizedOpt (s : option t) : Prop :=
    match s with
    | Some s' => Sized s'
    | None => True
    end.

  Lemma put_region_length (rs : regions) (i : nat) (x : m_summary M) :
    PullArray.size (put_region rs i x) = PullArray.size rs.
  Proof.
    apply PullArray.size_put.
  Qed.

  Lemma empty_regions_length :
    PullArray.size empty_regions = 2 * N + 1.
  Proof.
    apply PullArray.size_replicate.
  Qed.

  Lemma base_sized (x : m_summary M) : Sized (base x).
  Proof.
    unfold Sized, regions_well_sized, base; simpl.
    rewrite put_region_length; apply empty_regions_length.
  Qed.

  Theorem ne_sized : SizedOpt ne.
  Proof.
    unfold SizedOpt, ne; simpl; apply base_sized.
  Qed.

  Lemma append_region_sized (s : t) (x : m_summary M) :
    Sized s -> Sized (append_region s x).
  Proof.
    unfold Sized, regions_well_sized, append_region; simpl.
    intro H; now rewrite put_region_length.
  Qed.

  Lemma append_open_sized (s : t) :
    Sized s -> Sized (append_open s).
  Proof.
    unfold Sized, regions_well_sized, append_open; simpl.
    intro H; now rewrite put_region_length.
  Qed.

  Lemma append_close_sized (s s' : t) :
    Sized s -> append_close s = Some s' -> Sized s'.
  Proof.
    intros Hconsistent Hclose.
    unfold append_close in Hclose.
    destruct (Nat.ltb 0 (opens s)) eqn:Hopens.
    - destruct (close (region (regions_of s) (active s))) eqn:Hnested;
        try discriminate.
      inversion Hclose; subst; clear Hclose.
      unfold Sized, regions_well_sized in *; simpl in *.
      now rewrite !put_region_length.
    - inversion Hclose; subst; clear Hclose.
      unfold Sized, regions_well_sized in *; simpl in *.
      now rewrite put_region_length.
  Qed.

  Lemma replay_closes_sized
      (remaining j : nat) (source : t) (state : option t) :
    SizedOpt state ->
    SizedOpt (replay_closes remaining j source state).
  Proof.
    revert j state; induction remaining as [|remaining IH];
      intros j [s|] Hconsistent; simpl; try easy.
    destruct (append_close s) as [s'|] eqn:Hclose; simpl; try easy.
    apply IH, append_region_sized.
    eapply append_close_sized; eauto.
  Qed.

  Lemma replay_opens_sized
      (remaining j : nat) (source : t) (state : option t) :
    SizedOpt state ->
    SizedOpt (replay_opens remaining j source state).
  Proof.
    revert j state; induction remaining as [|remaining IH];
      intros j [s|] Hconsistent; simpl; try easy.
    apply IH, append_region_sized, append_open_sized; exact Hconsistent.
  Qed.

  Lemma replay_summary_sized (state source : t) :
    Sized state -> SizedOpt (replay_summary state source).
  Proof.
    intro Hstate.
    unfold replay_summary.
    assert (Hseed :
      Sized (append_region state (region (regions_of source) 0))).
    { apply append_region_sized; exact Hstate. }
    pose proof
      (replay_closes_sized (closes source) 0 source
        (Some (append_region state (region (regions_of source) 0))) Hseed)
      as Hcloses.
    destruct (replay_closes (closes source) 0 source
      (Some (append_region state (region (regions_of source) 0))))
      as [after_closes|]; simpl in Hcloses |- *; [|exact I].
    apply replay_opens_sized; exact Hcloses.
  Qed.

  Corollary replay_summary_result_sized (state source result : t) :
    Sized state ->
    replay_summary state source = Some result ->
    Sized result.
  Proof.
    intros Hstate Hresult.
    pose proof (replay_summary_sized (state:=state) source Hstate) as Hsized.
    rewrite Hresult in Hsized; exact Hsized.
  Qed.

  Theorem parens_n_op_preserves_size (a b : option t) :
    SizedOpt a ->
    SizedOpt b ->
    SizedOpt (parens_n_op a b).
  Proof.
    intros Ha Hb; destruct a as [a|], b as [b|]; simpl; try easy.
    unfold parens_n_op; simpl.
    destruct (Z.ltb (Z.of_nat N)
                (Z.max (hi a) (Z.add (net a) (hi b)) -
                 Z.min (lo a) (Z.add (net a) (lo b)))) eqn:Hvalid;
      simpl; try easy.
    set (s0 := append_region a (region (regions_of b) 0)).
    assert (Hs0 : Sized s0).
    { unfold s0; now apply append_region_sized. }
    pose proof (replay_closes_sized (closes b) 0 b (Some s0) Hs0)
      as Hcloses.
    destruct (replay_closes (closes b) 0 b (Some s0)) as [s1|]; simpl; try easy.
    pose proof (replay_opens_sized (opens b) 0 b (Some s1) Hcloses)
      as Hopens.
    destruct (replay_opens (opens b) 0 b (Some s1)) as [s2|]; simpl; try easy.
  Qed.

  Definition depth_consistent (s : t) : Prop :=
    Z.le (lo s) 0 /\
    Z.le 0 (hi s) /\
    Z.le (lo s) (net s) /\
    Z.le (net s) (hi s) /\
    Z.le (Z.sub (hi s) (lo s)) (Z.of_nat N).

  Definition padding_neutral (s : t) : Prop :=
    forall i,
      active s < i ->
      region (regions_of s) i = m_ne M.

  Definition agrees_through (k : nat) (xs ys : regions) : Prop :=
    forall i, i <= k -> region xs i = region ys i.

  Lemma region_put_same
      (rs : regions) (i : nat) (x : m_summary M) :
    i < PullArray.size rs -> region (put_region rs i x) i = x.
  Proof.
    apply PullArray.index_put_same.
  Qed.

  Lemma region_put_other
      (rs : regions) (i j : nat) (x : m_summary M) :
    i <> j ->
    region (put_region rs i x) j = region rs j.
  Proof.
    apply PullArray.index_put_other.
  Qed.

  Lemma agrees_through_put_next
      (k : nat) (xs ys : regions) (x : m_summary M) :
    agrees_through k xs ys ->
    S k < PullArray.size xs ->
    region ys (S k) = x ->
    agrees_through (S k) (put_region xs (S k) x) ys.
  Proof.
    intros Hagree Hbound Hnext i Hi.
    destruct (Nat.eq_dec i (S k)) as [->|Hneq].
    - rewrite region_put_same; [symmetry; exact Hnext|exact Hbound].
    - rewrite region_put_other.
      + apply Hagree; lia.
      + congruence.
  Qed.

  Definition closes_replay_state
      (j : nat) (source state : t) : Prop :=
    lo state = Z.opp (Z.of_nat j) /\
    hi state = 0%Z /\
    net state = Z.opp (Z.of_nat j) /\
    active state = j /\
    agrees_through j (regions_of state) (regions_of source) /\
    padding_neutral state.

  Definition opens_replay_state
      (c j : nat) (source state : t) : Prop :=
    lo state = Z.opp (Z.of_nat c) /\
    net state = Z.sub (Z.of_nat j) (Z.of_nat c) /\
    active state = c + j /\
    agrees_through (c + j) (regions_of state) (regions_of source) /\
    padding_neutral state.

  Lemma closes_replay_closes j source state :
    closes_replay_state j source state -> closes state = j.
  Proof.
    intros [Hlo _].
    unfold closes; rewrite Hlo, Z.opp_involutive, Nat2Z.id; reflexivity.
  Qed.

  Definition left_seed (source : t) : t :=
    append_region (base (m_ne M)) (region (regions_of source) 0).

  Lemma left_seed_closes_state :
    IsMonoid M ->
    forall source, closes_replay_state 0 source (left_seed source).
  Proof.
    intros [_ [HM_l _]] source.
    assert (Hzero :
      region (put_region empty_regions 0 (m_ne M)) 0 = m_ne M).
    { unfold region, empty_regions, put_region; destruct N; reflexivity. }
    unfold closes_replay_state, left_seed, append_region, base,
      active, closes, opens; simpl.
    rewrite Hzero, HM_l.
    repeat split; try reflexivity.
    intros i Hi; assert (i = 0) by lia; subst i.
    rewrite region_put_same.
    - reflexivity.
    - rewrite put_region_length, empty_regions_length; lia.
    - unfold padding_neutral.
      intros i Hi.
      cbn [active closes opens] in Hi.
      change
        (PullArray.index
           (PullArray.put
              (PullArray.put empty_regions 0 (m_ne M)) 0
              (region (regions_of source) 0)) i = m_ne M).
      repeat rewrite PullArray.index_put_other by lia.
      unfold empty_regions.
      apply PullArray.index_replicate.
  Qed.

  Lemma closes_replay_step
      (j : nat) (source state : t) :
    IsMonoid M ->
    Sized state ->
    S j < PullArray.size (regions_of state) ->
    closes_replay_state j source state ->
    match append_close state with
    | Some state' =>
        closes_replay_state (S j) source
          (append_region state'
            (region (regions_of source) (S j)))
    | None => False
    end.
  Proof.
    intros [_ [HM_l _]] Hsized Hbound Hstate.
    destruct Hstate as [Hlo [Hhi [Hnet [Hactive [Hagree Hpadding]]]]].
    assert (Hopens : opens state = 0).
    { unfold opens; rewrite Hlo, Hnet; simpl; now rewrite Z.sub_diag. }
    assert (Hcloses : closes state = j).
    { unfold closes; rewrite Hlo, Z.opp_involutive, Nat2Z.id; reflexivity. }
    unfold append_close.
    rewrite Hopens; simpl; rewrite Hcloses.
    unfold append_region; simpl.
    assert (Hactive_next :
      active
        (mk (Z.min (lo state) (net state - 1))
            (Z.max (hi state) (net state)) (net state - 1)
            (put_region (regions_of state) (j + 1) (m_ne M))) = S j).
    { unfold active, closes, opens; simpl.
      rewrite Hlo, Hnet; simpl.
      rewrite Z.min_r by lia.
      replace (Z.to_nat (Z.of_nat j + 1)) with (S j).
      2:{ apply Nat2Z.inj; rewrite Z2Nat.id by lia; simpl; lia. }
      lia. }
    rewrite Hactive_next.
    replace (j + 1) with (S j) by lia.
    rewrite region_put_same by lia.
    rewrite HM_l.
    unfold closes_replay_state; simpl.
    rewrite Hlo, Hhi, Hnet.
    rewrite Z.min_r by lia.
    rewrite Z.max_l by lia.
    repeat split; try lia.
    - unfold active, closes, opens; simpl.
      replace (Z.to_nat (Z.of_nat j + 1)) with (S j).
      2:{ apply Nat2Z.inj; rewrite Z2Nat.id by lia; simpl; lia. }
      lia.
    - apply agrees_through_put_next; try assumption.
        * intros i Hi.
          rewrite region_put_other; try (apply Hagree; lia); lia.
        * rewrite put_region_length; exact Hbound.
        * reflexivity.
    - unfold padding_neutral in Hpadding |- *; simpl.
      intros i Hi.
      assert (Hfar : S j < i).
      { match type of Hi with
        | active ?s < i =>
            assert (Ha : active s = S j)
        end.
        { unfold active, closes, opens; simpl.
          replace (Z.to_nat (- (- Z.of_nat j - 1))) with (S j).
          2:{ apply Nat2Z.inj; rewrite Z2Nat.id by lia;
              rewrite Nat2Z.inj_succ; lia. }
          replace (Z.to_nat (- Z.of_nat j - 1 - (- Z.of_nat j - 1)))
            with 0 by (replace (- Z.of_nat j - 1 - (- Z.of_nat j - 1))%Z
                         with 0%Z by lia; reflexivity).
          lia. }
        rewrite Ha in Hi; exact Hi. }
      rewrite region_put_other by lia.
      rewrite region_put_other by lia.
      apply Hpadding; lia.
  Qed.

  Lemma replay_closes_induction
      (remaining j : nat) (source state : t) :
    IsMonoid M ->
    Sized source ->
    active source < 2 * N + 1 ->
    Sized state ->
    closes_replay_state j source state ->
    j + remaining <= closes source ->
    exists final,
      replay_closes remaining j source (Some state) = Some final /\
      closes_replay_state (j + remaining) source final.
  Proof.
    revert j state.
    induction remaining as [|remaining IH]; intros j state HM Hsource_size
      Hsource_active Hsized
      Hstate Hcount.
    - exists state; simpl; split; [reflexivity|].
      now rewrite Nat.add_0_r.
    - assert (Hbound : S j < PullArray.size (regions_of state)).
      { pose proof Hsource_size as Hsource_length.
        pose proof Hsized as Hstate_length.
        unfold Sized, regions_well_sized in Hsource_length, Hstate_length.
        pose proof (closes_replay_closes Hstate) as Hcloses_state.
        unfold active in Hsource_active.
        lia. }
      pose proof (closes_replay_step (j:=j) (source:=source) (state:=state)
                    HM Hsized Hbound Hstate)
        as Hstep.
      destruct (append_close state) as [state'|] eqn:Hclose;
        simpl in Hstep; try contradiction.
      set (next := append_region state'
                    (region (regions_of source) (S j))) in *.
      assert (Hnext_sized : Sized next).
      { unfold next; apply append_region_sized.
        eapply append_close_sized; eauto. }
      destruct (@IH (S j) next HM Hsource_size Hsource_active
                   Hnext_sized Hstep) as
        [final [Hreplay Hfinal]]; try lia.
      exists final; simpl; rewrite Hclose.
      unfold next in Hreplay, Hfinal.
      split; [exact Hreplay|].
      replace (j + S remaining) with (S j + remaining) by lia.
      exact Hfinal.
  Qed.

  Lemma opens_replay_step
      (c j : nat) (source state : t) :
    IsMonoid M ->
    S (c + j) < PullArray.size (regions_of state) ->
    opens_replay_state c j source state ->
    opens_replay_state c (S j) source
      (append_region (append_open state)
        (region (regions_of source) (c + S j))).
  Proof.
    intros [_ [HM_l _]] Hbound Hstate.
    destruct Hstate as [Hlo [Hnet [Hactive [Hagree Hpadding]]]].
    unfold append_open, append_region; simpl.
    rewrite Hactive.
    replace (c + j + 1) with (c + S j) by lia.
    assert (Hactive_next :
      active
        (mk (Z.min (lo state) (net state))
            (Z.max (hi state) (net state + 1)) (net state + 1)
            (put_region (regions_of state) (c + S j) (m_ne M))) =
      c + S j).
    { unfold active, closes, opens; simpl.
      rewrite Hlo, Hnet.
      rewrite Z.min_l by lia.
      replace (Z.to_nat (Z.of_nat c)) with c by (symmetry; apply Nat2Z.id).
      replace (Z.to_nat (Z.of_nat (S j))) with (S j)
        by (symmetry; apply Nat2Z.id).
      lia. }
    rewrite Hactive_next.
    rewrite region_put_same by lia.
    rewrite HM_l.
    unfold opens_replay_state; simpl.
    rewrite Hlo, Hnet.
    rewrite Z.min_l by lia.
    split; [lia|].
    split.
    - change (Z.of_nat j - Z.of_nat c + 1 =
              Z.of_nat (S j) - Z.of_nat c)%Z.
      rewrite Nat2Z.inj_succ; lia.
    - split.
      + unfold active, closes, opens; simpl.
      replace (- - Z.of_nat c)%Z with (Z.of_nat c) by lia.
      replace (Z.of_nat j - Z.of_nat c + 1 - - Z.of_nat c)%Z
        with (Z.of_nat (S j)) by (rewrite Nat2Z.inj_succ; lia).
      replace (Z.to_nat (Z.of_nat c)) with c by (symmetry; apply Nat2Z.id).
      replace (Z.to_nat (Z.of_nat (S j))) with (S j)
        by (symmetry; apply Nat2Z.id).
        reflexivity.
      + split.
        * replace (c + S j) with (S (c + j)) by lia.
          apply agrees_through_put_next.
          -- intros i Hi.
             rewrite region_put_other; try (apply Hagree; lia); lia.
          -- rewrite put_region_length; exact Hbound.
          -- reflexivity.
        * unfold padding_neutral in Hpadding |- *; simpl.
          intros i Hi.
          assert (Hfar : c + S j < i).
          { match type of Hi with
            | active ?s < i =>
                assert (Ha : active s = c + S j)
            end.
            { unfold active, closes, opens; simpl.
              replace (- - Z.of_nat c)%Z with (Z.of_nat c) by lia.
              replace (Z.of_nat j - Z.of_nat c + 1 - - Z.of_nat c)%Z
                with (Z.of_nat (S j)) by (rewrite Nat2Z.inj_succ; lia).
              replace (Z.to_nat (Z.of_nat c)) with c
                by (symmetry; apply Nat2Z.id).
              replace (Z.to_nat (Z.of_nat (S j))) with (S j)
                by (symmetry; apply Nat2Z.id).
              reflexivity. }
            rewrite Ha in Hi; exact Hi. }
          rewrite region_put_other by lia.
          rewrite region_put_other by lia.
          apply Hpadding; lia.
  Qed.

  Lemma replay_opens_induction
      (remaining c j : nat) (source state : t) :
    IsMonoid M ->
    Sized source ->
    active source < 2 * N + 1 ->
    c = closes source ->
    Sized state ->
    opens_replay_state c j source state ->
    c + j + remaining <= active source ->
    exists final,
      replay_opens remaining j source (Some state) = Some final /\
      opens_replay_state c (j + remaining) source final.
  Proof.
    revert j state.
    induction remaining as [|remaining IH]; intros j state HM Hsource_size
      Hsource_active Hc Hsized Hstate Hcount.
    - exists state; simpl; split; [reflexivity|].
      now rewrite Nat.add_0_r.
    - assert (Hbound : S (c + j) < PullArray.size (regions_of state)).
      { pose proof Hsource_size as Hsource_length.
        pose proof Hsized as Hstate_length.
        unfold Sized, regions_well_sized in Hsource_length, Hstate_length.
        lia. }
      pose proof (opens_replay_step (c:=c) (j:=j) (source:=source)
                    (state:=state) HM Hbound Hstate) as Hstep.
      set (next := append_region (append_open state)
                    (region (regions_of source) (c + S j))) in *.
      assert (Hnext_sized : Sized next).
      { unfold next; apply append_region_sized, append_open_sized; exact Hsized. }
      destruct (@IH (S j) next HM Hsource_size Hsource_active Hc Hnext_sized
                   Hstep) as [final [Hreplay Hfinal]]; try lia.
      exists final; simpl.
      unfold next in Hreplay, Hfinal.
      split.
      + rewrite <- Hc; exact Hreplay.
      +
      replace (j + S remaining) with (S j + remaining) by lia.
      exact Hfinal.
  Qed.

  Lemma regions_eq_of_active_agreement
      (x y : t) :
    Sized x -> Sized y ->
    active x = active y ->
    agrees_through (active x) (regions_of x) (regions_of y) ->
    padding_neutral x -> padding_neutral y ->
    regions_of x = regions_of y.
  Proof.
    intros Hsx Hsy Hactive Hagree Hpx Hpy.
    apply PullArray.ext.
    - unfold Sized, regions_well_sized in *; lia.
    - intros i.
      destruct (Nat.leb i (active x)) eqn:Hle.
      + apply Nat.leb_le in Hle.
        unfold agrees_through in Hagree.
        exact (Hagree i Hle).
      + apply Nat.leb_gt in Hle.
        change (region (regions_of x) i = region (regions_of y) i).
        assert (Hax : active x < i) by exact Hle.
        assert (Hay : active y < i) by lia.
        now rewrite (Hpx i Hax), (Hpy i Hay).
  Qed.

  (** Purely structural consistency.  It gives no interpretation to active
      region summaries. *)
  Definition Consistent (s : t) : Prop :=
    Sized s /\
    depth_consistent s /\
    active s < 2 * N + 1 /\
    padding_neutral s.

  Definition ConsistentOpt (s : option t) : Prop :=
    match s with
    | Some s' => Consistent s'
    | None => True
    end.

  (** Keep the active close prefix of a region array and replace its suffix
      by neutral elements.  This is the state from which the surviving opens
      of a summary can be replayed. *)
  Definition retain_through (k : nat) (rs : regions) : regions :=
    PullArray.mk (PullArray.size rs)
      (fun i => if Nat.leb i k then region rs i else m_ne M).

  Definition open_base (s : t) : t :=
    mk (lo s) (hi s) (lo s)
      (retain_through (closes s) (regions_of s)).

  Lemma retain_through_inside (k i : nat) (rs : regions) :
    i <= k -> region (retain_through k rs) i = region rs i.
  Proof.
    intro H; unfold retain_through, region; simpl.
    now rewrite (proj2 (Nat.leb_le i k) H).
  Qed.

  Lemma retain_through_outside (k i : nat) (rs : regions) :
    k < i -> region (retain_through k rs) i = m_ne M.
  Proof.
    intro H; unfold retain_through, region; simpl.
    now rewrite (proj2 (Nat.leb_gt i k) H).
  Qed.

  Lemma open_base_sized (s : t) : Sized s -> Sized (open_base s).
  Proof.
    unfold Sized, regions_well_sized, open_base; simpl.
    exact id.
  Qed.

  Lemma open_base_active (s : t) :
    (lo s <= 0)%Z -> active (open_base s) = closes s.
  Proof.
    intro Hlo; unfold open_base, active, closes, opens; simpl.
    replace (Z.to_nat (lo s - lo s)) with 0 by
      (replace (lo s - lo s)%Z with 0%Z by lia; reflexivity).
    apply Nat.add_0_r.
  Qed.

  Lemma open_base_opens (s : t) : opens (open_base s) = 0.
  Proof.
    unfold open_base, opens; simpl.
    replace (lo s - lo s)%Z with 0%Z by lia; reflexivity.
  Qed.

  Lemma open_base_lo_nonpos (s : t) :
    (lo s <= 0)%Z -> (lo (open_base s) <= 0)%Z.
  Proof. unfold open_base; simpl; exact id. Qed.

  Lemma open_base_lo_net (s : t) :
    (lo (open_base s) <= net (open_base s))%Z.
  Proof. unfold open_base; simpl; lia. Qed.

  Lemma open_base_agrees (s : t) :
    agrees_through (closes s) (regions_of (open_base s)) (regions_of s).
  Proof.
    intros i Hi; apply retain_through_inside; exact Hi.
  Qed.

  Lemma open_base_padding (s : t) :
    (lo s <= 0)%Z -> padding_neutral (open_base s).
  Proof.
    intros Hlo i Hi.
    rewrite open_base_active in Hi by exact Hlo.
    apply retain_through_outside; exact Hi.
  Qed.

  Lemma base_ne_padding : padding_neutral (base (m_ne M)).
  Proof.
    intros i Hactive.
    unfold active, closes, opens, base in Hactive; simpl in Hactive.
    unfold region, regions_of, base, put_region.
    rewrite PullArray.index_put_other by lia.
    apply PullArray.index_replicate.
  Qed.

  Theorem ne_consistent : ConsistentOpt ne.
  Proof.
    unfold ConsistentOpt, ne, Consistent; simpl.
    split; [apply base_sized|].
    split.
    - unfold depth_consistent, base; simpl; lia.
    - split.
      + unfold active, closes, opens, base; simpl; lia.
      + apply base_ne_padding.
  Qed.

  Lemma region_empty_ne_zero :
    region (put_region empty_regions 0 (m_ne M)) 0 = m_ne M.
  Proof.
    unfold region, put_region.
    apply PullArray.index_put_same; simpl; lia.
  Qed.

  Lemma put_region_region_same (rs : regions) (i : nat) :
    i < PullArray.size rs -> put_region rs i (region rs i) = rs.
  Proof.
    apply PullArray.put_same.
  Qed.

  Theorem ne_right_neutral :
    IsMonoid M ->
    forall x, ConsistentOpt x -> parens_n_op x ne = x.
  Proof.
    intros HM [s|] Hconsistent; [|reflexivity].
    change (Consistent s) in Hconsistent.
    destruct Hconsistent as [Hsized [Hdepth [Hactive Hpadding]]].
    destruct Hdepth as [Hlo [Hhi [Hlonet [Hnethi Hspan]]]].
    unfold ne, parens_n_op; simpl.
    rewrite region_empty_ne_zero.
    destruct HM as [_ [_ HM_r]].
    rewrite HM_r.
    rewrite put_region_region_same.
    repeat rewrite Z.add_0_r.
    rewrite Z.min_l by exact Hlonet.
    rewrite Z.max_l by exact Hnethi.
    destruct (Z.ltb (Z.of_nat N) (hi s - lo s)) eqn:Hguard.
    - apply Z.ltb_lt in Hguard; lia.
    - simpl.
      destruct s; reflexivity.
    - unfold Sized, regions_well_sized in Hsized.
      lia.
  Qed.

  Lemma closes_as_depth (s : t) :
    Z.le (lo s) 0 -> Z.of_nat (closes s) = Z.opp (lo s).
  Proof.
    intro Hlo; unfold closes.
    rewrite Z2Nat.id; lia.
  Qed.

  Lemma opens_as_depth (s : t) :
    Z.le (lo s) (net s) ->
    Z.of_nat (opens s) = Z.sub (net s) (lo s).
  Proof.
    intro Hlo; unfold opens.
    rewrite Z2Nat.id; lia.
  Qed.

  Lemma depth_consistent_active_bound (s : t) :
    depth_consistent s -> active s < 2 * N + 1.
  Proof.
    intros [Hlo [Hhi [Hlonet [Hnethi Hspan]]]].
    pose proof (closes_as_depth s Hlo) as Hcloses.
    pose proof (opens_as_depth s Hlonet) as Hopens.
    unfold active.
    apply Nat2Z.inj_lt.
    rewrite Nat2Z.inj_add, Hcloses, Hopens.
    rewrite Nat2Z.inj_add, Nat2Z.inj_mul; simpl.
    assert (Hclose_bound : (- lo s <= Z.of_nat N)%Z) by lia.
    assert (Hopen_bound : (net s - lo s <= Z.of_nat N)%Z) by lia.
    change (- lo s + (net s - lo s) < 2 * Z.of_nat N + 1)%Z.
    lia.
  Qed.

  (** Every consistent summary is obtained, up to the fields relevant to
      replay, by retaining its close prefix and replaying its open suffix. *)
  Lemma replay_opens_reconstruct (s : t) :
    IsMonoid M ->
    Consistent s ->
    exists rebuilt,
      replay_opens (opens s) 0 s (Some (open_base s)) = Some rebuilt /\
      ReplayEq rebuilt s.
  Proof.
    intros HM [Hsized [Hdepth [Hactive Hpadding]]].
    destruct Hdepth as [Hlo [Hhi [Hlonet [Hnethi Hspan]]]].
    pose proof (closes_as_depth s Hlo) as Hcloses.
    pose proof (opens_as_depth s Hlonet) as Hopens.
    assert (Hbase_sized : Sized (open_base s)).
    { apply open_base_sized; exact Hsized. }
    assert (Hbase_state :
      opens_replay_state (closes s) 0 s (open_base s)).
    { unfold opens_replay_state.
      repeat split.
      - unfold open_base; simpl; lia.
      - unfold open_base; simpl; lia.
      - rewrite open_base_active by exact Hlo; lia.
      - replace (closes s + 0) with (closes s) by lia.
        apply open_base_agrees.
      - apply open_base_padding; exact Hlo. }
    assert (Hcount : closes s + 0 + opens s <= active s).
    { unfold active; lia. }
    destruct (replay_opens_induction (opens s)
                (c:=closes s) (j:=0)
                (source:=s) (state:=open_base s)
                HM Hsized Hactive eq_refl Hbase_sized Hbase_state Hcount)
      as [rebuilt [Hreplay Hrebuilt_state]].
    exists rebuilt; split; [exact Hreplay|].
    assert (Hrebuilt_sized : Sized rebuilt).
    { pose proof
        (replay_opens_sized (opens s) 0 s (Some (open_base s))
           Hbase_sized) as H.
      rewrite Hreplay in H; exact H. }
    destruct Hrebuilt_state as
      [Hrebuilt_lo [Hrebuilt_net
        [Hrebuilt_active [Hrebuilt_agree Hrebuilt_padding]]]].
    unfold ReplayEq; repeat split.
    - lia.
    - lia.
    - eapply regions_eq_of_active_agreement.
      + exact Hrebuilt_sized.
      + exact Hsized.
      + rewrite Hrebuilt_active; unfold active; lia.
      + rewrite Hrebuilt_active.
        replace (closes s + (0 + opens s)) with (active s)
          by (unfold active; lia).
        exact Hrebuilt_agree.
      + exact Hrebuilt_padding.
      + exact Hpadding.
  Qed.

  Corollary consistent_as_open_replay (s : t) :
    IsMonoid M ->
    Consistent s ->
    ReplayEqOpt
      (replay_opens (opens s) 0 s (Some (open_base s)))
      (Some s).
  Proof.
    intros HM Hconsistent.
    destruct (replay_opens_reconstruct (s:=s) HM Hconsistent)
      as [rebuilt [Hreplay Heq]].
    rewrite Hreplay; exact Heq.
  Qed.

  Lemma append_region_closes (s : t) (x : m_summary M) :
    closes (append_region s x) = closes s.
  Proof. reflexivity. Qed.

  Lemma append_region_opens (s : t) (x : m_summary M) :
    opens (append_region s x) = opens s.
  Proof. reflexivity. Qed.

  Lemma append_region_active (s : t) (x : m_summary M) :
    active (append_region s x) = active s.
  Proof. reflexivity. Qed.

  Lemma append_close_lo_net (s result : t) :
    append_close s = Some result ->
    (lo result <= net result)%Z.
  Proof.
    unfold append_close.
    destruct (Nat.ltb 0 (opens s)).
    - destruct (close (region (regions_of s) (active s)));
        try discriminate.
      intro H; inversion H; subst result; simpl.
      destruct (Z_le_dec (lo s) (net s - 1)).
      + rewrite Z.min_l by lia; lia.
      + rewrite Z.min_r by lia; lia.
    - intro H; inversion H; subst result; simpl.
      destruct (Z_le_dec (lo s) (net s - 1)).
      + rewrite Z.min_l by lia; lia.
      + rewrite Z.min_r by lia; lia.
  Qed.

  Lemma append_close_lo_nonpos (s result : t) :
    (lo s <= 0)%Z ->
    append_close s = Some result ->
    (lo result <= 0)%Z.
  Proof.
    intro Hlo; unfold append_close.
    destruct (Nat.ltb 0 (opens s)).
    - destruct (close (region (regions_of s) (active s)));
        try discriminate.
      intro H; inversion H; subst result; simpl.
      eapply Z.le_trans; [apply Z.le_min_l|exact Hlo].
    - intro H; inversion H; subst result; simpl.
      eapply Z.le_trans; [apply Z.le_min_l|exact Hlo].
  Qed.

  Lemma opens_positive_lo_lt_net (s : t) :
    (lo s <= net s)%Z ->
    0 < opens s ->
    (lo s < net s)%Z.
  Proof.
    intros Hlonet Hopens.
    pose proof (opens_as_depth s Hlonet) as Hdepth.
    assert (0 < Z.of_nat (opens s))%Z.
    { exact (proj1 (Nat2Z.inj_lt 0 (opens s)) Hopens). }
    lia.
  Qed.

  Lemma opens_zero_lo_eq_net (s : t) :
    (lo s <= net s)%Z ->
    opens s = 0 ->
    lo s = net s.
  Proof.
    intros Hlonet Hopens.
    pose proof (opens_as_depth s Hlonet) as Hdepth.
    rewrite Hopens in Hdepth; simpl in Hdepth; lia.
  Qed.

  Lemma append_close_active_open (s result : t) :
    (lo s <= 0)%Z ->
    (lo s <= net s)%Z ->
    0 < opens s ->
    append_close s = Some result ->
    S (active result) = active s.
  Proof.
    intros Hlo Hlonet Hopens Hclose.
    pose proof (opens_positive_lo_lt_net s Hlonet Hopens) as Hltnet.
    unfold append_close in Hclose.
    rewrite (proj2 (Nat.ltb_lt 0 (opens s)) Hopens) in Hclose.
    destruct (close (region (regions_of s) (active s)));
      try discriminate.
    inversion Hclose; subst result; clear Hclose.
    unfold active, closes, opens; simpl.
    rewrite Z.min_l by lia.
    apply Nat2Z.inj.
    rewrite Nat2Z.inj_succ, !Nat2Z.inj_add, !Z2Nat.id by lia.
    lia.
  Qed.

  Lemma append_close_active_no_open (s result : t) :
    (lo s <= 0)%Z ->
    (lo s <= net s)%Z ->
    opens s = 0 ->
    append_close s = Some result ->
    active result = S (active s).
  Proof.
    intros Hlo Hlonet Hopens Hclose.
    pose proof (opens_zero_lo_eq_net s Hlonet Hopens) as Heq.
    unfold append_close in Hclose.
    rewrite Hopens in Hclose; simpl in Hclose.
    inversion Hclose; subst result; clear Hclose.
    unfold active, closes, opens; simpl.
    rewrite Z.min_r by lia.
    apply Nat2Z.inj.
    rewrite Nat2Z.inj_succ, !Nat2Z.inj_add, !Z2Nat.id by lia.
    lia.
  Qed.

  Lemma append_close_counts_open (s result : t) :
    (lo s <= 0)%Z ->
    (lo s <= net s)%Z ->
    0 < opens s ->
    append_close s = Some result ->
    closes result = closes s /\
    S (opens result) = opens s.
  Proof.
    intros Hlo Hlonet Hopens Hclose.
    pose proof (opens_positive_lo_lt_net s Hlonet Hopens) as Hltnet.
    assert (Hactive : S (active result) = active s).
    { eapply append_close_active_open; eauto. }
    assert (Hcloses : closes result = closes s).
    { unfold append_close in Hclose.
      rewrite (proj2 (Nat.ltb_lt 0 (opens s)) Hopens) in Hclose.
      destruct (close (region (regions_of s) (active s)));
        try discriminate.
      inversion Hclose; subst result; clear Hclose.
      unfold closes; simpl.
      rewrite Z.min_l by lia; reflexivity. }
    split; [exact Hcloses|].
    unfold active in Hactive.
    lia.
  Qed.

  Lemma append_close_counts_no_open (s result : t) :
    (lo s <= 0)%Z ->
    (lo s <= net s)%Z ->
    opens s = 0 ->
    append_close s = Some result ->
    closes result = S (closes s) /\
    opens result = 0.
  Proof.
    intros Hlo Hlonet Hopens Hclose.
    pose proof (opens_zero_lo_eq_net s Hlonet Hopens) as Heq.
    assert (Hactive : active result = S (active s)).
    { eapply append_close_active_no_open; eauto. }
    assert (Hopens_result : opens result = 0).
    { unfold append_close in Hclose.
      rewrite Hopens in Hclose; simpl in Hclose.
      inversion Hclose; subst result; clear Hclose.
      unfold opens; simpl.
      rewrite Z.min_r by lia.
      replace (net s - 1 - (net s - 1))%Z with 0%Z by lia.
      reflexivity. }
    split; [|exact Hopens_result].
    unfold active in Hactive.
    rewrite Hopens, Hopens_result in Hactive; lia.
  Qed.

  Lemma append_close_no_open_region_old
      (s result : t) (i : nat) :
    opens s = 0 ->
    i <= active s ->
    append_close s = Some result ->
    region (regions_of result) i = region (regions_of s) i.
  Proof.
    intros Hopens Hi Hclose.
    unfold append_close in Hclose.
    rewrite Hopens in Hclose; simpl in Hclose.
    inversion Hclose; subst result; clear Hclose.
    simpl; rewrite region_put_other; [reflexivity|].
    unfold active in Hi; rewrite Hopens in Hi; lia.
  Qed.

  Lemma append_close_no_open_region_new
      (s result : t) :
    Sized s ->
    opens s = 0 ->
    active s < 2 * N ->
    append_close s = Some result ->
    region (regions_of result) (S (active s)) = m_ne M.
  Proof.
    intros Hsized Hopens Hbound Hclose.
    unfold append_close in Hclose.
    rewrite Hopens in Hclose; simpl in Hclose.
    inversion Hclose; subst result; clear Hclose.
    simpl.
    replace (closes s + 1) with (S (active s)).
    2:{ unfold active; rewrite Hopens; lia. }
    rewrite region_put_same.
    - reflexivity.
    - unfold Sized, regions_well_sized in Hsized; lia.
  Qed.

  Lemma append_close_padding (s result : t) :
    Sized s ->
    (lo s <= 0)%Z ->
    (lo s <= net s)%Z ->
    active s < PullArray.size (regions_of s) ->
    padding_neutral s ->
    append_close s = Some result ->
    padding_neutral result.
  Proof.
    intros Hsized Hlo Hlonet Hbound Hpadding Hclose.
    destruct (Nat.eq_dec (opens s) 0) as [Hnoopen|Hhasopen].
    - assert (Hactive_result : active result = S (active s)).
      { eapply append_close_active_no_open; eauto. }
      unfold append_close in Hclose.
      rewrite Hnoopen in Hclose; simpl in Hclose.
      inversion Hclose; subst result; clear Hclose.
      unfold padding_neutral; intros i Hi; simpl in *.
      unfold region, put_region; simpl.
      rewrite PullArray.index_put_other.
      + apply Hpadding.
        unfold active in *; rewrite Hnoopen in *; lia.
      + unfold active in Hactive_result; simpl in Hactive_result.
        unfold active in Hi; simpl in Hi; lia.
    - assert (Hopen : 0 < opens s) by lia.
      assert (Hactive_result : S (active result) = active s).
      { eapply append_close_active_open; eauto. }
      unfold append_close in Hclose.
      rewrite (proj2 (Nat.ltb_lt 0 (opens s)) Hopen) in Hclose.
      destruct (close (region (regions_of s) (active s)));
        try discriminate.
      inversion Hclose; subst result; clear Hclose.
      unfold padding_neutral; intros i Hi; simpl in *.
      destruct (Nat.eq_dec i (active s)) as [Heq|Hneq].
      + subst i.
        unfold region, put_region.
        rewrite PullArray.index_put_same.
        * reflexivity.
        * rewrite PullArray.size_put; exact Hbound.
      + unfold region, put_region.
        rewrite PullArray.index_put_other by congruence.
        rewrite PullArray.index_put_other by lia.
        apply Hpadding.
        lia.
  Qed.

  Lemma replay_closes_counts
      (remaining j : nat) (source state result : t) :
    (lo state <= 0)%Z ->
    (lo state <= net state)%Z ->
    replay_closes remaining j source (Some state) = Some result ->
    opens result = opens state - remaining /\
    closes result = closes state + (remaining - opens state).
  Proof.
    revert j state.
    induction remaining as [|remaining IH];
      intros j state Hlo Hlonet Hreplay.
    - simpl in Hreplay; inversion Hreplay; subst result.
      simpl; lia.
    - simpl in Hreplay.
      destruct (append_close state) as [after_close|] eqn:Hclose;
        try discriminate.
      set (next := append_region after_close
        (region (regions_of source) (S j))) in Hreplay.
      assert (Hnext_lo : (lo next <= 0)%Z).
      { unfold next; simpl.
        eapply append_close_lo_nonpos; eauto. }
      assert (Hnext_lonet : (lo next <= net next)%Z).
      { unfold next; simpl.
        eapply append_close_lo_net; eauto. }
      specialize (IH (S j) next Hnext_lo Hnext_lonet Hreplay).
      destruct IH as [IHopens IHcloses].
      assert (Hnext_opens : opens next = opens after_close).
      { unfold next; apply append_region_opens. }
      assert (Hnext_closes : closes next = closes after_close).
      { unfold next; apply append_region_closes. }
      destruct (Nat.eq_dec (opens state) 0) as [Hnone|Hsome].
      + pose proof
          (append_close_counts_no_open state Hlo Hlonet Hnone Hclose)
          as [Hstep_closes Hstep_opens].
        rewrite Hnext_opens, Hstep_opens in IHopens.
        rewrite Hnext_closes, Hstep_closes,
          Hnext_opens, Hstep_opens in IHcloses.
        split; lia.
      + assert (Hpositive : 0 < opens state) by lia.
        pose proof
          (append_close_counts_open state Hlo Hlonet Hpositive Hclose)
          as [Hstep_closes Hstep_opens].
        rewrite Hnext_opens in IHopens.
        rewrite Hnext_closes, Hstep_closes, Hnext_opens in IHcloses.
        split; lia.
  Qed.

  Lemma replay_closes_order
      (remaining j : nat) (source state result : t) :
    (lo state <= 0)%Z ->
    (lo state <= net state)%Z ->
    replay_closes remaining j source (Some state) = Some result ->
    (lo result <= 0)%Z /\ (lo result <= net result)%Z.
  Proof.
    revert j state.
    induction remaining as [|remaining IH];
      intros j state Hlo Hlonet Hreplay.
    - simpl in Hreplay; inversion Hreplay; subst result.
      split; assumption.
    - simpl in Hreplay.
      destruct (append_close state) as [after_close|] eqn:Hclose;
        try discriminate.
      set (next := append_region after_close
        (region (regions_of source) (S j))) in Hreplay.
      apply (IH (S j) next).
      + unfold next; simpl; eapply append_close_lo_nonpos; eauto.
      + unfold next; simpl; eapply append_close_lo_net; eauto.
      + exact Hreplay.
  Qed.

  Corollary replay_closes_active_exact
      (remaining j : nat) (source state result : t) :
    (lo state <= 0)%Z ->
    (lo state <= net state)%Z ->
    replay_closes remaining j source (Some state) = Some result ->
    active result =
      closes state + (remaining - opens state) +
      (opens state - remaining).
  Proof.
    intros Hlo Hlonet Hreplay.
    assert (Hcounts :
      opens result = opens state - remaining /\
      closes result = closes state + (remaining - opens state)).
    { eapply replay_closes_counts; eauto. }
    destruct Hcounts as [Hopens Hcloses].
    unfold active; now rewrite Hopens, Hcloses.
  Qed.

  Lemma close_count_within_endpoints
      (initial_closes initial_opens prefix total : nat) :
    prefix <= total ->
    initial_closes + (prefix - initial_opens) +
        (initial_opens - prefix) <=
      Nat.max (initial_closes + initial_opens)
        (initial_closes + (total - initial_opens) +
          (initial_opens - total)).
  Proof.
    intro Hprefix.
    destruct (le_dec prefix initial_opens) as [Hp|Hp];
      destruct (le_dec total initial_opens) as [Ht|Ht]; simpl; lia.
  Qed.

  Corollary replay_closes_active_within_endpoints
      (prefix total j : nat) (source state result : t) :
    prefix <= total ->
    (lo state <= 0)%Z ->
    (lo state <= net state)%Z ->
    replay_closes prefix j source (Some state) = Some result ->
    active result <=
      Nat.max (active state)
        (closes state + (total - opens state) +
          (opens state - total)).
  Proof.
    intros Hprefix Hlo Hlonet Hreplay.
    assert (Hactive : active result =
      closes state + (prefix - opens state) +
      (opens state - prefix)).
    { eapply replay_closes_active_exact; eauto. }
    rewrite Hactive.
    unfold active at 1.
    apply close_count_within_endpoints; exact Hprefix.
  Qed.

  Lemma append_open_closes (s : t) :
    (lo s <= net s)%Z ->
    closes (append_open s) = closes s.
  Proof.
    intro Hlonet.
    unfold append_open, closes; simpl.
    now rewrite Z.min_l.
  Qed.

  Lemma append_open_opens (s : t) :
    (lo s <= net s)%Z ->
    opens (append_open s) = S (opens s).
  Proof.
    intro Hlonet; apply Nat2Z.inj.
    rewrite (opens_as_depth (append_open s)).
    - unfold append_open; simpl.
      rewrite Z.min_l by exact Hlonet.
      simpl.
      change (net s + 1 - lo s = Z.of_nat (S (opens s)))%Z.
      rewrite Nat2Z.inj_succ, (opens_as_depth s Hlonet); lia.
    - unfold append_open; simpl.
      rewrite Z.min_l by exact Hlonet; lia.
  Qed.

  Lemma append_open_active (s : t) :
    (lo s <= net s)%Z ->
    active (append_open s) = S (active s).
  Proof.
    intro Hlonet; unfold active.
    rewrite append_open_closes by exact Hlonet.
    rewrite append_open_opens by exact Hlonet.
    lia.
  Qed.

  Lemma append_region_padding
      (s : t) (x : m_summary M) :
    padding_neutral s -> padding_neutral (append_region s x).
  Proof.
    intros Hpadding i Hi.
    rewrite append_region_active in Hi.
    unfold append_region; simpl.
    rewrite region_put_other by lia.
    now apply Hpadding.
  Qed.

  Lemma append_open_lo_net (s : t) :
    (lo s <= net s)%Z ->
    (lo (append_open s) <= net (append_open s))%Z.
  Proof.
    intro Hlonet; unfold append_open; simpl.
    rewrite Z.min_l by exact Hlonet; lia.
  Qed.

  Lemma append_open_padding (s : t) :
    (lo s <= net s)%Z ->
    padding_neutral s -> padding_neutral (append_open s).
  Proof.
    intros Hlonet Hpadding i Hi.
    rewrite append_open_active in Hi by exact Hlonet.
    unfold append_open; simpl.
    rewrite region_put_other by lia.
    apply Hpadding; lia.
  Qed.

  Lemma append_open_region_old (s : t) (i : nat) :
    (lo s <= net s)%Z ->
    i <= active s ->
    region (regions_of (append_open s)) i =
      region (regions_of s) i.
  Proof.
    intros Hlonet Hi.
    unfold append_open; simpl.
    rewrite region_put_other; [reflexivity|lia].
  Qed.

  Lemma append_open_region_new (s : t) :
    Sized s ->
    (lo s <= net s)%Z ->
    S (active s) < PullArray.size (regions_of s) ->
    region (regions_of (append_open s)) (S (active s)) = m_ne M.
  Proof.
    intros Hsized Hlonet Hbound.
    unfold append_open; simpl.
    replace (S (active s)) with (active s + 1) by lia.
    rewrite region_put_same; [reflexivity|lia].
  Qed.

  Lemma append_region_at_active (s : t) (x : m_summary M) :
    active s < PullArray.size (regions_of s) ->
    region (regions_of (append_region s x)) (active s) =
      m_op M (region (regions_of s) (active s)) x.
  Proof.
    intro Hbound; unfold append_region; simpl.
    apply region_put_same; exact Hbound.
  Qed.

  Lemma append_region_before_active
      (s : t) (x : m_summary M) (i : nat) :
    i < active s ->
    region (regions_of (append_region s x)) i =
      region (regions_of s) i.
  Proof.
    intro Hi; unfold append_region; simpl.
    rewrite region_put_other; [reflexivity|lia].
  Qed.

  Lemma replay_closes_padding_endpoints
      (remaining j : nat) (source state result : t) :
    Sized state ->
    (lo state <= 0)%Z ->
    (lo state <= net state)%Z ->
    padding_neutral state ->
    Nat.max (active state)
      (closes state + (remaining - opens state) +
        (opens state - remaining)) <
      PullArray.size (regions_of state) ->
    replay_closes remaining j source (Some state) = Some result ->
    padding_neutral result.
  Proof.
    revert j state.
    induction remaining as [|remaining IH];
      intros j state Hsized Hlo Hlonet Hpadding Hbound Hreplay.
    - simpl in Hreplay; inversion Hreplay; subst result; exact Hpadding.
    - simpl in Hreplay.
      destruct (append_close state) as [after_close|] eqn:Hclose;
        try discriminate.
      set (next := append_region after_close
        (region (regions_of source) (S j))) in Hreplay.
      assert (Hstate_bound : active state < PullArray.size (regions_of state)).
      { eapply Nat.le_lt_trans; [apply Nat.le_max_l|exact Hbound]. }
      assert (Hclose_padding : padding_neutral after_close).
      { eapply append_close_padding; eauto. }
      assert (Hnext_padding : padding_neutral next).
      { unfold next; apply append_region_padding; exact Hclose_padding. }
      assert (Hnext_sized : Sized next).
      { unfold next; apply append_region_sized.
        eapply append_close_sized; eauto. }
      assert (Hnext_lo : (lo next <= 0)%Z).
      { unfold next; simpl; eapply append_close_lo_nonpos; eauto. }
      assert (Hnext_lonet : (lo next <= net next)%Z).
      { unfold next; simpl; eapply append_close_lo_net; eauto. }
      assert (Hstep :
        replay_closes 1 j source (Some state) = Some next).
      { simpl; rewrite Hclose; reflexivity. }
      assert (Hnext_active_bound :
        active next <=
          Nat.max (active state)
            (closes state + (S remaining - opens state) +
              (opens state - S remaining))).
      { eapply replay_closes_active_within_endpoints
          with (prefix:=1) (total:=S remaining)
               (j:=j) (source:=source) (state:=state).
        - lia.
        - exact Hlo.
        - exact Hlonet.
        - exact Hstep. }
      assert (Hstep_counts :
        opens next = opens state - 1 /\
        closes next = closes state + (1 - opens state)).
      { eapply replay_closes_counts; eauto. }
      destruct Hstep_counts as [Hnext_opens Hnext_closes].
      assert (Hfinal_counts :
        closes next + (remaining - opens next) +
            (opens next - remaining) =
        closes state + (S remaining - opens state) +
            (opens state - S remaining)).
      { lia. }
      assert (Hnext_bound :
        Nat.max (active next)
          (closes next + (remaining - opens next) +
            (opens next - remaining)) <
        PullArray.size (regions_of next)).
      { unfold Sized, regions_well_sized in Hsized, Hnext_sized.
        rewrite Hfinal_counts.
        destruct (le_dec (active next)
          (closes state + (S remaining - opens state) +
            (opens state - S remaining))) as [Hle|Hgt].
        - rewrite Nat.max_r by exact Hle; lia.
        - rewrite Nat.max_l by lia; lia. }
      eapply IH; eauto.
  Qed.

  Lemma replay_opens_preserves_prefix_invariants
      (remaining j : nat) (source state : t) :
    (lo state <= net state)%Z ->
    padding_neutral state ->
    exists final,
      replay_opens remaining j source (Some state) = Some final /\
      (lo final <= net final)%Z /\
      active final = active state + remaining /\
      padding_neutral final.
  Proof.
    revert j state.
    induction remaining as [|remaining IH];
      intros j state Hlonet Hpadding.
    - exists state; simpl; repeat split; try assumption; lia.
    - set (next := append_region (append_open state)
        (region (regions_of source) (closes source + S j))).
      assert (Hnext_lonet : (lo next <= net next)%Z).
      { unfold next; simpl; now apply append_open_lo_net. }
      assert (Hnext_active : active next = S (active state)).
      { unfold next; rewrite append_region_active.
        now apply append_open_active. }
      assert (Hnext_padding : padding_neutral next).
      { unfold next; apply append_region_padding, append_open_padding;
          assumption. }
      destruct (@IH (S j) next Hnext_lonet Hnext_padding)
        as [final [Hreplay [Hfinal_lonet [Hfinal_active Hfinal_padding]]]].
      exists final; simpl.
      fold next.
      repeat split; try assumption.
      rewrite Hfinal_active, Hnext_active; lia.
  Qed.

  Lemma replay_opens_result_invariants
      (remaining j : nat) (source state final : t) :
    replay_opens remaining j source (Some state) = Some final ->
    (lo state <= net state)%Z ->
    padding_neutral state ->
    (lo final <= net final)%Z /\
    active final = active state + remaining /\
    padding_neutral final.
  Proof.
    intros Hreplay Hlonet Hpadding.
    destruct (replay_opens_preserves_prefix_invariants
      remaining j source Hlonet Hpadding)
      as [computed [Hcomputed Hinvariants]].
    rewrite Hreplay in Hcomputed; inversion Hcomputed; subst computed.
    exact Hinvariants.
  Qed.

  Lemma replay_opens_region_layout
      (remaining j : nat) (source state result : t) :
    IsMonoid M ->
    Sized state ->
    (lo state <= net state)%Z ->
    active state + remaining < PullArray.size (regions_of state) ->
    replay_opens remaining j source (Some state) = Some result ->
    (forall i, i <= active state ->
      region (regions_of result) i = region (regions_of state) i) /\
    (forall r, r < remaining ->
      region (regions_of result) (active state + S r) =
      region (regions_of source) (closes source + S (j + r))).
  Proof.
    revert j state.
    induction remaining as [|remaining IH];
      intros j state HM Hsized Hlonet Hbound Hreplay.
    - simpl in Hreplay; inversion Hreplay; subst result.
      split; [intros; reflexivity|lia].
    - simpl in Hreplay.
      set (next := append_region (append_open state)
        (region (regions_of source) (closes source + S j))) in Hreplay.
      assert (Hopen_active :
        active (append_open state) = S (active state)).
      { apply append_open_active; exact Hlonet. }
      assert (Hnext_active : active next = S (active state)).
      { unfold next; rewrite append_region_active; exact Hopen_active. }
      assert (Hnext_sized : Sized next).
      { unfold next; apply append_region_sized, append_open_sized;
          exact Hsized. }
      assert (Hnext_lonet : (lo next <= net next)%Z).
      { unfold next; simpl; apply append_open_lo_net; exact Hlonet. }
      assert (Hnext_bound :
        active next + remaining < PullArray.size (regions_of next)).
      { unfold Sized, regions_well_sized in Hsized, Hnext_sized; lia. }
      assert (Hnext_prefix : forall i, i <= active state ->
        region (regions_of next) i = region (regions_of state) i).
      { intros i Hi; unfold next.
        rewrite append_region_before_active.
        - apply append_open_region_old; assumption.
        - rewrite Hopen_active; lia. }
      assert (Hnext_head :
        region (regions_of next) (S (active state)) =
        region (regions_of source) (closes source + S j)).
      { unfold next.
        rewrite <- Hopen_active.
        rewrite append_region_at_active.
        - rewrite Hopen_active.
          rewrite append_open_region_new.
          + destruct HM as [_ [HM_l _]]; now rewrite HM_l.
          + exact Hsized.
          + exact Hlonet.
          + unfold Sized, regions_well_sized in Hsized; lia.
        - unfold Sized, regions_well_sized in Hsized.
          rewrite Hopen_active.
          unfold append_open; simpl; rewrite put_region_length; lia. }
      specialize (IH (S j) next HM Hnext_sized Hnext_lonet
        Hnext_bound Hreplay).
      destruct IH as [IHprefix IHsuffix].
      split.
      + intros i Hi.
        rewrite IHprefix; [apply Hnext_prefix; exact Hi|].
        rewrite Hnext_active; lia.
      + intros r Hr.
        destruct r as [|r].
        * replace (active state + 1) with (S (active state)) by lia.
          rewrite IHprefix.
          -- replace (j + 0) with j by lia; exact Hnext_head.
          -- rewrite Hnext_active; lia.
        * replace (active state + S (S r))
            with (active next + S r) by (rewrite Hnext_active; lia).
          rewrite IHsuffix by lia.
          replace (S j + r) with (j + S r) by lia.
          reflexivity.
  Qed.

  Lemma replay_closes_no_open_region_layout
      (remaining j : nat) (source state result : t) :
    IsMonoid M ->
    Sized state ->
    (lo state <= 0)%Z ->
    (lo state <= net state)%Z ->
    opens state = 0 ->
    active state + remaining < PullArray.size (regions_of state) ->
    replay_closes remaining j source (Some state) = Some result ->
    (forall i, i <= active state ->
      region (regions_of result) i = region (regions_of state) i) /\
    (forall r, r < remaining ->
      region (regions_of result) (active state + S r) =
      region (regions_of source) (S (j + r))).
  Proof.
    revert j state.
    induction remaining as [|remaining IH];
      intros j state HM Hsized Hlo Hlonet Hnoopen Hbound Hreplay.
    - simpl in Hreplay; inversion Hreplay; subst result.
      split; [intros; reflexivity|lia].
    - simpl in Hreplay.
      destruct (append_close state) as [after_close|] eqn:Hclose;
        try discriminate.
      set (next := append_region after_close
        (region (regions_of source) (S j))) in Hreplay.
      assert (Hclose_active : active after_close = S (active state)).
      { eapply append_close_active_no_open; eauto. }
      assert (Hclose_counts :
        closes after_close = S (closes state) /\
        opens after_close = 0).
      { eapply append_close_counts_no_open; eauto. }
      destruct Hclose_counts as [Hclose_closes Hclose_opens].
      assert (Hnext_active : active next = S (active state)).
      { unfold next; rewrite append_region_active; exact Hclose_active. }
      assert (Hnext_noopen : opens next = 0).
      { unfold next; rewrite append_region_opens; exact Hclose_opens. }
      assert (Hafter_sized : Sized after_close).
      { eapply append_close_sized; eauto. }
      assert (Hnext_sized : Sized next).
      { unfold next; apply append_region_sized.
        exact Hafter_sized. }
      assert (Hnext_lo : (lo next <= 0)%Z).
      { unfold next; simpl; eapply append_close_lo_nonpos; eauto. }
      assert (Hnext_lonet : (lo next <= net next)%Z).
      { unfold next; simpl; eapply append_close_lo_net; eauto. }
      assert (Hnext_bound :
        active next + remaining < PullArray.size (regions_of next)).
      { unfold Sized, regions_well_sized in Hsized, Hnext_sized; lia. }
      assert (Hnext_prefix : forall i, i <= active state ->
        region (regions_of next) i = region (regions_of state) i).
      { intros i Hi; unfold next.
        rewrite append_region_before_active.
        - eapply append_close_no_open_region_old; eauto.
        - rewrite Hclose_active; lia. }
      assert (Hnext_head :
        region (regions_of next) (S (active state)) =
        region (regions_of source) (S j)).
      { unfold next; rewrite <- Hclose_active.
        rewrite append_region_at_active.
        - rewrite Hclose_active.
          rewrite (append_close_no_open_region_new
            (s:=state) Hsized Hnoopen).
          + destruct HM as [_ [HM_l _]]; now rewrite HM_l.
          + unfold Sized, regions_well_sized in Hsized; lia.
          + exact Hclose.
        - unfold Sized, regions_well_sized in Hsized.
          unfold Sized, regions_well_sized in Hafter_sized.
          lia. }
      specialize (IH (S j) next HM Hnext_sized Hnext_lo Hnext_lonet
        Hnext_noopen Hnext_bound Hreplay).
      destruct IH as [IHprefix IHsuffix].
      split.
      + intros i Hi.
        rewrite IHprefix; [apply Hnext_prefix; exact Hi|].
        rewrite Hnext_active; lia.
      + intros r Hr; destruct r as [|r].
        * replace (active state + 1) with (S (active state)) by lia.
          rewrite IHprefix.
          -- replace (j + 0) with j by lia; exact Hnext_head.
          -- rewrite Hnext_active; lia.
        * replace (active state + S (S r))
            with (active next + S r) by (rewrite Hnext_active; lia).
          rewrite IHsuffix by lia.
          replace (S j + r) with (j + S r) by lia.
          reflexivity.
  Qed.

  Lemma append_open_close_cancel
      (s : t) (x : m_summary M) :
    IsMonoid M ->
    (lo s <= net s)%Z ->
    S (active s) < PullArray.size (regions_of s) ->
    padding_neutral s ->
    ReplayEqOpt
      (append_close (append_region (append_open s) x))
      (match close x with
       | Some nested_summary => Some (append_region s nested_summary)
       | None => None
       end).
  Proof.
    intros [_ [HM_l _]] Hlonet Hbound Hpadding.
    assert (Hactive_open : active (append_open s) = S (active s)).
    { now apply append_open_active. }
    assert (Hopens_open : opens (append_open s) = S (opens s)).
    { now apply append_open_opens. }
    assert (Hinner :
      region
        (regions_of (append_region (append_open s) x))
        (S (active s)) = x).
    { unfold append_region; simpl.
      rewrite Hactive_open.
      rewrite region_put_same.
      - unfold append_open; simpl.
        unfold region, put_region.
        replace (active s + 1) with (S (active s)) by lia.
        rewrite PullArray.index_put_same.
        + apply HM_l.
        + exact Hbound.
      - unfold append_open; simpl.
        rewrite put_region_length; exact Hbound. }
    assert (Houter :
      region
        (regions_of (append_region (append_open s) x))
        (active s) = region (regions_of s) (active s)).
    { unfold append_region; simpl.
      rewrite Hactive_open.
      rewrite region_put_other by lia.
      unfold append_open; simpl.
      rewrite region_put_other by lia.
      reflexivity. }
    unfold append_close.
    rewrite append_region_opens, Hopens_open.
    replace (Nat.ltb 0 (S (opens s))) with true
      by (symmetry; apply Nat.ltb_lt; lia).
    rewrite append_region_active, Hactive_open.
    rewrite Hinner.
    replace (S (active s) - 1) with (active s) by lia.
    rewrite Houter.
    destruct (close x) as [nested_summary|] eqn:Hclose; simpl; [|exact I].
    unfold ReplayEq; simpl.
    split.
    - unfold append_open; simpl.
      replace (Z.min (lo s) (net s)) with (lo s)
        by (symmetry; apply Z.min_l; exact Hlonet).
      rewrite Z.min_l by lia; reflexivity.
    - split; [lia|].
      unfold append_region; simpl.
      rewrite Hactive_open.
      unfold append_open; simpl.
      replace (active s + 1) with (S (active s)) by lia.
      rewrite region_put_same by exact Hbound.
      rewrite HM_l.
      unfold put_region.
      rewrite PullArray.put_put_same_index.
      rewrite PullArray.put_put_other_index by lia.
      rewrite PullArray.put_put_same_index.
      assert (Hpad :
        PullArray.index (regions_of s) (S (active s)) = m_ne M).
      { unfold region in Hpadding; apply Hpadding; lia. }
      rewrite <- Hpad.
      rewrite PullArray.put_same by exact Hbound.
      reflexivity.
  Qed.

  Lemma append_open_close_cancel_two
      (s : t) (x y : m_summary M) :
    IsMonoid M ->
    (lo s <= net s)%Z ->
    S (active s) < PullArray.size (regions_of s) ->
    padding_neutral s ->
    ReplayEqOpt
      (append_close
        (append_region (append_region (append_open s) x) y))
      (match close (m_op M x y) with
       | Some nested_summary => Some (append_region s nested_summary)
       | None => None
       end).
  Proof.
    intros HM Hlonet Hbound Hpadding.
    assert (Happend :
      append_region (append_region (append_open s) x) y =
      append_region (append_open s) (m_op M x y)).
    { apply append_region_assoc; [exact HM|].
      rewrite append_open_active by exact Hlonet.
      unfold append_open; simpl.
      rewrite put_region_length; exact Hbound. }
    rewrite Happend.
    now apply append_open_close_cancel.
  Qed.

  Lemma replay_one_cancelled_open
      (j : nat) (close_source before : t)
      (x y : m_summary M) :
    IsMonoid M ->
    (lo before <= net before)%Z ->
    S (active before) < PullArray.size (regions_of before) ->
    padding_neutral before ->
    ReplayEqOpt
      (replay_closes 1 j close_source
        (Some
          (append_region (append_region (append_open before) x) y)))
      (match close (m_op M x y) with
       | Some nested_summary =>
           Some
             (append_region (append_region before nested_summary)
               (region (regions_of close_source) (S j)))
       | None => None
       end).
  Proof.
    intros HM Hlonet Hbound Hpadding.
    pose proof
      (append_open_close_cancel_two (s:=before) x y
        HM Hlonet Hbound Hpadding) as Hcancel.
    simpl.
    destruct (append_close
      (append_region (append_region (append_open before) x) y))
      as [after_close|] eqn:Hafter,
      (close (m_op M x y)) as [nested_summary|] eqn:Hnested;
      simpl in Hcancel |- *; try contradiction.
    - apply append_region_replay_eq; exact Hcancel.
    - exact I.
  Qed.

  Fixpoint cancel_pairs
      (remaining open_count close_index : nat)
      (open_source close_source : t)
      (acc : m_summary M) : option (m_summary M) :=
    match remaining, open_count with
    | 0, _ => Some acc
    | S remaining', S open_count' =>
        let open_region :=
          region (regions_of open_source)
            (closes open_source + S open_count') in
        match close (m_op M open_region acc) with
        | None => None
        | Some nested_summary =>
            let next_region :=
              region (regions_of close_source) (S close_index) in
            cancel_pairs remaining' open_count' (S close_index)
              open_source close_source
              (m_op M nested_summary next_region)
        end
    | S _, 0 => None
    end.

  Lemma cancel_pairs_plus
      (p q open_count close_index : nat)
      (open_source close_source : t) (acc : m_summary M) :
    p <= open_count ->
    cancel_pairs (p + q) open_count close_index
      open_source close_source acc =
    option_bind
      (cancel_pairs p open_count close_index
        open_source close_source acc)
      (fun acc' =>
        cancel_pairs q (open_count - p) (close_index + p)
          open_source close_source acc').
  Proof.
    revert open_count close_index acc.
    induction p as [|p IH]; intros open_count close_index acc Hbound.
    - simpl; rewrite Nat.sub_0_r, Nat.add_0_r; reflexivity.
    - destruct open_count as [|open_count]; [lia|].
      replace (S p + q) with (S (p + q)) by lia.
      simpl.
      destruct (close
        (m_op M
          (region (regions_of open_source)
            (closes open_source + S open_count)) acc))
        as [nested_summary|] eqn:Hclose; simpl; [|reflexivity].
      rewrite IH by lia.
      replace (S open_count - S p) with (open_count - p) by lia.
      replace (close_index + S p) with (S close_index + p) by lia.
      reflexivity.
  Qed.

  Lemma cancel_pairs_extensional
      (remaining open_count_x open_count_y
        close_index_x close_index_y : nat)
      (open_source_x open_source_y close_source_x close_source_y : t)
      (acc : m_summary M) :
    remaining <= open_count_x ->
    remaining <= open_count_y ->
    (forall r, r < remaining ->
      region (regions_of open_source_x)
        (closes open_source_x + (open_count_x - r)) =
      region (regions_of open_source_y)
        (closes open_source_y + (open_count_y - r))) ->
    (forall r, r < remaining ->
      region (regions_of close_source_x) (S (close_index_x + r)) =
      region (regions_of close_source_y) (S (close_index_y + r))) ->
    cancel_pairs remaining open_count_x close_index_x
      open_source_x close_source_x acc =
    cancel_pairs remaining open_count_y close_index_y
      open_source_y close_source_y acc.
  Proof.
    revert open_count_x open_count_y close_index_x close_index_y acc.
    induction remaining as [|remaining IH];
      intros open_count_x open_count_y close_index_x close_index_y acc
        Hbound_x Hbound_y Hopens Hcloses.
    - reflexivity.
    - destruct open_count_x as [|open_count_x],
        open_count_y as [|open_count_y]; try lia.
      simpl.
      assert (Hopen_head :
        region (regions_of open_source_x)
          (closes open_source_x + S open_count_x) =
        region (regions_of open_source_y)
          (closes open_source_y + S open_count_y)).
      { assert (Hzero : 0 < S remaining) by lia.
        pose proof (Hopens 0 Hzero) as Hhead.
        replace (S open_count_x) with (S open_count_x - 0) by lia.
        replace (S open_count_y) with (S open_count_y - 0) by lia.
        exact Hhead. }
      rewrite Hopen_head.
      destruct (close
        (m_op M
          (region (regions_of open_source_y)
            (closes open_source_y + S open_count_y)) acc));
        [|reflexivity].
      assert (Hclose_head :
        region (regions_of close_source_x) (S close_index_x) =
        region (regions_of close_source_y) (S close_index_y)).
      { assert (Hzero : 0 < S remaining) by lia.
        pose proof (Hcloses 0 Hzero) as Hhead.
        replace close_index_x with (close_index_x + 0) by lia.
        replace close_index_y with (close_index_y + 0) by lia.
        exact Hhead. }
      rewrite Hclose_head.
      apply IH; try lia.
      + intros r Hr.
        assert (Hsr : S r < S remaining) by lia.
        specialize (Hopens (S r) Hsr).
        replace (open_count_x - r) with (S open_count_x - S r) by lia.
        replace (open_count_y - r) with (S open_count_y - S r) by lia.
        exact Hopens.
      + intros r Hr.
        assert (Hsr : S r < S remaining) by lia.
        specialize (Hcloses (S r) Hsr).
        replace (S close_index_x + r) with (close_index_x + S r) by lia.
        replace (S close_index_y + r) with (close_index_y + S r) by lia.
        exact Hcloses.
  Qed.

  Lemma cancel_pairs_acc_eq
      (remaining open_count close_index : nat)
      (open_source close_source : t)
      (acc_x acc_y : m_summary M) :
    acc_x = acc_y ->
    cancel_pairs remaining open_count close_index
      open_source close_source acc_x =
    cancel_pairs remaining open_count close_index
      open_source close_source acc_y.
  Proof. now intros ->. Qed.

  Lemma cancel_pairs_pivot_assoc
      (remaining open_count_x open_count_y close_index : nat)
      (open_source_x open_source_y close_source : t)
      (pivot tail : m_summary M) :
    IsMonoid M ->
    S remaining <= open_count_x ->
    S remaining <= open_count_y ->
    region (regions_of open_source_x)
      (closes open_source_x + open_count_x) =
      m_op M
        (region (regions_of open_source_y)
          (closes open_source_y + open_count_y)) pivot ->
    (forall r, r < remaining ->
      region (regions_of open_source_x)
        (closes open_source_x + (open_count_x - S r)) =
      region (regions_of open_source_y)
        (closes open_source_y + (open_count_y - S r))) ->
    cancel_pairs (S remaining) open_count_x close_index
      open_source_x close_source tail =
    cancel_pairs (S remaining) open_count_y close_index
      open_source_y close_source (m_op M pivot tail).
  Proof.
    intros [Hassoc Hneutral] Hbound_x Hbound_y Hhead Htail.
    destruct open_count_x as [|open_count_x]; [lia|].
    destruct open_count_y as [|open_count_y]; [lia|].
    simpl.
    rewrite Hhead, Hassoc.
    destruct (close
      (m_op M
        (region (regions_of open_source_y)
          (closes open_source_y + S open_count_y))
        (m_op M pivot tail))) as [nested_summary|] eqn:Hclose;
      [|reflexivity].
    apply cancel_pairs_extensional; try lia.
    - intros r Hr.
      specialize (Htail r Hr).
      replace (S open_count_x - S r) with (open_count_x - r) in Htail
        by lia.
      replace (S open_count_y - S r) with (open_count_y - r) in Htail
        by lia.
      exact Htail.
    - intros r Hr; reflexivity.
  Qed.

  Lemma cancel_pairs_close_pivot_assoc
      (remaining open_count close_index : nat)
      (open_source close_source_x close_source_y : t)
      (acc pivot : m_summary M) :
    IsMonoid M ->
    S remaining <= open_count ->
    (forall r, r < remaining ->
      region (regions_of close_source_x) (S (close_index + r)) =
      region (regions_of close_source_y) (S (close_index + r))) ->
    region (regions_of close_source_x) (S (close_index + remaining)) =
      m_op M
        (region (regions_of close_source_y) (S (close_index + remaining)))
        pivot ->
    cancel_pairs (S remaining) open_count close_index
      open_source close_source_x acc =
    option_bind
      (cancel_pairs (S remaining) open_count close_index
        open_source close_source_y acc)
      (fun result => Some (m_op M result pivot)).
  Proof.
    revert open_count close_index acc.
    induction remaining as [|remaining IH];
      intros open_count close_index acc HM Hbound Hprefix Hpivot.
    - destruct open_count as [|open_count]; [lia|].
      simpl.
      replace (S (close_index + 0)) with (S close_index) in Hpivot by lia.
      rewrite Hpivot.
      destruct (close
        (m_op M
          (region (regions_of open_source)
            (closes open_source + S open_count)) acc))
        as [nested_summary|] eqn:Hclose; simpl; [|reflexivity].
      destruct HM as [Hassoc _].
      rewrite Hassoc; reflexivity.
    - destruct open_count as [|open_count]; [lia|].
      simpl.
      assert (Hhead :
        region (regions_of close_source_x) (S close_index) =
        region (regions_of close_source_y) (S close_index)).
      { specialize (Hprefix 0 ltac:(lia)).
        replace (close_index + 0) with close_index in Hprefix by lia.
        exact Hprefix. }
      rewrite Hhead.
      destruct (close
        (m_op M
          (region (regions_of open_source)
            (closes open_source + S open_count)) acc))
        as [nested_summary|] eqn:Hclose; simpl; [|reflexivity].
      apply IH; try assumption; try lia.
      + intros r Hr.
        specialize (Hprefix (S r) ltac:(lia)).
        replace (S close_index + r) with (close_index + S r) by lia.
        exact Hprefix.
      + replace (S close_index + remaining)
          with (close_index + S remaining) by lia.
        exact Hpivot.
  Qed.

  Lemma replay_cancel_pairs
      (k q open_index close_index : nat)
      (open_source close_source base : t)
      (acc : m_summary M) :
    IsMonoid M ->
    Sized base ->
    (lo base <= net base)%Z ->
    padding_neutral base ->
    active base + q + k < 2 * N + 1 ->
    ReplayEqOpt
      (option_bind
        (replay_opens (q + k) open_index open_source (Some base))
        (fun after_opens =>
          replay_closes k close_index close_source
            (Some (append_region after_opens acc))))
      (option_bind
        (cancel_pairs k (open_index + q + k) close_index
          open_source close_source acc)
        (fun acc' =>
          option_bind
            (replay_opens q open_index open_source (Some base))
            (fun after_opens => Some (append_region after_opens acc')))).
  Proof.
    revert q open_index close_index acc.
    induction k as [|k IH];
      intros q open_index close_index acc HM Hsized Hlonet Hpadding Hbound.
    - replace (q + 0) with q by lia.
      simpl.
      destruct (replay_opens q open_index open_source (Some base));
        apply ReplayEqOpt_refl.
    - replace (q + S k) with (S (q + k)) by lia.
      rewrite replay_opens_last.
      destruct (replay_opens (q + k) open_index open_source (Some base))
        as [before|] eqn:Hbefore.
      2:{ exfalso.
          destruct (replay_opens_preserves_prefix_invariants
            (q + k) open_index open_source Hlonet Hpadding)
            as [computed [Hcomputed _]].
          rewrite Hbefore in Hcomputed; discriminate. }
      simpl.
      assert (Hbefore_inv :
        (lo before <= net before)%Z /\
        active before = active base + (q + k) /\
        padding_neutral before).
      { eapply replay_opens_result_invariants; eauto. }
      destruct Hbefore_inv as
        [Hbefore_lonet [Hbefore_active Hbefore_padding]].
      assert (Hbefore_sized : Sized before).
      { pose proof
          (replay_opens_sized (q + k) open_index open_source
            (Some base) Hsized) as H.
        rewrite Hbefore in H; exact H. }
      assert (Hbefore_bound :
        S (active before) < PullArray.size (regions_of before)).
      { unfold Sized, regions_well_sized in Hsized, Hbefore_sized.
        lia. }
      set (x := region (regions_of open_source)
        (closes open_source + S (open_index + (q + k)))).
      pose proof
        (replay_one_cancelled_open close_index close_source
          (before:=before) x acc
          HM Hbefore_lonet Hbefore_bound Hbefore_padding) as Hone.
      replace (open_index + q + S k)
        with (S (open_index + q + k)) by lia.
      unfold x in Hone.
      lazymatch goal with
      | |- ReplayEqOpt ?lhs ?rhs =>
          change (ReplayEqOpt
            (replay_closes (S k) close_index close_source
              (Some
                (append_region (append_region (append_open before)
                  (region (regions_of open_source)
                    (closes open_source + S (open_index + (q + k)))))
                  acc))) rhs)
      end.
      replace (S k) with (1 + k) by lia.
      rewrite replay_closes_plus.
      replace (close_index + 1) with (S close_index) by lia.
      replace (open_index + q + k) with (open_index + (q + k)) by lia.
      destruct (close
        (m_op M
          (region (regions_of open_source)
            (closes open_source + S (open_index + (q + k)))) acc))
        as [nested_summary|] eqn:Hclose.
      2:{ simpl in Hone |- *.
          eapply ReplayEqOpt_trans.
          - apply replay_closes_replay_eq.
            + apply ReplayEq_refl.
            + exact Hone.
          - rewrite replay_closes_none; apply ReplayEqOpt_refl. }
      simpl.
      set (next_region :=
        region (regions_of close_source) (S close_index)).
      set (next_acc := m_op M nested_summary next_region).
      assert (Happend :
        append_region (append_region before nested_summary) next_region =
        append_region before next_acc).
      { unfold next_acc.
        apply append_region_assoc; [exact HM|].
        unfold Sized, regions_well_sized in Hbefore_sized.
        lia. }
      simpl in Hone.
      assert (Hfirst : ReplayEqOpt
        (replay_closes k (S close_index) close_source
          (replay_closes 1 close_index close_source
            (Some
              (append_region
                (append_region (append_open before) x) acc))))
        (replay_closes k (S close_index) close_source
          (Some (append_region before next_acc)))).
      { apply replay_closes_replay_eq.
        - apply ReplayEq_refl.
        - eapply ReplayEqOpt_trans with
            (y:=Some (append_region
              (append_region before nested_summary) next_region));
            [exact Hone|].
          simpl; rewrite Happend; apply ReplayEq_refl. }
      eapply ReplayEqOpt_trans; [exact Hfirst|].
      pose proof
        (IH q open_index (S close_index) next_acc
          HM Hsized Hlonet Hpadding) as Hrest.
      assert (Hrest_bound : active base + q + k < 2 * N + 1) by lia.
      specialize (Hrest Hrest_bound).
      rewrite Hbefore in Hrest; simpl in Hrest.
      replace (open_index + q + k) with (open_index + (q + k)) in Hrest
        by lia.
      exact Hrest.
  Qed.

  Lemma replay_cancel_prefix
      (k p open_index close_index : nat)
      (open_source close_source base : t)
      (acc : m_summary M) :
    k <= p ->
    IsMonoid M ->
    Sized base ->
    (lo base <= net base)%Z ->
    padding_neutral base ->
    active base + p < 2 * N + 1 ->
    ReplayEqOpt
      (option_bind
        (replay_opens p open_index open_source (Some base))
        (fun after_opens =>
          replay_closes k close_index close_source
            (Some (append_region after_opens acc))))
      (option_bind
        (cancel_pairs k (open_index + p) close_index
          open_source close_source acc)
        (fun acc' =>
          option_bind
            (replay_opens (p - k) open_index open_source (Some base))
            (fun after_opens => Some (append_region after_opens acc')))).
  Proof.
    intros Hkp HM Hsized Hlonet Hpadding Hbound.
    pose proof
      (replay_cancel_pairs k (p - k) open_index close_index
        open_source close_source (base:=base) acc
        HM Hsized Hlonet Hpadding) as H.
    assert (Hbound' : active base + (p - k) + k < 2 * N + 1) by lia.
    specialize (H Hbound').
    replace (p - k + k) with p in H by lia.
    replace (open_index + (p - k) + k) with (open_index + p) in H
      by lia.
    exact H.
  Qed.

  Lemma replay_closes_after_open_reconstruction
      (k close_index : nat) (b close_source : t)
      (acc : m_summary M) :
    IsMonoid M ->
    Consistent b ->
    ReplayEqOpt
      (option_bind
        (replay_opens (opens b) 0 b (Some (open_base b)))
        (fun after_opens =>
          replay_closes k close_index close_source
            (Some (append_region after_opens acc))))
      (replay_closes k close_index close_source
        (Some (append_region b acc))).
  Proof.
    intros HM Hconsistent.
    pose proof (consistent_as_open_replay (s:=b) HM Hconsistent) as Hreplay.
    eapply ReplayEqOpt_bind with
      (f:=fun after_opens =>
        replay_closes k close_index close_source
          (Some (append_region after_opens acc)))
      (g:=fun state =>
        replay_closes k close_index close_source
          (Some (append_region state acc))) in Hreplay.
    - exact Hreplay.
    - intros x y Hxy.
      apply replay_closes_replay_eq.
      + apply ReplayEq_refl.
      + simpl; apply append_region_replay_eq; exact Hxy.
  Qed.

  (** Cancellation specialised to an arbitrary consistent open source.
      The synthetic open replay has disappeared from the left-hand side. *)
  Lemma replay_cancel_consistent_prefix
      (k close_index : nat) (b close_source : t)
      (acc : m_summary M) :
    k <= opens b ->
    IsMonoid M ->
    Consistent b ->
    ReplayEqOpt
      (replay_closes k close_index close_source
        (Some (append_region b acc)))
      (option_bind
        (cancel_pairs k (opens b) close_index b close_source acc)
        (fun acc' =>
          option_bind
            (replay_opens (opens b - k) 0 b (Some (open_base b)))
            (fun after_opens => Some (append_region after_opens acc')))).
  Proof.
    intros Hk HM Hconsistent.
    pose proof Hconsistent as
      [Hsized [Hdepth [Hactive Hpadding]]].
    destruct Hdepth as [Hlo [Hhi [Hlonet [Hnethi Hspan]]]].
    pose proof
      (replay_closes_after_open_reconstruction
        (b:=b) k close_index close_source acc HM Hconsistent)
      as Hexpand.
    pose proof
      (replay_cancel_prefix (k:=k) (p:=opens b)
        0 close_index b close_source (base:=open_base b) acc Hk HM)
      as Hcancel.
    assert (Hbase_sized : Sized (open_base b)).
    { apply open_base_sized; exact Hsized. }
    assert (Hbase_lonet : (lo (open_base b) <= net (open_base b))%Z).
    { unfold open_base; simpl; lia. }
    assert (Hbase_padding : padding_neutral (open_base b)).
    { apply open_base_padding; exact Hlo. }
    assert (Hbound : active (open_base b) + opens b < 2 * N + 1).
    { rewrite open_base_active by exact Hlo.
      unfold active in Hactive; lia. }
    specialize (Hcancel Hbase_sized Hbase_lonet Hbase_padding Hbound).
    replace (0 + opens b) with (opens b) in Hcancel by lia.
    eapply ReplayEqOpt_trans.
    - apply ReplayEqOpt_sym; exact Hexpand.
    - exact Hcancel.
  Qed.

  Corollary replay_cancel_consistent_all
      (close_index : nat) (b close_source : t)
      (acc : m_summary M) :
    IsMonoid M ->
    Consistent b ->
    ReplayEqOpt
      (replay_closes (opens b) close_index close_source
        (Some (append_region b acc)))
      (option_bind
        (cancel_pairs (opens b) (opens b) close_index
          b close_source acc)
        (fun acc' => Some (append_region (open_base b) acc'))).
  Proof.
    intros HM Hconsistent.
    pose proof
      (replay_cancel_consistent_prefix
        (k:=opens b) (b:=b) close_index close_source acc
        (Nat.le_refl (opens b)) HM Hconsistent) as H.
    replace (opens b - opens b) with 0 in H by lia.
    simpl in H; exact H.
  Qed.

  Corollary replay_cancel_consistent_closes
      (b c : t) (acc : m_summary M) :
    closes c <= opens b ->
    IsMonoid M ->
    Consistent b ->
    ReplayEqOpt
      (replay_closes (closes c) 0 c
        (Some (append_region b acc)))
      (option_bind
        (cancel_pairs (closes c) (opens b) 0 b c acc)
        (fun acc' =>
          option_bind
            (replay_opens (opens b - closes c) 0 b (Some (open_base b)))
            (fun after_opens => Some (append_region after_opens acc')))).
  Proof.
    intros Hcb HM Hconsistent.
    exact (replay_cancel_consistent_prefix
      (k:=closes c) (b:=b) 0 c acc Hcb HM Hconsistent).
  Qed.

  Corollary replay_cancel_consistent_all_then_closes
      (b c : t) (acc : m_summary M) :
    opens b <= closes c ->
    IsMonoid M ->
    Consistent b ->
    ReplayEqOpt
      (replay_closes (closes c) 0 c
        (Some (append_region b acc)))
      (option_bind
        (cancel_pairs (opens b) (opens b) 0 b c acc)
        (fun acc' =>
          replay_closes (closes c - opens b) (opens b) c
            (Some (append_region (open_base b) acc')))).
  Proof.
    intros Hbc HM Hconsistent.
    pose proof
      (replay_cancel_consistent_all (b:=b) 0 c acc HM Hconsistent)
      as Hcancel.
    pose proof
      (replay_closes_replay_eq (closes c - opens b) (opens b)
        (replay_closes (opens b) 0 c
          (Some (append_region b acc)))
        (option_bind
          (cancel_pairs (opens b) (opens b) 0 b c acc)
          (fun acc' => Some (append_region (open_base b) acc')))
        (ReplayEq_refl c) Hcancel) as Htail.
    pose proof
      (replay_closes_plus (opens b) (closes c - opens b) 0 c
        (Some (append_region b acc))) as Hfuse.
    simpl in Hfuse.
    replace (opens b + (closes c - opens b)) with (closes c) in Hfuse
      by lia.
    rewrite Hfuse.
    destruct (cancel_pairs (opens b) (opens b) 0 b c acc) as [acc'|].
    - simpl in Htail |- *; exact Htail.
    - simpl in Htail |- *.
      rewrite replay_closes_none in Htail; exact Htail.
  Qed.

  Definition boundary_pairs (b c : t) : nat :=
    Nat.min (opens b) (closes c).

  Lemma min_sum_left_decompose (u v w : nat) :
    Nat.min (u + v) w =
      Nat.min u w + Nat.min v (w - u).
  Proof.
    repeat match goal with
    | |- context [Nat.min ?x ?y] =>
        destruct (le_dec x y);
        [rewrite Nat.min_l by lia|rewrite Nat.min_r by lia]
    end;
    lia.
  Qed.

  Lemma min_sum_right_decompose (u v w : nat) :
    Nat.min u (v + w) =
      Nat.min u v + Nat.min (u - v) w.
  Proof.
    repeat match goal with
    | |- context [Nat.min ?x ?y] =>
        destruct (le_dec x y);
        [rewrite Nat.min_l by lia|rewrite Nat.min_r by lia]
    end;
    lia.
  Qed.

  Lemma min_left_decomposition_prefix (u v w : nat) :
    Nat.min (Nat.min u w + Nat.min v (w - u)) u = Nat.min u w.
  Proof.
    repeat match goal with
    | |- context [Nat.min ?x ?y] =>
        destruct (le_dec x y);
        [rewrite Nat.min_l by lia|rewrite Nat.min_r by lia]
    end;
    lia.
  Qed.

  Definition three_way_boundary_pairs (a b c : t) : nat :=
    Nat.min (opens a - closes b) (closes c - opens b).

  Lemma three_way_boundary_pairs_zero_iff (a b c : t) :
    three_way_boundary_pairs a b c = 0 <->
      opens a <= closes b \/ closes c <= opens b.
  Proof.
    unfold three_way_boundary_pairs.
    destruct (le_dec (opens a - closes b) (closes c - opens b)).
    - rewrite Nat.min_l by assumption.
      split; intro H.
      + left; lia.
      + destruct H; lia.
    - rewrite Nat.min_r by lia.
      split; intro H.
      + right; lia.
      + destruct H; lia.
  Qed.

  Lemma three_way_boundary_pairs_positive_iff (a b c : t) :
    0 < three_way_boundary_pairs a b c <->
      closes b < opens a /\ opens b < closes c.
  Proof.
    unfold three_way_boundary_pairs.
    destruct (le_dec (opens a - closes b) (closes c - opens b)).
    - rewrite Nat.min_l by assumption; lia.
    - rewrite Nat.min_r by lia; lia.
  Qed.

  Lemma boundary_pairs_le_opens (b c : t) :
    boundary_pairs b c <= opens b.
  Proof.
    unfold boundary_pairs.
    destruct (Nat.le_ge_cases (opens b) (closes c)) as [Hle|Hge].
    - rewrite Nat.min_l by exact Hle; lia.
    - rewrite Nat.min_r by exact Hge; lia.
  Qed.

  Definition close_boundary_normal_form
      (b c : t) (acc : m_summary M) : option t :=
    if Nat.leb (closes c) (opens b) then
      option_bind
        (cancel_pairs (closes c) (opens b) 0 b c acc)
        (fun acc' =>
          option_bind
            (replay_opens (opens b - closes c) 0 b (Some (open_base b)))
            (fun after_opens => Some (append_region after_opens acc')))
    else
      option_bind
        (cancel_pairs (opens b) (opens b) 0 b c acc)
        (fun acc' =>
          replay_closes (closes c - opens b) (opens b) c
            (Some (append_region (open_base b) acc'))).

  Lemma close_boundary_normal_form_open
      (b c : t) (acc : m_summary M) :
    closes c <= opens b ->
    close_boundary_normal_form b c acc =
      option_bind
        (cancel_pairs (closes c) (opens b) 0 b c acc)
        (fun acc' =>
          option_bind
            (replay_opens (opens b - closes c) 0 b
              (Some (open_base b)))
            (fun after_opens => Some (append_region after_opens acc'))).
  Proof.
    intro Hopen.
    unfold close_boundary_normal_form.
    now rewrite (proj2 (Nat.leb_le (closes c) (opens b)) Hopen).
  Qed.

  Lemma close_boundary_normal_form_close
      (b c : t) (acc : m_summary M) :
    opens b < closes c ->
    close_boundary_normal_form b c acc =
      option_bind
        (cancel_pairs (opens b) (opens b) 0 b c acc)
        (fun acc' =>
          replay_closes (closes c - opens b) (opens b) c
            (Some (append_region (open_base b) acc'))).
  Proof.
    intro Hclose.
    unfold close_boundary_normal_form.
    now rewrite (proj2 (Nat.leb_gt (closes c) (opens b)) Hclose).
  Qed.

  Lemma close_boundary_normal_form_open_success
      (b c : t) (acc : m_summary M) (result : t) :
    closes c <= opens b ->
    close_boundary_normal_form b c acc = Some result ->
    exists acc' after_opens,
      cancel_pairs (closes c) (opens b) 0 b c acc = Some acc' /\
      replay_opens (opens b - closes c) 0 b (Some (open_base b)) =
        Some after_opens /\
      result = append_region after_opens acc'.
  Proof.
    intros Hle Hresult.
    unfold close_boundary_normal_form in Hresult.
    rewrite (proj2 (Nat.leb_le (closes c) (opens b)) Hle) in Hresult.
    destruct (cancel_pairs (closes c) (opens b) 0 b c acc)
      as [acc'|] eqn:Hcancel; simpl in Hresult; try discriminate.
    destruct (replay_opens (opens b - closes c) 0 b (Some (open_base b)))
      as [after_opens|] eqn:Hopens; simpl in Hresult; try discriminate.
    inversion Hresult; subst result.
    exists acc', after_opens; repeat split; assumption.
  Qed.

  Lemma close_boundary_normal_form_close_success
      (b c : t) (acc : m_summary M) (result : t) :
    opens b < closes c ->
    close_boundary_normal_form b c acc = Some result ->
    exists acc',
      cancel_pairs (opens b) (opens b) 0 b c acc = Some acc' /\
      replay_closes (closes c - opens b) (opens b) c
        (Some (append_region (open_base b) acc')) = Some result.
  Proof.
    intros Hlt Hresult.
    unfold close_boundary_normal_form in Hresult.
    assert (Hfalse : Nat.leb (closes c) (opens b) = false).
    { apply Nat.leb_gt; exact Hlt. }
    rewrite Hfalse in Hresult.
    destruct (cancel_pairs (opens b) (opens b) 0 b c acc)
      as [acc'|] eqn:Hcancel; simpl in Hresult; try discriminate.
    exists acc'; split; [reflexivity|exact Hresult].
  Qed.

  Lemma replay_closes_as_boundary_normal_form
      (b c : t) (acc : m_summary M) :
    IsMonoid M ->
    Consistent b ->
    ReplayEqOpt
      (replay_closes (closes c) 0 c (Some (append_region b acc)))
      (close_boundary_normal_form b c acc).
  Proof.
    intros HM Hconsistent.
    unfold close_boundary_normal_form.
    destruct (Nat.leb (closes c) (opens b)) eqn:Hle.
    - apply Nat.leb_le in Hle.
      exact (replay_cancel_consistent_closes
        (b:=b) c acc Hle HM Hconsistent).
    - apply Nat.leb_gt in Hle.
      assert (Hbc : opens b <= closes c) by lia.
      exact (replay_cancel_consistent_all_then_closes
        (b:=b) c acc Hbc HM Hconsistent).
  Qed.

  Definition replay_summary_normal_form (state source : t) : option t :=
    option_bind
      (close_boundary_normal_form state source
        (region (regions_of source) 0))
      (fun after_closes =>
        replay_opens (opens source) 0 source (Some after_closes)).

  Lemma replay_summary_normal_form_open
      (state source : t) :
    closes source <= opens state ->
    replay_summary_normal_form state source =
      option_bind
        (cancel_pairs (closes source) (opens state) 0 state source
          (region (regions_of source) 0))
        (fun acc' =>
          option_bind
            (replay_opens (opens state - closes source) 0 state
              (Some (open_base state)))
            (fun after_opens =>
              replay_opens (opens source) 0 source
                (Some (append_region after_opens acc')))).
  Proof.
    intro Hopen.
    unfold replay_summary_normal_form.
    rewrite close_boundary_normal_form_open by exact Hopen.
    destruct (cancel_pairs (closes source) (opens state) 0 state source
      (region (regions_of source) 0)) as [acc'|]; simpl; [|reflexivity].
    destruct (replay_opens (opens state - closes source) 0 state
      (Some (open_base state))); reflexivity.
  Qed.

  Lemma replay_summary_normal_form_close
      (state source : t) :
    opens state < closes source ->
    replay_summary_normal_form state source =
      option_bind
        (cancel_pairs (opens state) (opens state) 0 state source
          (region (regions_of source) 0))
        (fun acc' =>
          option_bind
            (replay_closes (closes source - opens state) (opens state)
              source (Some (append_region (open_base state) acc')))
            (fun after_closes =>
              replay_opens (opens source) 0 source
                (Some after_closes))).
  Proof.
    intro Hclose.
    unfold replay_summary_normal_form.
    rewrite close_boundary_normal_form_close by exact Hclose.
    destruct (cancel_pairs (opens state) (opens state) 0 state source
      (region (regions_of source) 0)) as [acc'|]; simpl; [|reflexivity].
    destruct (replay_closes (closes source - opens state) (opens state)
      source (Some (append_region (open_base state) acc')));
      reflexivity.
  Qed.

  Lemma replay_summary_as_boundary_normal_form (state source : t) :
    IsMonoid M ->
    Consistent state ->
    ReplayEqOpt
      (replay_summary state source)
      (replay_summary_normal_form state source).
  Proof.
    intros HM Hconsistent.
    pose proof
      (replay_closes_as_boundary_normal_form
        (b:=state) source (region (regions_of source) 0)
        HM Hconsistent) as Hcloses.
    unfold replay_summary, replay_summary_normal_form.
    eapply ReplayEqOpt_bind.
    - exact Hcloses.
    - intros x y Hxy.
      apply replay_opens_replay_eq.
      + apply ReplayEq_refl.
      + exact Hxy.
  Qed.

  Definition array_depth (s : t) : Depth :=
    depth (lo s) (hi s) (net s).

  Definition combined_depth (a b : t) : Depth :=
    depth_op (array_depth a) (array_depth b).

  Definition finish_replay (a b replayed : t) : t :=
    match combined_depth a b with
    | depth combined_lo combined_hi combined_net =>
        mk combined_lo combined_hi combined_net (regions_of replayed)
    end.

  Lemma finish_replay_sized (a b replayed : t) :
    Sized replayed -> Sized (finish_replay a b replayed).
  Proof.
    unfold Sized, regions_well_sized, finish_replay.
    destruct (combined_depth a b); simpl; exact id.
  Qed.

  Definition depth_supported_n (a b : t) : bool :=
    Z.leb (depth_span (combined_depth a b)) (Z.of_nat N).

  Lemma finish_replay_depth_consistent (a b replayed : t) :
    Consistent a ->
    Consistent b ->
    depth_supported_n a b = true ->
    depth_consistent (finish_replay a b replayed).
  Proof.
    intros [_ [Ha _]] [_ [Hb _]] Hsupported.
    destruct Ha as [Halo [Hahi [Halonet [Hanethi Haspan]]]].
    destruct Hb as [Hblo [Hbhi [Hblonet [Hbnethi Hbspan]]]].
    pose proof
      (depth_op_bounds (array_depth a) (array_depth b)
        Halo Hahi Hblonet Hbnethi) as Hbounds.
    unfold depth_supported_n in Hsupported.
    apply Z.leb_le in Hsupported.
    unfold combined_depth in Hsupported.
    unfold finish_replay, combined_depth.
    destruct (depth_op (array_depth a) (array_depth b))
      as [combined_lo combined_hi combined_net] eqn:Hcombined.
    unfold depth_consistent; simpl in *.
    destruct Hbounds as [Hlo [Hhi [Hlonet Hnethi]]].
    repeat split; assumption.
  Qed.

  Lemma regions_finish_replay (a b replayed : t) :
    regions_of (finish_replay a b replayed) = regions_of replayed.
  Proof.
    unfold finish_replay; destruct (combined_depth a b); reflexivity.
  Qed.

  Lemma finish_replay_consistent_of_replay_invariants
      (a b replayed : t) :
    Consistent a ->
    Consistent b ->
    depth_supported_n a b = true ->
    Sized replayed ->
    padding_neutral replayed ->
    active replayed = active (finish_replay a b replayed) ->
    Consistent (finish_replay a b replayed).
  Proof.
    intros Ha Hb Hsupported Hsized Hpadding Hactive.
    assert (Hdepth : depth_consistent (finish_replay a b replayed)).
    { apply finish_replay_depth_consistent; assumption. }
    unfold Consistent.
    split.
    - apply finish_replay_sized; exact Hsized.
    - split; [exact Hdepth|].
      split.
      + apply depth_consistent_active_bound; exact Hdepth.
      + intros i Hi.
        rewrite regions_finish_replay.
        apply Hpadding.
        rewrite Hactive; exact Hi.
  Qed.

  Lemma array_depth_finish_replay (a b replayed : t) :
    array_depth (finish_replay a b replayed) = combined_depth a b.
  Proof.
    unfold finish_replay; destruct (combined_depth a b); reflexivity.
  Qed.

  Lemma closes_finish_replay
      (a b replayed : t) :
    (lo a <= 0)%Z ->
    (lo a <= net a)%Z ->
    (lo b <= 0)%Z ->
    closes (finish_replay a b replayed) =
      closes a + (closes b - opens a).
  Proof.
    intros Halo Halonet Hblo.
    pose proof (closes_as_depth a Halo) as Hca.
    pose proof (opens_as_depth a Halonet) as Hoa.
    pose proof (closes_as_depth b Hblo) as Hcb.
    unfold finish_replay, combined_depth, array_depth, depth_op, zmin, zmax;
      simpl.
    destruct (le_dec (closes b) (opens a)) as [Hcancel|Hexcess].
    - rewrite Z.min_l by (apply Nat2Z.inj_le in Hcancel; lia).
      replace (closes b - opens a) with 0 by lia.
      change (closes a = closes a + 0).
      lia.
    - assert (Hmore : opens a < closes b) by lia.
      rewrite Z.min_r by (apply Nat2Z.inj_lt in Hmore; lia).
      apply Nat2Z.inj.
      change
        (Z.of_nat (Z.to_nat (- (net a + lo b))) =
         Z.of_nat (closes a + (closes b - opens a))).
      rewrite Z2Nat.id by (apply Nat2Z.inj_lt in Hmore; lia).
      rewrite Nat2Z.inj_add.
      rewrite Nat2Z.inj_sub by lia.
      lia.
  Qed.

  Lemma opens_finish_replay
      (a b replayed : t) :
    (lo a <= 0)%Z ->
    (lo a <= net a)%Z ->
    (lo b <= 0)%Z ->
    (lo b <= net b)%Z ->
    opens (finish_replay a b replayed) =
      opens b + (opens a - closes b).
  Proof.
    intros Halo Halonet Hblo Hblonet.
    pose proof (closes_as_depth a Halo) as Hca.
    pose proof (opens_as_depth a Halonet) as Hoa.
    pose proof (closes_as_depth b Hblo) as Hcb.
    pose proof (opens_as_depth b Hblonet) as Hob.
    unfold finish_replay, combined_depth, array_depth, depth_op, zmin, zmax;
      simpl.
    destruct (le_dec (closes b) (opens a)) as [Hcancel|Hexcess].
    - rewrite Z.min_l by (apply Nat2Z.inj_le in Hcancel; lia).
      apply Nat2Z.inj.
      change
        (Z.of_nat (Z.to_nat (net a + net b - lo a)) =
         Z.of_nat (opens b + (opens a - closes b))).
      rewrite Z2Nat.id by (apply Nat2Z.inj_le in Hcancel; lia).
      rewrite Nat2Z.inj_add.
      rewrite Nat2Z.inj_sub by exact Hcancel.
      lia.
    - assert (Hmore : opens a < closes b) by lia.
      rewrite Z.min_r by (apply Nat2Z.inj_lt in Hmore; lia).
      replace (opens a - closes b) with 0 by lia.
      apply Nat2Z.inj.
      change
        (Z.of_nat (Z.to_nat (net a + net b - (net a + lo b))) =
         Z.of_nat (opens b + 0)).
      rewrite Z2Nat.id by lia.
      simpl.
      lia.
  Qed.

  Lemma closes_finish_replay_consistent
      (a b replayed : t) :
    Consistent a -> Consistent b ->
    closes (finish_replay a b replayed) =
      closes a + (closes b - opens a).
  Proof.
    intros [_ [Ha _]] [_ [Hb _]].
    destruct Ha as [Halo [_ [Halonet _]]].
    destruct Hb as [Hblo _].
    apply closes_finish_replay; assumption.
  Qed.

  Lemma opens_finish_replay_consistent
      (a b replayed : t) :
    Consistent a -> Consistent b ->
    opens (finish_replay a b replayed) =
      opens b + (opens a - closes b).
  Proof.
    intros [_ [Ha _]] [_ [Hb _]].
    destruct Ha as [Halo [_ [Halonet _]]].
    destruct Hb as [Hblo [_ [Hblonet _]]].
    apply opens_finish_replay; assumption.
  Qed.

  Lemma boundary_pairs_left_outer_decompose
      (a b c replayed_ab : t) :
    Consistent a ->
    Consistent b ->
    boundary_pairs (finish_replay a b replayed_ab) c =
      boundary_pairs b c + three_way_boundary_pairs a b c.
  Proof.
    intros Ha Hb.
    unfold boundary_pairs, three_way_boundary_pairs.
    rewrite opens_finish_replay_consistent by assumption.
    apply min_sum_left_decompose.
  Qed.

  Lemma boundary_pairs_right_outer_decompose
      (a b c replayed_bc : t) :
    Consistent b ->
    Consistent c ->
    boundary_pairs a (finish_replay b c replayed_bc) =
      boundary_pairs a b + three_way_boundary_pairs a b c.
  Proof.
    intros Hb Hc.
    unfold boundary_pairs, three_way_boundary_pairs.
    rewrite closes_finish_replay_consistent by assumption.
    apply min_sum_right_decompose.
  Qed.

  Lemma opens_finish_replay_left_blocked
      (a b replayed_ab : t) :
    Consistent a ->
    Consistent b ->
    opens a <= closes b ->
    opens (finish_replay a b replayed_ab) = opens b.
  Proof.
    intros Ha Hb Hblocked.
    rewrite opens_finish_replay_consistent by assumption.
    replace (opens a - closes b) with 0 by lia.
    lia.
  Qed.

  Lemma positive_outer_open_branch_assoc_iff
      (a b c replayed_ab replayed_bc : t) :
    Consistent a ->
    Consistent b ->
    Consistent c ->
    0 < three_way_boundary_pairs a b c ->
    (closes c <= opens (finish_replay a b replayed_ab) <->
     closes (finish_replay b c replayed_bc) <= opens a).
  Proof.
    intros Ha Hb Hc Hpositive.
    apply three_way_boundary_pairs_positive_iff in Hpositive.
    destruct Hpositive as [Hba Hcb].
    rewrite opens_finish_replay_consistent by assumption.
    rewrite closes_finish_replay_consistent by assumption.
    lia.
  Qed.

  Lemma positive_outer_close_branch_assoc_iff
      (a b c replayed_ab replayed_bc : t) :
    Consistent a ->
    Consistent b ->
    Consistent c ->
    0 < three_way_boundary_pairs a b c ->
    (opens (finish_replay a b replayed_ab) < closes c <->
     opens a < closes (finish_replay b c replayed_bc)).
  Proof.
    intros Ha Hb Hc Hpositive.
    pose proof (positive_outer_open_branch_assoc_iff
      (a:=a) (b:=b) (c:=c) replayed_ab replayed_bc
      Ha Hb Hc Hpositive) as H.
    lia.
  Qed.

  Lemma positive_outer_residual_opens_assoc
      (a b c replayed_ab replayed_bc : t) :
    Consistent a ->
    Consistent b ->
    Consistent c ->
    0 < three_way_boundary_pairs a b c ->
    opens (finish_replay a b replayed_ab) - closes c =
      opens a - closes (finish_replay b c replayed_bc).
  Proof.
    intros Ha Hb Hc Hpositive.
    apply three_way_boundary_pairs_positive_iff in Hpositive.
    destruct Hpositive as [Hba Hcb].
    rewrite opens_finish_replay_consistent by assumption.
    rewrite closes_finish_replay_consistent by assumption.
    lia.
  Qed.

  Lemma positive_outer_residual_closes_assoc
      (a b c replayed_ab replayed_bc : t) :
    Consistent a ->
    Consistent b ->
    Consistent c ->
    0 < three_way_boundary_pairs a b c ->
    closes c - opens (finish_replay a b replayed_ab) =
      closes (finish_replay b c replayed_bc) - opens a.
  Proof.
    intros Ha Hb Hc Hpositive.
    apply three_way_boundary_pairs_positive_iff in Hpositive.
    destruct Hpositive as [Hba Hcb].
    rewrite opens_finish_replay_consistent by assumption.
    rewrite closes_finish_replay_consistent by assumption.
    lia.
  Qed.

  Lemma closes_finish_replay_right_blocked
      (b c replayed_bc : t) :
    Consistent b ->
    Consistent c ->
    closes c <= opens b ->
    closes (finish_replay b c replayed_bc) = closes b.
  Proof.
    intros Hb Hc Hblocked.
    rewrite closes_finish_replay_consistent by assumption.
    replace (closes c - opens b) with 0 by lia.
    lia.
  Qed.

  Lemma left_blocked_close_finish_counts
      (a b c replayed_ab replayed_bc : t) :
    Consistent a ->
    Consistent b ->
    Consistent c ->
    opens a <= closes b ->
    opens b < closes c ->
    opens (finish_replay a b replayed_ab) = opens b /\
    closes (finish_replay b c replayed_bc) =
      closes b + (closes c - opens b) /\
    opens (finish_replay b c replayed_bc) = opens c.
  Proof.
    intros Ha Hb Hc Hab Hbc.
    repeat split.
    - apply opens_finish_replay_left_blocked; assumption.
    - apply closes_finish_replay_consistent; assumption.
    - rewrite opens_finish_replay_consistent by assumption.
      replace (opens b - closes c) with 0 by lia.
      lia.
  Qed.

  Lemma left_blocked_close_right_residual_decompose
      (a b c replayed_bc : t) :
    Consistent b ->
    Consistent c ->
    opens a <= closes b ->
    opens b < closes c ->
    closes (finish_replay b c replayed_bc) - opens a =
      (closes b - opens a) + (closes c - opens b).
  Proof.
    intros Hb Hc Hab Hbc.
    rewrite closes_finish_replay_consistent by assumption.
    lia.
  Qed.

  Lemma left_blocked_close_right_replay_split
      (a b c replayed_bc : t) (initial : option t) :
    Consistent b ->
    Consistent c ->
    opens a <= closes b ->
    opens b < closes c ->
    replay_closes
      (closes (finish_replay b c replayed_bc) - opens a)
      (opens a) (finish_replay b c replayed_bc) initial =
    replay_closes (closes c - opens b) (closes b)
      (finish_replay b c replayed_bc)
      (replay_closes (closes b - opens a) (opens a)
        (finish_replay b c replayed_bc) initial).
  Proof.
    intros Hb Hc Hab Hbc.
    rewrite left_blocked_close_right_residual_decompose by assumption.
    rewrite replay_closes_plus.
    replace (opens a + (closes b - opens a)) with (closes b) by lia.
    reflexivity.
  Qed.

  Lemma left_blocked_close_outer_branches
      (a b c replayed_ab replayed_bc : t) :
    Consistent a ->
    Consistent b ->
    Consistent c ->
    opens a <= closes b ->
    opens b < closes c ->
    opens (finish_replay a b replayed_ab) < closes c /\
    opens a < closes (finish_replay b c replayed_bc).
  Proof.
    intros Ha Hb Hc Hab Hbc.
    destruct (left_blocked_close_finish_counts
      (a:=a) (b:=b) (c:=c) replayed_ab replayed_bc
      Ha Hb Hc Hab Hbc) as [Hleft [Hright_closes Hright_opens]].
    split; lia.
  Qed.

  Lemma boundary_pairs_left_outer_trailing_count
      (a b c replayed_ab : t) :
    Consistent a ->
    Consistent b ->
    Nat.min (boundary_pairs (finish_replay a b replayed_ab) c) (opens b) =
      boundary_pairs b c.
  Proof.
    intros Ha Hb.
    rewrite boundary_pairs_left_outer_decompose by assumption.
    unfold boundary_pairs, three_way_boundary_pairs.
    apply min_left_decomposition_prefix.
  Qed.

  Lemma surviving_open_normal_form_region_layout
      (b c : t) (after_opens : t) :
    IsMonoid M ->
    Consistent b ->
    closes c <= opens b ->
    replay_opens (opens b - closes c) 0 b (Some (open_base b)) =
      Some after_opens ->
    (forall i, i <= active (open_base b) ->
      region (regions_of after_opens) i =
      region (regions_of (open_base b)) i) /\
    (forall r, r < opens b - closes c ->
      region (regions_of after_opens) (active (open_base b) + S r) =
      region (regions_of b) (closes b + S r)).
  Proof.
    intros HM Hb Hcancel Hreplay.
    pose proof Hb as [Hb_sized [Hb_depth [Hb_bound Hb_padding]]].
    destruct Hb_depth as [Hb_lo _].
    assert (Hbase_sized : Sized (open_base b)).
    { apply open_base_sized; exact Hb_sized. }
    assert (Hbase_lonet :
      (lo (open_base b) <= net (open_base b))%Z).
    { apply open_base_lo_net. }
    assert (Hbase_bound :
      active (open_base b) + (opens b - closes c) <
        PullArray.size (regions_of (open_base b))).
    { unfold Sized, regions_well_sized in Hb_sized, Hbase_sized.
      rewrite open_base_active by exact Hb_lo.
      unfold active in Hb_bound; lia. }
    assert (Hlayout :
      (forall i, i <= active (open_base b) ->
        region (regions_of after_opens) i =
        region (regions_of (open_base b)) i) /\
      (forall r, r < opens b - closes c ->
        region (regions_of after_opens) (active (open_base b) + S r) =
        region (regions_of b) (closes b + S (0 + r)))).
    { eapply replay_opens_region_layout; eauto. }
    destruct Hlayout as [Hprefix Hsuffix].
    split; [exact Hprefix|].
    intros r Hr; specialize (Hsuffix r Hr).
    replace (0 + r) with r in Hsuffix by lia; exact Hsuffix.
  Qed.

  Lemma surviving_open_normal_form_append_layout
      (b c : t) (acc' : m_summary M) (after_opens result : t) :
    IsMonoid M ->
    Consistent b ->
    closes c <= opens b ->
    replay_opens (opens b - closes c) 0 b (Some (open_base b)) =
      Some after_opens ->
    result = append_region after_opens acc' ->
    (forall i, i < active after_opens ->
      region (regions_of result) i = region (regions_of after_opens) i) /\
    region (regions_of result) (active after_opens) =
      m_op M (region (regions_of after_opens) (active after_opens)) acc'.
  Proof.
    intros HM Hb Hcancel Hreplay ->.
    pose proof Hb as [Hb_sized [Hb_depth [Hb_bound Hb_padding]]].
    assert (Hafter_sized : Sized after_opens).
    { pose proof
        (replay_opens_sized (opens b - closes c) 0 b
          (Some (open_base b)) (open_base_sized Hb_sized)) as H.
      rewrite Hreplay in H; exact H. }
    assert (Hafter_active :
      active after_opens = active (open_base b) + (opens b - closes c)).
    { pose proof (open_base_padding b) as Hbase_padding.
      destruct Hb_depth as [Hb_lo [_ [Hb_lonet _]]].
      pose proof
        (replay_opens_result_invariants
          (opens b - closes c) 0 b
          Hreplay (open_base_lo_net b) (Hbase_padding Hb_lo))
        as [_ [Hactive _]].
      lia. }
    assert (Hactive_bound :
      active after_opens < PullArray.size (regions_of after_opens)).
    { unfold Sized, regions_well_sized in Hb_sized, Hafter_sized.
      rewrite Hafter_active, open_base_active by
        (destruct Hb_depth as [Hb_lo _]; exact Hb_lo).
      unfold active in Hb_bound; lia. }
    split.
    - intros i Hi; apply append_region_before_active; exact Hi.
    - apply append_region_at_active; exact Hactive_bound.
  Qed.

  Lemma excess_close_normal_form_region_layout
      (b c : t) (acc acc' : m_summary M) (result : t) :
    IsMonoid M ->
    Consistent b ->
    Consistent c ->
    depth_supported_n b c = true ->
    opens b < closes c ->
    cancel_pairs (opens b) (opens b) 0 b c acc = Some acc' ->
    replay_closes (closes c - opens b) (opens b) c
      (Some (append_region (open_base b) acc')) = Some result ->
    (forall i, i <= active (append_region (open_base b) acc') ->
      region (regions_of result) i =
      region (regions_of (append_region (open_base b) acc')) i) /\
    (forall r, r < closes c - opens b ->
      region (regions_of result)
        (active (append_region (open_base b) acc') + S r) =
      region (regions_of c) (S (opens b + r))).
  Proof.
    intros HM Hb Hc Hsupported Hexcess Hcancel Hreplay.
    pose proof Hb as [Hb_sized [Hb_depth [Hb_bound Hb_padding]]].
    destruct Hb_depth as [Hb_lo _].
    set (base := append_region (open_base b) acc').
    assert (Hbase_sized : Sized base).
    { unfold base; apply append_region_sized, open_base_sized; exact Hb_sized. }
    assert (Hbase_lo : (lo base <= 0)%Z).
    { unfold base; simpl; apply open_base_lo_nonpos; exact Hb_lo. }
    assert (Hbase_lonet : (lo base <= net base)%Z).
    { unfold base; simpl; apply open_base_lo_net. }
    assert (Hbase_opens : opens base = 0).
    { unfold base; rewrite append_region_opens; apply open_base_opens. }
    assert (Hbase_active : active base = closes b).
    { unfold base; rewrite append_region_active.
      apply open_base_active; exact Hb_lo. }
    assert (Hfinish_depth :
      depth_consistent (finish_replay b c b)).
    { apply finish_replay_depth_consistent; assumption. }
    assert (Hfinish_bound : active (finish_replay b c b) < 2 * N + 1).
    { apply depth_consistent_active_bound; exact Hfinish_depth. }
    assert (Hfinish_closes :
      closes (finish_replay b c b) =
        closes b + (closes c - opens b)).
    { apply closes_finish_replay_consistent; assumption. }
    assert (Hbase_bound :
      active base + (closes c - opens b) <
        PullArray.size (regions_of base)).
    { unfold Sized, regions_well_sized in Hbase_sized.
      rewrite Hbase_active, Hbase_sized.
      unfold active in Hfinish_bound.
      lia. }
    change (replay_closes (closes c - opens b) (opens b) c
      (Some base) = Some result) in Hreplay.
    change
      ((forall i, i <= active base ->
          region (regions_of result) i = region (regions_of base) i) /\
       (forall r, r < closes c - opens b ->
          region (regions_of result) (active base + S r) =
          region (regions_of c) (S (opens b + r)))).
    eapply replay_closes_no_open_region_layout; eauto.
  Qed.

  Lemma replay_summary_result_invariants
      (state source result : t) :
    Consistent state ->
    Consistent source ->
    depth_supported_n state source = true ->
    replay_summary state source = Some result ->
    Sized result /\
    padding_neutral result /\
    active result = active (finish_replay state source result).
  Proof.
    intros Hstate_consistent Hsource_consistent Hsupported Hreplay.
    pose proof Hstate_consistent as
      [Hstate_sized [Hstate_depth [Hstate_bound Hstate_padding]]].
    pose proof Hsource_consistent as
      [Hsource_sized [Hsource_depth [Hsource_bound Hsource_padding]]].
    destruct Hstate_depth as
      [Hstate_lo [Hstate_hi [Hstate_lonet [Hstate_nethi Hstate_span]]]].
    destruct Hsource_depth as
      [Hsource_lo [Hsource_hi
        [Hsource_lonet [Hsource_nethi Hsource_span]]]].
    set (seed := append_region state
      (region (regions_of source) 0)).
    unfold replay_summary in Hreplay; fold seed in Hreplay.
    destruct (replay_closes (closes source) 0 source (Some seed))
      as [after_closes|] eqn:Hcloses; try discriminate.
    destruct (replay_opens (opens source) 0 source (Some after_closes))
      as [after_opens|] eqn:Hopens; try discriminate.
    inversion Hreplay; subst after_opens; clear Hreplay.

    assert (Hseed_sized : Sized seed).
    { unfold seed; apply append_region_sized; exact Hstate_sized. }
    assert (Hseed_lo : (lo seed <= 0)%Z).
    { unfold seed; simpl; exact Hstate_lo. }
    assert (Hseed_lonet : (lo seed <= net seed)%Z).
    { unfold seed; simpl; exact Hstate_lonet. }
    assert (Hseed_padding : padding_neutral seed).
    { unfold seed; apply append_region_padding; exact Hstate_padding. }
    assert (Hseed_active : active seed = active state).
    { unfold seed; apply append_region_active. }

    set (close_endpoint :=
      closes state + (closes source - opens state) +
        (opens state - closes source)).
    assert (Hfinish_active :
      active (finish_replay state source result) =
        close_endpoint + opens source).
    { assert (Hfinish_closes :
        closes (finish_replay state source result) =
          closes state + (closes source - opens state)).
      { apply closes_finish_replay_consistent; assumption. }
      assert (Hfinish_opens :
        opens (finish_replay state source result) =
          opens source + (opens state - closes source)).
      { apply opens_finish_replay_consistent; assumption. }
      unfold active, close_endpoint.
      rewrite Hfinish_closes, Hfinish_opens.
      lia. }
    assert (Hfinish_depth :
      depth_consistent (finish_replay state source result)).
    { apply finish_replay_depth_consistent; assumption. }
    assert (Hfinish_bound :
      active (finish_replay state source result) < 2 * N + 1).
    { apply depth_consistent_active_bound; exact Hfinish_depth. }
    assert (Hendpoint_bound :
      Nat.max (active seed) close_endpoint <
        PullArray.size (regions_of seed)).
    { unfold Sized, regions_well_sized in Hseed_sized.
      rewrite Hseed_active, Hseed_sized.
      destruct (le_dec (active state) close_endpoint) as [Hle|Hgt].
      - rewrite Nat.max_r by exact Hle; lia.
      - rewrite Nat.max_l by lia; exact Hstate_bound. }
    assert (Hcloses_padding : padding_neutral after_closes).
    { eapply replay_closes_padding_endpoints; eauto. }
    assert (Hcloses_order :
      (lo after_closes <= 0)%Z /\
      (lo after_closes <= net after_closes)%Z).
    { eapply replay_closes_order; eauto. }
    destruct Hcloses_order as [Hcloses_lo Hcloses_lonet].
    assert (Hcloses_active : active after_closes = close_endpoint).
    { assert (Hraw : active after_closes =
        closes seed + (closes source - opens seed) +
          (opens seed - closes source)).
      { eapply replay_closes_active_exact.
        - exact Hseed_lo.
        - exact Hseed_lonet.
        - exact Hcloses. }
      unfold close_endpoint, seed in *; exact Hraw. }
    assert (Hopens_invariants :
      (lo result <= net result)%Z /\
      active result = active after_closes + opens source /\
      padding_neutral result).
    { eapply replay_opens_result_invariants; eauto. }
    destruct Hopens_invariants as
      [Hresult_lonet [Hresult_active Hresult_padding]].
    assert (Hafter_closes_sized : Sized after_closes).
    { pose proof
        (replay_closes_sized (closes source) 0 source (Some seed)
          Hseed_sized) as H.
      rewrite Hcloses in H; exact H. }
    assert (Hresult_sized : Sized result).
    { pose proof
        (replay_opens_sized (opens source) 0 source (Some after_closes)
          Hafter_closes_sized) as H.
      rewrite Hopens in H; exact H. }
    split; [exact Hresult_sized|].
    split; [exact Hresult_padding|].
    rewrite Hresult_active, Hcloses_active, Hfinish_active; reflexivity.
  Qed.

  Lemma replay_summary_close_phase_invariants (state source result : t) :
    Consistent state -> Consistent source ->
    depth_supported_n state source = true ->
    replay_summary state source = Some result ->
    exists after_closes,
      replay_closes (closes source) 0 source
        (Some (append_region state (region (regions_of source) 0))) =
        Some after_closes /\
      replay_opens (opens source) 0 source (Some after_closes) = Some result /\
      Sized after_closes /\ (lo after_closes <= 0)%Z /\
      (lo after_closes <= net after_closes)%Z /\
      padding_neutral after_closes /\
      active after_closes + opens source < PullArray.size (regions_of after_closes).
  Proof.
    intros Hstate Hsource Hsupported Hsummary.
    pose proof Hsummary as Hsummary'.
    unfold replay_summary in Hsummary'.
    set (seed := append_region state (region (regions_of source) 0))
      in Hsummary'.
    destruct (replay_closes (closes source) 0 source (Some seed))
      as [after_closes|] eqn:Hcloses; try discriminate.
    destruct (replay_opens (opens source) 0 source (Some after_closes))
      as [after_opens|] eqn:Hopens; try discriminate.
    inversion Hsummary'; subst after_opens; clear Hsummary'.
    pose proof Hstate as
      [Hstate_sized [Hstate_depth [Hstate_bound Hstate_padding]]].
    pose proof Hsource as
      [Hsource_sized [Hsource_depth [Hsource_bound Hsource_padding]]].
    destruct Hstate_depth as [Hstate_lo [_ [Hstate_lonet _]]].
    assert (Hseed_sized : Sized seed).
    { unfold seed; apply append_region_sized; exact Hstate_sized. }
    assert (Hafter_sized : Sized after_closes).
    { pose proof
        (replay_closes_sized (closes source) 0 source (Some seed)
          Hseed_sized) as H.
      rewrite Hcloses in H; exact H. }
    assert (Hseed_lo : (lo seed <= 0)%Z).
    { unfold seed; simpl; exact Hstate_lo. }
    assert (Hseed_lonet : (lo seed <= net seed)%Z).
    { unfold seed; simpl; exact Hstate_lonet. }
    assert (Hseed_padding : padding_neutral seed).
    { unfold seed; apply append_region_padding; exact Hstate_padding. }
    assert (Hseed_active : active seed = active state).
    { unfold seed; apply append_region_active. }
    assert (Hafter_order :
      (lo after_closes <= 0)%Z /\
      (lo after_closes <= net after_closes)%Z).
    { eapply replay_closes_order; eauto. }
    destruct Hafter_order as [Hafter_lo Hafter_lonet].
    assert (Hafter_active :
      active after_closes =
        closes state + (closes source - opens state) +
          (opens state - closes source)).
    { assert (Hraw : active after_closes =
        closes seed + (closes source - opens seed) +
          (opens seed - closes source)).
      { eapply replay_closes_active_exact; eauto. }
      unfold seed in Hraw; simpl in Hraw; exact Hraw. }
    assert (Hresult_invariants :
      Sized result /\ padding_neutral result /\
      active result = active (finish_replay state source result)).
    { eapply replay_summary_result_invariants; eauto. }
    destruct Hresult_invariants as
      [Hresult_sized [Hresult_padding Hresult_active]].
    assert (Hfinish_depth :
      depth_consistent (finish_replay state source result)).
    { apply finish_replay_depth_consistent; assumption. }
    assert (Hfinish_bound :
      active (finish_replay state source result) < 2 * N + 1).
    { apply depth_consistent_active_bound; exact Hfinish_depth. }
    set (close_endpoint :=
      closes state + (closes source - opens state) +
        (opens state - closes source)).
    assert (Hfinish_active :
      active (finish_replay state source result) =
        close_endpoint + opens source).
    { assert (Hfinish_closes :
        closes (finish_replay state source result) =
          closes state + (closes source - opens state)).
      { apply closes_finish_replay_consistent; assumption. }
      assert (Hfinish_opens :
        opens (finish_replay state source result) =
          opens source + (opens state - closes source)).
      { apply opens_finish_replay_consistent; assumption. }
      unfold active, close_endpoint.
      rewrite Hfinish_closes, Hfinish_opens; lia. }
    assert (Hendpoint_bound :
      Nat.max (active seed) close_endpoint <
        PullArray.size (regions_of seed)).
    { unfold Sized, regions_well_sized in Hseed_sized.
      rewrite Hseed_active, Hseed_sized.
      destruct (le_dec (active state) close_endpoint) as [Hle|Hgt].
      - rewrite Nat.max_r by exact Hle; lia.
      - rewrite Nat.max_l by lia; exact Hstate_bound. }
    assert (Hafter_padding : padding_neutral after_closes).
    { apply (replay_closes_padding_endpoints
        (closes source) 0 source
        (state:=seed) (result:=after_closes));
        assumption. }
    assert (Hopen_invariants :
      (lo result <= net result)%Z /\
      active result = active after_closes + opens source /\
      padding_neutral result).
    { exact (replay_opens_result_invariants
        (opens source) 0 source
        (state:=after_closes) (final:=result)
        Hopens Hafter_lonet Hafter_padding). }
    destruct Hopen_invariants as [_ [Hopen_active _]].
    assert (Hopen_bound :
      active after_closes + opens source <
        PullArray.size (regions_of after_closes)).
    { unfold Sized, regions_well_sized in Hafter_sized.
      rewrite Hafter_sized, <- Hopen_active, Hresult_active.
      exact Hfinish_bound. }
    exists after_closes; repeat split; assumption.
  Qed.

  Lemma replay_summary_open_suffix_layout
      (state source result : t) :
    IsMonoid M ->
    Consistent state ->
    Consistent source ->
    depth_supported_n state source = true ->
    replay_summary state source = Some result ->
    exists after_closes,
      replay_closes (closes source) 0 source
        (Some (append_region state (region (regions_of source) 0))) =
          Some after_closes /\
      active after_closes =
        closes state + (closes source - opens state) +
          (opens state - closes source) /\
      (forall i, i <= active after_closes ->
        region (regions_of result) i =
        region (regions_of after_closes) i) /\
      (forall r, r < opens source ->
        region (regions_of result) (active after_closes + S r) =
        region (regions_of source) (closes source + S r)).
  Proof.
    intros HM Hstate Hsource Hsupported Hsummary.
    destruct (replay_summary_close_phase_invariants
      Hstate Hsource Hsupported Hsummary)
      as [after_closes [Hcloses [Hopens
        [Hafter_sized [Hafter_lo [Hafter_lonet [Hafter_padding Hopen_bound]]]]]]].
    pose proof Hstate as [_ [[Hstate_lo [_ [Hstate_lonet _]]] _]].
    assert (Hafter_active :
      active after_closes =
        closes state + (closes source - opens state) +
          (opens state - closes source)).
    { pose proof (replay_closes_active_exact
        (closes source) 0 source
        (append_region state (region (regions_of source) 0))
        (result:=after_closes) Hstate_lo Hstate_lonet Hcloses) as H.
      exact H. }
    assert (Hlayout :
      (forall i, i <= active after_closes ->
        region (regions_of result) i =
        region (regions_of after_closes) i) /\
      (forall r, r < opens source ->
        region (regions_of result) (active after_closes + S r) =
        region (regions_of source) (closes source + S (0 + r)))).
    { eapply replay_opens_region_layout; eauto. }
    destruct Hlayout as [Hprefix Hsuffix].
    exists after_closes; split; [exact Hcloses|].
    split; [exact Hafter_active|].
    split; [exact Hprefix|].
    intros r Hr; specialize (Hsuffix r Hr).
    replace (0 + r) with r in Hsuffix by lia; exact Hsuffix.
  Qed.

  Lemma replay_summary_left_blocked_close_phase
      (state source result : t) :
    IsMonoid M ->
    Consistent state ->
    Consistent source ->
    depth_supported_n state source = true ->
    replay_summary state source = Some result ->
    opens state <= closes source ->
    exists after_closes,
      replay_closes (closes source) 0 source
        (Some (append_region state (region (regions_of source) 0))) =
          Some after_closes /\
      replay_opens (opens source) 0 source (Some after_closes) =
        Some result /\
      opens after_closes = 0 /\
      closes after_closes =
        closes state + (closes source - opens state) /\
      Sized after_closes /\
      (lo after_closes <= 0)%Z /\
      net after_closes = lo after_closes /\
      padding_neutral after_closes /\
      active after_closes + opens source <
        PullArray.size (regions_of after_closes).
  Proof.
    intros HM Hstate Hsource Hsupported Hsummary Hblocked.
    destruct (replay_summary_open_suffix_layout
      (state:=state) (source:=source) (result:=result)
      HM Hstate Hsource Hsupported Hsummary)
      as [after_closes [Hcloses [Hactive [Hprefix Hsuffix]]]].
    exists after_closes; split; [exact Hcloses|].
    assert (Hopens :
      replay_opens (opens source) 0 source (Some after_closes) =
        Some result).
    { unfold replay_summary in Hsummary.
      rewrite Hcloses in Hsummary; exact Hsummary. }
    split; [exact Hopens|].
    pose proof Hstate as
      [Hstate_sized [Hdepth [Hstate_bound Hstate_padding]]].
    destruct Hdepth as [Hlo [_ [Hlonet _]]].
    pose proof (replay_closes_counts
      (closes source) 0 source
      (append_region state (region (regions_of source) 0))
      (result:=after_closes)
      Hlo Hlonet Hcloses) as Hcounts.
    rewrite append_region_opens, append_region_closes in Hcounts.
    destruct Hcounts as [Hafter_opens Hafter_closes].
    split; [lia|].
    split; [exact Hafter_closes|].
    set (seed := append_region state (region (regions_of source) 0)).
    assert (Hseed_sized : Sized seed).
    { unfold seed; apply append_region_sized; exact Hstate_sized. }
    assert (Hafter_sized : Sized after_closes).
    { pose proof (replay_closes_sized (closes source) 0 source
        (Some seed) Hseed_sized) as H.
      unfold seed in H; rewrite Hcloses in H; exact H. }
    assert (Hseed_padding : padding_neutral seed).
    { unfold seed; apply append_region_padding; exact Hstate_padding. }
    assert (Hseed_active : active seed = active state).
    { unfold seed; apply append_region_active. }
    assert (Hfinish_bound :
      active (finish_replay state source result) < 2 * N + 1).
    { apply depth_consistent_active_bound.
      apply finish_replay_depth_consistent; assumption. }
    assert (Hfinish_active :
      active (finish_replay state source result) =
        active after_closes + opens source).
    { unfold active at 1.
      rewrite Hactive.
      rewrite closes_finish_replay_consistent by assumption.
      rewrite opens_finish_replay_consistent by assumption.
      lia. }
    assert (Hendpoint_bound :
      Nat.max (active seed) (active after_closes) <
        PullArray.size (regions_of seed)).
    { unfold Sized, regions_well_sized in Hseed_sized.
      rewrite Hseed_sized, Hseed_active.
      destruct (le_dec (active state) (active after_closes)) as [Hle|Hgt].
      - rewrite Nat.max_r by exact Hle.
        lia.
      - rewrite Nat.max_l by lia; exact Hstate_bound. }
    assert (Hendpoint_exact :
      Nat.max (active seed)
        (closes seed + (closes source - opens seed) +
          (opens seed - closes source)) <
        PullArray.size (regions_of seed)).
    { unfold seed in Hendpoint_bound |- *; simpl in Hendpoint_bound |- *.
      rewrite Hactive in Hendpoint_bound.
      exact Hendpoint_bound. }
    assert (Hafter_padding : padding_neutral after_closes).
    { eapply (replay_closes_padding_endpoints
        (closes source) 0 source
        (state:=seed) (result:=after_closes)).
      - exact Hseed_sized.
      - unfold seed; simpl; exact Hlo.
      - unfold seed; simpl; exact Hlonet.
      - exact Hseed_padding.
      - exact Hendpoint_exact.
      - unfold seed; exact Hcloses. }
    assert (Hafter_order :
      (lo after_closes <= 0)%Z /\
      (lo after_closes <= net after_closes)%Z).
    { apply (replay_closes_order (closes source) 0 source
        seed (result:=after_closes));
        try assumption; unfold seed; simpl; assumption. }
    destruct Hafter_order as [Hafter_lo Hafter_lonet].
    assert (Hafter_net : net after_closes = lo after_closes).
    { assert (Hafter_opens_zero : opens after_closes = 0) by lia.
      unfold opens in Hafter_opens_zero.
      assert (Hz : (0 <= net after_closes - lo after_closes)%Z) by lia.
      pose proof (Z2Nat.id (net after_closes - lo after_closes) Hz) as H.
      rewrite Hafter_opens_zero in H; simpl in H; lia. }
    assert (Hresult_invariants :
      active result = active (finish_replay state source result)).
    { destruct (replay_summary_result_invariants
        (state:=state) (source:=source) (result:=result)
        Hstate Hsource Hsupported Hsummary) as [_ [_ Hresult_active]].
      exact Hresult_active. }
    assert (Hopen_active : active result = active after_closes + opens source).
    { destruct (replay_opens_result_invariants
        (opens source) 0 source (state:=after_closes) (final:=result)
        Hopens Hafter_lonet Hafter_padding) as [_ [Hopen_active _]].
      exact Hopen_active. }
    repeat split; try assumption.
    unfold Sized, regions_well_sized in Hafter_sized.
    rewrite Hafter_sized, <- Hopen_active, Hresult_invariants.
    exact Hfinish_bound.
  Qed.

  Corollary replay_summary_region_layout
      (state source result : t) :
    IsMonoid M ->
    Consistent state ->
    Consistent source ->
    depth_supported_n state source = true ->
    replay_summary state source = Some result ->
    exists after_closes,
      replay_closes (closes source) 0 source
        (Some (append_region state (region (regions_of source) 0))) =
          Some after_closes /\
      active after_closes =
        closes state + (closes source - opens state) +
          (opens state - closes source) /\
      (forall i,
        i <= closes state + (closes source - opens state) +
          (opens state - closes source) ->
        region (regions_of result) i =
        region (regions_of after_closes) i) /\
      (forall r, r < opens source ->
        region (regions_of result)
          (closes state + (closes source - opens state) +
            (opens state - closes source) + S r) =
        region (regions_of source) (closes source + S r)).
  Proof.
    intros HM Hstate Hsource Hsupported Hsummary.
    destruct (replay_summary_open_suffix_layout
      (state:=state) (source:=source) (result:=result)
      HM Hstate Hsource Hsupported Hsummary)
      as [after_closes [Hcloses [Hactive [Hprefix Hsuffix]]]].
    exists after_closes; repeat split; try assumption.
    - intros i Hi. rewrite <- Hactive in Hi. exact (Hprefix i Hi).
    - intros r Hr. rewrite <- Hactive. exact (Hsuffix r Hr).
  Qed.

  Lemma finish_replay_trailing_open_regions
      (state source result : t) :
    IsMonoid M ->
    Consistent state ->
    Consistent source ->
    depth_supported_n state source = true ->
    replay_summary state source = Some result ->
    forall r, r < opens source ->
      region (regions_of (finish_replay state source result))
        (closes (finish_replay state source result) +
          (opens (finish_replay state source result) - r)) =
      region (regions_of source)
        (closes source + (opens source - r)).
  Proof.
    intros HM Hstate Hsource Hsupported Hsummary r Hr.
    destruct (replay_summary_region_layout
      (state:=state) (source:=source) (result:=result)
      HM Hstate Hsource Hsupported Hsummary)
      as [after_closes [Hcloses [Hactive [Hprefix Hsuffix]]]].
    assert (Hfinish_closes :
      closes (finish_replay state source result) =
        closes state + (closes source - opens state)).
    { apply closes_finish_replay_consistent; assumption. }
    assert (Hfinish_opens :
      opens (finish_replay state source result) =
        opens source + (opens state - closes source)).
    { apply opens_finish_replay_consistent; assumption. }
    set (q := opens source - S r).
    assert (Hq : q < opens source) by (unfold q; lia).
    specialize (Hsuffix q Hq).
    rewrite regions_finish_replay.
    rewrite Hfinish_closes, Hfinish_opens.
    replace
      (closes state + (closes source - opens state) +
        (opens source + (opens state - closes source) - r))
      with
      (closes state + (closes source - opens state) +
        (opens state - closes source) + S q) by (unfold q; lia).
    replace (closes source + (opens source - r))
      with (closes source + S q) by (unfold q; lia).
      exact Hsuffix.
  Qed.

  Lemma replay_opens_result_lo
      (remaining j : nat) (source state result : t) :
    (lo state <= net state)%Z ->
    replay_opens remaining j source (Some state) = Some result ->
    lo result = lo state.
  Proof.
    revert j state.
    induction remaining as [|remaining IH]; intros j state Hlonet Hreplay.
    - simpl in Hreplay; now inversion Hreplay.
    - simpl in Hreplay.
      set (next := append_region (append_open state)
        (region (regions_of source) (closes source + S j))) in Hreplay.
      assert (Hnext_lonet : (lo next <= net next)%Z).
      { unfold next; simpl; apply append_open_lo_net; exact Hlonet. }
      specialize (IH (S j) next Hnext_lonet Hreplay).
      unfold next in IH; simpl in IH.
      rewrite Z.min_l in IH by exact Hlonet.
      exact IH.
  Qed.

  Lemma open_base_after_replay_opens
      (remaining j : nat) (source state result : t) :
    IsMonoid M ->
    Sized state ->
    (lo state <= 0)%Z ->
    net state = lo state ->
    padding_neutral state ->
    active state + remaining < PullArray.size (regions_of state) ->
    replay_opens remaining j source (Some state) = Some result ->
    ReplayEq (open_base result) state.
  Proof.
    intros HM Hsized Hlo Hnet Hpadding Hbound Hreplay.
    assert (Hlonet : (lo state <= net state)%Z) by lia.
    assert (Hresult_sized : Sized result).
    { pose proof (replay_opens_sized remaining j source
        (Some state) Hsized) as H.
      rewrite Hreplay in H; exact H. }
    assert (Hresult_lo : lo result = lo state).
    { eapply replay_opens_result_lo; eauto. }
    assert (Hcloses : closes result = closes state).
    { unfold closes; now rewrite Hresult_lo. }
    assert (Hstate_active : active state = closes state).
    { unfold active, opens; rewrite Hnet, Z.sub_diag; simpl; lia. }
    destruct (replay_opens_region_layout
      remaining j source (state:=state) (result:=result) HM
      Hsized Hlonet Hbound Hreplay) as [Hprefix Hsuffix].
    unfold ReplayEq.
    split; [simpl; exact Hresult_lo|].
    split; [simpl; lia|].
    apply regions_eq_of_active_agreement.
    - apply open_base_sized; exact Hresult_sized.
    - exact Hsized.
    - rewrite open_base_active by (rewrite Hresult_lo; exact Hlo).
      rewrite Hcloses; symmetry; exact Hstate_active.
    - intros i Hi.
      rewrite open_base_active in Hi by (rewrite Hresult_lo; exact Hlo).
      rewrite (open_base_agrees result (i:=i) Hi).
      apply Hprefix; rewrite Hstate_active, <- Hcloses; exact Hi.
    - apply open_base_padding; rewrite Hresult_lo; exact Hlo.
    - exact Hpadding.
  Qed.

  Corollary finish_replay_left_blocked_open_base
      (state source result : t) :
    IsMonoid M ->
    Consistent state ->
    Consistent source ->
    depth_supported_n state source = true ->
    replay_summary state source = Some result ->
    opens state <= closes source ->
    exists after_closes,
      replay_closes (closes source) 0 source
        (Some (append_region state (region (regions_of source) 0))) =
          Some after_closes /\
      ReplayEq (open_base (finish_replay state source result))
        after_closes.
  Proof.
    intros HM Hstate Hsource Hsupported Hsummary Hblocked.
    destruct (replay_summary_left_blocked_close_phase
      (state:=state) (source:=source) (result:=result)
      HM Hstate Hsource Hsupported Hsummary Hblocked)
      as [after_closes [Hcloses Hrest]].
    destruct Hrest as [Hopens Hrest].
    destruct Hrest as [Hafter_opens Hrest].
    destruct Hrest as [Hafter_closes Hrest].
    destruct Hrest as [Hafter_sized Hrest].
    destruct Hrest as [Hafter_lo Hrest].
    destruct Hrest as [Hafter_net Hrest].
    destruct Hrest as [Hafter_padding Hafter_bound].
    exists after_closes; split; [exact Hcloses|].
    pose proof (open_base_after_replay_opens
      (opens source) 0 source
      (state:=after_closes) (result:=result)
      HM Hafter_sized Hafter_lo Hafter_net Hafter_padding
      Hafter_bound Hopens) as Hstrip.
    assert (Hresult_lo : lo result = lo after_closes).
    { eapply replay_opens_result_lo; eauto; lia. }
    assert (Hfinish_lo_nonpos :
      (lo (finish_replay state source result) <= 0)%Z).
    { destruct (finish_replay_depth_consistent
        (a:=state) (b:=source) result Hstate Hsource Hsupported) as [Hlo _].
      exact Hlo. }
    assert (Hfinish_closes :
      closes (finish_replay state source result) = closes after_closes).
    { rewrite closes_finish_replay_consistent by assumption.
      symmetry; exact Hafter_closes. }
    assert (Hfinish_lo :
      lo (finish_replay state source result) = lo result).
    { pose proof (closes_as_depth
        (finish_replay state source result) Hfinish_lo_nonpos) as Hfinish.
      pose proof (closes_as_depth after_closes Hafter_lo) as Hafter.
      rewrite Hfinish_closes in Hfinish.
      lia. }
    assert (Hresult_closes : closes result = closes after_closes).
    { unfold closes; now rewrite Hresult_lo. }
    eapply ReplayEq_trans; [|exact Hstrip].
    unfold ReplayEq.
    split; [simpl; exact Hfinish_lo|].
    split; [simpl; exact Hfinish_lo|].
    change
      (retain_through (closes (finish_replay state source result))
        (regions_of (finish_replay state source result)) =
       retain_through (closes result) (regions_of result)).
    rewrite Hfinish_closes, Hresult_closes.
    rewrite regions_finish_replay; reflexivity.
  Qed.

  Lemma finish_replay_excess_close_regions
      (state source result : t) :
    IsMonoid M ->
    Consistent state ->
    Consistent source ->
    depth_supported_n state source = true ->
    replay_summary state source = Some result ->
    opens state < closes source ->
    forall r, r < closes source - opens state ->
      region (regions_of (finish_replay state source result))
        (closes state + S r) =
      region (regions_of source) (S (opens state + r)).
  Proof.
    intros HM Hstate Hsource Hsupported Hsummary Hexcess r Hr.
    destruct (replay_summary_open_suffix_layout
      (state:=state) (source:=source) (result:=result)
      HM Hstate Hsource Hsupported Hsummary)
      as [after_closes [Hcloses [Hafter_active [Hprefix Hsuffix]]]].
    pose proof (replay_closes_as_boundary_normal_form
      (b:=state) source (region (regions_of source) 0) HM Hstate)
      as Hnormal.
    rewrite Hcloses in Hnormal.
    destruct (close_boundary_normal_form state source
      (region (regions_of source) 0)) as [normalized|] eqn:Hnormalized;
      simpl in Hnormal; try contradiction.
    destruct Hnormal as [Hnormal_lo [Hnormal_net Hnormal_regions]].
    destruct (close_boundary_normal_form_close_success
      state source (region (regions_of source) 0)
      (result:=normalized) Hexcess Hnormalized)
      as [acc' [Hcancel Hclose_replay]].
    pose proof (excess_close_normal_form_region_layout
      (b:=state) (c:=source) (region (regions_of source) 0)
      (acc':=acc') (result:=normalized)
      HM Hstate Hsource Hsupported Hexcess Hcancel Hclose_replay)
      as [Hnormal_prefix Hnormal_suffix].
    pose proof Hstate as [_ [Hstate_depth _]].
    destruct Hstate_depth as [Hstate_lo _].
    assert (Hbase_active :
      active (append_region (open_base state) acc') = closes state).
    { rewrite append_region_active.
      apply open_base_active; exact Hstate_lo. }
    assert (Hindex_bound : closes state + S r <= active after_closes).
    { rewrite Hafter_active.
      replace (opens state - closes source) with 0 by lia.
      lia. }
    rewrite regions_finish_replay.
    rewrite (Hprefix (closes state + S r) Hindex_bound).
    rewrite Hnormal_regions.
    specialize (Hnormal_suffix r Hr).
    rewrite Hbase_active in Hnormal_suffix.
    exact Hnormal_suffix.
  Qed.

  Lemma finish_replay_close_prefix_pivot
      (state source result : t) :
    IsMonoid M ->
    Consistent state ->
    Consistent source ->
    depth_supported_n state source = true ->
    replay_summary state source = Some result ->
    opens state < closes source ->
    exists acc',
      cancel_pairs (opens state) (opens state) 0
        state source (region (regions_of source) 0) = Some acc' /\
      (forall i, i < closes state ->
        region (regions_of (finish_replay state source result)) i =
        region (regions_of state) i) /\
      region (regions_of (finish_replay state source result))
        (closes state) =
      m_op M (region (regions_of state) (closes state)) acc'.
  Proof.
    intros HM Hstate Hsource Hsupported Hsummary Hexcess.
    destruct (replay_summary_open_suffix_layout
      (state:=state) (source:=source) (result:=result)
      HM Hstate Hsource Hsupported Hsummary)
      as [after_closes [Hcloses [Hafter_active [Hfinal_prefix Hfinal_suffix]]]].
    pose proof (replay_closes_as_boundary_normal_form
      (b:=state) source (region (regions_of source) 0) HM Hstate)
      as Hnormal.
    rewrite Hcloses in Hnormal.
    destruct (close_boundary_normal_form state source
      (region (regions_of source) 0)) as [normalized|] eqn:Hnormalized;
      simpl in Hnormal; try contradiction.
    destruct Hnormal as [Hnormal_lo [Hnormal_net Hnormal_regions]].
    destruct (close_boundary_normal_form_close_success
      state source (region (regions_of source) 0)
      (result:=normalized) Hexcess Hnormalized)
      as [acc' [Hcancel Hclose_replay]].
    pose proof (excess_close_normal_form_region_layout
      (b:=state) (c:=source) (region (regions_of source) 0)
      (acc':=acc') (result:=normalized)
      HM Hstate Hsource Hsupported Hexcess Hcancel Hclose_replay)
      as [Hnormal_prefix Hnormal_suffix].
    pose proof Hstate as
      [Hstate_sized [Hstate_depth [Hstate_bound Hstate_padding]]].
    destruct Hstate_depth as [Hstate_lo _].
    assert (Hbase_active :
      active (append_region (open_base state) acc') = closes state).
    { rewrite append_region_active.
      apply open_base_active; exact Hstate_lo. }
    assert (Hbase_sized : Sized (open_base state)).
    { apply open_base_sized; exact Hstate_sized. }
    assert (Hbase_bound :
      active (open_base state) < PullArray.size (regions_of (open_base state))).
    { unfold Sized, regions_well_sized in Hstate_sized, Hbase_sized.
      rewrite open_base_active by exact Hstate_lo.
      unfold active in Hstate_bound; lia. }
    exists acc'; split; [exact Hcancel|].
    split.
    - intros i Hi.
      assert (Hidx_final : i <= active after_closes).
      { rewrite Hafter_active; lia. }
      rewrite regions_finish_replay.
      rewrite (Hfinal_prefix _ Hidx_final), Hnormal_regions.
      rewrite (Hnormal_prefix i ltac:(rewrite Hbase_active; lia)).
      rewrite append_region_before_active.
      + apply open_base_agrees; lia.
      + rewrite open_base_active by exact Hstate_lo; lia.
    - assert (Hidx_final : closes state <= active after_closes).
      { rewrite Hafter_active; lia. }
      rewrite regions_finish_replay.
      rewrite (Hfinal_prefix _ Hidx_final), Hnormal_regions.
      rewrite (Hnormal_prefix (closes state)
        ltac:(rewrite Hbase_active; lia)).
      pose proof (append_region_at_active
        (open_base state) acc' Hbase_bound) as Hpivot.
      rewrite open_base_active in Hpivot by exact Hstate_lo.
      rewrite Hpivot.
      apply f_equal2; [apply open_base_agrees; lia|reflexivity].
  Qed.

  Corollary finish_replay_close_prefix_region_zero
      (state source result : t) :
    IsMonoid M ->
    Consistent state ->
    Consistent source ->
    depth_supported_n state source = true ->
    replay_summary state source = Some result ->
    opens state < closes source ->
    0 < closes state ->
    region (regions_of (finish_replay state source result)) 0 =
      region (regions_of state) 0.
  Proof.
    intros HM Hstate Hsource Hsupported Hreplay Hexcess Hcloses.
    destruct (finish_replay_close_prefix_pivot
      (state:=state) (source:=source) (result:=result)
      HM Hstate Hsource Hsupported Hreplay Hexcess)
      as [acc' [Hcancel [Hbefore Hpivot]]].
    apply Hbefore; lia.
  Qed.

  Lemma left_blocked_close_right_source_layout
      (a b c replayed_bc : t) :
    IsMonoid M ->
    Consistent b ->
    Consistent c ->
    depth_supported_n b c = true ->
    replay_summary b c = Some replayed_bc ->
    opens a <= closes b ->
    opens b < closes c ->
    exists acc_bc,
      cancel_pairs (opens b) (opens b) 0 b c
        (region (regions_of c) 0) = Some acc_bc /\
      (forall r, S (opens a + r) < closes b ->
        region (regions_of (finish_replay b c replayed_bc))
          (S (opens a + r)) =
        region (regions_of b) (S (opens a + r))) /\
      region (regions_of (finish_replay b c replayed_bc)) (closes b) =
        m_op M (region (regions_of b) (closes b)) acc_bc /\
      (forall r, r < closes c - opens b ->
        region (regions_of (finish_replay b c replayed_bc))
          (closes b + S r) =
        region (regions_of c) (S (opens b + r))).
  Proof.
    intros HM Hb Hc Hbc Hreplay Hab Hclose.
    destruct (finish_replay_close_prefix_pivot
      (state:=b) (source:=c) (result:=replayed_bc)
      HM Hb Hc Hbc Hreplay Hclose)
      as [acc_bc [Hcancel [Hprefix Hpivot]]].
    exists acc_bc; repeat split; try assumption.
    - intros r Hr; apply Hprefix; exact Hr.
    - intros r Hr.
      apply finish_replay_excess_close_regions; assumption.
  Qed.

  Lemma left_blocked_close_outer_cancel_strict
      (a b c replayed_bc : t) :
    IsMonoid M ->
    Consistent b ->
    Consistent c ->
    depth_supported_n b c = true ->
    replay_summary b c = Some replayed_bc ->
    opens a < closes b ->
    opens b < closes c ->
    cancel_pairs (opens a) (opens a) 0
      a (finish_replay b c replayed_bc)
      (region (regions_of (finish_replay b c replayed_bc)) 0) =
    cancel_pairs (opens a) (opens a) 0
      a b (region (regions_of b) 0).
  Proof.
    intros HM Hb Hc Hbc Hreplay Hab Hclose.
    assert (Hzero :
      region (regions_of (finish_replay b c replayed_bc)) 0 =
      region (regions_of b) 0).
    { apply finish_replay_close_prefix_region_zero; try assumption; lia. }
    rewrite Hzero.
    apply cancel_pairs_extensional; try lia.
    - intros r Hr; reflexivity.
    - intros r Hr.
      destruct (finish_replay_close_prefix_pivot
        (state:=b) (source:=c) (result:=replayed_bc)
        HM Hb Hc Hbc Hreplay Hclose)
        as [acc_bc [Hcancel [Hprefix Hpivot]]].
      apply Hprefix; lia.
  Qed.

  Lemma left_blocked_close_outer_cancel_at_pivot
      (a b c replayed_bc : t) :
    IsMonoid M ->
    Consistent b ->
    Consistent c ->
    depth_supported_n b c = true ->
    replay_summary b c = Some replayed_bc ->
    opens a = closes b ->
    opens b < closes c ->
    exists acc_bc,
      cancel_pairs (opens b) (opens b) 0 b c
        (region (regions_of c) 0) = Some acc_bc /\
      cancel_pairs (opens a) (opens a) 0
        a (finish_replay b c replayed_bc)
        (region (regions_of (finish_replay b c replayed_bc)) 0) =
      option_bind
        (cancel_pairs (opens a) (opens a) 0
          a b (region (regions_of b) 0))
        (fun result => Some (m_op M result acc_bc)).
  Proof.
    intros HM Hb Hc Hbc Hreplay Hab Hclose.
    destruct (finish_replay_close_prefix_pivot
      (state:=b) (source:=c) (result:=replayed_bc)
      HM Hb Hc Hbc Hreplay Hclose)
      as [acc_bc [Hcancel [Hprefix Hpivot]]].
    exists acc_bc; split; [exact Hcancel|].
    destruct (opens a) as [|remaining] eqn:Ha_opens.
    - simpl.
      apply f_equal.
      rewrite <- (regions_finish_replay b c replayed_bc).
      rewrite <- Hab in Hpivot.
      exact Hpivot.
    - assert (Hb_closes : 0 < closes b) by lia.
      rewrite (finish_replay_close_prefix_region_zero
        (state:=b) (source:=c) (result:=replayed_bc)
        HM Hb Hc Hbc Hreplay Hclose Hb_closes).
      apply cancel_pairs_close_pivot_assoc; try lia.
      + exact HM.
      + intros r Hr; apply Hprefix; lia.
      + replace (S (0 + remaining)) with (closes b) by lia.
        exact Hpivot.
  Qed.

  Lemma left_blocked_close_left_outer_cancel
      (a b c replayed_ab : t) :
    IsMonoid M ->
    Consistent a ->
    Consistent b ->
    depth_supported_n a b = true ->
    replay_summary a b = Some replayed_ab ->
    opens a <= closes b ->
    cancel_pairs (opens (finish_replay a b replayed_ab))
      (opens (finish_replay a b replayed_ab)) 0
      (finish_replay a b replayed_ab) c
      (region (regions_of c) 0) =
    cancel_pairs (opens b) (opens b) 0 b c
      (region (regions_of c) 0).
  Proof.
    intros HM Ha Hb Hab Hreplay Hblocked.
    assert (Hopens : opens (finish_replay a b replayed_ab) = opens b).
    { apply opens_finish_replay_left_blocked; assumption. }
    rewrite Hopens.
    apply cancel_pairs_extensional; try lia.
    - intros r Hr.
      pose proof (finish_replay_trailing_open_regions
        (state:=a) (source:=b) (result:=replayed_ab)
        HM Ha Hb Hab Hreplay (r:=r) Hr) as Hregion.
      rewrite Hopens in Hregion.
      exact Hregion.
    - intros r Hr; reflexivity.
  Qed.

  Corollary left_blocked_close_left_outer_cancel_success
      (a b c replayed_ab replayed_bc : t) :
    IsMonoid M ->
    Consistent a ->
    Consistent b ->
    Consistent c ->
    depth_supported_n a b = true ->
    depth_supported_n b c = true ->
    replay_summary a b = Some replayed_ab ->
    replay_summary b c = Some replayed_bc ->
    opens a <= closes b ->
    opens b < closes c ->
    exists acc_bc,
      cancel_pairs (opens b) (opens b) 0 b c
        (region (regions_of c) 0) = Some acc_bc /\
      cancel_pairs (opens (finish_replay a b replayed_ab))
        (opens (finish_replay a b replayed_ab)) 0
        (finish_replay a b replayed_ab) c
        (region (regions_of c) 0) = Some acc_bc.
  Proof.
    intros HM Ha Hb Hc Hab Hbc Hreplay_ab Hreplay_bc Hblocked Hclose.
    destruct (finish_replay_close_prefix_pivot
      (state:=b) (source:=c) (result:=replayed_bc)
      HM Hb Hc Hbc Hreplay_bc Hclose)
      as [acc_bc [Hcancel_bc [Hprefix Hpivot]]].
    exists acc_bc; split; [exact Hcancel_bc|].
    rewrite left_blocked_close_left_outer_cancel
      with (a:=a) (b:=b) (replayed_ab:=replayed_ab);
      assumption.
  Qed.

  Lemma finish_replay_surviving_open_pivot
      (state source result : t) :
    IsMonoid M ->
    Consistent state ->
    Consistent source ->
    depth_supported_n state source = true ->
    replay_summary state source = Some result ->
    closes source <= opens state ->
    exists acc',
      cancel_pairs (closes source) (opens state) 0
        state source (region (regions_of source) 0) = Some acc' /\
      (forall r, S r < opens state - closes source ->
        region (regions_of (finish_replay state source result))
          (closes state + S r) =
        region (regions_of state) (closes state + S r)) /\
      (0 < opens state - closes source ->
        region (regions_of (finish_replay state source result))
          (closes state + (opens state - closes source)) =
        m_op M
          (region (regions_of state)
            (closes state + (opens state - closes source))) acc').
  Proof.
    intros HM Hstate Hsource Hsupported Hsummary Hsurvives.
    destruct (replay_summary_open_suffix_layout
      (state:=state) (source:=source) (result:=result)
      HM Hstate Hsource Hsupported Hsummary)
      as [after_closes [Hcloses [Hafter_active [Hfinal_prefix Hfinal_suffix]]]].
    pose proof (replay_closes_as_boundary_normal_form
      (b:=state) source (region (regions_of source) 0) HM Hstate)
      as Hnormal.
    rewrite Hcloses in Hnormal.
    destruct (close_boundary_normal_form state source
      (region (regions_of source) 0)) as [normalized|] eqn:Hnormalized;
      simpl in Hnormal; try contradiction.
    destruct Hnormal as [Hnormal_lo [Hnormal_net Hnormal_regions]].
    destruct (close_boundary_normal_form_open_success
      state source (region (regions_of source) 0)
      (result:=normalized) Hsurvives Hnormalized)
      as [acc' [after_opens [Hcancel [Hopens Hnormalized_eq]]]].
    pose proof (surviving_open_normal_form_region_layout
      (b:=state) source (after_opens:=after_opens)
      HM Hstate Hsurvives Hopens) as [Hopen_prefix Hopen_suffix].
    pose proof (surviving_open_normal_form_append_layout
      (b:=state) source (acc':=acc')
      (after_opens:=after_opens) (result:=normalized)
      HM Hstate Hsurvives Hopens Hnormalized_eq)
      as [Happend_prefix Happend_pivot].
    pose proof Hstate as [_ [Hstate_depth _]].
    destruct Hstate_depth as [Hstate_lo _].
    assert (Hopen_active :
      active after_opens = closes state + (opens state - closes source)).
    { pose proof (replay_opens_result_invariants
        (opens state - closes source) 0 state
        (state:=open_base state) (final:=after_opens)
        Hopens (open_base_lo_net state) (open_base_padding state Hstate_lo))
        as [_ [Hactive _]].
      rewrite Hactive, open_base_active by exact Hstate_lo; lia. }
    exists acc'; split; [exact Hcancel|].
    split.
    - intros r Hr.
      assert (Hidx_lt : closes state + S r < active after_opens)
        by (rewrite Hopen_active; lia).
      assert (Hidx_final : closes state + S r <= active after_closes).
      { rewrite Hafter_active.
        replace (closes source - opens state) with 0 by lia; lia. }
      rewrite regions_finish_replay.
      rewrite (Hfinal_prefix _ Hidx_final), Hnormal_regions.
      rewrite (Happend_prefix _ Hidx_lt).
      specialize (Hopen_suffix r ltac:(lia)).
      rewrite open_base_active in Hopen_suffix by exact Hstate_lo.
      exact Hopen_suffix.
    - intro Hpositive.
      assert (Hidx_final :
        closes state + (opens state - closes source) <= active after_closes).
      { rewrite Hafter_active.
        replace (closes source - opens state) with 0 by lia; lia. }
      rewrite regions_finish_replay.
      rewrite (Hfinal_prefix _ Hidx_final), Hnormal_regions.
      pose proof Happend_pivot as Hpivot.
      rewrite Hopen_active in Hpivot.
      set (r := opens state - closes source - 1).
      assert (Hr : r < opens state - closes source) by (unfold r; lia).
      specialize (Hopen_suffix r Hr).
      rewrite open_base_active in Hopen_suffix by exact Hstate_lo.
      replace (closes state + S r)
        with (closes state + (opens state - closes source)) in Hopen_suffix
        by (unfold r; lia).
      rewrite Hopen_suffix in Hpivot.
      exact Hpivot.
  Qed.

  Lemma finish_replay_surviving_open_prefix
      (state source result : t) :
    IsMonoid M ->
    Consistent state ->
    Consistent source ->
    depth_supported_n state source = true ->
    replay_summary state source = Some result ->
    closes source < opens state ->
    forall i, i <= closes state ->
      region (regions_of (finish_replay state source result)) i =
      region (regions_of state) i.
  Proof.
    intros HM Hstate Hsource Hsupported Hsummary Hsurvives i Hi.
    destruct (replay_summary_open_suffix_layout
      (state:=state) (source:=source) (result:=result)
      HM Hstate Hsource Hsupported Hsummary)
      as [after_closes [Hcloses [Hafter_active [Hfinal_prefix Hsuffix]]]].
    pose proof (replay_closes_as_boundary_normal_form
      (b:=state) source (region (regions_of source) 0) HM Hstate)
      as Hnormal.
    rewrite Hcloses in Hnormal.
    destruct (close_boundary_normal_form state source
      (region (regions_of source) 0)) as [normalized|] eqn:Hnormalized;
      simpl in Hnormal; try contradiction.
    destruct Hnormal as [_ [_ Hnormal_regions]].
    destruct (close_boundary_normal_form_open_success
      state source (region (regions_of source) 0)
      (result:=normalized) ltac:(lia) Hnormalized)
      as [acc' [after_opens [Hcancel [Hopens Hnormalized_eq]]]].
    pose proof (surviving_open_normal_form_region_layout
      (b:=state) source (after_opens:=after_opens)
      HM Hstate ltac:(lia) Hopens) as [Hopen_prefix Hopen_suffix].
    pose proof (surviving_open_normal_form_append_layout
      (b:=state) source (acc':=acc')
      (after_opens:=after_opens) (result:=normalized)
      HM Hstate ltac:(lia) Hopens Hnormalized_eq)
      as [Happend_prefix Happend_pivot].
    pose proof Hstate as
      [Hstate_sized [Hstate_depth [Hstate_bound Hstate_padding]]].
    destruct Hstate_depth as [Hstate_lo _].
    assert (Hopen_active :
      active after_opens = closes state + (opens state - closes source)).
    { pose proof (replay_opens_result_invariants
        (opens state - closes source) 0 state
        (state:=open_base state) (final:=after_opens)
        Hopens (open_base_lo_net state) (open_base_padding state Hstate_lo))
        as [_ [Hactive _]].
      rewrite Hactive, open_base_active by exact Hstate_lo; lia. }
    assert (Hidx_after : i <= active after_closes).
    { rewrite Hafter_active.
      replace (closes source - opens state) with 0 by lia.
      lia. }
    assert (Hidx_open : i < active after_opens).
    { rewrite Hopen_active; lia. }
    rewrite regions_finish_replay.
    rewrite (Hfinal_prefix i Hidx_after), Hnormal_regions.
    rewrite (Happend_prefix i Hidx_open).
    rewrite (Hopen_prefix i).
    - apply open_base_agrees; exact Hi.
    - rewrite open_base_active by exact Hstate_lo; exact Hi.
  Qed.

  Lemma left_blocked_cancel_success
      (a b replayed_ab : t) :
    IsMonoid M ->
    Consistent a ->
    Consistent b ->
    depth_supported_n a b = true ->
    replay_summary a b = Some replayed_ab ->
    opens a <= closes b ->
    exists acc_ab,
      cancel_pairs (opens a) (opens a) 0 a b
        (region (regions_of b) 0) = Some acc_ab.
  Proof.
    intros HM Ha Hb Hab Hreplay Hblocked.
    destruct (lt_dec (opens a) (closes b)) as [Hstrict|Hequal].
    - destruct (finish_replay_close_prefix_pivot
        (state:=a) (source:=b) (result:=replayed_ab)
        HM Ha Hb Hab Hreplay Hstrict)
        as [acc_ab [Hcancel [Hprefix Hpivot]]].
      exists acc_ab; exact Hcancel.
    - assert (Heq : closes b = opens a) by lia.
      destruct (finish_replay_surviving_open_pivot
        (state:=a) (source:=b) (result:=replayed_ab)
        HM Ha Hb Hab Hreplay ltac:(lia))
        as [acc_ab [Hcancel [Hprefix Hpivot]]].
      exists acc_ab.
      rewrite Heq in Hcancel.
      exact Hcancel.
  Qed.

  Lemma right_blocked_finish_open_layout
      (b c replayed_bc : t) (acc_bc : m_summary M) :
    IsMonoid M ->
    Consistent b ->
    Consistent c ->
    depth_supported_n b c = true ->
    replay_summary b c = Some replayed_bc ->
    closes c <= opens b ->
    cancel_pairs (closes c) (opens b) 0 b c
      (region (regions_of c) 0) = Some acc_bc ->
    opens (finish_replay b c replayed_bc) =
      opens c + (opens b - closes c) /\
    (forall r, S r < opens b - closes c ->
      region (regions_of (finish_replay b c replayed_bc))
        (closes b + S r) =
      region (regions_of b) (closes b + S r)) /\
    (0 < opens b - closes c ->
      region (regions_of (finish_replay b c replayed_bc))
        (closes b + (opens b - closes c)) =
      m_op M
        (region (regions_of b) (closes b + (opens b - closes c)))
        acc_bc) /\
    (forall r, r < opens c ->
      region (regions_of (finish_replay b c replayed_bc))
        (closes (finish_replay b c replayed_bc) +
          (opens (finish_replay b c replayed_bc) - r)) =
      region (regions_of c) (closes c + (opens c - r))).
  Proof.
    intros HM Hb Hc Hbc Hreplay Hblocked Hcancel.
    assert (Hopens : opens (finish_replay b c replayed_bc) =
      opens c + (opens b - closes c)).
    { rewrite opens_finish_replay_consistent by assumption; reflexivity. }
    destruct (finish_replay_surviving_open_pivot
      (state:=b) (source:=c) (result:=replayed_bc)
      HM Hb Hc Hbc Hreplay Hblocked)
      as [acc_bc' [Hcancel' [Hprefix Hpivot]]].
    rewrite Hcancel in Hcancel'; inversion Hcancel'; subst acc_bc'.
    repeat split; try assumption.
    intros r Hr.
    apply finish_replay_trailing_open_regions; assumption.
  Qed.

  Corollary left_blocked_close_right_outer_cancel_strict_success
      (a b c replayed_ab replayed_bc : t) :
    IsMonoid M ->
    Consistent a ->
    Consistent b ->
    Consistent c ->
    depth_supported_n a b = true ->
    depth_supported_n b c = true ->
    replay_summary a b = Some replayed_ab ->
    replay_summary b c = Some replayed_bc ->
    opens a < closes b ->
    opens b < closes c ->
    exists acc_ab,
      cancel_pairs (opens a) (opens a) 0 a b
        (region (regions_of b) 0) = Some acc_ab /\
      cancel_pairs (opens a) (opens a) 0
        a (finish_replay b c replayed_bc)
        (region (regions_of (finish_replay b c replayed_bc)) 0) =
        Some acc_ab.
  Proof.
    intros HM Ha Hb Hc Hab Hbc Hreplay_ab Hreplay_bc Hstrict Hclose.
    destruct (left_blocked_cancel_success
      (a:=a) (b:=b) (replayed_ab:=replayed_ab)
      HM Ha Hb Hab Hreplay_ab ltac:(lia)) as [acc_ab Hcancel].
    exists acc_ab; split; [exact Hcancel|].
    rewrite left_blocked_close_outer_cancel_strict
      with (b:=b) (c:=c) (replayed_bc:=replayed_bc);
      assumption.
  Qed.

  Corollary left_blocked_close_right_outer_cancel_pivot_success
      (a b c replayed_ab replayed_bc : t) :
    IsMonoid M ->
    Consistent a ->
    Consistent b ->
    Consistent c ->
    depth_supported_n a b = true ->
    depth_supported_n b c = true ->
    replay_summary a b = Some replayed_ab ->
    replay_summary b c = Some replayed_bc ->
    opens a = closes b ->
    opens b < closes c ->
    exists acc_ab acc_bc,
      cancel_pairs (opens a) (opens a) 0 a b
        (region (regions_of b) 0) = Some acc_ab /\
      cancel_pairs (opens b) (opens b) 0 b c
        (region (regions_of c) 0) = Some acc_bc /\
      cancel_pairs (opens a) (opens a) 0
        a (finish_replay b c replayed_bc)
        (region (regions_of (finish_replay b c replayed_bc)) 0) =
        Some (m_op M acc_ab acc_bc).
  Proof.
    intros HM Ha Hb Hc Hab Hbc Hreplay_ab Hreplay_bc Heq Hclose.
    destruct (left_blocked_cancel_success
      (a:=a) (b:=b) (replayed_ab:=replayed_ab)
      HM Ha Hb Hab Hreplay_ab ltac:(lia)) as [acc_ab Hcancel_ab].
    destruct (left_blocked_close_outer_cancel_at_pivot
      a (b:=b) (c:=c) (replayed_bc:=replayed_bc)
      HM Hb Hc Hbc Hreplay_bc Heq Hclose)
      as [acc_bc [Hcancel_bc Houter]].
    exists acc_ab, acc_bc; repeat split; try assumption.
    rewrite Hcancel_ab in Houter; exact Houter.
  Qed.

  Lemma left_blocked_residual_closes_reconstruct_open_base
      (a b replayed_ab : t) (acc_ab : m_summary M) :
    IsMonoid M ->
    Consistent a ->
    Consistent b ->
    depth_supported_n a b = true ->
    replay_summary a b = Some replayed_ab ->
    opens a <= closes b ->
    cancel_pairs (opens a) (opens a) 0 a b
      (region (regions_of b) 0) = Some acc_ab ->
    ReplayEqOpt
      (replay_closes (closes b - opens a) (opens a) b
        (Some (append_region (open_base a) acc_ab)))
      (Some (open_base (finish_replay a b replayed_ab))).
  Proof.
    intros HM Ha Hb Hab Hreplay Hblocked Hcancel.
    destruct (finish_replay_left_blocked_open_base
      (state:=a) (source:=b) (result:=replayed_ab)
      HM Ha Hb Hab Hreplay Hblocked)
      as [after_closes [Hafter Hbase]].
    pose proof (replay_cancel_consistent_all_then_closes
      (b:=a) b (region (regions_of b) 0)
      Hblocked HM Ha) as Hnormal.
    rewrite Hafter, Hcancel in Hnormal; simpl in Hnormal.
    eapply ReplayEqOpt_trans with (y:=Some after_closes).
    - apply ReplayEqOpt_sym; exact Hnormal.
    - simpl; apply ReplayEq_sym; exact Hbase.
  Qed.

  Lemma replay_closes_after_replay_eq_state
      (remaining close_index : nat) (source base : t)
      (tail : m_summary M) (state : option t) :
    ReplayEqOpt state (Some base) ->
    ReplayEqOpt
      (option_bind state
        (fun s => replay_closes remaining close_index source
          (Some (append_region s tail))))
      (replay_closes remaining close_index source
        (Some (append_region base tail))).
  Proof.
    intro Hstate.
    change (ReplayEqOpt
      (option_bind state
        (fun s => replay_closes remaining close_index source
          (Some (append_region s tail))))
      (option_bind (Some base)
        (fun s => replay_closes remaining close_index source
          (Some (append_region s tail))))).
    eapply ReplayEqOpt_bind; [exact Hstate|].
    intros x y Hxy; simpl.
    apply replay_closes_replay_eq.
    - apply ReplayEq_refl.
    - simpl; apply append_region_replay_eq; exact Hxy.
  Qed.

  Lemma replay_closes_close_pivot_assoc
      (p j : nat) (source_x source_y : t) (state : option t)
      (pivot : m_summary M) :
    IsMonoid M ->
    (forall r, r < p ->
      region (regions_of source_x) (S (j + r)) =
      region (regions_of source_y) (S (j + r))) ->
    region (regions_of source_x) (S (j + p)) =
      m_op M (region (regions_of source_y) (S (j + p))) pivot ->
    (forall before_y after_y,
      replay_closes p j source_y state = Some before_y ->
      append_close before_y = Some after_y ->
      active after_y < PullArray.size (regions_of after_y)) ->
    ReplayEqOpt
      (replay_closes (S p) j source_x state)
      (option_bind (replay_closes (S p) j source_y state)
        (fun after_y => Some (append_region after_y pivot))).
  Proof.
    intros HM Hprefix Hpivot Hbound.
    assert (Hbefore : ReplayEqOpt
      (replay_closes p j source_x state)
      (replay_closes p j source_y state)).
    { apply replay_closes_extensional.
      - apply ReplayEqOpt_refl.
      - exact Hprefix. }
    rewrite !replay_closes_last.
    destruct (replay_closes p j source_x state) as [before_x|] eqn:Hx,
      (replay_closes p j source_y state) as [before_y|] eqn:Hy;
      simpl in Hbefore |- *; try contradiction; [|exact I].
    rewrite Hpivot.
    pose proof (append_close_replay_eq Hbefore) as Hclose.
    destruct (append_close before_x) as [after_x|] eqn:Hafter_x,
      (append_close before_y) as [after_y|] eqn:Hafter_y;
      simpl in Hclose |- *; try contradiction; [|exact I].
    rewrite append_region_assoc.
    - apply append_region_replay_eq; exact Hclose.
    - exact HM.
    - eapply Hbound; eauto.
  Qed.

  Lemma replay_opens_open_pivot_assoc
      (p j : nat) (source_x source_y : t) (state : option t)
      (pivot : m_summary M) :
    IsMonoid M ->
    (forall r, r < p ->
      region (regions_of source_x) (closes source_x + S (j + r)) =
      region (regions_of source_y) (closes source_y + S (j + r))) ->
    region (regions_of source_x) (closes source_x + S (j + p)) =
      m_op M
        (region (regions_of source_y) (closes source_y + S (j + p)))
        pivot ->
    (forall before_y,
      replay_opens p j source_y state = Some before_y ->
      active (append_open before_y) <
        PullArray.size (regions_of (append_open before_y))) ->
    ReplayEqOpt
      (replay_opens (S p) j source_x state)
      (option_bind (replay_opens (S p) j source_y state)
        (fun after_y => Some (append_region after_y pivot))).
  Proof.
    intros HM Hprefix Hpivot Hbound.
    assert (Hbefore : ReplayEqOpt
      (replay_opens p j source_x state)
      (replay_opens p j source_y state)).
    { apply replay_opens_extensional.
      - apply ReplayEqOpt_refl.
      - exact Hprefix. }
    rewrite !replay_opens_last.
    destruct (replay_opens p j source_x state) as [before_x|] eqn:Hx,
      (replay_opens p j source_y state) as [before_y|] eqn:Hy;
      simpl in Hbefore |- *; try contradiction; [|exact I].
    rewrite Hpivot.
    rewrite append_region_assoc.
    - apply append_region_replay_eq.
      apply append_open_replay_eq; exact Hbefore.
    - exact HM.
    - eapply Hbound; eauto.
  Qed.

  Lemma right_blocked_replay_surviving_b_opens
      (b c replayed_bc : t) (acc_bc : m_summary M)
      (state : option t) :
    IsMonoid M ->
    Consistent b ->
    Consistent c ->
    depth_supported_n b c = true ->
    replay_summary b c = Some replayed_bc ->
    closes c < opens b ->
    cancel_pairs (closes c) (opens b) 0 b c
      (region (regions_of c) 0) = Some acc_bc ->
    (forall before_b,
      replay_opens (opens b - closes c - 1) 0 b state = Some before_b ->
      active (append_open before_b) <
        PullArray.size (regions_of (append_open before_b))) ->
    ReplayEqOpt
      (replay_opens (opens b - closes c) 0
        (finish_replay b c replayed_bc) state)
      (option_bind
        (replay_opens (opens b - closes c) 0 b state)
        (fun after_b => Some (append_region after_b acc_bc))).
  Proof.
    intros HM Hb Hc Hbc Hreplay Hstrict Hcancel Hroom.
    destruct (right_blocked_finish_open_layout
      (b:=b) (c:=c) (replayed_bc:=replayed_bc) (acc_bc:=acc_bc)
      HM Hb Hc Hbc Hreplay ltac:(lia) Hcancel)
      as [Hopens [Hprefix [Hpivot Htrailing]]].
    set (p := opens b - closes c - 1).
    assert (Hcount : opens b - closes c = S p) by (unfold p; lia).
    rewrite Hcount.
    apply replay_opens_open_pivot_assoc; try assumption.
    - intros r Hr.
      rewrite closes_finish_replay_right_blocked by (try assumption; lia).
      apply Hprefix; unfold p in Hr; lia.
    - rewrite closes_finish_replay_right_blocked by (try assumption; lia).
      replace (S (0 + p)) with (opens b - closes c) by (unfold p; lia).
      apply Hpivot; lia.
  Qed.

  Lemma replay_opens_prefix_room (p j : nat) (source seed before : t) :
    Sized seed ->
    (lo seed <= net seed)%Z ->
    padding_neutral seed ->
    active seed + S p < PullArray.size (regions_of seed) ->
    replay_opens p j source (Some seed) = Some before ->
    active (append_open before) <
      PullArray.size (regions_of (append_open before)).
  Proof.
    intros Hsize Horder Hpad Hroom Hreplay.
    destruct (replay_opens_result_invariants p j source
      Hreplay Horder Hpad) as [Hord [Hactive Hpadding]].
    pose proof (replay_opens_sized p j source (Some seed) Hsize) as Hsz.
    rewrite Hreplay in Hsz.
    pose proof (append_open_sized Hsz) as Hopen.
    unfold Sized, regions_well_sized in Hsize, Hopen.
    rewrite append_open_active by exact Hord.
    rewrite Hopen, Hactive, Hsize in *; lia.
  Qed.

  Lemma right_blocked_trailing_open_replay
      (b c bc : t) (x y : option t) :
    IsMonoid M -> Consistent b -> Consistent c ->
    depth_supported_n b c = true -> replay_summary b c = Some bc ->
    closes c <= opens b -> ReplayEqOpt x y ->
    ReplayEqOpt
      (replay_opens (opens c) (opens b - closes c)
        (finish_replay b c bc) x)
      (replay_opens (opens c) 0 c y).
  Proof.
    intros HM Hb Hc Hdepth Hreplay Hblocked Hxy.
    apply replay_opens_extensional; [exact Hxy|].
    intros r Hr.
    pose proof (finish_replay_trailing_open_regions
      (state:=b) (source:=c) (result:=bc) HM Hb Hc Hdepth Hreplay
      (r:=opens c - S r) ltac:(lia)) as Hreg.
    rewrite opens_finish_replay_consistent in Hreg by assumption.
    replace (opens c + (opens b - closes c) - (opens c - S r))
      with (S (opens b - closes c + r)) in Hreg by lia.
    replace (opens c - (opens c - S r)) with (S (0 + r)) in Hreg by lia.
    exact Hreg.
  Qed.

  Lemma right_blocked_open_replay_decompose
      (b c bc seed : t) (acc : m_summary M) :
    IsMonoid M -> Consistent b -> Consistent c ->
    depth_supported_n b c = true -> replay_summary b c = Some bc ->
    closes c < opens b ->
    cancel_pairs (closes c) (opens b) 0 b c
      (region (regions_of c) 0) = Some acc ->
    Sized seed -> (lo seed <= net seed)%Z -> padding_neutral seed ->
    active seed + (opens b - closes c) < PullArray.size (regions_of seed) ->
    ReplayEqOpt
      (replay_opens (opens (finish_replay b c bc)) 0
        (finish_replay b c bc) (Some seed))
      (option_bind (replay_opens (opens b - closes c) 0 b (Some seed))
        (fun after_b => replay_opens (opens c) 0 c
          (Some (append_region after_b acc)))).
  Proof.
    intros HM Hb Hc Hdepth Hreplay Hstrict Hcancel Hsize Horder Hpad Hroom.
    assert (Hpivot : ReplayEqOpt
      (replay_opens (opens b - closes c) 0 (finish_replay b c bc) (Some seed))
      (option_bind (replay_opens (opens b - closes c) 0 b (Some seed))
        (fun s => Some (append_region s acc)))).
    { apply right_blocked_replay_surviving_b_opens; try assumption.
      intros before Hbefore.
      eapply replay_opens_prefix_room; eauto; lia. }
    rewrite opens_finish_replay_consistent by assumption.
    replace (opens c + (opens b - closes c))
      with ((opens b - closes c) + opens c) by lia.
    rewrite replay_opens_plus; simpl.
    pose proof (right_blocked_trailing_open_replay
      (b:=b) (c:=c) (bc:=bc)
      _ _
      HM Hb Hc Hdepth Hreplay ltac:(lia) Hpivot) as H.
    destruct (replay_opens (opens b - closes c) 0 b (Some seed));
      simpl in H |- *; [exact H|].
    rewrite replay_opens_none in H; exact H.
  Qed.

  Lemma left_blocked_close_prefix_has_room
      (a b : t) (acc : m_summary M) (p : nat)
      (before after : t) :
    Consistent a ->
    Consistent b ->
    depth_supported_n a b = true ->
    opens a <= closes b ->
    p < closes b - opens a ->
    replay_closes p (opens a) b
      (Some (append_region (open_base a) acc)) = Some before ->
    append_close before = Some after ->
    active after < PullArray.size (regions_of after).
  Proof.
    intros Ha Hb Hab Hblocked Hp Hbefore Hafter.
    pose proof Ha as [Ha_sized [Ha_depth [Ha_bound Ha_padding]]].
    destruct Ha_depth as [Ha_lo [Ha_hi [Ha_lonet [Ha_nethi Ha_span]]]].
    assert (Hbase_sized : Sized (open_base a)).
    { apply open_base_sized; exact Ha_sized. }
    assert (Hseed_sized : Sized (append_region (open_base a) acc)).
    { apply append_region_sized; exact Hbase_sized. }
    assert (Hbefore_sized : Sized before).
    { pose proof (replay_closes_sized p (opens a) b
        (Some (append_region (open_base a) acc)) Hseed_sized) as H.
      rewrite Hbefore in H; exact H. }
    assert (Hafter_sized : Sized after).
    { eapply append_close_sized; eauto. }
    assert (Hseed_lo : (lo (append_region (open_base a) acc) <= 0)%Z).
    { simpl; exact Ha_lo. }
    assert (Hseed_lonet :
      (lo (append_region (open_base a) acc) <=
       net (append_region (open_base a) acc))%Z).
    { simpl; lia. }
    destruct (replay_closes_counts p (opens a) b
      (append_region (open_base a) acc) (result:=before)
      Hseed_lo Hseed_lonet Hbefore) as [Hbefore_opens Hbefore_closes].
    rewrite append_region_opens, open_base_opens in Hbefore_opens.
    assert (Hbefore_zero : opens before = 0) by lia.
    destruct (replay_closes_order p (opens a) b
      (append_region (open_base a) acc) (result:=before)
      Hseed_lo Hseed_lonet Hbefore) as [Hbefore_lo Hbefore_lonet].
    pose proof (append_close_active_no_open before (result:=after)
      Hbefore_lo Hbefore_lonet Hbefore_zero Hafter) as Hactive_after.
    assert (Hbase_closes : closes (open_base a) = closes a).
    { unfold closes, open_base; simpl; reflexivity. }
    assert (Hbefore_active : active before = closes a + p).
    { pose proof (replay_closes_active_exact p (opens a) b
        (append_region (open_base a) acc) (result:=before)
        Hseed_lo Hseed_lonet Hbefore) as Hactive.
      rewrite append_region_closes, append_region_opens,
        Hbase_closes, open_base_opens in Hactive.
      lia. }
    assert (Hfinish_bound :
      active (finish_replay a b before) < 2 * N + 1).
    { apply depth_consistent_active_bound.
      apply finish_replay_depth_consistent; assumption. }
    unfold active in Hfinish_bound.
    rewrite closes_finish_replay_consistent in Hfinish_bound by assumption.
    rewrite opens_finish_replay_consistent in Hfinish_bound by assumption.
    rewrite Hafter_sized, Hactive_after, Hbefore_active.
    lia.
  Qed.

  Lemma left_blocked_close_right_prefix_replay_strict
      (a b c replayed_bc : t) (acc_ab acc_bc : m_summary M) :
    IsMonoid M ->
    Consistent a ->
    Consistent b ->
    Consistent c ->
    depth_supported_n a b = true ->
    depth_supported_n b c = true ->
    replay_summary b c = Some replayed_bc ->
    opens a < closes b ->
    opens b < closes c ->
    cancel_pairs (opens b) (opens b) 0 b c
      (region (regions_of c) 0) = Some acc_bc ->
    ReplayEqOpt
      (replay_closes (closes b - opens a) (opens a)
        (finish_replay b c replayed_bc)
        (Some (append_region (open_base a) acc_ab)))
      (option_bind
        (replay_closes (closes b - opens a) (opens a) b
          (Some (append_region (open_base a) acc_ab)))
        (fun after_b => Some (append_region after_b acc_bc))).
  Proof.
    intros HM Ha Hb Hc Hab Hbc Hreplay Hstrict Hclose Hcancel_bc.
    destruct (left_blocked_close_right_source_layout
      a (b:=b) (c:=c) (replayed_bc:=replayed_bc)
      HM Hb Hc Hbc Hreplay ltac:(lia) Hclose)
      as [acc_bc' [Hcancel_bc' [Hprefix [Hpivot Hsuffix]]]].
    rewrite Hcancel_bc in Hcancel_bc'; inversion Hcancel_bc'; subst acc_bc'.
    set (p := closes b - opens a - 1).
    assert (Hcount : closes b - opens a = S p) by (unfold p; lia).
    rewrite Hcount.
    apply replay_closes_close_pivot_assoc; try assumption.
    - intros r Hr.
      apply Hprefix; unfold p in Hr; lia.
    - replace (S (opens a + p)) with (closes b) by (unfold p; lia).
      exact Hpivot.
    - intros before_y after_y Hbefore Hafter.
      eapply left_blocked_close_prefix_has_room
        with (a:=a) (b:=b) (acc:=acc_ab) (p:=p) (before:=before_y);
        eauto; unfold p; lia.
  Qed.

  Corollary left_blocked_residual_closes_with_tail
      (a b c replayed_ab : t) (acc_ab acc_bc : m_summary M) :
    IsMonoid M ->
    Consistent a ->
    Consistent b ->
    depth_supported_n a b = true ->
    replay_summary a b = Some replayed_ab ->
    opens a <= closes b ->
    cancel_pairs (opens a) (opens a) 0 a b
      (region (regions_of b) 0) = Some acc_ab ->
    ReplayEqOpt
      (replay_closes (closes c - opens b) (opens b) c
        (Some
          (append_region (open_base (finish_replay a b replayed_ab))
            acc_bc)))
      (option_bind
        (replay_closes (closes b - opens a) (opens a) b
          (Some (append_region (open_base a) acc_ab)))
        (fun after_b =>
          replay_closes (closes c - opens b) (opens b) c
            (Some (append_region after_b acc_bc)))).
  Proof.
    intros HM Ha Hb Hab Hreplay Hblocked Hcancel.
    pose proof (left_blocked_residual_closes_reconstruct_open_base
      (a:=a) (b:=b) (replayed_ab:=replayed_ab)
      HM Ha Hb Hab Hreplay Hblocked Hcancel) as Hbase.
    apply ReplayEqOpt_sym.
    apply replay_closes_after_replay_eq_state; exact Hbase.
  Qed.

  Lemma left_blocked_close_residual_replay_strict
      (a b c replayed_ab replayed_bc : t)
      (acc_ab acc_bc : m_summary M) :
    IsMonoid M ->
    Consistent a ->
    Consistent b ->
    Consistent c ->
    depth_supported_n a b = true ->
    depth_supported_n b c = true ->
    replay_summary a b = Some replayed_ab ->
    replay_summary b c = Some replayed_bc ->
    opens a < closes b ->
    opens b < closes c ->
    cancel_pairs (opens a) (opens a) 0 a b
      (region (regions_of b) 0) = Some acc_ab ->
    cancel_pairs (opens b) (opens b) 0 b c
      (region (regions_of c) 0) = Some acc_bc ->
    ReplayEqOpt
      (replay_closes (closes c - opens b) (opens b) c
        (Some
          (append_region (open_base (finish_replay a b replayed_ab))
            acc_bc)))
      (replay_closes
        (closes (finish_replay b c replayed_bc) - opens a)
        (opens a) (finish_replay b c replayed_bc)
        (Some (append_region (open_base a) acc_ab))).
  Proof.
    intros HM Ha Hb Hc Hab Hbc Hreplay_ab Hreplay_bc
      Hstrict Hclose Hcancel_ab Hcancel_bc.
    set (initial := Some (append_region (open_base a) acc_ab)).
    set (rb := replay_closes (closes b - opens a) (opens a) b initial).
    set (q := closes c - opens b).
    assert (Htail : ReplayEqOpt
      (replay_closes q (opens b) c
        (Some
          (append_region (open_base (finish_replay a b replayed_ab))
            acc_bc)))
      (option_bind rb
        (fun after_b => replay_closes q (opens b) c
          (Some (append_region after_b acc_bc))))).
    { unfold q, rb, initial.
      apply left_blocked_residual_closes_with_tail; try assumption; lia. }
    assert (Hpivot : ReplayEqOpt
      (replay_closes (closes b - opens a) (opens a)
        (finish_replay b c replayed_bc) initial)
      (option_bind rb
        (fun after_b => Some (append_region after_b acc_bc)))).
    { unfold rb, initial.
      apply left_blocked_close_right_prefix_replay_strict;
        assumption. }
    assert (Hsource : ReplayEqOpt
      (option_bind rb
        (fun after_b => replay_closes q (opens b) c
          (Some (append_region after_b acc_bc))))
      (option_bind rb
        (fun after_b => replay_closes q (closes b)
          (finish_replay b c replayed_bc)
          (Some (append_region after_b acc_bc))))).
    { eapply ReplayEqOpt_bind; [apply ReplayEqOpt_refl|].
      intros x y Hxy; simpl.
      apply replay_closes_extensional.
      - simpl; apply append_region_replay_eq; exact Hxy.
      - intros r Hr.
        symmetry.
        unfold q in Hr.
        pose proof (finish_replay_excess_close_regions
          (state:=b) (source:=c) (result:=replayed_bc)
          HM Hb Hc Hbc Hreplay_bc Hclose (r:=r) Hr) as Hregion.
        replace (closes b + S r) with (S (closes b + r)) in Hregion
          by lia.
        exact Hregion. }
    assert (Hlift : ReplayEqOpt
      (replay_closes q (closes b) (finish_replay b c replayed_bc)
        (replay_closes (closes b - opens a) (opens a)
          (finish_replay b c replayed_bc) initial))
      (option_bind rb
        (fun after_b => replay_closes q (closes b)
          (finish_replay b c replayed_bc)
          (Some (append_region after_b acc_bc))))).
    { pose proof (replay_closes_replay_eq q (closes b)
        (source_x:=finish_replay b c replayed_bc)
        (source_y:=finish_replay b c replayed_bc)
        (replay_closes (closes b - opens a) (opens a)
          (finish_replay b c replayed_bc) initial)
        (option_bind rb
          (fun after_b => Some (append_region after_b acc_bc)))
        (ReplayEq_refl _) Hpivot) as H.
      destruct rb as [after_b|].
      - simpl in H |- *; exact H.
      - simpl in H |- *.
        rewrite replay_closes_none in H.
        exact H. }
    eapply ReplayEqOpt_trans; [exact Htail|].
    eapply ReplayEqOpt_trans; [exact Hsource|].
    apply ReplayEqOpt_sym.
    rewrite left_blocked_close_right_replay_split
      with (a:=a) (b:=b) (c:=c); try assumption; try lia.
  Qed.

  Lemma excess_close_trailing_open_source_regions
      (b c replayed_bc : t) :
    IsMonoid M ->
    Consistent b ->
    Consistent c ->
    depth_supported_n b c = true ->
    replay_summary b c = Some replayed_bc ->
    opens b < closes c ->
    opens (finish_replay b c replayed_bc) = opens c /\
    (forall r, r < opens c ->
      region (regions_of (finish_replay b c replayed_bc))
        (closes (finish_replay b c replayed_bc) + S r) =
      region (regions_of c) (closes c + S r)).
  Proof.
    intros HM Hb Hc Hbc Hreplay Hclose.
    assert (Hopens : opens (finish_replay b c replayed_bc) = opens c).
    { rewrite opens_finish_replay_consistent by assumption.
      replace (opens b - closes c) with 0 by lia; lia. }
    split; [exact Hopens|].
    intros r Hr.
    set (back := opens c - S r).
    assert (Hback : back < opens c) by (unfold back; lia).
    pose proof (finish_replay_trailing_open_regions
      (state:=b) (source:=c) (result:=replayed_bc)
      HM Hb Hc Hbc Hreplay (r:=back) Hback) as Hregion.
    rewrite Hopens in Hregion.
    replace (opens c - back) with (S r) in Hregion by (unfold back; lia).
    exact Hregion.
  Qed.

  Lemma excess_close_trailing_open_replay_eq
      (b c replayed_bc : t) (left right : option t) :
    IsMonoid M ->
    Consistent b ->
    Consistent c ->
    depth_supported_n b c = true ->
    replay_summary b c = Some replayed_bc ->
    opens b < closes c ->
    ReplayEqOpt left right ->
    ReplayEqOpt
      (option_bind left
        (fun state => replay_opens (opens c) 0 c (Some state)))
      (option_bind right
        (fun state =>
          replay_opens (opens (finish_replay b c replayed_bc)) 0
            (finish_replay b c replayed_bc) (Some state))).
  Proof.
    intros HM Hb Hc Hbc Hreplay Hclose Hstates.
    destruct (excess_close_trailing_open_source_regions
      (b:=b) (c:=c) (replayed_bc:=replayed_bc)
      HM Hb Hc Hbc Hreplay Hclose) as [Hopens Hregions].
    rewrite Hopens.
    eapply ReplayEqOpt_bind; [exact Hstates|].
    intros x y Hxy; simpl.
    apply replay_opens_extensional.
    - exact Hxy.
    - intros r Hr.
      replace (0 + r) with r by lia.
      symmetry; apply Hregions; exact Hr.
  Qed.

  Lemma left_blocked_close_residual_replay_at_pivot
      (a b c replayed_ab replayed_bc : t)
      (acc_ab acc_bc : m_summary M) :
    IsMonoid M ->
    Consistent a ->
    Consistent b ->
    Consistent c ->
    depth_supported_n a b = true ->
    depth_supported_n b c = true ->
    replay_summary a b = Some replayed_ab ->
    replay_summary b c = Some replayed_bc ->
    opens a = closes b ->
    opens b < closes c ->
    cancel_pairs (opens a) (opens a) 0 a b
      (region (regions_of b) 0) = Some acc_ab ->
    ReplayEqOpt
      (replay_closes (closes c - opens b) (opens b) c
        (Some
          (append_region (open_base (finish_replay a b replayed_ab))
            acc_bc)))
      (replay_closes
        (closes (finish_replay b c replayed_bc) - opens a)
        (opens a) (finish_replay b c replayed_bc)
        (Some (append_region (open_base a) (m_op M acc_ab acc_bc)))).
  Proof.
    intros HM Ha Hb Hc Hab Hbc Hreplay_ab Hreplay_bc
      Heq Hclose Hcancel_ab.
    pose proof (left_blocked_residual_closes_reconstruct_open_base
      (a:=a) (b:=b) (replayed_ab:=replayed_ab)
      (acc_ab:=acc_ab) HM Ha Hb Hab Hreplay_ab ltac:(lia) Hcancel_ab)
      as Hbase_opt.
    replace (closes b - opens a) with 0 in Hbase_opt by lia.
    simpl in Hbase_opt.
    assert (Hbase : ReplayEq
      (open_base (finish_replay a b replayed_ab))
      (append_region (open_base a) acc_ab)).
    { apply ReplayEq_sym; exact Hbase_opt. }
    assert (Hopen_base_bound :
      active (open_base a) < PullArray.size (regions_of (open_base a))).
    { pose proof Ha as [Ha_sized [Ha_depth [Ha_bound Ha_padding]]].
      destruct Ha_depth as [Ha_lo _].
      unfold Sized, regions_well_sized in Ha_sized.
      rewrite open_base_active by exact Ha_lo.
      unfold active in Ha_bound.
      unfold open_base; simpl.
      rewrite Ha_sized; lia. }
    assert (Hseed : ReplayEq
      (append_region (open_base (finish_replay a b replayed_ab)) acc_bc)
      (append_region (open_base a) (m_op M acc_ab acc_bc))).
    { rewrite <- append_region_assoc by assumption.
      apply append_region_replay_eq; exact Hbase. }
    assert (Hcount :
      closes (finish_replay b c replayed_bc) - opens a =
        closes c - opens b).
    { rewrite closes_finish_replay_consistent by assumption; lia. }
    rewrite Hcount.
    apply replay_closes_extensional.
    - simpl; exact Hseed.
    - intros r Hr.
      pose proof (finish_replay_excess_close_regions
        (state:=b) (source:=c) (result:=replayed_bc)
        HM Hb Hc Hbc Hreplay_bc Hclose (r:=r) Hr) as Hregion.
      replace (S (opens a + r)) with (closes b + S r) by lia.
      symmetry; exact Hregion.
  Qed.

  Lemma replay_summary_normal_forms_assoc_zero_left_blocked_close_strict
      (a b c replayed_ab replayed_bc : t) :
    IsMonoid M ->
    Consistent a ->
    Consistent b ->
    Consistent c ->
    depth_supported_n a b = true ->
    depth_supported_n b c = true ->
    replay_summary a b = Some replayed_ab ->
    replay_summary b c = Some replayed_bc ->
    opens a < closes b ->
    opens b < closes c ->
    ReplayEqOpt
      (replay_summary_normal_form (finish_replay a b replayed_ab) c)
      (replay_summary_normal_form
        a (finish_replay b c replayed_bc)).
  Proof.
    intros HM Ha Hb Hc Hab Hbc Hreplay_ab Hreplay_bc Hstrict Hclose.
    assert (Hblocked : opens a <= closes b) by lia.
    destruct (left_blocked_close_outer_branches
      (a:=a) (b:=b) (c:=c) replayed_ab replayed_bc
      Ha Hb Hc Hblocked Hclose) as [Hleft_close Hright_close].
    rewrite replay_summary_normal_form_close by exact Hleft_close.
    rewrite replay_summary_normal_form_close by exact Hright_close.
    destruct (left_blocked_close_left_outer_cancel_success
      (a:=a) (b:=b) (c:=c)
      (replayed_ab:=replayed_ab) (replayed_bc:=replayed_bc)
      HM Ha Hb Hc Hab Hbc Hreplay_ab Hreplay_bc Hblocked Hclose)
      as [acc_bc [Hcancel_bc Hcancel_left]].
    destruct (left_blocked_close_right_outer_cancel_strict_success
      (a:=a) (b:=b) (c:=c)
      (replayed_ab:=replayed_ab) (replayed_bc:=replayed_bc)
      HM Ha Hb Hc Hab Hbc Hreplay_ab Hreplay_bc Hstrict Hclose)
      as [acc_ab [Hcancel_ab Hcancel_right]].
    rewrite Hcancel_left, Hcancel_right; simpl.
    assert (Hopens_ab :
      opens (finish_replay a b replayed_ab) = opens b).
    { apply opens_finish_replay_left_blocked; assumption. }
    rewrite Hopens_ab.
    apply excess_close_trailing_open_replay_eq
      with (b:=b) (c:=c) (replayed_bc:=replayed_bc);
      try assumption.
    apply left_blocked_close_residual_replay_strict
      with (a:=a) (b:=b) (c:=c)
        (replayed_ab:=replayed_ab) (replayed_bc:=replayed_bc)
        (acc_ab:=acc_ab) (acc_bc:=acc_bc);
      assumption.
  Qed.

  Lemma replay_summary_normal_forms_assoc_zero_left_blocked_close_pivot
      (a b c replayed_ab replayed_bc : t) :
    IsMonoid M ->
    Consistent a ->
    Consistent b ->
    Consistent c ->
    depth_supported_n a b = true ->
    depth_supported_n b c = true ->
    replay_summary a b = Some replayed_ab ->
    replay_summary b c = Some replayed_bc ->
    opens a = closes b ->
    opens b < closes c ->
    ReplayEqOpt
      (replay_summary_normal_form (finish_replay a b replayed_ab) c)
      (replay_summary_normal_form
        a (finish_replay b c replayed_bc)).
  Proof.
    intros HM Ha Hb Hc Hab Hbc Hreplay_ab Hreplay_bc Heq Hclose.
    assert (Hblocked : opens a <= closes b) by lia.
    destruct (left_blocked_close_outer_branches
      (a:=a) (b:=b) (c:=c) replayed_ab replayed_bc
      Ha Hb Hc Hblocked Hclose) as [Hleft_close Hright_close].
    rewrite replay_summary_normal_form_close by exact Hleft_close.
    rewrite replay_summary_normal_form_close by exact Hright_close.
    destruct (left_blocked_close_left_outer_cancel_success
      (a:=a) (b:=b) (c:=c)
      (replayed_ab:=replayed_ab) (replayed_bc:=replayed_bc)
      HM Ha Hb Hc Hab Hbc Hreplay_ab Hreplay_bc Hblocked Hclose)
      as [acc_bc_left [Hcancel_bc_left Hcancel_left]].
    destruct (left_blocked_close_right_outer_cancel_pivot_success
      (a:=a) (b:=b) (c:=c)
      (replayed_ab:=replayed_ab) (replayed_bc:=replayed_bc)
      HM Ha Hb Hc Hab Hbc Hreplay_ab Hreplay_bc Heq Hclose)
      as [acc_ab [acc_bc [Hcancel_ab [Hcancel_bc Hcancel_right]]]].
    rewrite Hcancel_bc in Hcancel_bc_left.
    inversion Hcancel_bc_left; subst acc_bc_left.
    rewrite Hcancel_left, Hcancel_right; simpl.
    assert (Hopens_ab :
      opens (finish_replay a b replayed_ab) = opens b).
    { apply opens_finish_replay_left_blocked; assumption. }
    rewrite Hopens_ab.
    apply excess_close_trailing_open_replay_eq
      with (b:=b) (c:=c) (replayed_bc:=replayed_bc);
      try assumption.
    apply left_blocked_close_residual_replay_at_pivot
      with (a:=a) (b:=b) (c:=c)
        (replayed_ab:=replayed_ab) (replayed_bc:=replayed_bc)
        (acc_ab:=acc_ab) (acc_bc:=acc_bc);
      assumption.
  Qed.

  Lemma positive_open_residual_source_regions
      (a b c replayed_ab : t) :
    IsMonoid M ->
    Consistent a ->
    Consistent b ->
    depth_supported_n a b = true ->
    replay_summary a b = Some replayed_ab ->
    0 < three_way_boundary_pairs a b c ->
    closes c <= opens (finish_replay a b replayed_ab) ->
    forall r,
      r < opens (finish_replay a b replayed_ab) - closes c ->
      region (regions_of (finish_replay a b replayed_ab))
        (closes (finish_replay a b replayed_ab) + S r) =
      region (regions_of a) (closes a + S r).
  Proof.
    intros HM Ha Hb Hab Hreplay Hpositive Houter r Hr.
    pose proof Hpositive as Hbounds.
    apply three_way_boundary_pairs_positive_iff in Hbounds.
    destruct Hbounds as [Hba Hcb].
    destruct (finish_replay_surviving_open_pivot
      (state:=a) (source:=b) (result:=replayed_ab)
      HM Ha Hb Hab Hreplay ltac:(lia))
      as [acc_ab [Hcancel [Hbefore Hpivot]]].
    rewrite closes_finish_replay_consistent by assumption.
    replace (closes b - opens a) with 0 by lia.
    replace (closes a + 0) with (closes a) by lia.
    apply Hbefore.
    rewrite opens_finish_replay_consistent in Hr by assumption.
    lia.
  Qed.

  Lemma positive_open_bases_replay_eq
      (a b c replayed_ab : t) :
    IsMonoid M ->
    Consistent a ->
    Consistent b ->
    depth_supported_n a b = true ->
    replay_summary a b = Some replayed_ab ->
    0 < three_way_boundary_pairs a b c ->
    ReplayEq
      (open_base (finish_replay a b replayed_ab))
      (open_base a).
  Proof.
    intros HM Ha Hb Hab Hreplay Hpositive.
    pose proof Hpositive as Hbounds.
    apply three_way_boundary_pairs_positive_iff in Hbounds.
    destruct Hbounds as [Hba Hcb].
    pose proof Ha as [Ha_sized [Ha_depth [Ha_bound Ha_padding]]].
    assert (Hreplayed_sized : Sized replayed_ab).
    { eapply replay_summary_result_sized; eauto. }
    assert (Hf_sized : Sized (finish_replay a b replayed_ab)).
    { apply finish_replay_sized; exact Hreplayed_sized. }
    assert (Hf_depth : depth_consistent (finish_replay a b replayed_ab)).
    { apply finish_replay_depth_consistent; assumption. }
    destruct Ha_depth as [Ha_lo _].
    destruct Hf_depth as [Hf_lo _].
    assert (Hcloses :
      closes (finish_replay a b replayed_ab) = closes a).
    { rewrite closes_finish_replay_consistent by assumption.
      replace (closes b - opens a) with 0 by lia; lia. }
    assert (Hlo : lo (finish_replay a b replayed_ab) = lo a).
    { pose proof (closes_as_depth
        (finish_replay a b replayed_ab) Hf_lo) as Hf_as_depth.
      pose proof (closes_as_depth a Ha_lo) as Ha_as_depth.
      rewrite Hcloses in Hf_as_depth; lia. }
    unfold ReplayEq.
    split; [simpl; exact Hlo|].
    split; [simpl; exact Hlo|].
    apply regions_eq_of_active_agreement.
    - apply open_base_sized; exact Hf_sized.
    - apply open_base_sized; exact Ha_sized.
    - rewrite !open_base_active by assumption; exact Hcloses.
    - intros i Hi.
      rewrite open_base_active in Hi by exact Hf_lo.
      rewrite (open_base_agrees (finish_replay a b replayed_ab)
        (i:=i) Hi).
      rewrite (open_base_agrees a (i:=i)
        ltac:(rewrite Hcloses in Hi; exact Hi)).
      apply finish_replay_surviving_open_prefix; try assumption; lia.
    - apply open_base_padding; exact Hf_lo.
    - apply open_base_padding; exact Ha_lo.
  Qed.

  Lemma positive_open_residual_replay_eq
      (a b c replayed_ab replayed_bc : t) :
    IsMonoid M ->
    Consistent a ->
    Consistent b ->
    Consistent c ->
    depth_supported_n a b = true ->
    replay_summary a b = Some replayed_ab ->
    0 < three_way_boundary_pairs a b c ->
    closes c <= opens (finish_replay a b replayed_ab) ->
    ReplayEqOpt
      (replay_opens
        (opens (finish_replay a b replayed_ab) - closes c) 0
        (finish_replay a b replayed_ab)
        (Some (open_base (finish_replay a b replayed_ab))))
      (replay_opens
        (opens a - closes (finish_replay b c replayed_bc)) 0 a
        (Some (open_base a))).
  Proof.
    intros HM Ha Hb Hc Hab Hreplay Hpositive Houter.
    pose proof (positive_outer_residual_opens_assoc
      (a:=a) (b:=b) (c:=c) replayed_ab replayed_bc
      Ha Hb Hc Hpositive) as Hcount.
    rewrite <- Hcount.
    apply replay_opens_extensional.
    - simpl.
      apply positive_open_bases_replay_eq with (c:=c); assumption.
    - intros r Hr.
      replace (0 + r) with r by lia.
      apply positive_open_residual_source_regions
        with (a:=a) (b:=b) (c:=c) (replayed_ab:=replayed_ab);
        try assumption.
  Qed.

  Lemma positive_trailing_open_source_regions
      (a b c replayed_bc : t) :
    IsMonoid M ->
    Consistent b ->
    Consistent c ->
    depth_supported_n b c = true ->
    replay_summary b c = Some replayed_bc ->
    0 < three_way_boundary_pairs a b c ->
    opens (finish_replay b c replayed_bc) = opens c /\
    (forall r, r < opens c ->
      region (regions_of (finish_replay b c replayed_bc))
        (closes (finish_replay b c replayed_bc) + S r) =
      region (regions_of c) (closes c + S r)).
  Proof.
    intros HM Hb Hc Hbc Hreplay Hpositive.
    pose proof Hpositive as Hbounds.
    apply three_way_boundary_pairs_positive_iff in Hbounds.
    destruct Hbounds as [_ Hcb].
    assert (Hopens : opens (finish_replay b c replayed_bc) = opens c).
    { rewrite opens_finish_replay_consistent by assumption.
      replace (opens b - closes c) with 0 by lia.
      lia. }
    split; [exact Hopens|].
    intros r Hr.
    set (back := opens c - S r).
    assert (Hback : back < opens c) by (unfold back; lia).
    pose proof (finish_replay_trailing_open_regions
      (state:=b) (source:=c) (result:=replayed_bc)
      HM Hb Hc Hbc Hreplay (r:=back) Hback) as Hregion.
    rewrite Hopens in Hregion.
    replace (opens c - back) with (S r) in Hregion by (unfold back; lia).
    exact Hregion.
  Qed.

  Lemma positive_trailing_open_replay_eq
      (a b c replayed_bc : t)
      (residual_left residual_right : option t)
      (acc : m_summary M) :
    IsMonoid M ->
    Consistent b ->
    Consistent c ->
    depth_supported_n b c = true ->
    replay_summary b c = Some replayed_bc ->
    0 < three_way_boundary_pairs a b c ->
    ReplayEqOpt residual_left residual_right ->
    ReplayEqOpt
      (option_bind residual_left
        (fun state =>
          replay_opens (opens c) 0 c
            (Some (append_region state acc))))
      (option_bind residual_right
        (fun state =>
          replay_opens (opens (finish_replay b c replayed_bc)) 0
            (finish_replay b c replayed_bc)
            (Some (append_region state acc)))).
  Proof.
    intros HM Hb Hc Hbc Hreplay Hpositive Hresidual.
    destruct (positive_trailing_open_source_regions
      a (b:=b) (c:=c) (replayed_bc:=replayed_bc)
      HM Hb Hc Hbc Hreplay Hpositive) as [Hopens Hregions].
    rewrite Hopens.
    eapply ReplayEqOpt_bind; [exact Hresidual|].
    intros left right Hstate; simpl.
    apply replay_opens_extensional.
    - simpl; apply append_region_replay_eq; exact Hstate.
    - intros r Hr.
      replace (0 + r) with r by lia.
      symmetry; apply Hregions; exact Hr.
  Qed.

  Lemma positive_trailing_open_replay_eq_direct
      (a b c replayed_bc : t)
      (residual_left residual_right : option t) :
    IsMonoid M ->
    Consistent b ->
    Consistent c ->
    depth_supported_n b c = true ->
    replay_summary b c = Some replayed_bc ->
    0 < three_way_boundary_pairs a b c ->
    ReplayEqOpt residual_left residual_right ->
    ReplayEqOpt
      (option_bind residual_left
        (fun state => replay_opens (opens c) 0 c (Some state)))
      (option_bind residual_right
        (fun state =>
          replay_opens (opens (finish_replay b c replayed_bc)) 0
            (finish_replay b c replayed_bc) (Some state))).
  Proof.
    intros HM Hb Hc Hbc Hreplay Hpositive Hresidual.
    destruct (positive_trailing_open_source_regions
      a (b:=b) (c:=c) (replayed_bc:=replayed_bc)
      HM Hb Hc Hbc Hreplay Hpositive) as [Hopens Hregions].
    rewrite Hopens.
    eapply ReplayEqOpt_bind; [exact Hresidual|].
    intros left right Hstate; simpl.
    apply replay_opens_extensional.
    - exact Hstate.
    - intros r Hr.
      replace (0 + r) with r by lia.
      symmetry; apply Hregions; exact Hr.
  Qed.

  Lemma positive_close_residual_source_regions
      (a b c replayed_ab replayed_bc : t) :
    IsMonoid M ->
    Consistent a ->
    Consistent b ->
    Consistent c ->
    depth_supported_n b c = true ->
    replay_summary b c = Some replayed_bc ->
    0 < three_way_boundary_pairs a b c ->
    opens (finish_replay a b replayed_ab) < closes c ->
    forall r,
      r < closes c - opens (finish_replay a b replayed_ab) ->
      region (regions_of c)
        (S (opens (finish_replay a b replayed_ab) + r)) =
      region (regions_of (finish_replay b c replayed_bc))
        (S (opens a + r)).
  Proof.
    intros HM Ha Hb Hc Hbc Hreplay Hpositive Houter r Hr.
    pose proof Hpositive as Hbounds.
    apply three_way_boundary_pairs_positive_iff in Hbounds.
    destruct Hbounds as [Hba Hcb].
    set (r' := opens a - closes b + r).
    assert (Hr' : r' < closes c - opens b).
    { unfold r'.
      rewrite opens_finish_replay_consistent in Hr by assumption.
      lia. }
    pose proof (finish_replay_excess_close_regions
      (state:=b) (source:=c) (result:=replayed_bc)
      HM Hb Hc Hbc Hreplay Hcb (r:=r') Hr') as Hregion.
    symmetry.
    replace (closes b + S r') with (S (opens a + r)) in Hregion
      by (unfold r'; lia).
    replace (S (opens b + r'))
      with (S (opens (finish_replay a b replayed_ab) + r)) in Hregion.
    - exact Hregion.
    - rewrite opens_finish_replay_consistent by assumption.
      unfold r'; lia.
  Qed.

  Lemma positive_close_residual_replay_eq
      (a b c replayed_ab replayed_bc : t)
      (acc : m_summary M) :
    IsMonoid M ->
    Consistent a ->
    Consistent b ->
    Consistent c ->
    depth_supported_n a b = true ->
    depth_supported_n b c = true ->
    replay_summary a b = Some replayed_ab ->
    replay_summary b c = Some replayed_bc ->
    0 < three_way_boundary_pairs a b c ->
    opens (finish_replay a b replayed_ab) < closes c ->
    ReplayEqOpt
      (replay_closes
        (closes c - opens (finish_replay a b replayed_ab))
        (opens (finish_replay a b replayed_ab)) c
        (Some
          (append_region (open_base (finish_replay a b replayed_ab)) acc)))
      (replay_closes
        (closes (finish_replay b c replayed_bc) - opens a)
        (opens a) (finish_replay b c replayed_bc)
        (Some (append_region (open_base a) acc))).
  Proof.
    intros HM Ha Hb Hc Hab Hbc Hreplay_ab Hreplay_bc Hpositive Houter.
    pose proof (positive_outer_residual_closes_assoc
      (a:=a) (b:=b) (c:=c) replayed_ab replayed_bc
      Ha Hb Hc Hpositive) as Hcount.
    rewrite <- Hcount.
    apply replay_closes_extensional.
    - simpl; apply append_region_replay_eq.
      apply positive_open_bases_replay_eq with (c:=c); assumption.
    - intros r Hr.
      apply positive_close_residual_source_regions
        with (a:=a) (b:=b) (c:=c)
          (replayed_ab:=replayed_ab) (replayed_bc:=replayed_bc);
        assumption.
  Qed.

  Lemma cancel_pairs_from_excess_close_source
      (state source replayed open_source : t)
      (remaining open_count : nat) (acc : m_summary M) :
    IsMonoid M ->
    Consistent state ->
    Consistent source ->
    depth_supported_n state source = true ->
    replay_summary state source = Some replayed ->
    remaining <= open_count ->
    remaining <= closes source - opens state ->
    cancel_pairs remaining open_count (closes state)
      open_source (finish_replay state source replayed) acc =
    cancel_pairs remaining open_count (opens state)
      open_source source acc.
  Proof.
    intros HM Hstate Hsource Hsupported Hreplay
      Hopen_bound Hclose_bound.
    apply cancel_pairs_extensional; try assumption.
    - intros r Hr; reflexivity.
    - intros r Hr.
      replace (S (closes state + r)) with (closes state + S r) by lia.
      apply finish_replay_excess_close_regions; try assumption; lia.
  Qed.

  Lemma cancel_pairs_from_trailing_open_source
      (state source replayed close_source : t)
      (remaining close_index : nat) (acc : m_summary M) :
    IsMonoid M ->
    Consistent state ->
    Consistent source ->
    depth_supported_n state source = true ->
    replay_summary state source = Some replayed ->
    remaining <= opens source ->
    cancel_pairs remaining
      (opens (finish_replay state source replayed)) close_index
      (finish_replay state source replayed) close_source acc =
    cancel_pairs remaining (opens source) close_index
      source close_source acc.
  Proof.
    intros HM Hstate Hsource Hsupported Hreplay Hremaining.
    apply cancel_pairs_extensional.
    - rewrite opens_finish_replay_consistent by assumption; lia.
    - exact Hremaining.
    - intros r Hr.
      apply finish_replay_trailing_open_regions; try assumption; lia.
    - intros r Hr; reflexivity.
  Qed.

  Lemma cancel_pairs_split_trailing_open_source
      (state source replayed close_source : t)
      (remaining close_index : nat) (acc : m_summary M) :
    IsMonoid M ->
    Consistent state ->
    Consistent source ->
    depth_supported_n state source = true ->
    replay_summary state source = Some replayed ->
    remaining <= opens (finish_replay state source replayed) ->
    let trailing := Nat.min remaining (opens source) in
    cancel_pairs remaining
      (opens (finish_replay state source replayed)) close_index
      (finish_replay state source replayed) close_source acc =
    option_bind
      (cancel_pairs trailing (opens source) close_index
        source close_source acc)
      (fun after_trailing =>
        cancel_pairs (remaining - trailing)
          (opens (finish_replay state source replayed) - trailing)
          (close_index + trailing)
          (finish_replay state source replayed) close_source after_trailing).
  Proof.
    intros HM Hstate Hsource Hsupported Hreplay Hremaining.
    set (trailing := Nat.min remaining (opens source)).
    assert (Htrailing_remaining : trailing <= remaining).
    { unfold trailing.
      destruct (le_dec remaining (opens source)) as [Hle|Hgt].
      - rewrite Nat.min_l by exact Hle; lia.
      - rewrite Nat.min_r by lia; lia. }
    assert (Htrailing_source : trailing <= opens source).
    { unfold trailing.
      destruct (le_dec remaining (opens source)) as [Hle|Hgt].
      - rewrite Nat.min_l by exact Hle; lia.
      - rewrite Nat.min_r by lia; lia. }
    etransitivity.
    - pose proof (cancel_pairs_plus
        (p:=trailing)
        (open_count:=opens (finish_replay state source replayed))
        (remaining - trailing) close_index
        (finish_replay state source replayed) close_source acc)
        as Hsplit.
      specialize (Hsplit ltac:(lia)).
      replace (trailing + (remaining - trailing)) with remaining in Hsplit
        by lia.
      exact Hsplit.
    -
    assert (Hfirst :
      cancel_pairs trailing
        (opens (finish_replay state source replayed)) close_index
        (finish_replay state source replayed) close_source acc =
      cancel_pairs trailing (opens source) close_index
        source close_source acc).
    { exact (cancel_pairs_from_trailing_open_source
        (state:=state) (source:=source) (replayed:=replayed)
        close_source (remaining:=trailing) close_index acc
        HM Hstate Hsource Hsupported Hreplay Htrailing_source). }
      rewrite Hfirst; reflexivity.
  Qed.

  Lemma cancel_pairs_left_outer_decompose
      (a b c replayed_ab : t) (acc : m_summary M) :
    IsMonoid M ->
    Consistent a ->
    Consistent b ->
    depth_supported_n a b = true ->
    replay_summary a b = Some replayed_ab ->
    cancel_pairs (boundary_pairs (finish_replay a b replayed_ab) c)
      (opens (finish_replay a b replayed_ab)) 0
      (finish_replay a b replayed_ab) c acc =
    option_bind
      (cancel_pairs (boundary_pairs b c) (opens b) 0 b c acc)
      (fun after_bc =>
        cancel_pairs (three_way_boundary_pairs a b c)
          (opens (finish_replay a b replayed_ab) - boundary_pairs b c)
          (boundary_pairs b c)
          (finish_replay a b replayed_ab) c after_bc).
  Proof.
    intros HM Ha Hb Hab Hreplay_ab.
    pose proof (cancel_pairs_split_trailing_open_source
      (state:=a) (source:=b) (replayed:=replayed_ab) c
      (remaining:=boundary_pairs (finish_replay a b replayed_ab) c)
      0 acc HM Ha Hb Hab Hreplay_ab
      (boundary_pairs_le_opens (finish_replay a b replayed_ab) c))
      as Hsplit.
    cbn zeta in Hsplit.
    rewrite (boundary_pairs_left_outer_trailing_count
      (a:=a) (b:=b) c replayed_ab Ha Hb) in Hsplit.
    rewrite (boundary_pairs_left_outer_decompose
      (a:=a) (b:=b) c replayed_ab Ha Hb) in Hsplit.
    replace
      (boundary_pairs b c + three_way_boundary_pairs a b c -
        boundary_pairs b c)
      with (three_way_boundary_pairs a b c) in Hsplit by lia.
    replace (0 + boundary_pairs b c) with (boundary_pairs b c) in Hsplit
      by lia.
    rewrite (boundary_pairs_left_outer_decompose
      (a:=a) (b:=b) c replayed_ab Ha Hb).
    exact Hsplit.
  Qed.

  Lemma cancel_pairs_left_outer_second_stage
      (a b c replayed_ab : t) :
    IsMonoid M ->
    Consistent a ->
    Consistent b ->
    depth_supported_n a b = true ->
    replay_summary a b = Some replayed_ab ->
    0 < three_way_boundary_pairs a b c ->
    exists acc_ab,
      cancel_pairs (closes b) (opens a) 0 a b
        (region (regions_of b) 0) = Some acc_ab /\
      forall tail,
        cancel_pairs (three_way_boundary_pairs a b c)
          (opens (finish_replay a b replayed_ab) - boundary_pairs b c)
          (boundary_pairs b c)
          (finish_replay a b replayed_ab) c tail =
        cancel_pairs (three_way_boundary_pairs a b c)
          (opens a - closes b) (opens b) a c
          (m_op M acc_ab tail).
  Proof.
    intros HM Ha Hb Hab Hreplay Hthree.
    unfold three_way_boundary_pairs in Hthree.
    assert (Hsurvives : closes b <= opens a).
    { destruct (le_dec (opens a - closes b) (closes c - opens b));
        rewrite ?Nat.min_l, ?Nat.min_r in Hthree by lia; lia. }
    assert (Hexcess : opens b < closes c).
    { destruct (le_dec (opens a - closes b) (closes c - opens b));
        rewrite ?Nat.min_l, ?Nat.min_r in Hthree by lia; lia. }
    assert (Hpair_bc : boundary_pairs b c = opens b).
    { unfold boundary_pairs; rewrite Nat.min_l by lia; reflexivity. }
    assert (Hfinish_opens :
      opens (finish_replay a b replayed_ab) =
        opens b + (opens a - closes b)).
    { apply opens_finish_replay_consistent; assumption. }
    assert (Hfinish_closes :
      closes (finish_replay a b replayed_ab) = closes a).
    { rewrite closes_finish_replay_consistent by assumption.
      replace (closes b - opens a) with 0 by lia; lia. }
    destruct (finish_replay_surviving_open_pivot
      (state:=a) (source:=b) (result:=replayed_ab)
      HM Ha Hb Hab Hreplay Hsurvives)
      as [acc_ab [Hcancel [Hbefore Hpivot]]].
    exists acc_ab; split; [exact Hcancel|].
    intro tail.
    rewrite Hpair_bc, Hfinish_opens.
    replace (opens b + (opens a - closes b) - opens b)
      with (opens a - closes b) by lia.
    set (q := three_way_boundary_pairs a b c).
    assert (Hq_survives : q <= opens a - closes b).
    { unfold q, three_way_boundary_pairs.
      destruct (le_dec (opens a - closes b) (closes c - opens b));
        [rewrite Nat.min_l by lia|rewrite Nat.min_r by lia]; lia. }
    assert (Hq_positive : 0 < q) by (unfold q; exact Hthree).
    destruct q as [|remaining]; [lia|].
    apply cancel_pairs_pivot_assoc; try lia.
    - exact HM.
    - rewrite Hfinish_closes; apply Hpivot; lia.
    - intros r Hr.
      rewrite Hfinish_closes.
      set (i := opens a - closes b - S r).
      assert (Hi_positive : 0 < i) by (unfold i; lia).
      set (r' := i - 1).
      assert (Hr'_index : S r' = i) by (unfold r'; lia).
      assert (Hr'_bound : S r' < opens a - closes b)
        by (rewrite Hr'_index; unfold i; lia).
      specialize (Hbefore r' Hr'_bound).
      rewrite Hr'_index in Hbefore.
      unfold i in Hbefore.
      exact Hbefore.
  Qed.

  Lemma cancel_pairs_right_outer_first_stage
      (a b c replayed_bc : t) :
    IsMonoid M ->
    Consistent b ->
    Consistent c ->
    depth_supported_n b c = true ->
    replay_summary b c = Some replayed_bc ->
    0 < three_way_boundary_pairs a b c ->
    0 < closes b ->
    exists acc_bc,
      cancel_pairs (opens b) (opens b) 0 b c
        (region (regions_of c) 0) = Some acc_bc /\
      forall acc,
        cancel_pairs (boundary_pairs a b) (opens a) 0
          a (finish_replay b c replayed_bc) acc =
        option_bind
          (cancel_pairs (boundary_pairs a b) (opens a) 0 a b acc)
          (fun result => Some (m_op M result acc_bc)).
  Proof.
    intros HM Hb Hc Hbc Hreplay Hthree Hb_closes.
    unfold three_way_boundary_pairs in Hthree.
    assert (Ha_survives : closes b < opens a).
    { destruct (le_dec (opens a - closes b) (closes c - opens b));
        rewrite ?Nat.min_l, ?Nat.min_r in Hthree by lia; lia. }
    assert (Hc_excess : opens b < closes c).
    { destruct (le_dec (opens a - closes b) (closes c - opens b));
        rewrite ?Nat.min_l, ?Nat.min_r in Hthree by lia; lia. }
    assert (Hpair_ab : boundary_pairs a b = closes b).
    { unfold boundary_pairs; rewrite Nat.min_r by lia; reflexivity. }
    destruct (finish_replay_close_prefix_pivot
      (state:=b) (source:=c) (result:=replayed_bc)
      HM Hb Hc Hbc Hreplay Hc_excess)
      as [acc_bc [Hcancel [Hbefore Hpivot]]].
    exists acc_bc; split; [exact Hcancel|].
    intro acc; rewrite Hpair_ab.
    destruct (closes b) as [|remaining] eqn:Hcloses_count; [lia|].
    apply cancel_pairs_close_pivot_assoc; try lia.
    - exact HM.
    - intros r Hr.
      apply Hbefore; lia.
    - exact Hpivot.
  Qed.

  Corollary cancel_pairs_right_outer_first_stage_actual
      (a b c replayed_bc : t) :
    IsMonoid M ->
    Consistent b ->
    Consistent c ->
    depth_supported_n b c = true ->
    replay_summary b c = Some replayed_bc ->
    0 < three_way_boundary_pairs a b c ->
    0 < closes b ->
    exists acc_bc,
      cancel_pairs (opens b) (opens b) 0 b c
        (region (regions_of c) 0) = Some acc_bc /\
      cancel_pairs (boundary_pairs a b) (opens a) 0
        a (finish_replay b c replayed_bc)
        (region (regions_of (finish_replay b c replayed_bc)) 0) =
      option_bind
        (cancel_pairs (boundary_pairs a b) (opens a) 0 a b
          (region (regions_of b) 0))
        (fun result => Some (m_op M result acc_bc)).
  Proof.
    intros HM Hb Hc Hbc Hreplay Hthree Hb_closes.
    destruct (cancel_pairs_right_outer_first_stage
      a (b:=b) (c:=c) (replayed_bc:=replayed_bc)
      HM Hb Hc Hbc Hreplay Hthree Hb_closes)
      as [acc_bc [Hcancel Hstage]].
    exists acc_bc; split; [exact Hcancel|].
    specialize (Hstage
      (region (regions_of (finish_replay b c replayed_bc)) 0)).
    assert (Hzero :
      region (regions_of (finish_replay b c replayed_bc)) 0 =
      region (regions_of b) 0).
    { apply finish_replay_close_prefix_region_zero; try assumption.
      unfold three_way_boundary_pairs in Hthree.
      destruct (le_dec (opens a - closes b) (closes c - opens b));
        rewrite ?Nat.min_l, ?Nat.min_r in Hthree by lia; lia. }
    assert (Hacc :
      cancel_pairs (boundary_pairs a b) (opens a) 0 a b
        (region (regions_of (finish_replay b c replayed_bc)) 0) =
      cancel_pairs (boundary_pairs a b) (opens a) 0 a b
        (region (regions_of b) 0)).
    { apply cancel_pairs_acc_eq; exact Hzero. }
    rewrite Hacc in Hstage.
    exact Hstage.
  Qed.

  Lemma cancel_pairs_right_outer_decompose
      (a b c replayed_bc : t) :
    IsMonoid M ->
    Consistent b ->
    Consistent c ->
    depth_supported_n b c = true ->
    replay_summary b c = Some replayed_bc ->
    0 < three_way_boundary_pairs a b c ->
    0 < closes b ->
    exists acc_bc,
      cancel_pairs (opens b) (opens b) 0 b c
        (region (regions_of c) 0) = Some acc_bc /\
      cancel_pairs (boundary_pairs a (finish_replay b c replayed_bc))
        (opens a) 0 a (finish_replay b c replayed_bc)
        (region (regions_of (finish_replay b c replayed_bc)) 0) =
      option_bind
        (cancel_pairs (boundary_pairs a b) (opens a) 0 a b
          (region (regions_of b) 0))
        (fun acc_ab =>
          cancel_pairs (three_way_boundary_pairs a b c)
            (opens a - boundary_pairs a b) (opens b) a c
            (m_op M acc_ab acc_bc)).
  Proof.
    intros HM Hb Hc Hbc Hreplay Hthree Hb_closes.
    destruct (cancel_pairs_right_outer_first_stage_actual
      a (b:=b) (c:=c) (replayed_bc:=replayed_bc)
      HM Hb Hc Hbc Hreplay Hthree Hb_closes)
      as [acc_bc [Hcancel_bc Hfirst]].
    exists acc_bc; split; [exact Hcancel_bc|].
    assert (Hpair_ab : boundary_pairs a b = closes b).
    { unfold three_way_boundary_pairs in Hthree.
      assert (closes b < opens a).
      { destruct (le_dec (opens a - closes b) (closes c - opens b));
          rewrite ?Nat.min_l, ?Nat.min_r in Hthree by lia; lia. }
      unfold boundary_pairs; rewrite Nat.min_r by lia; reflexivity. }
    assert (Houter :
      boundary_pairs a (finish_replay b c replayed_bc) =
        boundary_pairs a b + three_way_boundary_pairs a b c).
    { apply boundary_pairs_right_outer_decompose; assumption. }
    pose proof (cancel_pairs_plus
      (p:=boundary_pairs a b) (open_count:=opens a)
      (three_way_boundary_pairs a b c) 0
      a (finish_replay b c replayed_bc)
      (region (regions_of (finish_replay b c replayed_bc)) 0)
      (boundary_pairs_le_opens a b)) as Hsplit.
    rewrite <- Houter in Hsplit.
    rewrite Hfirst in Hsplit.
    destruct (cancel_pairs (boundary_pairs a b) (opens a) 0 a b
      (region (regions_of b) 0)) as [acc_ab|] eqn:Hab_cancel;
      simpl in Hsplit |- *; [|exact Hsplit].
    assert (Hq_open :
      three_way_boundary_pairs a b c <= opens a - boundary_pairs a b).
    { rewrite Hpair_ab; unfold three_way_boundary_pairs.
      destruct (le_dec (opens a - closes b) (closes c - opens b));
        [rewrite Nat.min_l by lia|rewrite Nat.min_r by lia]; lia. }
    assert (Hq_close :
      three_way_boundary_pairs a b c <= closes c - opens b).
    { unfold three_way_boundary_pairs.
      destruct (le_dec (opens a - closes b) (closes c - opens b));
        [rewrite Nat.min_l by lia|rewrite Nat.min_r by lia]; lia. }
    rewrite Hpair_ab in Hq_open.
    assert (Hsecond :
      cancel_pairs (three_way_boundary_pairs a b c)
        (opens a - boundary_pairs a b) (boundary_pairs a b)
        a (finish_replay b c replayed_bc) (m_op M acc_ab acc_bc) =
      cancel_pairs (three_way_boundary_pairs a b c)
        (opens a - boundary_pairs a b) (opens b)
        a c (m_op M acc_ab acc_bc)).
    { rewrite Hpair_ab.
      exact (cancel_pairs_from_excess_close_source
        (state:=b) (source:=c) (replayed:=replayed_bc) a
        (remaining:=three_way_boundary_pairs a b c)
        (open_count:=opens a - closes b) (m_op M acc_ab acc_bc)
        HM Hb Hc Hbc Hreplay Hq_open Hq_close). }
    rewrite Hsecond in Hsplit.
    exact Hsplit.
  Qed.

  Lemma cancel_pairs_left_outer_canonical
      (a b c replayed_ab replayed_bc : t) :
    IsMonoid M ->
    Consistent a ->
    Consistent b ->
    Consistent c ->
    depth_supported_n a b = true ->
    depth_supported_n b c = true ->
    replay_summary a b = Some replayed_ab ->
    replay_summary b c = Some replayed_bc ->
    0 < three_way_boundary_pairs a b c ->
    exists acc_ab acc_bc,
      cancel_pairs (closes b) (opens a) 0 a b
        (region (regions_of b) 0) = Some acc_ab /\
      cancel_pairs (opens b) (opens b) 0 b c
        (region (regions_of c) 0) = Some acc_bc /\
      cancel_pairs (boundary_pairs (finish_replay a b replayed_ab) c)
        (opens (finish_replay a b replayed_ab)) 0
        (finish_replay a b replayed_ab) c (region (regions_of c) 0) =
      cancel_pairs (three_way_boundary_pairs a b c)
        (opens a - closes b) (opens b) a c (m_op M acc_ab acc_bc).
  Proof.
    intros HM Ha Hb Hc Hab Hbc Hreplay_ab Hreplay_bc Hthree.
    assert (Hc_excess : opens b < closes c).
    { unfold three_way_boundary_pairs in Hthree.
      destruct (le_dec (opens a - closes b) (closes c - opens b));
        rewrite ?Nat.min_l, ?Nat.min_r in Hthree by lia; lia. }
    destruct (finish_replay_close_prefix_pivot
      (state:=b) (source:=c) (result:=replayed_bc)
      HM Hb Hc Hbc Hreplay_bc Hc_excess)
      as [acc_bc [Hcancel_bc [Hbefore_bc Hpivot_bc]]].
    destruct (cancel_pairs_left_outer_second_stage
      (a:=a) (b:=b) c (replayed_ab:=replayed_ab)
      HM Ha Hb Hab Hreplay_ab Hthree)
      as [acc_ab [Hcancel_ab Hsecond]].
    exists acc_ab, acc_bc; repeat split; try assumption.
    pose proof (cancel_pairs_left_outer_decompose
      (a:=a) (b:=b) c (replayed_ab:=replayed_ab)
      (region (regions_of c) 0)
      HM Ha Hb Hab Hreplay_ab) as Houter.
    assert (Hpair_bc : boundary_pairs b c = opens b).
    { unfold boundary_pairs; rewrite Nat.min_l by lia; reflexivity. }
    assert (Hcancel_boundary :
      cancel_pairs (boundary_pairs b c) (opens b) 0 b c
        (region (regions_of c) 0) = Some acc_bc).
    { rewrite Hpair_bc; exact Hcancel_bc. }
    rewrite Hcancel_boundary in Houter; simpl in Houter.
    rewrite (Hsecond acc_bc) in Houter.
    exact Houter.
  Qed.

  Lemma cancel_pairs_right_outer_canonical
      (a b c replayed_ab replayed_bc : t) :
    IsMonoid M ->
    Consistent a ->
    Consistent b ->
    Consistent c ->
    depth_supported_n a b = true ->
    depth_supported_n b c = true ->
    replay_summary a b = Some replayed_ab ->
    replay_summary b c = Some replayed_bc ->
    0 < three_way_boundary_pairs a b c ->
    0 < closes b ->
    exists acc_ab acc_bc,
      cancel_pairs (closes b) (opens a) 0 a b
        (region (regions_of b) 0) = Some acc_ab /\
      cancel_pairs (opens b) (opens b) 0 b c
        (region (regions_of c) 0) = Some acc_bc /\
      cancel_pairs (boundary_pairs a (finish_replay b c replayed_bc))
        (opens a) 0 a (finish_replay b c replayed_bc)
        (region (regions_of (finish_replay b c replayed_bc)) 0) =
      cancel_pairs (three_way_boundary_pairs a b c)
        (opens a - closes b) (opens b) a c (m_op M acc_ab acc_bc).
  Proof.
    intros HM Ha Hb Hc Hab Hbc Hreplay_ab Hreplay_bc Hthree Hb_closes.
    destruct (cancel_pairs_right_outer_decompose
      a (b:=b) (c:=c) (replayed_bc:=replayed_bc)
      HM Hb Hc Hbc Hreplay_bc Hthree Hb_closes)
      as [acc_bc [Hcancel_bc Houter]].
    assert (Hsurvives : closes b <= opens a).
    { unfold three_way_boundary_pairs in Hthree.
      destruct (le_dec (opens a - closes b) (closes c - opens b));
        rewrite ?Nat.min_l, ?Nat.min_r in Hthree by lia; lia. }
    destruct (finish_replay_surviving_open_pivot
      (state:=a) (source:=b) (result:=replayed_ab)
      HM Ha Hb Hab Hreplay_ab Hsurvives)
      as [acc_ab [Hcancel_ab [Hbefore_ab Hpivot_ab]]].
    exists acc_ab, acc_bc; repeat split; try assumption.
    assert (Hpair_ab : boundary_pairs a b = closes b).
    { unfold boundary_pairs; rewrite Nat.min_r by lia; reflexivity. }
    assert (Hcancel_boundary :
      cancel_pairs (boundary_pairs a b) (opens a) 0 a b
        (region (regions_of b) 0) = Some acc_ab).
    { rewrite Hpair_ab; exact Hcancel_ab. }
    rewrite Hcancel_boundary in Houter; simpl in Houter.
    rewrite Hpair_ab in Houter.
    rewrite regions_finish_replay.
    exact Houter.
  Qed.

  Corollary cancel_pairs_outer_assoc_positive
      (a b c replayed_ab replayed_bc : t) :
    IsMonoid M ->
    Consistent a ->
    Consistent b ->
    Consistent c ->
    depth_supported_n a b = true ->
    depth_supported_n b c = true ->
    replay_summary a b = Some replayed_ab ->
    replay_summary b c = Some replayed_bc ->
    0 < three_way_boundary_pairs a b c ->
    0 < closes b ->
    cancel_pairs (boundary_pairs (finish_replay a b replayed_ab) c)
      (opens (finish_replay a b replayed_ab)) 0
      (finish_replay a b replayed_ab) c (region (regions_of c) 0) =
    cancel_pairs (boundary_pairs a (finish_replay b c replayed_bc))
      (opens a) 0 a (finish_replay b c replayed_bc)
      (region (regions_of (finish_replay b c replayed_bc)) 0).
  Proof.
    intros HM Ha Hb Hc Hab Hbc Hreplay_ab Hreplay_bc Hthree Hb_closes.
    destruct (cancel_pairs_left_outer_canonical
      (a:=a) (b:=b) (c:=c) (replayed_ab:=replayed_ab)
      (replayed_bc:=replayed_bc)
      HM Ha Hb Hc Hab Hbc Hreplay_ab Hreplay_bc Hthree)
      as [acc_ab [acc_bc [Hab_acc [Hbc_acc Hleft]]]].
    destruct (cancel_pairs_right_outer_canonical
      (a:=a) (b:=b) (c:=c) (replayed_ab:=replayed_ab)
      (replayed_bc:=replayed_bc)
      HM Ha Hb Hc Hab Hbc Hreplay_ab Hreplay_bc Hthree Hb_closes)
      as [acc_ab' [acc_bc' [Hab_acc' [Hbc_acc' Hright]]]].
    rewrite Hab_acc in Hab_acc'; inversion Hab_acc'; subst acc_ab'.
    rewrite Hbc_acc in Hbc_acc'; inversion Hbc_acc'; subst acc_bc'.
    rewrite Hleft, Hright; reflexivity.
  Qed.

  Lemma cancel_pairs_right_outer_canonical_zero_closes
      (a b c replayed_bc : t) :
    IsMonoid M ->
    Consistent b ->
    Consistent c ->
    depth_supported_n b c = true ->
    replay_summary b c = Some replayed_bc ->
    0 < three_way_boundary_pairs a b c ->
    closes b = 0 ->
    exists acc_bc,
      cancel_pairs (opens b) (opens b) 0 b c
        (region (regions_of c) 0) = Some acc_bc /\
      cancel_pairs (boundary_pairs a (finish_replay b c replayed_bc))
        (opens a) 0 a (finish_replay b c replayed_bc)
        (region (regions_of (finish_replay b c replayed_bc)) 0) =
      cancel_pairs (three_way_boundary_pairs a b c)
        (opens a) (opens b) a c
        (m_op M (region (regions_of b) 0) acc_bc).
  Proof.
    intros HM Hb Hc Hbc Hreplay Hthree Hb_zero.
    assert (Hc_excess : opens b < closes c).
    { unfold three_way_boundary_pairs in Hthree.
      destruct (le_dec (opens a - closes b) (closes c - opens b));
        rewrite ?Nat.min_l, ?Nat.min_r in Hthree by lia; lia. }
    destruct (finish_replay_close_prefix_pivot
      (state:=b) (source:=c) (result:=replayed_bc)
      HM Hb Hc Hbc Hreplay Hc_excess)
      as [acc_bc [Hcancel_bc [Hbefore Hpivot]]].
    exists acc_bc; split; [exact Hcancel_bc|].
    assert (Houter :
      boundary_pairs a (finish_replay b c replayed_bc) =
        three_way_boundary_pairs a b c).
    { rewrite boundary_pairs_right_outer_decompose by assumption.
      unfold boundary_pairs; rewrite Hb_zero; simpl; lia. }
    assert (Hq_open : three_way_boundary_pairs a b c <= opens a).
    { unfold three_way_boundary_pairs; rewrite Hb_zero; simpl.
      destruct (le_dec (opens a) (closes c - opens b));
        [rewrite Nat.min_l by lia|rewrite Nat.min_r by lia]; lia. }
    assert (Hq_close :
      three_way_boundary_pairs a b c <= closes c - opens b).
    { unfold three_way_boundary_pairs.
      destruct (le_dec (opens a - closes b) (closes c - opens b));
        [rewrite Nat.min_l by lia|rewrite Nat.min_r by lia]; lia. }
    rewrite Houter.
    pose proof (cancel_pairs_from_excess_close_source
      (state:=b) (source:=c) (replayed:=replayed_bc) a
      (remaining:=three_way_boundary_pairs a b c)
      (open_count:=opens a)
      (region (regions_of (finish_replay b c replayed_bc)) 0)
      HM Hb Hc Hbc Hreplay Hq_open Hq_close) as Halign.
    rewrite Hb_zero in Halign.
    rewrite Hb_zero in Hpivot.
    rewrite Hpivot in Halign.
    rewrite Hpivot.
    exact Halign.
  Qed.

  Corollary cancel_pairs_outer_assoc_three_way_positive
      (a b c replayed_ab replayed_bc : t) :
    IsMonoid M ->
    Consistent a ->
    Consistent b ->
    Consistent c ->
    depth_supported_n a b = true ->
    depth_supported_n b c = true ->
    replay_summary a b = Some replayed_ab ->
    replay_summary b c = Some replayed_bc ->
    0 < three_way_boundary_pairs a b c ->
    cancel_pairs (boundary_pairs (finish_replay a b replayed_ab) c)
      (opens (finish_replay a b replayed_ab)) 0
      (finish_replay a b replayed_ab) c (region (regions_of c) 0) =
    cancel_pairs (boundary_pairs a (finish_replay b c replayed_bc))
      (opens a) 0 a (finish_replay b c replayed_bc)
      (region (regions_of (finish_replay b c replayed_bc)) 0).
  Proof.
    intros HM Ha Hb Hc Hab Hbc Hreplay_ab Hreplay_bc Hthree.
    destruct (Nat.eq_dec (closes b) 0) as [Hb_zero|Hb_positive].
    - destruct (cancel_pairs_left_outer_canonical
        (a:=a) (b:=b) (c:=c) (replayed_ab:=replayed_ab)
        (replayed_bc:=replayed_bc)
        HM Ha Hb Hc Hab Hbc Hreplay_ab Hreplay_bc Hthree)
        as [acc_ab [acc_bc [Hab_acc [Hbc_acc Hleft]]]].
      destruct (cancel_pairs_right_outer_canonical_zero_closes
        a (b:=b) (c:=c) (replayed_bc:=replayed_bc)
        HM Hb Hc Hbc Hreplay_bc Hthree Hb_zero)
      as [acc_bc' [Hbc_acc' Hright]].
      rewrite Hbc_acc in Hbc_acc'; inversion Hbc_acc'; subst acc_bc'.
      rewrite Hb_zero in Hab_acc; simpl in Hab_acc; inversion Hab_acc; subst.
      rewrite Hb_zero in Hleft; rewrite Nat.sub_0_r in Hleft.
      rewrite Hleft, Hright; reflexivity.
    - apply cancel_pairs_outer_assoc_positive; try assumption; lia.
  Qed.

  Theorem finish_replay_preserves_consistency
      (state source result : t) :
    Consistent state ->
    Consistent source ->
    depth_supported_n state source = true ->
    replay_summary state source = Some result ->
    Consistent (finish_replay state source result).
  Proof.
    intros Hstate Hsource Hsupported Hreplay.
    assert (Hinvariants :
      Sized result /\
      padding_neutral result /\
      active result = active (finish_replay state source result)).
    { eapply replay_summary_result_invariants; eauto. }
    destruct Hinvariants as [Hsized [Hpadding Hactive]].
    eapply finish_replay_consistent_of_replay_invariants; eauto.
  Qed.

  Lemma replay_summary_fusion_of_normal_forms
      (a b c replayed_ab replayed_bc : t) :
    IsMonoid M ->
    Consistent a ->
    Consistent b ->
    Consistent c ->
    depth_supported_n a b = true ->
    depth_supported_n b c = true ->
    replay_summary a b = Some replayed_ab ->
    replay_summary b c = Some replayed_bc ->
    ReplayEqOpt
      (replay_summary_normal_form
        (finish_replay a b replayed_ab) c)
      (replay_summary_normal_form
        a (finish_replay b c replayed_bc)) ->
    ReplayEqOpt
      (replay_summary (finish_replay a b replayed_ab) c)
      (replay_summary a (finish_replay b c replayed_bc)).
  Proof.
    intros HM Ha Hb Hc Hab Hbc Hreplay_ab Hreplay_bc Hnormal.
    assert (Hab_consistent :
      Consistent (finish_replay a b replayed_ab)).
    { eapply finish_replay_preserves_consistency; eauto. }
    pose proof
      (replay_summary_as_boundary_normal_form
        (state:=finish_replay a b replayed_ab) c HM Hab_consistent)
      as Hleft.
    pose proof
      (replay_summary_as_boundary_normal_form
        (state:=a) (finish_replay b c replayed_bc) HM Ha)
      as Hright.
    eapply ReplayEqOpt_trans; [exact Hleft|].
    eapply ReplayEqOpt_trans; [exact Hnormal|].
    apply ReplayEqOpt_sym; exact Hright.
  Qed.

  Lemma combined_depth_assoc
      (a b c replayed_ab replayed_bc : t) :
    combined_depth (finish_replay a b replayed_ab) c =
    combined_depth a (finish_replay b c replayed_bc).
  Proof.
    unfold combined_depth.
    rewrite !array_depth_finish_replay.
    apply depth_op_assoc.
  Qed.

  Lemma finish_replay_ext
      (a b c d replayed_x replayed_y : t) :
    combined_depth a b = combined_depth c d ->
    regions_of replayed_x = regions_of replayed_y ->
    finish_replay a b replayed_x = finish_replay c d replayed_y.
  Proof.
    intros Hdepth Hregions.
    unfold finish_replay.
    destruct (combined_depth a b) as [xlo xhi xnet] eqn:Hx.
    destruct (combined_depth c d) as [ylo yhi ynet] eqn:Hy.
    inversion Hdepth; subst; simpl.
    now rewrite Hregions.
  Qed.

  Lemma finish_replay_assoc_of_replay_eq
      (a b c replayed_ab replayed_bc replayed_left replayed_right : t) :
    ReplayEq replayed_left replayed_right ->
    finish_replay (finish_replay a b replayed_ab) c replayed_left =
    finish_replay a (finish_replay b c replayed_bc) replayed_right.
  Proof.
    intros [_ [_ Hregions]].
    apply finish_replay_ext.
    - apply combined_depth_assoc.
    - exact Hregions.
  Qed.

  Lemma depth_supported_n_assoc
      (a b c replayed_ab replayed_bc : t) :
    depth_supported_n (finish_replay a b replayed_ab) c =
    depth_supported_n a (finish_replay b c replayed_bc).
  Proof.
    unfold depth_supported_n.
    now rewrite (combined_depth_assoc a b c replayed_ab replayed_bc).
  Qed.

  Lemma depth_unsupported_left_propagates
      (a b c replayed_ab : t) :
    depth_supported_n a b = false ->
    depth_supported_n (finish_replay a b replayed_ab) c = false.
  Proof.
    unfold depth_supported_n, combined_depth.
    rewrite array_depth_finish_replay.
    intro Hab; apply Z.leb_gt in Hab; apply Z.leb_gt.
    eapply Z.lt_le_trans; [exact Hab|].
    apply depth_span_op_ge_l.
  Qed.

  Lemma depth_unsupported_right_propagates
      (a b c replayed_bc : t) :
    depth_supported_n b c = false ->
    depth_supported_n a (finish_replay b c replayed_bc) = false.
  Proof.
    unfold depth_supported_n, combined_depth.
    rewrite array_depth_finish_replay.
    intro Hbc; apply Z.leb_gt in Hbc; apply Z.leb_gt.
    eapply Z.lt_le_trans; [exact Hbc|].
    apply depth_span_op_ge_r.
  Qed.

  Definition finish_replay_opt
      (a b : t) (replayed : option t) : option t :=
    match replayed with
    | Some state => Some (finish_replay a b state)
    | None => None
    end.

  Lemma finish_replay_opt_assoc_of_replay_eq
      (a b c replayed_ab replayed_bc : t)
      (replayed_left replayed_right : option t) :
    ReplayEqOpt replayed_left replayed_right ->
    finish_replay_opt (finish_replay a b replayed_ab) c replayed_left =
    finish_replay_opt a (finish_replay b c replayed_bc) replayed_right.
  Proof.
    destruct replayed_left as [replayed_left|],
      replayed_right as [replayed_right|]; simpl; try contradiction;
      [|reflexivity].
    intro Heq.
    f_equal.
    now apply finish_replay_assoc_of_replay_eq.
  Qed.

  Lemma parens_n_op_as_replay_summary (a b : t) :
    parens_n_op (Some a) (Some b) =
      if depth_supported_n a b then
        match replay_summary a b with
        | Some replayed => Some (finish_replay a b replayed)
        | None => None
        end
      else None.
  Proof.
    unfold parens_n_op, depth_supported_n, combined_depth, array_depth,
      depth_span, depth_op, zmin, zmax, replay_summary, finish_replay;
      simpl.
    destruct (Z.ltb (Z.of_nat N)
      (Z.max (hi a) (net a + hi b) -
       Z.min (lo a) (net a + lo b))) eqn:Hlt.
    - apply Z.ltb_lt in Hlt.
      destruct (Z.leb
        (Z.max (hi a) (net a + hi b) -
         Z.min (lo a) (net a + lo b)) (Z.of_nat N)) eqn:Hle.
      + apply Z.leb_le in Hle; lia.
      + reflexivity.
    - apply Z.ltb_ge in Hlt.
      destruct (Z.leb
        (Z.max (hi a) (net a + hi b) -
         Z.min (lo a) (net a + lo b)) (Z.of_nat N)) eqn:Hle.
      + destruct (replay_closes (closes b) 0 b
          (Some (append_region a (region (regions_of b) 0))))
          as [after_closes|] eqn:Hcloses; simpl; [|reflexivity].
        destruct (replay_opens (opens b) 0 b (Some after_closes));
          reflexivity.
      + apply Z.leb_gt in Hle; lia.
  Qed.

  Lemma parens_n_op_as_guarded_replay (a b : t) :
    parens_n_op (Some a) (Some b) =
      if depth_supported_n a b then
        finish_replay_opt a b (replay_summary a b)
      else None.
  Proof.
    rewrite parens_n_op_as_replay_summary.
    destruct (depth_supported_n a b); [|reflexivity].
    unfold finish_replay_opt.
    destruct (replay_summary a b); reflexivity.
  Qed.

  Corollary parens_n_op_some_consistent
      (a b result : t) :
    Consistent a ->
    Consistent b ->
    parens_n_op (Some a) (Some b) = Some result ->
    Consistent result.
  Proof.
    intros Ha Hb Hop.
    rewrite parens_n_op_as_guarded_replay in Hop.
    destruct (depth_supported_n a b) eqn:Hsupported; try discriminate.
    unfold finish_replay_opt in Hop.
    destruct (replay_summary a b) as [replayed|] eqn:Hreplay;
      try discriminate.
    inversion Hop; subst result.
    eapply finish_replay_preserves_consistency; eauto.
  Qed.

  Theorem parens_n_op_preserves_consistency (a b : option t) :
    ConsistentOpt a ->
    ConsistentOpt b ->
    ConsistentOpt (parens_n_op a b).
  Proof.
    destruct a as [a|], b as [b|].
    - change (Consistent a -> Consistent b ->
        ConsistentOpt (parens_n_op (Some a) (Some b))).
      intros Ha Hb.
      destruct (parens_n_op (Some a) (Some b)) as [result|] eqn:Hop.
      + change (Consistent result).
        exact (parens_n_op_some_consistent (a:=a) (b:=b) Ha Hb Hop).
      + exact I.
    - simpl; easy.
    - simpl; easy.
    - simpl; easy.
  Qed.

  Lemma parens_n_op_assoc_of_replay_fusion
      (a b c replayed_ab replayed_bc : t) :
    depth_supported_n a b = true ->
    depth_supported_n b c = true ->
    replay_summary a b = Some replayed_ab ->
    replay_summary b c = Some replayed_bc ->
    ReplayEqOpt
      (replay_summary (finish_replay a b replayed_ab) c)
      (replay_summary a (finish_replay b c replayed_bc)) ->
    parens_n_op (parens_n_op (Some a) (Some b)) (Some c) =
    parens_n_op (Some a) (parens_n_op (Some b) (Some c)).
  Proof.
    intros Hab Hbc Hreplay_ab Hreplay_bc Hfusion.
    rewrite (parens_n_op_as_guarded_replay a b), Hab.
    unfold finish_replay_opt at 1.
    rewrite Hreplay_ab.
    rewrite (parens_n_op_as_guarded_replay b c), Hbc.
    unfold finish_replay_opt at 1.
    rewrite Hreplay_bc.
    rewrite
      (parens_n_op_as_guarded_replay
        (finish_replay a b replayed_ab) c),
      (parens_n_op_as_guarded_replay
        a (finish_replay b c replayed_bc)).
    rewrite (depth_supported_n_assoc a b c replayed_ab replayed_bc).
    destruct (depth_supported_n a (finish_replay b c replayed_bc));
      [apply finish_replay_opt_assoc_of_replay_eq; exact Hfusion|reflexivity].
  Qed.

  (** The remaining associativity argument is split according to whether a
      cancellation crosses both internal boundaries.  These three lemmas
      are the local region-layout obligations.  Keeping them separate makes
      the subsequent assembly independent of the representation details of
      [regions]. *)
  Lemma replay_summary_normal_forms_assoc_three_way_positive_open
      (a b c replayed_ab replayed_bc : t) :
    IsMonoid M ->
    Consistent a ->
    Consistent b ->
    Consistent c ->
    depth_supported_n a b = true ->
    depth_supported_n b c = true ->
    replay_summary a b = Some replayed_ab ->
    replay_summary b c = Some replayed_bc ->
    0 < three_way_boundary_pairs a b c ->
    closes c <= opens (finish_replay a b replayed_ab) ->
    ReplayEqOpt
      (replay_summary_normal_form (finish_replay a b replayed_ab) c)
      (replay_summary_normal_form
        a (finish_replay b c replayed_bc)).
  Proof.
    intros HM Ha Hb Hc Hab Hbc Hreplay_ab Hreplay_bc Hpositive Hopen.
    assert (Hopen_right :
      closes (finish_replay b c replayed_bc) <= opens a).
    { apply (proj1 (positive_outer_open_branch_assoc_iff
        (a:=a) (b:=b) (c:=c) replayed_ab replayed_bc
        Ha Hb Hc Hpositive)); exact Hopen. }
    rewrite replay_summary_normal_form_open by exact Hopen.
    rewrite replay_summary_normal_form_open by exact Hopen_right.
    pose proof (cancel_pairs_outer_assoc_three_way_positive
      (a:=a) (b:=b) (c:=c)
      (replayed_ab:=replayed_ab) (replayed_bc:=replayed_bc)
      HM Ha Hb Hc Hab Hbc Hreplay_ab Hreplay_bc Hpositive) as Hcancel.
    unfold boundary_pairs in Hcancel.
    rewrite Nat.min_r in Hcancel by exact Hopen.
    rewrite Nat.min_r in Hcancel by exact Hopen_right.
    rewrite Hcancel.
    destruct (cancel_pairs (closes (finish_replay b c replayed_bc))
      (opens a) 0 a (finish_replay b c replayed_bc)
      (region (regions_of (finish_replay b c replayed_bc)) 0))
      as [acc|] eqn:Hacc; simpl; [|exact I].
    apply positive_trailing_open_replay_eq
      with (a:=a) (b:=b) (c:=c) (replayed_bc:=replayed_bc);
      try assumption.
    apply positive_open_residual_replay_eq
      with (a:=a) (b:=b) (c:=c)
        (replayed_ab:=replayed_ab) (replayed_bc:=replayed_bc);
      assumption.
  Qed.

  Lemma replay_summary_normal_forms_assoc_three_way_positive_close
      (a b c replayed_ab replayed_bc : t) :
    IsMonoid M ->
    Consistent a ->
    Consistent b ->
    Consistent c ->
    depth_supported_n a b = true ->
    depth_supported_n b c = true ->
    replay_summary a b = Some replayed_ab ->
    replay_summary b c = Some replayed_bc ->
    0 < three_way_boundary_pairs a b c ->
    opens (finish_replay a b replayed_ab) < closes c ->
    ReplayEqOpt
      (replay_summary_normal_form (finish_replay a b replayed_ab) c)
      (replay_summary_normal_form
        a (finish_replay b c replayed_bc)).
  Proof.
    intros HM Ha Hb Hc Hab Hbc Hreplay_ab Hreplay_bc Hpositive Hclose.
    assert (Hclose_right :
      opens a < closes (finish_replay b c replayed_bc)).
    { apply (proj1 (positive_outer_close_branch_assoc_iff
        (a:=a) (b:=b) (c:=c) replayed_ab replayed_bc
        Ha Hb Hc Hpositive)); exact Hclose. }
    rewrite replay_summary_normal_form_close by exact Hclose.
    rewrite replay_summary_normal_form_close by exact Hclose_right.
    pose proof (cancel_pairs_outer_assoc_three_way_positive
      (a:=a) (b:=b) (c:=c)
      (replayed_ab:=replayed_ab) (replayed_bc:=replayed_bc)
      HM Ha Hb Hc Hab Hbc Hreplay_ab Hreplay_bc Hpositive) as Hcancel.
    unfold boundary_pairs in Hcancel.
    rewrite Nat.min_l in Hcancel by lia.
    rewrite Nat.min_l in Hcancel by lia.
    rewrite Hcancel.
    destruct (cancel_pairs (opens a) (opens a) 0 a
      (finish_replay b c replayed_bc)
      (region (regions_of (finish_replay b c replayed_bc)) 0))
      as [acc|] eqn:Hacc; simpl; [|exact I].
    apply positive_trailing_open_replay_eq_direct
      with (a:=a) (b:=b) (c:=c) (replayed_bc:=replayed_bc);
      try assumption.
    apply positive_close_residual_replay_eq
      with (a:=a) (b:=b) (c:=c)
        (replayed_ab:=replayed_ab) (replayed_bc:=replayed_bc);
      assumption.
  Qed.

  Lemma replay_summary_normal_forms_assoc_three_way_positive
      (a b c replayed_ab replayed_bc : t) :
    IsMonoid M ->
    Consistent a ->
    Consistent b ->
    Consistent c ->
    depth_supported_n a b = true ->
    depth_supported_n b c = true ->
    replay_summary a b = Some replayed_ab ->
    replay_summary b c = Some replayed_bc ->
    0 < three_way_boundary_pairs a b c ->
    ReplayEqOpt
      (replay_summary_normal_form (finish_replay a b replayed_ab) c)
      (replay_summary_normal_form
        a (finish_replay b c replayed_bc)).
  Proof.
    intros HM Ha Hb Hc Hab Hbc Hreplay_ab Hreplay_bc Hpositive.
    destruct (le_dec (closes c)
      (opens (finish_replay a b replayed_ab))) as [Hopen|Hclose].
    - eapply replay_summary_normal_forms_assoc_three_way_positive_open;
        eauto.
    - eapply replay_summary_normal_forms_assoc_three_way_positive_close;
        eauto; lia.
  Qed.

  Lemma replay_summary_assoc_three_way_positive
      (a b c replayed_ab replayed_bc : t) :
    IsMonoid M ->
    Consistent a ->
    Consistent b ->
    Consistent c ->
    depth_supported_n a b = true ->
    depth_supported_n b c = true ->
    replay_summary a b = Some replayed_ab ->
    replay_summary b c = Some replayed_bc ->
    0 < three_way_boundary_pairs a b c ->
    ReplayEqOpt
      (replay_summary (finish_replay a b replayed_ab) c)
      (replay_summary a (finish_replay b c replayed_bc)).
  Proof.
    intros HM Ha Hb Hc Hab Hbc Hreplay_ab Hreplay_bc Hpositive.
    eapply replay_summary_fusion_of_normal_forms; eauto.
    eapply replay_summary_normal_forms_assoc_three_way_positive; eauto.
  Qed.

  Lemma finish_replay_matches_result (a b ab : t) :
    Consistent a -> Consistent b -> depth_supported_n a b = true ->
    replay_summary a b = Some ab -> ReplayEq (finish_replay a b ab) ab.
  Proof.
    intros Ha Hb Hd Hr.
    destruct (replay_summary_close_phase_invariants Ha Hb Hd Hr)
      as [s [Hcl [Hop [Hsz [Hlo [Hord [Hpad Hroom]]]]]]].
    pose proof Ha as [_ [[Halo [_ [Haord _]]] _]].
    destruct (replay_closes_counts (closes b) 0 b
      (append_region a (region (regions_of b) 0))
      Halo Haord Hcl) as [Hopens Hcloses].
    rewrite append_region_closes, append_region_opens in Hcloses.
    pose proof (replay_opens_result_lo (opens b) 0 b s Hord Hop) as Habl.
    destruct (replay_opens_result_invariants (opens b) 0 b Hop Hord Hpad)
      as [Habord [Habactive _]].
    pose proof (finish_replay_depth_consistent (a:=a) (b:=b) ab Ha Hb Hd)
      as [Hfl [_ [Hford _]]].
    assert (Hcloseeq : closes (finish_replay a b ab) = closes s).
    { rewrite closes_finish_replay_consistent by assumption; lia. }
    pose proof (closes_as_depth (finish_replay a b ab) Hfl) as Hfd.
    pose proof (closes_as_depth s Hlo) as Hsd.
    rewrite Hcloseeq in Hfd.
    assert (Hleq : lo (finish_replay a b ab) = lo ab) by lia.
    destruct (replay_summary_result_invariants Ha Hb Hd Hr)
      as [_ [_ Hactive]].
    pose proof (opens_as_depth (finish_replay a b ab) Hford) as Hfo.
    pose proof (opens_as_depth ab Habord) as Hao.
    assert (Hceq : closes (finish_replay a b ab) = closes ab).
    { unfold closes; rewrite Hleq; reflexivity. }
    unfold active in Hactive.
    assert (Hoeq : opens (finish_replay a b ab) = opens ab) by lia.
    rewrite Hoeq in Hfo.
    unfold ReplayEq; split; [exact Hleq|].
    split; [lia|apply regions_finish_replay].
  Qed.

  Lemma replay_summary_normal_forms_assoc_right_blocked_strict
      (a b c ab bc : t) :
    IsMonoid M -> Consistent a -> Consistent b -> Consistent c ->
    depth_supported_n a b = true -> depth_supported_n b c = true ->
    replay_summary a b = Some ab -> replay_summary b c = Some bc ->
    closes c < opens b ->
    ReplayEqOpt
      (replay_summary_normal_form (finish_replay a b ab) c)
      (replay_summary_normal_form a (finish_replay b c bc)).
  Proof.
    intros HM Ha Hb Hc Hdab Hdbc Hab Hbc Hstrict.
    destruct (replay_summary_close_phase_invariants Ha Hb Hdab Hab)
      as [s [Hs [Hop [Hsize [Hslo [Hsord [Hpad Hroom]]]]]]].
    destruct (finish_replay_surviving_open_pivot
      (state:=b) (source:=c) (result:=bc) HM Hb Hc Hdbc Hbc ltac:(lia))
      as [acc [Hacc _]].
    set (residual := replay_opens (opens b - closes c) 0 b (Some s)).
    set (staged := option_bind residual
      (fun t => replay_opens (opens c) 0 c (Some (append_region t acc)))).
    assert (Hleftcl : ReplayEqOpt
      (replay_closes (closes c) 0 c
        (Some (append_region ab (region (regions_of c) 0))))
      (option_bind residual (fun t => Some (append_region t acc)))).
    { pose proof (replay_cancel_prefix
        (k:=closes c) (p:=opens b) 0 0 b c (base:=s)
        (region (regions_of c) 0) ltac:(lia) HM Hsize Hsord Hpad) as H.
      assert (Hbound : active s + opens b < 2*N+1).
      { unfold Sized, regions_well_sized in Hsize; lia. }
      specialize (H Hbound).
      simpl in H; rewrite Hop, Hacc in H; exact H. }
    assert (Hleft : ReplayEqOpt (replay_summary ab c) staged).
    { unfold replay_summary, staged.
      destruct (replay_closes (closes c) 0 c
        (Some (append_region ab (region (regions_of c) 0)))) as [l|],
        residual as [r|]; simpl in Hleftcl |- *; try contradiction.
      - apply replay_opens_replay_eq; [apply ReplayEq_refl|exact Hleftcl].
      - exact I. }
    assert (Hclose : ReplayEqOpt
      (replay_closes (closes (finish_replay b c bc)) 0
        (finish_replay b c bc)
        (Some (append_region a (region (regions_of (finish_replay b c bc)) 0))))
      (Some s)).
    { rewrite <- Hs.
      rewrite closes_finish_replay_right_blocked by (try assumption; lia).
      apply replay_closes_extensional.
      - rewrite (finish_replay_surviving_open_prefix
          (state:=b) (source:=c) (result:=bc)
          HM Hb Hc Hdbc Hbc Hstrict (i:=0) ltac:(lia)).
        apply ReplayEqOpt_refl.
      - intros r Hr.
        apply finish_replay_surviving_open_prefix; try assumption; lia. }
    assert (Hright : ReplayEqOpt
      (replay_summary a (finish_replay b c bc)) staged).
    { eapply ReplayEqOpt_trans with
        (y:=replay_opens (opens (finish_replay b c bc)) 0
          (finish_replay b c bc) (Some s)).
      - unfold replay_summary.
        destruct (replay_closes (closes (finish_replay b c bc)) 0
          (finish_replay b c bc)
          (Some (append_region a
            (region (regions_of (finish_replay b c bc)) 0))))
          as [right_close|]; simpl in Hclose; [|contradiction].
        apply replay_opens_replay_eq; [apply ReplayEq_refl|exact Hclose].
      - unfold staged, residual.
        apply right_blocked_open_replay_decompose; try assumption; lia. }
    assert (Hfab : Consistent (finish_replay a b ab)).
    { apply finish_replay_preserves_consistency; assumption. }
    eapply ReplayEqOpt_trans.
    - apply ReplayEqOpt_sym, replay_summary_as_boundary_normal_form;
        assumption.
    - eapply ReplayEqOpt_trans with (y:=replay_summary ab c).
      + apply replay_summary_replay_eq.
        * apply finish_replay_matches_result; assumption.
        * apply ReplayEq_refl.
      + eapply ReplayEqOpt_trans; [exact Hleft|].
        eapply ReplayEqOpt_trans; [apply ReplayEqOpt_sym; exact Hright|].
        apply replay_summary_as_boundary_normal_form; assumption.
  Qed.

  Lemma finish_replay_equal_boundary_close_layout (b c bc : t)
      (acc : m_summary M) :
    IsMonoid M -> Consistent b -> Consistent c ->
    depth_supported_n b c = true -> replay_summary b c = Some bc ->
    closes c = opens b ->
    cancel_pairs (closes c) (opens b) 0 b c
      (region (regions_of c) 0) = Some acc ->
    (forall i, i < closes b ->
      region (regions_of (finish_replay b c bc)) i = region (regions_of b) i) /\
    region (regions_of (finish_replay b c bc)) (closes b) =
      m_op M (region (regions_of b) (closes b)) acc.
  Proof.
    intros HM Hb Hc Hd Hr Heq Hcancel.
    destruct (replay_summary_open_suffix_layout
      (state:=b) (source:=c) (result:=bc) HM Hb Hc Hd Hr)
      as [s [Hs [Hactive [Hprefix Hsuffix]]]].
    pose proof (replay_closes_as_boundary_normal_form c
      (region (regions_of c) 0) HM Hb) as Hnormal.
    rewrite Hs, close_boundary_normal_form_open in Hnormal by lia.
    rewrite Hcancel in Hnormal.
    replace (opens b - closes c) with 0 in Hnormal by lia.
    simpl in Hnormal.
    destruct Hnormal as [_ [_ Hregions]].
    pose proof Hb as [Hsize [[Hlo _] [Hbound _]]].
    assert (Hroom : active (open_base b) < size (regions_of (open_base b))).
    { pose proof (open_base_sized Hsize) as Hsz.
      unfold Sized, regions_well_sized in Hsz.
      rewrite Hsz, open_base_active by assumption.
      unfold active in Hbound; lia. }
    assert (Hsactive : active s = closes b) by lia.
    split.
    - intros i Hi.
      rewrite regions_finish_replay, Hprefix by lia.
      rewrite Hregions, append_region_before_active.
      + apply open_base_agrees; lia.
      + rewrite open_base_active by assumption; lia.
    - rewrite regions_finish_replay, Hprefix by lia.
      rewrite Hregions.
      pose proof (append_region_at_active (open_base b) acc Hroom) as H.
      rewrite open_base_active in H by assumption.
      rewrite H.
      rewrite open_base_agrees by lia; reflexivity.
  Qed.

  Lemma equal_boundary_close_phase (a b c bc s : t) (acc : m_summary M) :
    IsMonoid M -> Consistent a -> Consistent b -> Consistent c ->
    depth_supported_n b c = true -> replay_summary b c = Some bc ->
    closes c = opens b ->
    cancel_pairs (closes c) (opens b) 0 b c
      (region (regions_of c) 0) = Some acc ->
    replay_closes (closes b) 0 b
      (Some (append_region a (region (regions_of b) 0))) = Some s ->
    active s < size (regions_of s) ->
    ReplayEqOpt
      (replay_closes (closes (finish_replay b c bc)) 0
        (finish_replay b c bc)
        (Some (append_region a (region (regions_of (finish_replay b c bc)) 0))))
      (Some (append_region s acc)).
  Proof.
    intros HM Ha Hb Hc Hd Hr Heq Hcancel Hs Hroom.
    destruct (finish_replay_equal_boundary_close_layout
      (b:=b) (c:=c) (bc:=bc) (acc:=acc) HM Hb Hc Hd Hr Heq Hcancel)
      as [Hprefix Hpivot].
    rewrite closes_finish_replay_right_blocked by (try assumption; lia).
    destruct (closes b) as [|p] eqn:Hcount.
    - simpl in Hs |- *; inversion Hs; subst s.
      rewrite regions_finish_replay in Hpivot.
      rewrite Hpivot.
      rewrite append_region_assoc; [apply ReplayEq_refl|exact HM|].
      pose proof Ha as [Hsize [_ [Hbound _]]].
      unfold Sized, regions_well_sized in Hsize; lia.
    - rewrite Hprefix by lia.
      assert (H : ReplayEqOpt
        (replay_closes (S p) 0 (finish_replay b c bc)
          (Some (append_region a (region (regions_of b) 0))))
        (option_bind (replay_closes (S p) 0 b
          (Some (append_region a (region (regions_of b) 0))))
          (fun s => Some (append_region s acc)))).
      { apply replay_closes_close_pivot_assoc; try assumption.
        - intros r Hrr; apply Hprefix; lia.
        - intros before after Hbefore Hafter.
          pose proof Hs as Hlast.
          rewrite replay_closes_last, Hbefore, Hafter in Hlast.
          inversion Hlast; subst s.
          rewrite append_region_active in Hroom.
          unfold append_region in Hroom; simpl in Hroom.
          rewrite put_region_length in Hroom; exact Hroom. }
      rewrite Hs in H; exact H.
  Qed.

  Lemma replay_summary_normal_forms_assoc_right_blocked_equal
      (a b c replayed_ab replayed_bc : t) :
    IsMonoid M ->
    Consistent a ->
    Consistent b ->
    Consistent c ->
    depth_supported_n a b = true ->
    depth_supported_n b c = true ->
    replay_summary a b = Some replayed_ab ->
    replay_summary b c = Some replayed_bc ->
    closes c = opens b ->
    ReplayEqOpt
      (replay_summary_normal_form (finish_replay a b replayed_ab) c)
      (replay_summary_normal_form
        a (finish_replay b c replayed_bc)).
  Proof.
    intros HM Ha Hb Hc Hdab Hdbc Hab Hbc Heq.
    rename replayed_ab into ab; rename replayed_bc into bc.
    destruct (replay_summary_close_phase_invariants Ha Hb Hdab Hab)
      as [s [Hs [Hop [Hsize [Hslo [Hsord [Hpad Hroom]]]]]]].
    destruct (finish_replay_surviving_open_pivot
      (state:=b) (source:=c) (result:=bc) HM Hb Hc Hdbc Hbc ltac:(lia))
      as [acc [Hacc _]].
    assert (Hleftcl : ReplayEqOpt
      (replay_closes (closes c) 0 c
        (Some (append_region ab (region (regions_of c) 0))))
      (Some (append_region s acc))).
    { pose proof (replay_cancel_prefix
        (k:=closes c) (p:=opens b) 0 0 b c (base:=s)
        (region (regions_of c) 0) ltac:(lia) HM Hsize Hsord Hpad) as H.
      assert (Hbound : active s + opens b < 2*N+1).
      { unfold Sized, regions_well_sized in Hsize; lia. }
      specialize (H Hbound).
      simpl in H; rewrite Hop, Hacc in H.
      replace (opens b - closes c) with 0 in H by lia; exact H. }
    assert (Hrightcl : ReplayEqOpt
      (replay_closes (closes (finish_replay b c bc)) 0 (finish_replay b c bc)
        (Some (append_region a (region (regions_of (finish_replay b c bc)) 0))))
      (Some (append_region s acc))).
    { apply equal_boundary_close_phase; try assumption; lia. }
    assert (Hraw : ReplayEqOpt (replay_summary ab c)
      (replay_summary a (finish_replay b c bc))).
    { unfold replay_summary.
      destruct (replay_closes (closes c) 0 c
        (Some (append_region ab (region (regions_of c) 0)))) as [l|],
        (replay_closes (closes (finish_replay b c bc)) 0 (finish_replay b c bc)
          (Some (append_region a (region (regions_of (finish_replay b c bc)) 0))))
          as [r|]; simpl in Hleftcl, Hrightcl; try contradiction.
      rewrite opens_finish_replay_consistent by assumption.
      replace (opens b - closes c) with 0 by lia.
      rewrite Nat.add_0_r.
      apply ReplayEqOpt_sym.
      pose proof (right_blocked_trailing_open_replay
        (b:=b) (c:=c) (bc:=bc) (Some r) (Some l)
        HM Hb Hc Hdbc Hbc ltac:(lia)) as H.
      replace (opens b - closes c) with 0 in H by lia.
      apply H; simpl.
      eapply ReplayEq_trans; [exact Hrightcl|].
      apply ReplayEq_sym; exact Hleftcl. }
    assert (Hfab : Consistent (finish_replay a b ab)).
    { apply finish_replay_preserves_consistency; assumption. }
    eapply ReplayEqOpt_trans.
    - apply ReplayEqOpt_sym, replay_summary_as_boundary_normal_form; assumption.
    - eapply ReplayEqOpt_trans with (y:=replay_summary ab c).
      + apply replay_summary_replay_eq.
        * apply finish_replay_matches_result; assumption.
        * apply ReplayEq_refl.
      + eapply ReplayEqOpt_trans; [exact Hraw|].
        apply replay_summary_as_boundary_normal_form; assumption.
  Qed.

  Lemma replay_summary_normal_forms_assoc_zero_right_blocked_core
      (a b c replayed_ab replayed_bc : t) :
    IsMonoid M -> Consistent a -> Consistent b -> Consistent c ->
    depth_supported_n a b = true -> depth_supported_n b c = true ->
    replay_summary a b = Some replayed_ab ->
    replay_summary b c = Some replayed_bc ->
    closes c <= opens b ->
    ReplayEqOpt
      (replay_summary_normal_form (finish_replay a b replayed_ab) c)
      (replay_summary_normal_form a (finish_replay b c replayed_bc)).
  Proof.
    intros HM Ha Hb Hc Hab Hbc Hreplay_ab Hreplay_bc Hblocked.
    destruct (lt_dec (closes c) (opens b)) as [Hstrict|Heq].
    - apply replay_summary_normal_forms_assoc_right_blocked_strict; assumption.
    - apply replay_summary_normal_forms_assoc_right_blocked_equal;
        try assumption; lia.
  Qed.

  Lemma replay_summary_normal_forms_assoc_zero_left_blocked_open
      (a b c replayed_ab replayed_bc : t) :
    IsMonoid M ->
    Consistent a ->
    Consistent b ->
    Consistent c ->
    depth_supported_n a b = true ->
    depth_supported_n b c = true ->
    replay_summary a b = Some replayed_ab ->
    replay_summary b c = Some replayed_bc ->
    opens a <= closes b ->
    closes c <= opens b ->
    ReplayEqOpt
      (replay_summary_normal_form (finish_replay a b replayed_ab) c)
      (replay_summary_normal_form
        a (finish_replay b c replayed_bc)).
  Proof.
    intros HM Ha Hb Hc Hab Hbc Hreplay_ab Hreplay_bc Hleft Hright.
    eapply replay_summary_normal_forms_assoc_zero_right_blocked_core;
      eauto.
  Qed.

  Lemma replay_summary_normal_forms_assoc_zero_left_blocked_close
      (a b c replayed_ab replayed_bc : t) :
    IsMonoid M ->
    Consistent a ->
    Consistent b ->
    Consistent c ->
    depth_supported_n a b = true ->
    depth_supported_n b c = true ->
    replay_summary a b = Some replayed_ab ->
    replay_summary b c = Some replayed_bc ->
    opens a <= closes b ->
    opens b < closes c ->
    ReplayEqOpt
      (replay_summary_normal_form (finish_replay a b replayed_ab) c)
      (replay_summary_normal_form
        a (finish_replay b c replayed_bc)).
  Proof.
    intros HM Ha Hb Hc Hab Hbc Hreplay_ab Hreplay_bc Hblocked Hclose.
    destruct (lt_dec (opens a) (closes b)) as [Hstrict|Hpivot].
    - apply replay_summary_normal_forms_assoc_zero_left_blocked_close_strict;
        assumption.
    - apply replay_summary_normal_forms_assoc_zero_left_blocked_close_pivot;
        try assumption; lia.
  Qed.

  Lemma replay_summary_normal_forms_assoc_zero_left_blocked
      (a b c replayed_ab replayed_bc : t) :
    IsMonoid M ->
    Consistent a ->
    Consistent b ->
    Consistent c ->
    depth_supported_n a b = true ->
    depth_supported_n b c = true ->
    replay_summary a b = Some replayed_ab ->
    replay_summary b c = Some replayed_bc ->
    opens a <= closes b ->
    ReplayEqOpt
      (replay_summary_normal_form (finish_replay a b replayed_ab) c)
      (replay_summary_normal_form
        a (finish_replay b c replayed_bc)).
  Proof.
    intros HM Ha Hb Hc Hab Hbc Hreplay_ab Hreplay_bc Hblocked.
    destruct (le_dec (closes c) (opens b)) as [Hopen|Hclose].
    - eapply replay_summary_normal_forms_assoc_zero_left_blocked_open;
        eauto.
    - eapply replay_summary_normal_forms_assoc_zero_left_blocked_close;
        eauto; lia.
  Qed.

  Lemma replay_summary_assoc_zero_left_blocked
      (a b c replayed_ab replayed_bc : t) :
    IsMonoid M ->
    Consistent a ->
    Consistent b ->
    Consistent c ->
    depth_supported_n a b = true ->
    depth_supported_n b c = true ->
    replay_summary a b = Some replayed_ab ->
    replay_summary b c = Some replayed_bc ->
    opens a <= closes b ->
    ReplayEqOpt
      (replay_summary (finish_replay a b replayed_ab) c)
      (replay_summary a (finish_replay b c replayed_bc)).
  Proof.
    intros HM Ha Hb Hc Hab Hbc Hreplay_ab Hreplay_bc Hblocked.
    eapply replay_summary_fusion_of_normal_forms; eauto.
    eapply replay_summary_normal_forms_assoc_zero_left_blocked; eauto.
  Qed.

  Lemma replay_summary_normal_forms_assoc_zero_right_blocked
      (a b c replayed_ab replayed_bc : t) :
    IsMonoid M ->
    Consistent a ->
    Consistent b ->
    Consistent c ->
    depth_supported_n a b = true ->
    depth_supported_n b c = true ->
    replay_summary a b = Some replayed_ab ->
    replay_summary b c = Some replayed_bc ->
    closes c <= opens b ->
    ReplayEqOpt
      (replay_summary_normal_form (finish_replay a b replayed_ab) c)
      (replay_summary_normal_form
        a (finish_replay b c replayed_bc)).
  Proof.
    intros HM Ha Hb Hc Hab Hbc Hreplay_ab Hreplay_bc Hblocked.
    eapply replay_summary_normal_forms_assoc_zero_right_blocked_core;
      eauto.
  Qed.

  Lemma replay_summary_assoc_zero_right_blocked
      (a b c replayed_ab replayed_bc : t) :
    IsMonoid M ->
    Consistent a ->
    Consistent b ->
    Consistent c ->
    depth_supported_n a b = true ->
    depth_supported_n b c = true ->
    replay_summary a b = Some replayed_ab ->
    replay_summary b c = Some replayed_bc ->
    closes c <= opens b ->
    ReplayEqOpt
      (replay_summary (finish_replay a b replayed_ab) c)
      (replay_summary a (finish_replay b c replayed_bc)).
  Proof.
    intros HM Ha Hb Hc Hab Hbc Hreplay_ab Hreplay_bc Hblocked.
    eapply replay_summary_fusion_of_normal_forms; eauto.
    eapply replay_summary_normal_forms_assoc_zero_right_blocked; eauto.
  Qed.

  Lemma replay_summary_assoc_successful
      (a b c replayed_ab replayed_bc : t) :
    IsMonoid M ->
    Consistent a ->
    Consistent b ->
    Consistent c ->
    depth_supported_n a b = true ->
    depth_supported_n b c = true ->
    replay_summary a b = Some replayed_ab ->
    replay_summary b c = Some replayed_bc ->
    ReplayEqOpt
      (replay_summary (finish_replay a b replayed_ab) c)
      (replay_summary a (finish_replay b c replayed_bc)).
  Proof.
    intros HM Ha Hb Hc Hab Hbc Hreplay_ab Hreplay_bc.
    destruct (Nat.eq_dec (three_way_boundary_pairs a b c) 0)
      as [Hzero|Hpositive].
    - apply three_way_boundary_pairs_zero_iff in Hzero.
      destruct Hzero as [Hleft|Hright].
      + eapply replay_summary_assoc_zero_left_blocked; eauto.
      + eapply replay_summary_assoc_zero_right_blocked; eauto.
    - eapply replay_summary_assoc_three_way_positive; eauto; lia.
  Qed.

  Corollary parens_n_op_assoc_successful
      (a b c replayed_ab replayed_bc : t) :
    IsMonoid M ->
    Consistent a ->
    Consistent b ->
    Consistent c ->
    depth_supported_n a b = true ->
    depth_supported_n b c = true ->
    replay_summary a b = Some replayed_ab ->
    replay_summary b c = Some replayed_bc ->
    parens_n_op (parens_n_op (Some a) (Some b)) (Some c) =
    parens_n_op (Some a) (parens_n_op (Some b) (Some c)).
  Proof.
    intros HM Ha Hb Hc Hab Hbc Hreplay_ab Hreplay_bc.
    apply parens_n_op_assoc_of_replay_fusion
      with (replayed_ab:=replayed_ab) (replayed_bc:=replayed_bc);
      try assumption.
    eapply replay_summary_assoc_successful; eauto.
  Qed.

  (** Besides successful replay fusion, associativity requires failure to be
      independent of the association order.  This is deliberately isolated
      from the region-layout proof above. *)
  Lemma replay_closes_no_open_succeeds remaining j source state :
    (lo state <= 0)%Z -> (lo state <= net state)%Z -> opens state = 0 ->
    exists result, replay_closes remaining j source (Some state) = Some result.
  Proof.
    revert j state; induction remaining as [|remaining IH]; intros j state Hl Ho Hz.
    - exists state; reflexivity.
    - assert (Hex : exists next, append_close state = Some next).
      { unfold append_close; rewrite Hz; simpl; eauto. }
      destruct Hex as [next Hnext].
      simpl; rewrite Hnext.
      apply IH.
      + simpl; eapply append_close_lo_nonpos; eauto.
      + simpl; eapply append_close_lo_net; eauto.
      + rewrite append_region_opens.
        exact (proj2 (append_close_counts_no_open state Hl Ho Hz Hnext)).
  Qed.

  Lemma replay_summary_failure_iff_cancel (b c : t) :
    IsMonoid M -> Consistent b ->
    (replay_summary b c = None <->
     cancel_pairs (boundary_pairs b c) (opens b) 0 b c
       (region (regions_of c) 0) = None).
  Proof.
    intros HM Hb.
    pose proof (replay_summary_as_boundary_normal_form c HM Hb) as Hnormal.
    destruct (le_dec (closes c) (opens b)) as [Hle|Hlt].
    - rewrite replay_summary_normal_form_open in Hnormal by assumption.
      unfold boundary_pairs; rewrite Nat.min_r by lia.
      destruct (cancel_pairs (closes c) (opens b) 0 b c
        (region (regions_of c) 0)) as [acc|] eqn:Hcancel.
      + destruct (replay_opens (opens b - closes c) 0 b (Some (open_base b)))
          as [after|] eqn:Hr.
        2: { apply replay_opens_none_iff in Hr; discriminate. }
        simpl in Hnormal.
        destruct (replay_opens (opens c) 0 c (Some (append_region after acc)))
          eqn:Hlast.
        2: { apply replay_opens_none_iff in Hlast; discriminate. }
        destruct (replay_summary b c); simpl in Hnormal; intuition discriminate.
      + destruct (replay_summary b c); simpl in Hnormal; intuition discriminate.
    - rewrite replay_summary_normal_form_close in Hnormal by lia.
      unfold boundary_pairs; rewrite Nat.min_l by lia.
      destruct (cancel_pairs (opens b) (opens b) 0 b c
        (region (regions_of c) 0)) as [acc|] eqn:Hcancel.
      + destruct (replay_closes_no_open_succeeds (closes c - opens b)
          (opens b) c (append_region (open_base b) acc)) as [after Hr].
        { simpl; apply open_base_lo_nonpos; exact (proj1 (proj1 (proj2 Hb))). }
        { simpl; apply open_base_lo_net. }
        { rewrite append_region_opens; apply open_base_opens. }
        simpl in Hnormal; rewrite Hr in Hnormal; simpl in Hnormal.
        destruct (replay_opens (opens c) 0 c (Some after)) eqn:Hlast.
        2: { apply replay_opens_none_iff in Hlast; discriminate. }
        destruct (replay_summary b c); simpl in Hnormal; intuition discriminate.
      + destruct (replay_summary b c); simpl in Hnormal; intuition discriminate.
  Qed.

  Lemma replay_failure_propagates_left (a b c ab : t) :
    IsMonoid M -> Consistent a -> Consistent b ->
    depth_supported_n a b = true -> replay_summary a b = Some ab ->
    replay_summary b c = None ->
    replay_summary (finish_replay a b ab) c = None.
  Proof.
    intros HM Ha Hb Hd Hr Hfail.
    apply (proj2 (replay_summary_failure_iff_cancel c HM
      (finish_replay_preserves_consistency Ha Hb Hd Hr))).
    rewrite cancel_pairs_left_outer_decompose by assumption.
    rewrite (proj1 (replay_summary_failure_iff_cancel c HM Hb) Hfail).
    reflexivity.
  Qed.

  (** Failure does not inspect the region following the last cancelled pair. *)
  Lemma cancel_pairs_failure_prefix remaining open_count j a b c acc :
    (forall i, j < i < j + remaining ->
      region (regions_of b) i = region (regions_of c) i) ->
    (cancel_pairs remaining open_count j a b acc = None <->
     cancel_pairs remaining open_count j a c acc = None).
  Proof.
    revert open_count j acc; induction remaining as [|remaining IH];
      intros open_count j acc Hprefix; [simpl; tauto|].
    destruct open_count as [|open_count]; [simpl; tauto|].
    simpl; destruct (close (m_op M
      (region (regions_of a) (closes a + S open_count)) acc)); [|tauto].
    destruct remaining as [|remaining]; [simpl; intuition discriminate|].
    rewrite (Hprefix (S j)) by lia.
    apply IH; intros i Hi; apply Hprefix; lia.
  Qed.

  Lemma finish_replay_close_prefix (b c bc : t) :
    IsMonoid M -> Consistent b -> Consistent c ->
    depth_supported_n b c = true -> replay_summary b c = Some bc ->
    forall i, i < closes b ->
      region (regions_of (finish_replay b c bc)) i = region (regions_of b) i.
  Proof.
    intros HM Hb Hc Hd Hr i Hi.
    destruct (lt_dec (closes c) (opens b)) as [Hlt|Hge].
    - apply finish_replay_surviving_open_prefix; try assumption; lia.
    - destruct (lt_dec (opens b) (closes c)) as [Hgt|Heq].
      + destruct (finish_replay_close_prefix_pivot HM Hb Hc Hd Hr Hgt)
          as [acc [Hcancel [Hprefix Hpivot]]]; auto.
      + assert (Hequal : closes c = opens b) by lia.
        assert (Hex : exists acc, cancel_pairs (boundary_pairs b c)
          (opens b) 0 b c (region (regions_of c) 0) = Some acc).
        { destruct (cancel_pairs (boundary_pairs b c) (opens b) 0 b c
            (region (regions_of c) 0)) eqn:Hcancel; [eauto|].
          apply (proj2 (replay_summary_failure_iff_cancel c HM Hb)) in Hcancel.
          congruence. }
        destruct Hex as [acc Hcancel].
        unfold boundary_pairs in Hcancel; rewrite Nat.min_r in Hcancel by lia.
        exact (proj1 (finish_replay_equal_boundary_close_layout
          HM Hb Hc Hd Hr Hequal Hcancel) i Hi).
  Qed.

  Lemma replay_failure_propagates_right (a b c bc : t) :
    IsMonoid M -> Consistent a -> Consistent b -> Consistent c ->
    depth_supported_n b c = true -> replay_summary b c = Some bc ->
    replay_summary a b = None ->
    replay_summary a (finish_replay b c bc) = None.
  Proof.
    intros HM Ha Hb Hc Hd Hr Hfail.
    apply (proj2 (replay_summary_failure_iff_cancel
      (finish_replay b c bc) HM Ha)).
    apply (proj1 (replay_summary_failure_iff_cancel b HM Ha)) in Hfail.
    assert (Hpositive : 0 < boundary_pairs a b).
    { destruct (boundary_pairs a b); [discriminate|lia]. }
    assert (Hbound : boundary_pairs a b <= closes b).
    { unfold boundary_pairs; apply Nat.le_min_r. }
    pose proof (finish_replay_close_prefix HM Hb Hc Hd Hr) as Hprefix.
    rewrite boundary_pairs_right_outer_decompose by assumption.
    rewrite cancel_pairs_plus by apply boundary_pairs_le_opens.
    rewrite (Hprefix 0) by lia.
    assert (Hfirst : cancel_pairs (boundary_pairs a b) (opens a) 0 a
      (finish_replay b c bc) (region (regions_of b) 0) = None).
    { apply (proj2 (@cancel_pairs_failure_prefix
        (boundary_pairs a b) (opens a) 0 a (finish_replay b c bc) b
        (region (regions_of b) 0) ltac:(intros i Hi; apply Hprefix; lia))).
      exact Hfail. }
    rewrite Hfirst; reflexivity.
  Qed.

  Lemma parens_n_op_assoc_depth_failure (a b c : t) :
    (depth_supported_n a b = false \/ depth_supported_n b c = false) ->
    parens_n_op (parens_n_op (Some a) (Some b)) (Some c) =
    parens_n_op (Some a) (parens_n_op (Some b) (Some c)).
  Proof.
    intro Hfailure.
    rewrite (parens_n_op_as_replay_summary a b),
      (parens_n_op_as_replay_summary b c).
    destruct Hfailure as [Hab|Hbc].
    - rewrite Hab.
      destruct (depth_supported_n b c); [|reflexivity].
      destruct (replay_summary b c) as [bc|]; [|reflexivity].
      rewrite parens_n_op_as_replay_summary.
      assert (Houter : depth_supported_n a (finish_replay b c bc) = false).
      { rewrite <- (depth_supported_n_assoc a b c a bc).
        apply depth_unsupported_left_propagates; exact Hab. }
      rewrite Houter; reflexivity.
    - rewrite Hbc.
      destruct (depth_supported_n a b); [|reflexivity].
      destruct (replay_summary a b) as [ab|]; [|reflexivity].
      rewrite parens_n_op_as_replay_summary.
      assert (Houter : depth_supported_n (finish_replay a b ab) c = false).
      { rewrite (depth_supported_n_assoc a b c ab c).
        apply depth_unsupported_right_propagates; exact Hbc. }
      rewrite Houter; reflexivity.
  Qed.

  Lemma parens_n_op_assoc_replay_failure
      (a b c : t) :
    IsMonoid M ->
    Consistent a ->
    Consistent b ->
    Consistent c ->
    depth_supported_n a b = true ->
    depth_supported_n b c = true ->
    (replay_summary a b = None \/ replay_summary b c = None) ->
    parens_n_op (parens_n_op (Some a) (Some b)) (Some c) =
    parens_n_op (Some a) (parens_n_op (Some b) (Some c)).
  Proof.
    intros HM Ha Hb Hc Hdab Hdbc Hfail.
    rewrite (parens_n_op_as_replay_summary a b),
      (parens_n_op_as_replay_summary b c), Hdab, Hdbc.
    destruct (replay_summary a b) as [ab|] eqn:Hab;
      destruct (replay_summary b c) as [bc|] eqn:Hbc.
    - destruct Hfail; discriminate.
    - rewrite parens_n_op_as_replay_summary.
      rewrite (replay_failure_propagates_left c HM Ha Hb Hdab Hab Hbc).
      destruct (depth_supported_n (finish_replay a b ab) c); reflexivity.
    - rewrite parens_n_op_as_replay_summary.
      rewrite (replay_failure_propagates_right HM Ha Hb Hc Hdbc Hbc Hab).
      destruct (depth_supported_n a (finish_replay b c bc)); reflexivity.
    - reflexivity.
  Qed.

  Lemma parens_n_op_assoc_non_successful
      (a b c : t) :
    IsMonoid M ->
    Consistent a ->
    Consistent b ->
    Consistent c ->
    (depth_supported_n a b = false \/
     depth_supported_n b c = false \/
     replay_summary a b = None \/
     replay_summary b c = None) ->
    parens_n_op (parens_n_op (Some a) (Some b)) (Some c) =
    parens_n_op (Some a) (parens_n_op (Some b) (Some c)).
  Proof.
    intros HM Ha Hb Hc Hfailure.
    destruct (depth_supported_n a b) eqn:Hab.
    2: { apply parens_n_op_assoc_depth_failure; auto. }
    destruct (depth_supported_n b c) eqn:Hbc.
    2: { apply parens_n_op_assoc_depth_failure; auto. }
    apply parens_n_op_assoc_replay_failure; try assumption.
    destruct Hfailure as [H|[H|H]]; congruence.
  Qed.

  Theorem parens_n_op_assoc_some
      (a b c : t) :
    IsMonoid M ->
    Consistent a ->
    Consistent b ->
    Consistent c ->
    parens_n_op (parens_n_op (Some a) (Some b)) (Some c) =
    parens_n_op (Some a) (parens_n_op (Some b) (Some c)).
  Proof.
    intros HM Ha Hb Hc.
    destruct (depth_supported_n a b) eqn:Hab;
      [|eapply parens_n_op_assoc_non_successful; eauto].
    destruct (depth_supported_n b c) eqn:Hbc;
      [|eapply parens_n_op_assoc_non_successful; eauto].
    destruct (replay_summary a b) as [replayed_ab|] eqn:Hreplay_ab;
      [|eapply parens_n_op_assoc_non_successful; eauto].
    destruct (replay_summary b c) as [replayed_bc|] eqn:Hreplay_bc;
      [|eapply parens_n_op_assoc_non_successful; eauto].
    eapply parens_n_op_assoc_successful; eauto.
  Qed.

  Lemma parens_n_op_none_left (x : option t) :
    parens_n_op None x = None.
  Proof. destruct x; reflexivity. Qed.

  Lemma parens_n_op_none_right (x : option t) :
    parens_n_op x None = None.
  Proof. destruct x; reflexivity. Qed.

  Theorem parens_n_op_assoc :
    IsMonoid M ->
    forall a b c,
      ConsistentOpt a ->
      ConsistentOpt b ->
      ConsistentOpt c ->
      parens_n_op (parens_n_op a b) c =
      parens_n_op a (parens_n_op b c).
  Proof.
    intros HM [a|] [b|] [c|] Ha Hb Hc.
    - now apply parens_n_op_assoc_some.
    - rewrite parens_n_op_none_right, parens_n_op_none_right.
      reflexivity.
    - rewrite parens_n_op_none_right, parens_n_op_none_left,
        parens_n_op_none_right.
      reflexivity.
    - rewrite parens_n_op_none_right, parens_n_op_none_left,
        parens_n_op_none_right.
      reflexivity.
    - rewrite !parens_n_op_none_left.
      reflexivity.
    - rewrite !parens_n_op_none_left.
      reflexivity.
    - rewrite !parens_n_op_none_left.
      reflexivity.
    - rewrite !parens_n_op_none_left.
      reflexivity.
  Qed.

  Lemma parens_n_op_depth
      (a b result : t) :
    parens_n_op (Some a) (Some b) = Some result ->
    array_depth result = depth_op (array_depth a) (array_depth b).
  Proof.
    unfold parens_n_op.
    destruct (Z.ltb (Z.of_nat N)
      (Z.max (hi a) (net a + hi b) -
       Z.min (lo a) (net a + lo b))) eqn:Hguard; try discriminate.
    destruct (replay_closes (closes b) 0 b
      (Some (append_region a (region (regions_of b) 0))))
      as [s1|] eqn:Hcloses; try discriminate.
    destruct (replay_opens (opens b) 0 b (Some s1))
      as [s2|] eqn:Hopens; try discriminate.
    intro H; inversion H; subst result.
    unfold array_depth, depth_op, zmin, zmax; reflexivity.
  Qed.

  Lemma parens_n_op_assoc_depth
      (a b c ab left bc right : t) :
    parens_n_op (Some a) (Some b) = Some ab ->
    parens_n_op (Some ab) (Some c) = Some left ->
    parens_n_op (Some b) (Some c) = Some bc ->
    parens_n_op (Some a) (Some bc) = Some right ->
    array_depth left = array_depth right.
  Proof.
    intros Hab Hleft Hbc Hright.
    rewrite (parens_n_op_depth ab c (result:=left) Hleft),
      (parens_n_op_depth a b (result:=ab) Hab).
    rewrite (parens_n_op_depth a bc (result:=right) Hright),
      (parens_n_op_depth b c (result:=bc) Hbc).
    apply depth_op_assoc.
  Qed.

  Theorem ne_left_neutral :
    IsMonoid M ->
    forall x, ConsistentOpt x -> parens_n_op ne x = x.
  Proof.
    intros HM [s|] Hconsistent; [|reflexivity].
    change (Consistent s) in Hconsistent.
    destruct Hconsistent as [Hsized [Hdepth [Hactive Hpadding]]].
    destruct Hdepth as [Hlo [Hhi [Hlonet [Hnethi Hspan]]]].

    assert (Hseed_sized : Sized (left_seed s)).
    { unfold left_seed; apply append_region_sized, base_sized. }
    pose proof (left_seed_closes_state HM s) as Hseed_state.
    destruct (replay_closes_induction (closes s)
                (j:=0)
                (source:=s) (state:=left_seed s)
                HM Hsized Hactive Hseed_sized Hseed_state)
      as [s1 [Hcloses Hs1state]]; try lia.

    assert (Hs1_sized : Sized s1).
    { pose proof
        (replay_closes_sized (closes s) 0 s (Some (left_seed s))
           Hseed_sized) as H.
      rewrite Hcloses in H; exact H. }

    assert (Hs1_open_state : opens_replay_state (closes s) 0 s s1).
    { destruct Hs1state as
        [Hs1lo [_ [Hs1net [Hs1active [Hs1agree Hs1padding]]]]].
      unfold opens_replay_state.
      repeat split; try assumption; try lia.
      now rewrite Nat.add_0_r. }

    assert (Hopen_count : closes s + 0 + opens s <= active s).
    { unfold active; lia. }

    destruct (replay_opens_induction (opens s)
                (c:=closes s) (j:=0)
                (source:=s) (state:=s1)
                HM Hsized Hactive eq_refl Hs1_sized Hs1_open_state
                Hopen_count)
      as [s2 [Hopens Hs2state]].

    assert (Hs2_sized : Sized s2).
    { pose proof
        (replay_opens_sized (opens s) 0 s (Some s1) Hs1_sized) as H.
      rewrite Hopens in H; exact H. }

    destruct Hs2state as
      [Hs2lo [Hs2net [Hs2active [Hs2agree Hs2padding]]]].
    assert (Hregions : regions_of s2 = regions_of s).
    { eapply regions_eq_of_active_agreement.
      - exact Hs2_sized.
      - exact Hsized.
      - rewrite Hs2active; unfold active; lia.
      - rewrite Hs2active.
        replace (closes s + (0 + opens s)) with (active s)
          by (unfold active; lia).
        exact Hs2agree.
      - exact Hs2padding.
      - exact Hpadding. }

    unfold ne, parens_n_op; simpl.
    rewrite Z.min_r by exact Hlo.
    rewrite Z.max_r by exact Hhi.
    destruct (Z.ltb (Z.of_nat N) (hi s - lo s)) eqn:Hguard.
    - apply Z.ltb_lt in Hguard; lia.
    - simpl.
      fold left_seed.
      change
        (append_region (base (m_ne M)) (region (regions_of s) 0))
        with (left_seed s).
      rewrite Hcloses, Hopens; simpl.
      rewrite Hregions.
      destruct s; reflexivity.
  Qed.

  (** The packaged combinator corresponding to the Futhark module returned
      by [parens_n N X M D]. *)
  Definition parens_n : MonoidalOps (del Raw Delimiter) Value :=
    {| m_summary := option t;
       m_ne := ne;
       m_op := parens_n_op;
       m_gen := parens_n_gen;
       m_obs := parens_n_obs |}.
End ParensNDefinition.
End ParensN.
