From Stdlib Require Import List Arith ZArith Lia.
Require Import Monoid Parens ParensRegions ParensTuple.
Set Implicit Arguments.
Set Universe Polymorphism.

(** Direct algebra of the executable tuple replay.  This file deliberately
    does not import the array implementation or its correspondence proof. *)
Module TupleDirect.
Module T := ParensTuple.ParensTuple.
Module R := ParensRegions.ParensRegions.
Section Replay.
Context {Raw Value : Type}.
Context (M : MonoidalOps (Nest Raw Value) Value).
Context (S : R.regions (m_summary M)).

Lemma pop_push r x padding : R.Laws S -> R.last S r = padding ->
  R.pop S (R.push S r x) padding = r.
Proof.
  intros HS Hlast. apply (R.view_injective HS).
  pose proof (R.view_pop HS (R.push S r x) padding) as Hpop.
  pose proof (R.view_push HS r x) as Hpush.
  rewrite <- Hlast in Hpop. rewrite Hpush in Hpop.
  rewrite Hlast in Hpop. now injection Hpop.
Qed.

Lemma push_pop r padding : R.Laws S ->
  R.push S (R.pop S r padding) (R.top S r) = r.
Proof.
  intro HS. apply (R.view_injective HS).
  pose proof (R.view_push HS (R.pop S r padding) (R.top S r)) as H.
  rewrite (R.view_pop HS) in H.
  now apply app_inj_tail in H as [H _].
Qed.

Lemma replay_closes_plus p q state :
  @T.replay_closes Raw Value M S (p+q) state =
  @T.replay_closes Raw Value M S q (@T.replay_closes Raw Value M S p state).
Proof.
  revert state; induction p as [|p IH]; intro state; [reflexivity|].
  destruct state as [[s r]|]; cbn [Nat.add T.replay_closes].
  - destruct (@T.append_close Raw Value M S s); [apply IH|].
    symmetry; apply T.replay_closes_none.
  - symmetry; apply T.replay_closes_none.
Qed.

Lemma append_region_consistent s x : R.Laws S -> T.Consistent s ->
  T.Consistent (@T.append_region Raw Value M S s x).
Proof.
  intros HS [Hdepth [Hactive Hpadding]].
  unfold T.Consistent.
  split; [exact Hdepth|].
  split; [exact Hactive|].
  change (skipn (Datatypes.S (T.active s))
    (R.view S (R.replace S (T.regions s)
      (m_op M (R.top S (T.regions s)) x))) =
    repeat (m_ne M) (2*T.depth M S-T.active s)).
  rewrite (R.view_replace HS).
  cbn [skipn].
  rewrite (R.view_top HS (T.regions s)) in Hpadding.
  exact Hpadding.
Qed.

Lemma replay_opens_plus p q state :
  @T.replay_opens Raw Value M S (p+q) state =
  @T.replay_opens Raw Value M S q (@T.replay_opens Raw Value M S p state).
Proof.
  revert state; induction p as [|p IH]; intro state; [reflexivity|].
  destruct state as [[s r]|]; cbn [Nat.add T.replay_opens].
  - apply IH.
  - symmetry; apply T.replay_opens_none.
Qed.

Lemma append_region_associative s x y : IsMonoid M ->
  R.Laws S ->
  @T.append_region Raw Value M S (@T.append_region Raw Value M S s x) y =
  @T.append_region Raw Value M S s (m_op M x y).
Proof.
  intros [Hassoc _] HS.
  assert (Htop : forall r x, R.top S (R.replace S r x) = x).
  { intros r v.
    pose proof (R.view_top HS (R.replace S r v)) as H.
    rewrite (R.view_replace HS) in H. injection H; auto. }
  unfold T.append_region; cbn [T.lo T.hi T.net T.regions].
  rewrite Htop, Hassoc.
  f_equal.
  apply (R.view_injective HS).
  rewrite !(R.view_replace HS).
  reflexivity.
Qed.
End Replay.

Section Padding.
Context {A : Type} (S : R.regions A) (HS : R.Laws S) (e : A).
Let capacity := 2 * R.depth S + 1.
Definition Padded r k := k < capacity /\
  skipn (Datatypes.S k) (R.view S r) = repeat e (capacity - Datatypes.S k).

Lemma firstn_repeat_le n m : n <= m -> firstn n (repeat e m) = repeat e n.
Proof.
 revert m; induction n; intros [|m] H; cbn; try reflexivity; try lia.
 f_equal; apply IHn; lia.
Qed.

Lemma view_push_prefix r x :
 R.view S (R.push S r x) = firstn capacity (x :: R.view S r).
Proof.
 pose proof (f_equal (firstn capacity) (R.view_push HS r x)) as H.
 rewrite firstn_app, (R.view_size HS) in H.
 fold capacity in H.
 rewrite Nat.sub_diag in H; cbn [firstn] in H.
 rewrite app_nil_r, firstn_all2 in H by (rewrite (R.view_size HS); unfold capacity; lia).
 exact H.
Qed.

Lemma push_padded r k x : Padded r k -> Datatypes.S k < capacity ->
 Padded (R.push S r x) (Datatypes.S k).
Proof.
 intros [Hk Hp] Hroom. split; [exact Hroom|].
 rewrite view_push_prefix, skipn_firstn_comm.
 change (firstn (capacity - Datatypes.S (Datatypes.S k))
   (skipn (Datatypes.S k) (R.view S r)) = repeat e (capacity - Datatypes.S (Datatypes.S k))).
 rewrite Hp. apply firstn_repeat_le; lia.
Qed.

Lemma pop_padded r k : Padded r (Datatypes.S k) ->
 Padded (R.pop S r e) k.
Proof.
 intros [Hk Hp]. split; [lia|].
 pose proof (f_equal (skipn (Datatypes.S (Datatypes.S k))) (R.view_pop HS r e)) as H.
 rewrite skipn_app, (R.view_size HS) in H.
 fold capacity in H.
 replace (Datatypes.S (Datatypes.S k) - capacity) with 0 in H by lia.
 change (skipn (Datatypes.S k) (R.view S (R.pop S r e)) =
   skipn (Datatypes.S (Datatypes.S k)) (R.view S r) ++ (e :: nil)) in H.
 rewrite Hp in H.
 rewrite H.
 change (repeat e (capacity - Datatypes.S (Datatypes.S k)) ++ repeat e 1 =
   repeat e (capacity - Datatypes.S k)).
 rewrite <- repeat_app. f_equal; lia.
Qed.
End Padding.

Section Consistency.
Context {Raw Value : Type}.
Context (M : MonoidalOps (Nest Raw Value) Value).
Context (S : R.regions (m_summary M)) (HS : R.Laws S).

Lemma metadata_active_bound (s : T.t M S) :
 CompactDepth.consistent (Z.of_nat (T.depth M S)) (T.metadata s) ->
 T.active s <= 2 * T.depth M S.
Proof.
 unfold CompactDepth.consistent, T.metadata; cbn.
 intros H. unfold T.active, T.closes, T.opens.
 apply Nat2Z.inj_le. rewrite !Nat2Z.inj_add; try rewrite Nat2Z.inj_mul.
 rewrite !Z2Nat.id by lia. cbn; lia.
Qed.

Lemma append_open_active (s : T.t M S) : T.Consistent s ->
 T.active (T.append_open s) = Datatypes.S (T.active s).
Proof.
 intros [Hd _]. unfold CompactDepth.consistent, T.metadata in Hd; cbn in Hd.
 unfold T.active, T.closes, T.opens, T.append_open; cbn [T.lo T.net].
 rewrite Z.min_l by lia.
 replace (T.net s + 1 - T.lo s)%Z with (Z.succ (T.net s - T.lo s)) by lia.
 rewrite Z2Nat.inj_succ by lia. lia.
Qed.

Lemma append_open_consistent (s : T.t M S) : T.Consistent s ->
 CompactDepth.consistent (Z.of_nat (T.depth M S)) (T.metadata (T.append_open s)) ->
 T.Consistent (T.append_open s).
Proof.
 intros Hs Hd.
 pose proof (metadata_active_bound Hd) as Hb.
 pose proof (append_open_active Hs) as Ha.
 unfold T.Consistent. split; [exact Hd|]. split; [exact Hb|].
 rewrite Ha. cbn [T.append_open T.regions].
 pose proof (@push_padded _ S HS (m_ne M) (T.regions s) (T.active s) (m_ne M)) as H.
 assert (Hp : Padded S (m_ne M) (T.regions s) (T.active s)).
 { destruct Hs as [_ [Hbound Hpad]]. split; [unfold T.depth in *; lia|].
   replace (2 * R.depth S + 1 - Datatypes.S (T.active s)) with
     (2 * T.depth M S - T.active s) by (unfold T.depth; lia).
   exact Hpad. }
 specialize (H Hp ltac:(unfold T.depth in *; lia)).
 destruct H as [_ H].
 replace (2 * R.depth S + 1 - Datatypes.S (Datatypes.S (T.active s))) with
   (2 * T.depth M S - Datatypes.S (T.active s)) in H by (unfold T.depth; lia).
 exact H.
Qed.
Lemma consistent_padding (s : T.t M S) : T.Consistent s ->
 Padded S (m_ne M) (T.regions s) (T.active s).
Proof.
 intros [_ [Hb Hp]]. split; [unfold T.depth in *; lia|].
 replace (2 * R.depth S + 1 - Datatypes.S (T.active s)) with
   (2 * T.depth M S - T.active s) by (unfold T.depth; lia).
 exact Hp.
Qed.

Lemma consistent_of_padding (s : T.t M S) :
 CompactDepth.consistent (Z.of_nat (T.depth M S)) (T.metadata s) ->
 Padded S (m_ne M) (T.regions s) (T.active s) -> T.Consistent s.
Proof.
 intros Hd [_ Hp]. split; [exact Hd|].
 split; [apply metadata_active_bound; exact Hd|].
 replace (2 * R.depth S + 1 - Datatypes.S (T.active s)) with
   (2 * T.depth M S - T.active s) in Hp by (unfold T.depth; lia).
 exact Hp.
Qed.

Lemma replace_padded r k x : Padded S (m_ne M) r k ->
 Padded S (m_ne M) (R.replace S r x) k.
Proof.
 intros [Hb Hp]. split; [exact Hb|].
 rewrite (R.view_replace HS).
 rewrite (R.view_top HS r) in Hp.
 exact Hp.
Qed.

Lemma append_close_active (s t : T.t M S) : T.Consistent s ->
 T.append_close s = Some t ->
 if Nat.ltb 0 (T.opens s) then Datatypes.S (T.active t) = T.active s
 else T.active t = Datatypes.S (T.active s).
Proof.
 intros [Hd _] Hclose.
 unfold CompactDepth.consistent, T.metadata in Hd; cbn in Hd.
 unfold T.append_close in Hclose.
 destruct (Nat.ltb 0 (T.opens s)) eqn:Ho.
 - destruct (m_obs M (R.top S (T.regions s))) as [v|]; try discriminate.
   inversion Hclose; subst t; clear Hclose.
   apply Nat.ltb_lt in Ho. unfold T.opens in Ho.
   assert (Hpos : (0 < T.net s - T.lo s)%Z) by lia.
   unfold T.active, T.closes, T.opens; cbn [T.lo T.net].
   rewrite Z.min_l by lia.
   apply Nat2Z.inj. rewrite Nat2Z.inj_succ, !Nat2Z.inj_add.
   rewrite !Z2Nat.id by lia. lia.
 - inversion Hclose; subst t; clear Hclose.
   apply Nat.ltb_ge in Ho. unfold T.opens in Ho.
   assert (Heq : T.net s = T.lo s) by lia.
   unfold T.active, T.closes, T.opens; cbn [T.lo T.net].
   rewrite Z.min_r by lia.
   apply Nat2Z.inj. rewrite Nat2Z.inj_succ, !Nat2Z.inj_add.
   rewrite !Z2Nat.id by lia. lia.
Qed.

Lemma append_close_consistent (s t : T.t M S) : T.Consistent s ->
 T.append_close s = Some t ->
 CompactDepth.consistent (Z.of_nat (T.depth M S)) (T.metadata t) ->
 T.Consistent t.
Proof.
 intros Hs Hclose Hd.
 pose proof (append_close_active Hs Hclose) as Ha.
 pose proof (consistent_padding Hs) as Hp.
 apply consistent_of_padding; [exact Hd|].
 unfold T.append_close in Hclose.
 destruct (Nat.ltb 0 (T.opens s)) eqn:Ho.
 - destruct (m_obs M (R.top S (T.regions s))) as [v|]; try discriminate.
   inversion Hclose; subst t; clear Hclose.
   cbn [T.regions]. apply replace_padded.
   unfold T.pop. apply pop_padded; [exact HS|].
   unfold T.pop in Ha. rewrite Ha. exact Hp.
 - inversion Hclose; subst t; clear Hclose.
   rewrite Ha. cbn [T.regions]. apply push_padded; [exact HS|exact Hp|].
   pose proof (metadata_active_bound Hd) as Hb.
   rewrite Ha in Hb. unfold T.depth in Hb; lia.
Qed.
Lemma append_close_metadata (s t : T.t M S) :
 T.append_close s = Some t ->
 T.lo t = Z.min (T.lo s) (T.net s - 1) /\
 T.hi t = Z.max (T.hi s) (T.net s) /\ T.net t = (T.net s - 1)%Z.
Proof.
 unfold T.append_close.
 destruct (Nat.ltb 0 (T.opens s));
   [destruct (m_obs M (R.top S (T.regions s)))|];
   intro H; try discriminate; inversion H; subst; repeat split; reflexivity.
Qed.

Definition StateConsistent (state : option (T.t M S * R.carrier S)) :=
 match state with None => True | Some (s,_) => T.Consistent s end.

(** The entire closing replay stays inside this lower depth envelope.
    The queue is arbitrary: consistency does not constrain region values. *)
Lemma replay_closes_consistent n (s : T.t M S) q : T.Consistent s ->
 (T.hi s - Z.min (T.lo s) (T.net s - Z.of_nat n) <= Z.of_nat (T.depth M S))%Z ->
 StateConsistent (@T.replay_closes Raw Value M S n (Some (s,q))).
Proof.
 revert s q; induction n as [|n IH]; intros s q Hs Hbound.
 - exact Hs.
 - cbn [T.replay_closes].
   destruct (T.append_close s) as [t|] eqn:Hclose; [|exact I].
   pose proof (append_close_metadata s Hclose) as [Hl [Hh Hnet]].
   pose proof (proj1 Hs) as Hd.
   unfold CompactDepth.consistent, T.metadata in Hd; cbn in Hd.
   rewrite Nat2Z.inj_succ in Hbound.
   assert (Ht : T.Consistent t).
   { eapply append_close_consistent; [exact Hs|exact Hclose|].
     unfold CompactDepth.consistent, T.metadata; cbn.
     rewrite Hl, Hh, Hnet.
     rewrite Z.max_l by lia.
     pose proof (Z.le_min_l (T.lo s) (T.net s - Z.succ (Z.of_nat n))).
     pose proof (Z.le_min_r (T.lo s) (T.net s - Z.succ (Z.of_nat n))).
     destruct (Z_le_dec (T.lo s) (T.net s - 1));
       [rewrite Z.min_l by lia|rewrite Z.min_r by lia]; lia. }
   apply IH.
   + apply append_region_consistent; assumption.
   + change (T.hi t - Z.min (T.lo t) (T.net t - Z.of_nat n) <= Z.of_nat (T.depth M S))%Z.
     rewrite Hl, Hh, Hnet, Z.max_l by lia.
     replace (T.net s - 1 - Z.of_nat n)%Z with
       (T.net s - Z.succ (Z.of_nat n))%Z by lia.
     rewrite <- Z.min_assoc.
     rewrite (Z.min_r (T.net s - 1) (T.net s - Z.succ (Z.of_nat n))) by lia.
     exact Hbound.
Qed.
Lemma replay_opens_consistent n (s : T.t M S) q : T.Consistent s ->
 (T.net s + Z.of_nat n - T.lo s <= Z.of_nat (T.depth M S))%Z ->
 StateConsistent (@T.replay_opens Raw Value M S n (Some (s,q))).
Proof.
 revert s q; induction n as [|n IH]; intros s q Hs Hbound.
 - exact Hs.
 - cbn [T.replay_opens]. apply IH.
   + apply append_region_consistent; [exact HS|].
     apply append_open_consistent; [exact Hs|].
     pose proof (proj1 Hs) as Hd.
     unfold CompactDepth.consistent, T.metadata in Hd |- *.
     cbn [T.append_open T.lo T.hi T.net CompactDepth.lo CompactDepth.hi CompactDepth.net].
     cbn in Hd. rewrite Nat2Z.inj_succ in Hbound.
     rewrite Z.min_l by lia.
     destruct (Z_le_dec (T.hi s) (T.net s+1));
       [rewrite Z.max_r by lia|rewrite Z.max_l by lia]; lia.
   + change (T.net s + 1 + Z.of_nat n - Z.min (T.lo s) (T.net s) <=
       Z.of_nat (T.depth M S))%Z.
     pose proof (proj1 Hs) as Hd.
     unfold CompactDepth.consistent, T.metadata in Hd; cbn in Hd.
     rewrite Z.min_l by lia. rewrite Nat2Z.inj_succ in Hbound. lia.
Qed.
Lemma replay_closes_shape n (s t : T.t M S) q r :
 (T.lo s <= T.net s)%Z ->
 T.replay_closes n (Some (s,q)) = Some (t,r) ->
 T.lo t = Z.min (T.lo s) (T.net s - Z.of_nat n) /\
 T.net t = (T.net s - Z.of_nat n)%Z.
Proof.
 revert s q; induction n as [|n IH]; intros s q Hln Hrun.
 - cbn [T.replay_closes] in Hrun; inversion Hrun; subst.
   rewrite Z.sub_0_r, Z.min_l by assumption; auto.
 - cbn [T.replay_closes] in Hrun.
   destruct (T.append_close s) as [u|] eqn:Hclose; try discriminate.
   pose proof (append_close_metadata s Hclose) as [Hl [Hh Hnet]].
   assert (Huln : (T.lo u <= T.net u)%Z).
   { rewrite Hl,Hnet; apply Z.le_min_r. }
   specialize (IH (T.append_region u (R.top S q)) (T.pop M S q) Huln Hrun).
   change (T.lo t = Z.min (T.lo u) (T.net u - Z.of_nat n) /\
     T.net t = (T.net u - Z.of_nat n)%Z) in IH.
   rewrite Hl,Hnet in IH. rewrite Nat2Z.inj_succ.
   replace (T.net s - 1 - Z.of_nat n)%Z with
     (T.net s - Z.succ (Z.of_nat n))%Z in IH by lia.
   rewrite <- Z.min_assoc in IH.
   rewrite (Z.min_r (T.net s - 1) (T.net s - Z.succ (Z.of_nat n))) in IH by lia.
   exact IH.
Qed.

Lemma replay_opens_shape n (s t : T.t M S) q r :
 (T.lo s <= T.net s)%Z ->
 T.replay_opens n (Some (s,q)) = Some (t,r) ->
 T.lo t = T.lo s /\ T.net t = (T.net s + Z.of_nat n)%Z.
Proof.
 revert s q; induction n as [|n IH]; intros s q Hln Hrun.
 - cbn [T.replay_opens] in Hrun; inversion Hrun; subst.
   rewrite Z.add_0_r; auto.
 - cbn [T.replay_opens] in Hrun.
   specialize (IH (T.append_region (T.append_open s) (R.top S q)) (T.pop M S q)).
   assert (Hnext : (T.lo (T.append_region (T.append_open s) (R.top S q)) <=
       T.net (T.append_region (T.append_open s) (R.top S q)))%Z).
   { change (Z.min (T.lo s) (T.net s) <= T.net s+1)%Z.
     rewrite Z.min_l by lia; lia. }
   specialize (IH Hnext Hrun).
   change (T.lo t = Z.min (T.lo s) (T.net s) /\
     T.net t = (T.net s + 1 + Z.of_nat n)%Z) in IH.
   rewrite Z.min_l in IH by lia.
   rewrite Nat2Z.inj_succ. destruct IH; split; [assumption|lia].
Qed.
Theorem op_preserves_consistency (a b : option (T.t M S)) :
 T.ConsistentOpt a -> T.ConsistentOpt b -> T.ConsistentOpt (T.op a b).
Proof.
 destruct a as [a|], b as [b|]; cbn [T.ConsistentOpt]; try tauto.
 intros Ha Hb. unfold T.op.
 set (m := CompactDepth.combine (T.metadata a) (T.metadata b)).
 destruct (CompactDepth.valid (Z.of_nat (T.depth M S)) m) eqn:Hvalid;
   [|exact I].
 apply CompactDepth.valid_spec in Hvalid as [_ Hm].
 pose proof (proj1 Ha) as Hda. pose proof (proj1 Hb) as Hdb.
 unfold CompactDepth.consistent, T.metadata in Hda,Hdb; cbn in Hda,Hdb.
 assert (Hc : Z.of_nat (T.closes b) = (-T.lo b)%Z).
 { unfold T.closes; rewrite Z2Nat.id by lia; reflexivity. }
 assert (Ho : Z.of_nat (T.opens b) = (T.net b-T.lo b)%Z).
 { unfold T.opens; rewrite Z2Nat.id by lia; reflexivity. }
 assert (Hml : CompactDepth.lo m = Z.min (T.lo a) (T.net a + T.lo b)) by reflexivity.
 assert (Hmn : CompactDepth.net m = (T.net a + T.net b)%Z) by reflexivity.
 assert (Hmh : (T.hi a <= CompactDepth.hi m)%Z).
 { unfold m,CompactDepth.combine,T.metadata; cbn. apply Z.le_max_l. }
 pose proof Hm as Hmd. unfold CompactDepth.consistent in Hmd.
 set (q := Nat.iter (2*T.depth M S-T.active b) (T.pop M S)
   (R.reverse S (T.regions b))).
 set (s0 := T.append_region a (R.top S q)).
 assert (Hs0 : T.Consistent s0) by (apply append_region_consistent; assumption).
 assert (Hclosebound : (T.hi s0 - Z.min (T.lo s0)
     (T.net s0-Z.of_nat (T.closes b)) <= Z.of_nat (T.depth M S))%Z).
 { change (T.hi a - Z.min (T.lo a) (T.net a-Z.of_nat (T.closes b)) <=
     Z.of_nat (T.depth M S))%Z.
   rewrite Hc. replace (T.net a - -T.lo b)%Z with (T.net a+T.lo b)%Z by lia.
   rewrite <- Hml. lia. }
 pose proof (replay_closes_consistent (T.closes b) (T.pop M S q) Hs0 Hclosebound) as Hs1.
 destruct (T.replay_closes (T.closes b) (Some (s0,T.pop M S q)))
   as [[s1 q1]|] eqn:Hrun1.
 2: { rewrite T.replay_opens_none. exact I. }
 change (T.Consistent s1) in Hs1.
 pose proof (replay_closes_shape (T.closes b) s0 (T.pop M S q) ltac:(change (T.lo a<=T.net a)%Z; lia) Hrun1)
   as [Hl1 Hn1].
 change (T.lo s1 = Z.min (T.lo a) (T.net a-Z.of_nat (T.closes b))) in Hl1.
 change (T.net s1 = (T.net a-Z.of_nat (T.closes b))%Z) in Hn1.
 rewrite Hc in Hl1,Hn1.
 assert (Hl1m : T.lo s1 = CompactDepth.lo m) by (rewrite Hml,Hl1; f_equal; lia).
 assert (Hopenbound : (T.net s1+Z.of_nat (T.opens b)-T.lo s1 <=
     Z.of_nat (T.depth M S))%Z).
 { rewrite Hn1,Ho,Hl1m. rewrite Hmn in Hmd. lia. }
 pose proof (replay_opens_consistent (T.opens b) q1 Hs1 Hopenbound) as Hs2.
 destruct (T.replay_opens (T.opens b) (Some (s1,q1))) as [[s2 q2]|] eqn:Hrun2;
   [|exact I].
 change (T.Consistent s2) in Hs2.
 pose proof (proj1 Hs1) as Hd1.
 unfold CompactDepth.consistent,T.metadata in Hd1; cbn in Hd1.
 pose proof (replay_opens_shape (T.opens b) s1 q1 ltac:(lia) Hrun2) as [Hl2 Hn2].
 assert (Hl2m : T.lo s2 = CompactDepth.lo m) by congruence.
 assert (Hn2m : T.net s2 = CompactDepth.net m) by (rewrite Hn2,Hn1,Ho,Hmn; lia).
 cbn [T.ConsistentOpt]. apply consistent_of_padding; [exact Hm|].
 pose proof (consistent_padding Hs2) as Hp.
 change (Padded S (m_ne M) (T.regions s2)
   (Z.to_nat (-CompactDepth.lo m) + Z.to_nat (CompactDepth.net m-CompactDepth.lo m))).
 unfold T.active,T.closes,T.opens in Hp. rewrite Hl2m,Hn2m in Hp. exact Hp.
Qed.
End Consistency.
Section Queue.
Context {A : Type} (S : R.regions A) (HS : R.Laws S) (e : A).
Definition slot r j := nth j (R.view S r) e.
Lemma slot_top r : slot r 0 = R.top S r.
Proof. unfold slot; rewrite (R.view_top HS r); reflexivity. Qed.
Lemma slot_pop r j : slot (R.pop S r e) j = slot r (Datatypes.S j).
Proof.
 unfold slot.
 destruct (lt_dec j (2*R.depth S+1)) as [Hj|Hj].
 - pose proof (f_equal (fun xs => nth (Datatypes.S j) xs e) (R.view_pop HS r e)) as H.
   cbn in H.
   destruct (lt_dec (Datatypes.S j) (length (R.view S r))) as [Hk|Hk].
   + rewrite app_nth1 in H by exact Hk; exact H.
   + rewrite app_nth2 in H by lia. rewrite (R.view_size HS) in *.
     replace (Datatypes.S j-(2*R.depth S+1)) with 0 in H by lia.
     cbn in H. rewrite H; symmetry; apply nth_overflow; rewrite (R.view_size HS); lia.
 - rewrite !nth_overflow by (rewrite (R.view_size HS); lia); reflexivity.
Qed.
Lemma slot_iter_pop k r j :
 slot (Nat.iter k (fun q => R.pop S q e) r) j = slot r (j+k).
Proof.
 revert r j; induction k; intros r j.
 - rewrite Nat.add_0_r; reflexivity.
 - rewrite Nat.iter_succ, slot_pop, IHk. f_equal; lia.
Qed.

(** Reversing and discarding padding exposes the occupied prefix in
    replay order. This is a storage law, not an input-word semantics. *)
Lemma queue_slot r k j : k <= 2*R.depth S -> j <= k ->
 slot (Nat.iter (2*R.depth S-k) (fun q => R.pop S q e) (R.reverse S r)) j =
 slot r (k-j).
Proof.
 intros Hk Hj. rewrite slot_iter_pop. unfold slot.
 rewrite (R.view_reverse HS), rev_nth by (rewrite (R.view_size HS); lia).
 rewrite (R.view_size HS). f_equal; lia.
Qed.

Lemma padded_zero r : Padded S e r 0 ->
 R.replace S (R.fill S e) (R.top S r) = r.
Proof.
 intros [_ Hp]. apply (R.view_injective HS).
 rewrite (R.view_replace HS), (R.view_fill HS), (R.view_top HS r).
 change (R.top S r :: tl (repeat e (2*R.depth S+1)) = R.top S r :: tl (R.view S r)).
 f_equal.
 change (tl (R.view S r) = repeat e (2*R.depth S+1-1)) in Hp.
 rewrite Hp. replace (2*R.depth S+1) with (Datatypes.S (2*R.depth S)) by lia.
 cbn [repeat tl]. f_equal; lia.
Qed.
End Queue.
Section LeftIdentity.
Context {Raw Value : Type} (M : MonoidalOps (Nest Raw Value) Value).
Context (S : R.regions (m_summary M)) (HS : R.Laws S).

Lemma ne_left_neutral_balanced (s : T.t M S) : R.depth S < 50 ->
 IsMonoid M -> T.Consistent s -> T.active s = 0 ->
 T.op (T.ne M S) (Some s) = Some s.
Proof.
 intros HN HM Hs Hactive.
 assert (Hcounts : T.closes s = 0 /\ T.opens s = 0).
 { unfold T.active in Hactive; lia. }
 destruct Hcounts as [Hc Ho].
 pose proof (proj1 Hs) as Hd.
 unfold CompactDepth.consistent, T.metadata in Hd; cbn in Hd.
 assert (Hl : T.lo s = 0%Z) by (unfold T.closes in Hc; lia).
 assert (Hnet : T.net s = 0%Z) by (unfold T.opens in Ho; lia).
 unfold T.ne,T.supported,T.depth. rewrite (proj2 (Nat.ltb_lt _ _) HN).
 unfold T.op.
 assert (Hm : CompactDepth.combine (T.metadata (T.base M S (m_ne M)))
     (T.metadata s) = T.metadata s).
 { unfold CompactDepth.combine,T.metadata,T.base; cbn.
   rewrite Hl,Hnet. rewrite Z.max_r by lia. reflexivity. }
 rewrite Hm.
 assert (Hv : CompactDepth.valid (Z.of_nat (T.depth M S)) (T.metadata s) = true).
 { apply CompactDepth.valid_spec. split; [unfold T.depth; lia|exact (proj1 Hs)]. }
 rewrite Hv,Hc,Ho,Hactive. cbn [T.replay_closes T.replay_opens].
 assert (Hq : R.top S (Nat.iter (2*T.depth M S-0) (T.pop M S)
     (R.reverse S (T.regions s))) = R.top S (T.regions s)).
 { rewrite <- (slot_top HS (m_ne M)), <- (slot_top HS (m_ne M) (T.regions s)).
   unfold T.pop. exact (@queue_slot _ S HS (m_ne M) (T.regions s) 0 0 ltac:(lia) ltac:(lia)). }
 rewrite Hq.
 unfold T.append_region; cbn [T.lo T.hi T.net T.regions].
 rewrite (T.base_ne_regions M HS), (R.top_fill HS).
 destruct HM as [_ [Hleft _]]. rewrite Hleft.
 assert (Hr : R.replace S (R.fill S (m_ne M)) (R.top S (T.regions s)) = T.regions s).
 { apply padded_zero; [exact HS|].
   pose proof (consistent_padding Hs) as Hp. rewrite Hactive in Hp. exact Hp. }
 rewrite Hr. destruct s; reflexivity.
Qed.
End LeftIdentity.
Section Reconstruction.
Context {A : Type} (S : R.regions A) (HS : R.Laws S) (e : A).
Let cap := 2*R.depth S+1.
Lemma slot_push r x j : j < cap ->
 slot S e (R.push S r x) j = match j with 0 => x | Datatypes.S i => slot S e r i end.
Proof.
 intro Hj. unfold slot.
 pose proof (f_equal (fun xs => nth j xs e) (R.view_push HS r x)) as H.
 cbn beta in H.
 rewrite app_nth1 in H by (rewrite (R.view_size HS); exact Hj).
 destruct j; exact H.
Qed.
Lemma slot_replace r x j : slot S e (R.replace S r x) j =
 match j with 0 => x | Datatypes.S i => slot S e r (Datatypes.S i) end.
Proof.
 unfold slot; rewrite (R.view_replace HS). destruct j; [reflexivity|].
 rewrite (R.view_top HS r) at 2; reflexivity.
Qed.
Lemma slot_fill j : slot S e (R.fill S e) j = e.
Proof.
 unfold slot; rewrite (R.view_fill HS). apply nth_repeat.
Qed.
Lemma slot_ext r s : (forall j, j<cap -> slot S e r j=slot S e s j) -> r=s.
Proof.
 intro H; apply (R.view_injective HS). apply nth_ext with (d:=e) (d':=e).
 - rewrite !(R.view_size HS); reflexivity.
 - intros; apply H; unfold slot, cap in *; rewrite (R.view_size HS) in *; assumption.
Qed.
Lemma replace_push r x y : R.replace S (R.push S r x) y = R.push S r y.
Proof.
 apply slot_ext; intros j Hj. rewrite slot_replace.
 destruct j; rewrite !slot_push by assumption; reflexivity.
Qed.

Fixpoint consume n (r q : R.carrier S) : R.carrier S * R.carrier S :=
 match n with
 | 0 => (r,q)
 | Datatypes.S k => consume k (R.push S r (R.top S q)) (R.pop S q e)
 end.
Lemma consume_plus n m r q : consume (n+m) r q =
 let p := consume n r q in consume m (fst p) (snd p).
Proof. revert r q; induction n; intros; cbn [Nat.add consume]; auto. Qed.
Lemma consume_queue n r q : snd (consume n r q) = Nat.iter n (fun q => R.pop S q e) q.
Proof.
 revert r q; induction n; intros; cbn [consume]; [reflexivity|].
 rewrite IHn. rewrite Nat.iter_succ_r; reflexivity.
Qed.
Lemma consume_slot n r q j : j<cap ->
 slot S e (fst (consume n r q)) j =
 if j <? n then slot S e q (n-1-j) else slot S e r (j-n).
Proof.
 revert r q j; induction n; intros r q j Hj.
 - cbn [consume]. rewrite Nat.sub_0_r; reflexivity.
 - cbn [consume]. rewrite IHn by exact Hj.
   destruct (lt_dec j n) as [Hjn|Hjn].
   + rewrite (proj2 (Nat.ltb_lt _ _) Hjn).
     rewrite (proj2 (Nat.ltb_lt j (Datatypes.S n)) ltac:(lia)).
     rewrite (slot_pop HS). f_equal; lia.
   + rewrite (proj2 (Nat.ltb_ge j n) ltac:(lia)).
     rewrite slot_push by lia.
     destruct (Nat.eq_dec j n) as [->|Hneq].
     * rewrite Nat.sub_diag, (proj2 (Nat.ltb_lt n (Datatypes.S n)) ltac:(lia)).
       replace (Datatypes.S n-1-n) with 0 by lia. symmetry; apply slot_top; exact HS.
     * rewrite (proj2 (Nat.ltb_ge j (Datatypes.S n)) ltac:(lia)).
       destruct (j-n) eqn:Hsub; [lia|]. f_equal; lia.
Qed.
End Reconstruction.
Section ReplayReconstruction.
Context {Raw Value : Type} (M : MonoidalOps (Nest Raw Value) Value).
Context (S : R.regions (m_summary M)) (HS : R.Laws S) (HM : IsMonoid M).
Let e := m_ne M.
Lemma push_append r x :
 R.replace S (R.push S r e) (m_op M (R.top S (R.push S r e)) x) = R.push S r x.
Proof.
 assert (Htop : R.top S (R.push S r e) = e).
 { rewrite <- (slot_top HS e).
   apply (@slot_push _ S HS e r e 0); cbn; lia. }
 rewrite Htop. destruct HM as [_ [Hleft _]].
 rewrite Hleft. apply (replace_push HS e).
Qed.

Lemma replay_closes_unmatched n (s : T.t M S) q : T.lo s = T.net s ->
 exists t, T.replay_closes n (Some (s,q)) =
   Some (t,snd (consume S e n (T.regions s) q)) /\
 T.regions t = fst (consume S e n (T.regions s) q) /\ T.lo t = T.net t.
Proof.
 revert s q; induction n; intros s q Heq.
 - exists s; repeat split; try reflexivity; exact Heq.
 - assert (Ho : T.opens s = 0).
   { unfold T.opens; rewrite Heq,Z.sub_diag; reflexivity. }
   cbn [T.replay_closes]. unfold T.append_close; rewrite Ho; cbn [Nat.ltb].
   set (u := T.append_region
     (@T.mk Raw Value M S (Z.min (T.lo s) (T.net s-1))
       (Z.max (T.hi s) (T.net s)) (T.net s-1)%Z (R.push S (T.regions s) e)) (R.top S q)).
   assert (Hu : T.lo u = T.net u).
   { change (Z.min (T.lo s) (T.net s-1) = T.net s-1)%Z. rewrite Z.min_r by lia; reflexivity. }
   destruct (IHn u (T.pop M S q) Hu) as [t [Ht [Hr Hl]]].
   assert (Hreg : T.regions u = R.push S (T.regions s) (R.top S q)).
   { unfold u,T.append_region; cbn [T.regions]; apply push_append. }
   exists t. cbn [consume]. rewrite <- Hreg.
   exact (conj Ht (conj Hr Hl)).
Qed.

Lemma replay_opens_storage n (s : T.t M S) q :
 exists t, T.replay_opens n (Some (s,q)) =
   Some (t,snd (consume S e n (T.regions s) q)) /\
 T.regions t = fst (consume S e n (T.regions s) q).
Proof.
 revert s q; induction n; intros s q.
 - exists s; split; reflexivity.
 - cbn [T.replay_opens].
   destruct (IHn (T.append_region (T.append_open s) (R.top S q)) (T.pop M S q)) as [t [Ht Hr]].
   assert (Hreg : T.regions (T.append_region (T.append_open s) (R.top S q)) =
     R.push S (T.regions s) (R.top S q)).
   { unfold T.append_region,T.append_open; cbn [T.regions]; apply push_append. }
   exists t. cbn [consume]. rewrite <- Hreg. exact (conj Ht Hr).
Qed.
End ReplayReconstruction.
Section FinishReconstruction.
Context {A : Type} (S : R.regions A) (HS : R.Laws S) (e : A).
Lemma slot_padded r k j : Padded S e r k -> k<j -> slot S e r j=e.
Proof.
 intros [_ Hp] Hj. unfold slot.
 replace j with (Datatypes.S k + (j-Datatypes.S k)) by lia.
 rewrite <- nth_skipn, Hp. apply nth_repeat.
Qed.
Lemma reconstruct_regions r k : Padded S e r k ->
 let q := Nat.iter (2*R.depth S-k) (fun q => R.pop S q e) (R.reverse S r) in
 fst (consume S e k (R.replace S (R.fill S e) (R.top S q)) (R.pop S q e)) = r.
Proof.
 intros Hp q. pose proof (proj1 Hp) as Hk.
 apply (slot_ext HS e); intros j Hj.
 rewrite (consume_slot HS) by exact Hj.
 destruct (lt_dec j k) as [Hjk|Hjk].
 - rewrite (proj2 (Nat.ltb_lt _ _) Hjk), (slot_pop HS).
   unfold q. rewrite (queue_slot HS) by lia. f_equal; lia.
 - rewrite (proj2 (Nat.ltb_ge j k) ltac:(lia)), (slot_replace HS).
   destruct (Nat.eq_dec j k) as [->|Hneq].
   + rewrite Nat.sub_diag. rewrite <- (slot_top HS e q).
     unfold q. rewrite (queue_slot HS) by lia. f_equal; lia.
   + destruct (j-k) eqn:Hsub; [lia|]. rewrite (slot_fill HS).
     symmetry. apply slot_padded with (k:=k); [exact Hp|lia].
Qed.
End FinishReconstruction.
Section Identities.
Context {Raw Value : Type} (M : MonoidalOps (Nest Raw Value) Value).
Context (S : R.regions (m_summary M)) (HS : R.Laws S).

Theorem ne_left_neutral : R.depth S < 50 -> IsMonoid M ->
 forall s, T.ConsistentOpt s -> T.op (T.ne M S) s = s.
Proof.
 intros HN HM [s|] Hs; [|apply T.op_none_right].
 change (T.Consistent s) in Hs.
 pose proof (proj1 Hs) as Hd.
 unfold CompactDepth.consistent,T.metadata in Hd; cbn in Hd.
 unfold T.ne,T.supported,T.depth; rewrite (proj2 (Nat.ltb_lt _ _) HN).
 unfold T.op.
 assert (Hm : CompactDepth.combine (T.metadata (T.base M S (m_ne M)))
   (T.metadata s) = T.metadata s).
 { unfold CompactDepth.combine,T.metadata,T.base; cbn.
   rewrite Z.min_r, Z.max_r by lia; reflexivity. }
 rewrite Hm.
 assert (Hv : CompactDepth.valid (Z.of_nat (T.depth M S)) (T.metadata s) = true).
 { apply CompactDepth.valid_spec. split; [unfold T.depth; lia|exact (proj1 Hs)]. }
 rewrite Hv.
 set (q := Nat.iter (2*T.depth M S-T.active s) (T.pop M S) (R.reverse S (T.regions s))).
 set (s0 := T.append_region (T.base M S (m_ne M)) (R.top S q)).
 destruct (replay_closes_unmatched HS HM (T.closes s) s0 (T.pop M S q) eq_refl)
   as [s1 [Hrun1 [Hr1 Hl1]]].
 rewrite Hrun1.
 destruct (replay_opens_storage HS HM (T.opens s) s1
   (snd (consume S (m_ne M) (T.closes s) (T.regions s0) (T.pop M S q))))
   as [s2 [Hrun2 Hr2]].
 rewrite Hrun2.
 assert (Hr : T.regions s2 = T.regions s).
 { rewrite Hr2,Hr1.
   rewrite <- (consume_plus S (m_ne M)).
   fold (T.active s).
   assert (Hr0 : T.regions s0 = R.replace S (R.fill S (m_ne M)) (R.top S q)).
   { unfold s0,T.append_region; cbn [T.regions].
     rewrite (T.base_ne_regions M HS), (R.top_fill HS).
     destruct HM as [_ [Hleft _]]. rewrite Hleft; reflexivity. }
   rewrite Hr0. unfold q,T.depth,T.pop.
   apply reconstruct_regions; [exact HS|]. apply consistent_padding; exact Hs. }
 rewrite Hr. destruct s; reflexivity.
Qed.

Theorem ne_right_neutral : R.depth S < 50 -> IsMonoid M ->
 forall s, T.ConsistentOpt s -> T.op s (T.ne M S) = s.
Proof. apply (T.ne_right_neutral HS). Qed.
End Identities.
Section BoundaryCancellation.
Context {Raw Value : Type} (M : MonoidalOps (Nest Raw Value) Value).
Context (S : R.regions (m_summary M)) (HS : R.Laws S) (HM : IsMonoid M).
Let e := m_ne M.

Lemma padded_last r k : Padded S e r k -> k < 2*R.depth S -> R.last S r = e.
Proof.
 intros [_ Hp] Hroom.
 pose proof (firstn_skipn (Datatypes.S k) (R.view S r)) as Hsplit.
 rewrite Hp in Hsplit.
 replace (2*R.depth S+1-Datatypes.S k) with ((2*R.depth S-k-1)+1) in Hsplit by lia.
 rewrite repeat_app in Hsplit. cbn [repeat] in Hsplit.
 rewrite app_assoc in Hsplit.
 rewrite <- (R.view_last HS r e), <- Hsplit. apply last_last.
Qed.

(** Closing a newly opened region performs exactly one observation.
    The peak depth remains recorded even though lo and net return to
    their original values. No law is assumed of observation or generation. *)
Lemma close_open_region (s : T.t M S) x : T.Consistent s ->
 T.active s < 2*R.depth S ->
 T.append_close (T.append_region (T.append_open s) x) =
 option_map (fun v => @T.mk Raw Value M S (T.lo s)
   (Z.max (T.hi s) (T.net s+1)) (T.net s)
   (T.regions (T.append_region s (m_gen M (nested v))))) (m_obs M x).
Proof.
 intros Hs Hroom.
 pose proof (proj1 Hs) as Hd.
 unfold CompactDepth.consistent,T.metadata in Hd; cbn in Hd.
 assert (Hlast : R.last S (T.regions s) = e).
 { apply padded_last with (k:=T.active s); [apply consistent_padding; exact Hs|exact Hroom]. }
 set (u := T.append_region (T.append_open s) x).
 assert (Hreg : T.regions u = R.push S (T.regions s) x).
 { unfold u,T.append_region,T.append_open; cbn [T.regions]. apply push_append; assumption. }
 assert (Htop : R.top S (T.regions u) = x).
 { rewrite Hreg, <- (slot_top HS e).
   apply (@slot_push _ S HS e (T.regions s) x 0); cbn; lia. }
 assert (Hpop : T.pop M S (T.regions u) = T.regions s).
 { rewrite Hreg. unfold T.pop. apply pop_push; assumption. }
 assert (Hopen : (0 <? T.opens u) = true).
 { apply Nat.ltb_lt. unfold u,T.opens,T.append_region,T.append_open; cbn [T.lo T.net].
   rewrite Z.min_l by lia. lia. }
 fold u.
 unfold T.append_close. rewrite Hopen,Htop,Hpop.
 destruct (m_obs M x) as [v|]; [|reflexivity].
 cbn [option_map]. unfold u,T.append_region,T.append_open; cbn [T.lo T.hi T.net T.regions].
 rewrite Z.min_l by lia.
 replace (T.net s+1-1)%Z with (T.net s) by lia.
 rewrite Z.min_l by lia.
 rewrite (Z.max_l (Z.max (T.hi s) (T.net s+1)) (T.net s+1)) by apply Z.le_max_r.
 reflexivity.
Qed.
Lemma close_open_regions (s : T.t M S) x y : T.Consistent s ->
 T.active s < 2*R.depth S ->
 T.append_close (T.append_region (T.append_region (T.append_open s) x) y) =
 option_map (fun v => @T.mk Raw Value M S (T.lo s)
   (Z.max (T.hi s) (T.net s+1)) (T.net s)
   (T.regions (T.append_region s (m_gen M (nested v))))) (m_obs M (m_op M x y)).
Proof.
 intros Hs Hr. rewrite append_region_associative by assumption.
 apply close_open_region; assumption.
Qed.
End BoundaryCancellation.

(** Replay does not inspect hi. This relation is only for replay:
    [op]'s guard and final metadata still require the full depth record. *)
Section ReplayCongruence.
Context {Raw Value : Type} (M : MonoidalOps (Nest Raw Value) Value).
Context (S : R.regions (m_summary M)).
Definition SameCore (a b : T.t M S) :=
 T.lo a = T.lo b /\ T.net a = T.net b /\ T.regions a = T.regions b.
Definition SameCoreOpt a b := match a,b with
 | Some a,Some b => SameCore a b | None,None => True | _,_ => False end.
Definition SameState (a b : option (T.t M S * R.carrier S)) := match a,b with
 | Some (a,q),Some (b,r) => SameCore a b /\ q=r
 | None,None => True | _,_ => False end.

Lemma append_region_same_core a b x : SameCore a b ->
 SameCore (T.append_region a x) (T.append_region b x).
Proof.
 unfold SameCore,T.append_region. destruct a,b; cbn.
 intros [-> [-> ->]]; repeat split; reflexivity.
Qed.
Lemma append_open_same_core a b : SameCore a b ->
 SameCore (T.append_open a) (T.append_open b).
Proof.
 unfold SameCore,T.append_open. destruct a,b; cbn.
 intros [-> [-> ->]]; repeat split; reflexivity.
Qed.
Lemma append_close_same_core a b : SameCore a b ->
 SameCoreOpt (T.append_close a) (T.append_close b).
Proof.
 destruct a as [la ha na ra],b as [lb hb nb rb].
 unfold SameCore; cbn; intros [-> [-> ->]].
 unfold T.append_close,T.opens; cbn [T.lo T.net T.regions].
 destruct (0 <? Z.to_nat (nb-lb));
   [destruct (m_obs M (R.top S rb))|]; cbn [SameCoreOpt SameCore T.lo T.net T.regions];
   repeat split; reflexivity.
Qed.
Lemma replay_opens_same_core n a b : SameState a b ->
 SameState (T.replay_opens n a) (T.replay_opens n b).
Proof.
 revert a b; induction n; intros a b H; [exact H|].
 destruct a as [[a q]|],b as [[b r]|]; try contradiction; [|exact I].
 destruct H as [H ->]. cbn [T.replay_opens]. apply IHn.
 split; [apply append_region_same_core,append_open_same_core; exact H|reflexivity].
Qed.
Lemma replay_closes_same_core n a b : SameState a b ->
 SameState (T.replay_closes n a) (T.replay_closes n b).
Proof.
 revert a b; induction n; intros a b H; [exact H|].
 destruct a as [[a q]|],b as [[b r]|]; try contradiction; [|exact I].
 destruct H as [H ->]. cbn [T.replay_closes].
 pose proof (append_close_same_core H) as Hclose.
 destruct (T.append_close a), (T.append_close b); try contradiction; [|exact I].
 apply IHn. split; [apply append_region_same_core; exact Hclose|reflexivity].
Qed.
End ReplayCongruence.
Module DepthAlgebra.
Module D := CompactDepth.
Open Scope Z_scope.
Open Scope bool_scope.
Definition WellFormed a := D.lo a <= 0 /\ 0 <= D.hi a /\
 D.lo a <= D.net a /\ D.net a <= D.hi a.

Lemma combine_associative a b c : D.combine (D.combine a b) c = D.combine a (D.combine b c).
Proof.
 unfold D.combine; cbn. f_equal.
 - rewrite <- Z.add_min_distr_l, !Z.add_assoc, Z.min_assoc; reflexivity.
 - rewrite <- Z.add_max_distr_l, !Z.add_assoc, Z.max_assoc; reflexivity.
 - lia.
Qed.
Lemma combine_wellformed a b : WellFormed a -> WellFormed b -> WellFormed (D.combine a b).
Proof.
 unfold WellFormed,D.combine; cbn; intros Ha Hb.
 pose proof (Z.le_min_l (D.lo a) (D.net a+D.lo b)).
 pose proof (Z.le_min_r (D.lo a) (D.net a+D.lo b)).
 pose proof (Z.le_max_l (D.hi a) (D.net a+D.hi b)).
 pose proof (Z.le_max_r (D.hi a) (D.net a+D.hi b)). lia.
Qed.
Lemma valid_left d a b : WellFormed a -> D.valid d (D.combine a b) = true -> D.valid d a = true.
Proof.
 intros Ha H. apply D.valid_spec in H as [Hd H]. apply D.valid_spec. split; [exact Hd|].
 unfold D.consistent,D.combine in H; cbn in H.
 unfold D.consistent,WellFormed in *.
 pose proof (Z.le_min_l (D.lo a) (D.net a+D.lo b)).
 pose proof (Z.le_max_l (D.hi a) (D.net a+D.hi b)). lia.
Qed.
Lemma valid_right d a b : WellFormed b -> D.valid d (D.combine a b) = true -> D.valid d b = true.
Proof.
 intros Hb H. apply D.valid_spec in H as [Hd H]. apply D.valid_spec. split; [exact Hd|].
 unfold D.consistent,D.combine in H; cbn in H.
 unfold D.consistent,WellFormed in *.
 pose proof (Z.le_min_r (D.lo a) (D.net a+D.lo b)).
 pose proof (Z.le_max_r (D.hi a) (D.net a+D.hi b)). lia.
Qed.
Theorem guards_associative d a b c : WellFormed a -> WellFormed b -> WellFormed c ->
 (D.valid d (D.combine a b) && D.valid d (D.combine (D.combine a b) c)) =
 (D.valid d (D.combine b c) && D.valid d (D.combine a (D.combine b c))).
Proof.
 intros Ha Hb Hc. apply Bool.eq_true_iff_eq.
 rewrite !Bool.andb_true_iff, combine_associative.
 split; intros [_ H]; split; try exact H.
 - eapply valid_right; [apply combine_wellformed; eassumption|exact H].
 - rewrite <- combine_associative in H.
   eapply valid_left; [apply combine_wellformed; eassumption|exact H].
Qed.
End DepthAlgebra.
Module D := CompactDepth.
Section OperatorDepth.
Context {Raw Value : Type} (M : MonoidalOps (Nest Raw Value) Value).
Context (S : R.regions (m_summary M)).

Lemma op_success_metadata (a b r : T.t M S) :
 T.op (Some a) (Some b) = Some r ->
 T.metadata r = D.combine (T.metadata a) (T.metadata b).
Proof.
 unfold T.op.
 destruct (D.valid (Z.of_nat (T.depth M S)) (D.combine (T.metadata a) (T.metadata b)));
   [|discriminate].
 match goal with |- context [T.replay_opens ?n ?state] =>
   destruct (T.replay_opens n state) as [[s q]|] eqn:Hrun
 end; [|discriminate].
 intro H; inversion H; subst r.
 unfold T.metadata; cbn [T.lo T.hi T.net].
 destruct (D.combine (T.metadata a) (T.metadata b)); reflexivity.
Qed.

Lemma op_invalid (a b : T.t M S) :
 D.valid (Z.of_nat (T.depth M S)) (D.combine (T.metadata a) (T.metadata b)) = false ->
 T.op (Some a) (Some b) = None.
Proof. intro H; unfold T.op; rewrite H; reflexivity. Qed.

(** If the total depth envelope fails, neither grouping can succeed.
    This also covers an earlier observation failure on either side. *)
Theorem associative_depth_failure (a b c : T.t M S) :
 D.valid (Z.of_nat (T.depth M S))
   (D.combine (D.combine (T.metadata a) (T.metadata b)) (T.metadata c)) = false ->
 T.op (T.op (Some a) (Some b)) (Some c) = None /\
 T.op (Some a) (T.op (Some b) (Some c)) = None.
Proof.
 intro H. split.
 - destruct (T.op (Some a) (Some b)) as [ab|] eqn:Hab; [|reflexivity].
   apply op_invalid. rewrite (op_success_metadata a b Hab). exact H.
 - destruct (T.op (Some b) (Some c)) as [bc|] eqn:Hbc.
   + apply op_invalid. rewrite (op_success_metadata b c Hbc).
     rewrite <- DepthAlgebra.combine_associative. exact H.
   + apply T.op_none_right.
Qed.

Theorem associative_success_metadata (a b c ab bc l r : T.t M S) :
 T.op (Some a) (Some b) = Some ab -> T.op (Some b) (Some c) = Some bc ->
 T.op (Some ab) (Some c) = Some l -> T.op (Some a) (Some bc) = Some r ->
 T.metadata l = T.metadata r.
Proof.
 intros Hab Hbc Hl Hr.
 rewrite (op_success_metadata ab c Hl), (op_success_metadata a bc Hr),
   (op_success_metadata a b Hab), (op_success_metadata b c Hbc).
 apply DepthAlgebra.combine_associative.
Qed.
Lemma summary_ext (a b : T.t M S) : T.metadata a = T.metadata b ->
 T.regions a = T.regions b -> a=b.
Proof.
 destruct a,b; unfold T.metadata; cbn [T.lo T.hi T.net T.regions].
 intros H Hregions; inversion H; subst; reflexivity.
Qed.

(** The remaining associativity obligation is replay/core agreement.
    Full metadata equality is supplied by the independently proved depth
    algebra; this lemma does not assume the desired equality of summaries. *)
Lemma associativity_from_same_core (a b c : T.t M S) :
 SameCoreOpt
   (T.op (T.op (Some a) (Some b)) (Some c))
   (T.op (Some a) (T.op (Some b) (Some c))) ->
 T.op (T.op (Some a) (Some b)) (Some c) =
 T.op (Some a) (T.op (Some b) (Some c)).
Proof.
 destruct (T.op (Some a) (Some b)) as [ab|] eqn:Hab;
 destruct (T.op (Some b) (Some c)) as [bc|] eqn:Hbc.
 - destruct (T.op (Some ab) (Some c)) as [l|] eqn:Hl;
   destruct (T.op (Some a) (Some bc)) as [r|] eqn:Hr;
   intro H; try contradiction; [|reflexivity].
   f_equal. apply summary_ext.
   + exact (associative_success_metadata a b c Hab Hbc Hl Hr).
   + exact (proj2 (proj2 H)).
 - rewrite T.op_none_right.
   destruct (T.op (Some ab) (Some c)); intro H; [contradiction|reflexivity].
 - rewrite T.op_none_left.
   destruct (T.op (Some a) (Some bc)); intro H; [contradiction|reflexivity].
 - rewrite T.op_none_left,T.op_none_right. reflexivity.
Qed.
End OperatorDepth.
Section CancellationContext.
Context {Raw Value : Type} (M : MonoidalOps (Nest Raw Value) Value).
Context (S : R.regions (m_summary M)) (HS : R.Laws S) (HM : IsMonoid M).

Definition continue_replay closes opens state :=
 @T.replay_opens Raw Value M S opens (@T.replay_closes Raw Value M S closes state).

Lemma continue_same_core closes opens a b : SameState a b ->
 SameState (continue_replay closes opens a) (continue_replay closes opens b).
Proof. intro H; apply replay_opens_same_core,replay_closes_same_core; exact H. Qed.

(** The region on either side of a split is combined before observation.
    The continuation may contain any number of further closes and opens. *)
Theorem cancel_boundary_in_replay (s : T.t M S) x y z q closes opens :
 T.Consistent s -> T.active s < 2*R.depth S ->
 SameState
 (continue_replay closes opens
   (match T.append_close (T.append_region (T.append_region (T.append_open s) x) y) with
    | None => None
    | Some t => Some (T.append_region t z,q)
    end))
 (continue_replay closes opens
   (option_map (fun v => (T.append_region (T.append_region s (m_gen M (nested v))) z,q))
     (m_obs M (m_op M x y)))).
Proof.
 intros Hs Hroom. apply continue_same_core.
 rewrite (close_open_regions HS HM x y Hs Hroom).
 destruct (m_obs M (m_op M x y)); [|exact I].
 cbn [option_map SameState]. split; [|reflexivity].
 apply append_region_same_core. repeat split; reflexivity.
Qed.

Lemma same_state_none_iff (a b : option (T.t M S * R.carrier S)) :
 SameState a b -> (a=None <-> b=None).
Proof.
 destruct a as [[a q]|],b as [[b r]|]; intro H; try contradiction;
 split; intro Hnone; try discriminate; reflexivity.
Qed.

Corollary cancel_boundary_failure_iff (s : T.t M S) x y z q closes opens :
 T.Consistent s -> T.active s < 2*R.depth S ->
 (continue_replay closes opens
   (match T.append_close (T.append_region (T.append_region (T.append_open s) x) y) with
    | None => None | Some t => Some (T.append_region t z,q) end) = None <->
  continue_replay closes opens
   (option_map (fun v => (T.append_region (T.append_region s (m_gen M (nested v))) z,q))
     (m_obs M (m_op M x y))) = None).
Proof.
 intros Hs Hroom. apply same_state_none_iff.
 apply cancel_boundary_in_replay; assumption.
Qed.
Lemma same_state_trans (a b c : option (T.t M S * R.carrier S)) :
 SameState a b -> SameState b c -> SameState a c.
Proof.
 destruct a as [[a q]|],b as [[b r]|],c as [[c t]|];
 cbn [SameState]; try tauto.
 intros [[Hl [Hn Hr]] Hq] [[Hl' [Hn' Hr']] Hq'].
 split; [unfold SameCore; repeat split; congruence|congruence].
Qed.

(** Proof-only stacks of region summaries, innermost first. These are
    not character sequences or a parsing correctness interpretation. *)
Fixpoint open_stack (s : T.t M S) (xs : list (m_summary M)) :=
 match xs with
 | nil => s
 | x :: rest => T.append_region (T.append_open (open_stack s rest)) x
 end.
Fixpoint stack_safe (s : T.t M S) (xs : list (m_summary M)) : Prop :=
 match xs with
 | nil => True
 | _ :: rest => stack_safe s rest /\ T.Consistent (open_stack s rest) /\
   T.active (open_stack s rest) < 2*R.depth S
 end.

(** Collapse matched frames without constructing intermediate tuples. *)
Fixpoint cancel_values (xs : list (m_summary M)) y q : option (m_summary M * R.carrier S) :=
 match xs with
 | nil => Some (y,q)
 | x :: rest =>
   match m_obs M (m_op M x y) with
   | None => None
   | Some v => cancel_values rest (m_op M (m_gen M (nested v)) (R.top S q)) (T.pop M S q)
   end
 end.

Theorem cancel_stack_replay (s : T.t M S) xs y q : stack_safe s xs ->
 SameState
   (T.replay_closes (length xs) (Some (T.append_region (open_stack s xs) y,q)))
   (option_map (fun p => (T.append_region s (fst p),snd p)) (cancel_values xs y q)).
Proof.
 revert y q; induction xs as [|x xs IH]; intros y q Hsafe.
 - cbn [open_stack length T.replay_closes cancel_values option_map SameState SameCore];
   repeat split; reflexivity.
 - destruct Hsafe as [Hsafe [Hs Hroom]].
   cbn [open_stack length T.replay_closes].
   rewrite (close_open_regions HS HM x y Hs Hroom).
   cbn [cancel_values].
   destruct (m_obs M (m_op M x y)) as [v|].
   2: { exact I. }
   cbn [option_map].
   eapply same_state_trans with (b:=T.replay_closes (length xs)
     (Some (T.append_region (open_stack s xs)
       (m_op M (m_gen M (nested v)) (R.top S q)),T.pop M S q))).
   + apply replay_closes_same_core. split; [|reflexivity].
     rewrite <- (append_region_associative (open_stack s xs)
       (m_gen M (nested v)) (R.top S q) HM HS).
     apply append_region_same_core. repeat split; reflexivity.
   + apply IH; exact Hsafe.
Qed.
Corollary cancel_stack_with_tail (s : T.t M S) xs y q closes opens : stack_safe s xs ->
 SameState
   (continue_replay (length xs+closes) opens
     (Some (T.append_region (open_stack s xs) y,q)))
   (continue_replay closes opens
     (option_map (fun p => (T.append_region s (fst p),snd p)) (cancel_values xs y q))).
Proof.
 intro Hsafe. unfold continue_replay.
 rewrite replay_closes_plus.
 apply replay_opens_same_core,replay_closes_same_core,cancel_stack_replay; exact Hsafe.
Qed.

Corollary cancel_stack_failure (s : T.t M S) xs y q : stack_safe s xs ->
 (T.replay_closes (length xs) (Some (T.append_region (open_stack s xs) y,q)) = None <->
   cancel_values xs y q = None).
Proof.
 intro Hsafe. pose proof (same_state_none_iff _ _ (cancel_stack_replay s xs y q Hsafe)) as H.
 destruct (cancel_values xs y q) as [[v r]|]; cbn [option_map] in H;
   split; intro Hnone; try discriminate; try reflexivity.
 - apply H in Hnone; discriminate.
 - apply H; reflexivity.
Qed.
End CancellationContext.
Section OpenDecomposition.
Context {Raw Value : Type} (M : MonoidalOps (Nest Raw Value) Value).
Context (S : R.regions (m_summary M)) (HS : R.Laws S) (HM : IsMonoid M).

(** Remove one unmatched-open frame without observing it. The historical
    peak is retained, so rebuilding the frame restores the exact summary. *)
Definition peel_open (s : T.t M S) :=
 @T.mk Raw Value M S (T.lo s) (T.hi s) (T.net s-1)%Z (T.pop M S (T.regions s)).

Lemma peel_open_counts s : T.Consistent s -> 0<T.opens s ->
 Datatypes.S (T.opens (peel_open s)) = T.opens s /\
 Datatypes.S (T.active (peel_open s)) = T.active s.
Proof.
 intros [Hd _] Ho.
 unfold CompactDepth.consistent,T.metadata in Hd; cbn in Hd.
 unfold T.opens in Ho.
 assert (Hpos : (0<T.net s-T.lo s)%Z) by lia.
 unfold T.active,T.closes,T.opens,peel_open; cbn [T.lo T.net].
 assert (Hcount : Datatypes.S (Z.to_nat (T.net s-1-T.lo s)) = Z.to_nat (T.net s-T.lo s)).
 { apply Nat2Z.inj. rewrite Nat2Z.inj_succ,!Z2Nat.id by lia. lia. }
 split; lia.
Qed.

Lemma peel_open_consistent s : T.Consistent s -> 0<T.opens s ->
 T.Consistent (peel_open s).
Proof.
 intros Hs Ho. pose proof (peel_open_counts Hs Ho) as [Hopens Hactive].
 apply consistent_of_padding.
 - pose proof (proj1 Hs) as Hd.
   unfold CompactDepth.consistent,T.metadata in Hd |- *.
   cbn [peel_open T.lo T.hi T.net CompactDepth.lo CompactDepth.hi CompactDepth.net].
   cbn in Hd. unfold T.opens in Ho; lia.
 - change (Padded S (m_ne M) (R.pop S (T.regions s) (m_ne M)) (T.active (peel_open s))).
   apply pop_padded; [exact HS|]. rewrite Hactive.
   apply consistent_padding; exact Hs.
Qed.

Lemma peel_open_inverse s : T.Consistent s -> 0<T.opens s ->
 T.append_region (T.append_open (peel_open s)) (R.top S (T.regions s)) = s.
Proof.
 intros Hs Ho. pose proof (proj1 Hs) as Hd.
 unfold CompactDepth.consistent,T.metadata in Hd; cbn in Hd.
 assert (Hpos : (T.lo s <= T.net s-1)%Z) by (unfold T.opens in Ho; lia).
 unfold T.append_region,T.append_open,peel_open; cbn [T.lo T.hi T.net T.regions].
 rewrite (push_append HS HM).
 unfold T.pop. rewrite (push_pop M (T.regions s) (m_ne M) HS).
 rewrite Z.min_l by exact Hpos.
 replace (T.net s-1+1)%Z with (T.net s) by lia.
 rewrite Z.max_l by lia. destruct s; reflexivity.
Qed.

Theorem summary_open_decomposition (s : T.t M S) : T.Consistent s ->
 exists base xs,
 T.Consistent base /\ T.opens base=0 /\ length xs=T.opens s /\
 stack_safe base xs /\ open_stack base xs=s.
Proof.
 remember (T.opens s) as n eqn:Hn. revert s Hn.
 induction n as [|n IH]; intros s Hn Hs.
 - exists s,nil. split; [exact Hs|]. split; [lia|].
   split; [reflexivity|]. split; [exact I|reflexivity].
 - assert (Ho : 0<T.opens s) by lia.
   pose proof (peel_open_counts Hs Ho) as [Hopens Hactive].
   pose proof (peel_open_consistent Hs Ho) as Hp.
   destruct (IH (peel_open s) ltac:(lia) Hp)
     as [base [xs [Hb [Hbase [Hlen [Hsafe Hstack]]]]]].
   exists base,(R.top S (T.regions s)::xs).
   split; [exact Hb|]. split; [exact Hbase|].
   split; [cbn [length]; lia|]. split.
   + cbn [stack_safe]. split; [exact Hsafe|]. rewrite Hstack.
     split; [exact Hp|]. pose proof (proj1 (proj2 Hs)) as Hbound.
     unfold T.depth in Hbound; lia.
   + cbn [open_stack]. rewrite Hstack. apply peel_open_inverse; assumption.
Qed.
Theorem summary_open_prefix_decomposition k (s : T.t M S) :
 T.Consistent s -> k <= T.opens s ->
 exists base xs,
 T.Consistent base /\ length xs=k /\ T.opens base+k=T.opens s /\
 stack_safe base xs /\ open_stack base xs=s.
Proof.
 revert s; induction k as [|k IH]; intros s Hs Hk.
 - exists s,nil. split; [exact Hs|]. split; [reflexivity|].
   split; [lia|]. split; [exact I|reflexivity].
 - assert (Ho : 0<T.opens s) by lia.
   pose proof (peel_open_counts Hs Ho) as [Hopens Hactive].
   pose proof (peel_open_consistent Hs Ho) as Hp.
   destruct (IH (peel_open s) Hp ltac:(lia))
     as [base [xs [Hb [Hlen [Hbase [Hsafe Hstack]]]]]].
   exists base,(R.top S (T.regions s)::xs).
   split; [exact Hb|]. split; [cbn [length]; lia|].
   split; [lia|]. split.
   + cbn [stack_safe]. split; [exact Hsafe|]. rewrite Hstack.
     split; [exact Hp|]. pose proof (proj1 (proj2 Hs)) as Hbound.
     unfold T.depth in Hbound; lia.
   + cbn [open_stack]. rewrite Hstack. apply peel_open_inverse; assumption.
Qed.

(** Apply stack cancellation to an arbitrary summary, not merely to a
    caller-supplied stack. k may be the minimum of the available opens
    and the incoming closes. The unmatched remainder is replayed normally. *)
Theorem matched_replay_decomposition k (s : T.t M S) y q closes opens :
 T.Consistent s -> k <= T.opens s ->
 exists base xs,
 T.Consistent base /\ length xs=k /\ T.opens base+k=T.opens s /\
 SameState
   (continue_replay (k+closes) opens (Some (T.append_region s y,q)))
   (continue_replay closes opens
     (option_map (fun p => (T.append_region base (fst p),snd p)) (cancel_values M S xs y q))).
Proof.
 intros Hs Hk.
 destruct (summary_open_prefix_decomposition Hs Hk)
   as [base [xs [Hb [Hlen [Hcount [Hsafe Hstack]]]]]].
 exists base,xs. split; [exact Hb|]. split; [exact Hlen|]. split; [exact Hcount|].
 rewrite <- Hstack, <- Hlen. apply cancel_stack_with_tail; assumption.
Qed.
Corollary matched_operand_replay (a b : T.t M S) : T.Consistent a ->
 let k := Nat.min (T.opens a) (T.closes b) in
 let q := Nat.iter (2*T.depth M S-T.active b) (T.pop M S) (R.reverse S (T.regions b)) in
 exists base xs,
 T.Consistent base /\ length xs=k /\ T.opens base+k=T.opens a /\
 (T.opens base=0 \/ T.closes b-k=0) /\
 SameState
   (continue_replay (T.closes b) (T.opens b) (Some (T.append_region a (R.top S q),T.pop M S q)))
   (continue_replay (T.closes b-k) (T.opens b)
     (option_map (fun p => (T.append_region base (fst p),snd p))
       (cancel_values M S xs (R.top S q) (T.pop M S q)))).
Proof.
 intros Ha k q.
 assert (Hka : k<=T.opens a) by (unfold k; apply Nat.le_min_l).
 assert (Hkb : k<=T.closes b) by (unfold k; apply Nat.le_min_r).
 destruct (matched_replay_decomposition (R.top S q) (T.pop M S q)
   (T.closes b-k) (T.opens b) Ha Hka)
   as [base [xs [Hb [Hlen [Hcount Hreplay]]]]].
 exists base,xs. split; [exact Hb|]. split; [exact Hlen|]. split; [exact Hcount|].
 split.
 - unfold k in Hcount |- *.
   destruct (le_dec (T.opens a) (T.closes b)).
   + rewrite Nat.min_l in Hcount by assumption; left; lia.
   + rewrite Nat.min_r by lia; right; lia.
 - replace (k+(T.closes b-k)) with (T.closes b) in Hreplay by lia.
   exact Hreplay.
Qed.
End OpenDecomposition.
Section CancellationComposition.
Context {Raw Value : Type} (M : MonoidalOps (Nest Raw Value) Value).
Context (S : R.regions (m_summary M)) (HS : R.Laws S).

Lemma open_stack_app s xs ys :
 open_stack (M:=M) (S:=S) s (xs++ys) = open_stack (open_stack s ys) xs.
Proof. induction xs; cbn [app open_stack]; [reflexivity|rewrite IHxs; reflexivity]. Qed.

Lemma stack_safe_app s xs ys :
 stack_safe (M:=M) (S:=S) s (xs++ys) <->
 stack_safe s ys /\ stack_safe (open_stack s ys) xs.
Proof.
 induction xs; cbn [app stack_safe]; [tauto|].
 rewrite IHxs,open_stack_app. tauto.
Qed.

(** Grouping matched frames into blocks does not change the scalar
    cancellation result, including failure at any position. *)
Theorem cancel_values_app xs ys y q :
 cancel_values M S (xs++ys) y q =
 match cancel_values M S xs y q with
 | None => None | Some (z,r) => cancel_values M S ys z r
 end.
Proof.
 revert y q; induction xs as [|x xs IH]; intros y q; cbn [app cancel_values].
 - reflexivity.
 - destruct (m_obs M (m_op M x y)); [apply IH|reflexivity].
Qed.

Corollary cancel_values_failure_prefix xs ys y q :
 cancel_values M S xs y q = None -> cancel_values M S (xs++ys) y q = None.
Proof. intro H; rewrite cancel_values_app,H; reflexivity. Qed.

Lemma cancel_values_head_associative x y z xs q : IsMonoid M ->
 cancel_values M S (m_op M x y::xs) z q =
 cancel_values M S (x::xs) (m_op M y z) q.
Proof. intros [Hassoc _]; cbn [cancel_values]; rewrite Hassoc; reflexivity. Qed.

Lemma cancel_values_queue xs y q z r : cancel_values M S xs y q = Some (z,r) ->
 r = Nat.iter (length xs) (T.pop M S) q.
Proof.
 revert y q; induction xs as [|x xs IH]; intros y q H.
 - cbn [cancel_values] in H; inversion H; reflexivity.
 - cbn [cancel_values] in H. destruct (m_obs M (m_op M x y)); [|discriminate].
   specialize (IH _ _ H). cbn [length]. rewrite Nat.iter_succ_r. exact IH.
Qed.

(** Cancellation inspects only the queue prefix it consumes. This is
    deliberately weaker than equality of whole fixed-capacity tuples. *)
Theorem cancel_values_queue_prefix xs y q r :
 (forall j, j<length xs -> slot S (m_ne M) q j = slot S (m_ne M) r j) ->
 option_map (@fst (m_summary M) (R.carrier S)) (cancel_values M S xs y q) =
 option_map (@fst (m_summary M) (R.carrier S)) (cancel_values M S xs y r).
Proof.
 revert y q r; induction xs as [|x xs IH]; intros y q r Hprefix.
 - reflexivity.
 - cbn [cancel_values]. destruct (m_obs M (m_op M x y)); [|reflexivity].
   assert (Htop : R.top S q=R.top S r).
   { rewrite <- (slot_top HS (m_ne M) q), <- (slot_top HS (m_ne M) r).
     apply Hprefix; cbn [length]; lia. }
   rewrite Htop. apply IH. intros j Hj.
   unfold T.pop. rewrite !(slot_pop HS).
   apply Hprefix; cbn [length]; lia.
Qed.
Theorem cancel_values_boundary_associative prefix suffix x y z q : IsMonoid M ->
 cancel_values M S (prefix ++ (m_op M x y::suffix)) z q =
 match cancel_values M S prefix z q with
 | None => None
 | Some (v,r) => cancel_values M S (x::suffix) (m_op M y v) r
 end.
Proof.
 intro HM. rewrite cancel_values_app.
 destruct (cancel_values M S prefix z q) as [[v r]|]; [|reflexivity].
 apply cancel_values_head_associative; exact HM.
Qed.

Theorem replay_cancel_two_blocks (s : T.t M S) xs ys z q : IsMonoid M ->
 stack_safe s (xs++ys) ->
 SameState
   (T.replay_closes (length xs+length ys)
     (Some (T.append_region (open_stack (open_stack s ys) xs) z,q)))
   (match cancel_values M S xs z q with
    | None => None
    | Some (v,r) => option_map (fun p => (T.append_region s (fst p),snd p))
         (cancel_values M S ys v r)
    end).
Proof.
 intros HM Hsafe. rewrite <- open_stack_app, <- length_app.
 pose proof (cancel_stack_replay HS HM s (xs++ys) z q Hsafe) as H.
 rewrite cancel_values_app in H.
 destruct (cancel_values M S xs z q) as [[v r]|]; exact H.
Qed.

Corollary cancel_values_queue_failure xs y q r :
 (forall j, j<length xs -> slot S (m_ne M) q j = slot S (m_ne M) r j) ->
 (cancel_values M S xs y q=None <-> cancel_values M S xs y r=None).
Proof.
 intro Hprefix. pose proof (cancel_values_queue_prefix xs y q r Hprefix) as H.
 destruct (cancel_values M S xs y q), (cancel_values M S xs y r);
   cbn [option_map] in H; split; intro Hnone; try discriminate; reflexivity.
Qed.
End CancellationComposition.
Section DeterministicFrames.
Context {Raw Value : Type} (M : MonoidalOps (Nest Raw Value) Value).
Context (S : R.regions (m_summary M)) (HS : R.Laws S) (HM : IsMonoid M).

Lemma open_stack_regions s x xs :
 T.regions (open_stack (M:=M) (S:=S) s (x::xs)) =
 R.push S (T.regions (open_stack s xs)) x.
Proof.
 cbn [open_stack]. unfold T.append_region,T.append_open; cbn [T.regions].
 apply push_append; assumption.
Qed.

Lemma open_stack_slots s xs j : j<length xs -> j<2*R.depth S+1 ->
 slot S (m_ne M) (T.regions (open_stack (M:=M) (S:=S) s xs)) j = nth j xs (m_ne M).
Proof.
 revert j; induction xs as [|x xs IH]; intros j Hlen Hcap; [cbn in Hlen; lia|].
 rewrite open_stack_regions, (slot_push HS) by exact Hcap.
 destruct j; [reflexivity|]. cbn [nth]. apply IH; cbn [length] in Hlen; lia.
Qed.

Lemma open_stack_frame_count s xs : stack_safe (M:=M) (S:=S) s xs ->
 length xs <= 2*R.depth S.
Proof.
 intro Hsafe.
 assert (Hactive : T.active (open_stack s xs) = T.active s+length xs).
 { induction xs as [|x xs IH]; [cbn [open_stack length]; lia|].
   destruct Hsafe as [Hsafe [Hcons Hroom]]. specialize (IH Hsafe).
   cbn [open_stack length].
   change (T.active (T.append_open (open_stack s xs)) = T.active s+Datatypes.S (length xs)).
   rewrite (append_open_active Hcons). lia. }
 destruct xs as [|x xs]; [cbn; lia|].
 destruct Hsafe as [_ [Hcons Hroom]].
 cbn [open_stack length] in Hactive.
 change (T.active (T.append_open (open_stack s xs)) = T.active s+Datatypes.S (length xs)) in Hactive.
 rewrite (append_open_active Hcons) in Hactive. cbn [length]; lia.
Qed.

Theorem open_stack_frames_exact s xs : stack_safe (M:=M) (S:=S) s xs ->
 firstn (length xs) (R.view S (T.regions (open_stack s xs))) = xs.
Proof.
 intro Hsafe. pose proof (open_stack_frame_count s xs Hsafe) as Hlen.
 apply nth_ext with (d:=m_ne M) (d':=m_ne M).
 - rewrite length_firstn,(R.view_size HS),Nat.min_l by lia; reflexivity.
 - intros j Hj. rewrite length_firstn,(R.view_size HS),Nat.min_l in Hj by lia.
   rewrite nth_firstn, (proj2 (Nat.ltb_lt _ _) Hj).
   apply open_stack_slots; lia.
Qed.

Theorem summary_open_prefix_exact k (s : T.t M S) : T.Consistent s -> k<=T.opens s ->
 exists base,
 T.Consistent base /\ T.opens base+k=T.opens s /\
 stack_safe base (firstn k (R.view S (T.regions s))) /\
 open_stack base (firstn k (R.view S (T.regions s)))=s.
Proof.
 intros Hs Hk.
 destruct (summary_open_prefix_decomposition HS HM Hs Hk)
   as [base [xs [Hb [Hlen [Hcount [Hsafe Hstack]]]]]].
 pose proof (open_stack_frames_exact base xs Hsafe) as Hframes.
 rewrite Hlen,Hstack in Hframes. rewrite Hframes.
 exists base. split; [exact Hb|]. split; [exact Hcount|]. split; assumption.
Qed.
Lemma open_stack_pop_regions s x xs : stack_safe (M:=M) (S:=S) s (x::xs) ->
 T.pop M S (T.regions (open_stack s (x::xs))) = T.regions (open_stack s xs).
Proof.
 intros [_ [Hcons Hroom]]. rewrite open_stack_regions. unfold T.pop.
 apply pop_push; [exact HS|].
 apply (padded_last M HS) with (k:=T.active (open_stack s xs)); [apply consistent_padding; exact Hcons|exact Hroom].
Qed.

Theorem open_stack_remaining_regions s xs : stack_safe (M:=M) (S:=S) s xs ->
 Nat.iter (length xs) (T.pop M S) (T.regions (open_stack s xs)) = T.regions s.
Proof.
 induction xs as [|x xs IH]; intro Hsafe; [reflexivity|].
 cbn [length]. rewrite Nat.iter_succ_r, (open_stack_pop_regions Hsafe).
 apply IH. exact (proj1 Hsafe).
Qed.

Theorem summary_open_prefix_layout k (s : T.t M S) : T.Consistent s -> k<=T.opens s ->
 exists base,
 T.Consistent base /\ T.opens base+k=T.opens s /\
 T.regions base = Nat.iter k (T.pop M S) (T.regions s) /\
 stack_safe base (firstn k (R.view S (T.regions s))) /\
 open_stack base (firstn k (R.view S (T.regions s)))=s.
Proof.
 intros Hs Hk.
 destruct (summary_open_prefix_decomposition HS HM Hs Hk)
   as [base [xs [Hb [Hlen [Hcount [Hsafe Hstack]]]]]].
 pose proof (open_stack_frames_exact base xs Hsafe) as Hframes.
 pose proof (open_stack_remaining_regions base xs Hsafe) as Hremaining.
 rewrite Hlen,Hstack in Hframes,Hremaining.
 exists base. rewrite Hframes. split; [exact Hb|]. split; [exact Hcount|].
 split; [symmetry; exact Hremaining|]. split; assumption.
Qed.
End DeterministicFrames.

Section UnmatchedRemainder.
Context {Raw Value : Type} (M : MonoidalOps (Nest Raw Value) Value).
Context (S : R.regions (m_summary M)) (HS : R.Laws S) (HM : IsMonoid M).

(** After matched frames have been cancelled, the remaining closes are
    unmatched. Both remaining phases are therefore pure tuple shifts. *)
Lemma replay_unmatched_layout c o (s : T.t M S) q :
 (T.lo s = T.net s \/ c=0) ->
 exists t,
 continue_replay c o (Some (s,q)) =
   Some (t,snd (consume S (m_ne M) (c+o) (T.regions s) q)) /\
 T.regions t = fst (consume S (m_ne M) (c+o) (T.regions s) q).
Proof.
 intro Hunmatched.
 assert (Hcl : exists t, T.replay_closes c (Some (s,q)) =
   Some (t,snd (consume S (m_ne M) c (T.regions s) q)) /\
   T.regions t = fst (consume S (m_ne M) c (T.regions s) q)).
 { destruct Hunmatched as [Heq|Hzero].
   - destruct (replay_closes_unmatched HS HM c s q Heq) as [t [Ht [Hr _]]].
     exists t; auto.
   - subst c; exists s; split; reflexivity. }
 destruct Hcl as [t1 [Ht1 Hr1]].
 destruct (replay_opens_storage HS HM o t1
   (snd (consume S (m_ne M) c (T.regions s) q))) as [t2 [Ht2 Hr2]].
 exists t2. unfold continue_replay. rewrite Ht1,Ht2.
 rewrite consume_plus. cbn beta zeta. rewrite <- Hr1. split; [reflexivity|exact Hr2].
Qed.
End UnmatchedRemainder.
Section OperandLayout.
Context {Raw Value : Type} (M : MonoidalOps (Nest Raw Value) Value).
Context (S : R.regions (m_summary M)) (HS : R.Laws S) (HM : IsMonoid M).
Definition operand_queue (b : T.t M S) :=
 Nat.iter (2*T.depth M S-T.active b) (T.pop M S) (R.reverse S (T.regions b)).
Definition operand_replay (a b : T.t M S) :=
 let q := operand_queue b in
 continue_replay (T.closes b) (T.opens b) (Some (T.append_region a (R.top S q),T.pop M S q)).
Definition operand_regions (a b : T.t M S) : option (R.carrier S) :=
 let k := Nat.min (T.opens a) (T.closes b) in
 let frames := firstn k (R.view S (T.regions a)) in
 let rest := Nat.iter k (T.pop M S) (T.regions a) in
 let q := operand_queue b in
 match cancel_values M S frames (R.top S q) (T.pop M S q) with
 | None => None
 | Some (v,r) => Some (fst (consume S (m_ne M) (T.closes b-k+T.opens b)
     (R.replace S rest (m_op M (R.top S rest) v)) r))
 end.

Lemma same_state_regions (a b : option (T.t M S * R.carrier S)) : SameState a b ->
 option_map (fun p => T.regions (fst p)) a = option_map (fun p => T.regions (fst p)) b.
Proof.
 destruct a as [[a q]|],b as [[b r]|]; try (intro H; contradiction); [|reflexivity].
 intros [[_ [_ Hr]] _]; cbn [option_map fst]; now rewrite Hr.
Qed.

Theorem operand_replay_layout (a b : T.t M S) : T.Consistent a ->
 option_map (fun p => T.regions (fst p)) (operand_replay a b) = operand_regions a b.
Proof.
 intro Ha. unfold operand_regions,operand_replay.
 set (k:=Nat.min (T.opens a) (T.closes b)).
 set (q:=operand_queue b).
 assert (Hka : k<=T.opens a) by (unfold k; apply Nat.le_min_l).
 assert (Hkb : k<=T.closes b) by (unfold k; apply Nat.le_min_r).
 destruct (summary_open_prefix_layout HS HM Ha Hka)
   as [base [Hb [Hcount [Hrest [Hsafe Hstack]]]]].
 set (frames := firstn k (R.view S (T.regions a))) in *.
 assert (Hlen : length frames=k).
 { unfold frames. rewrite length_firstn,(R.view_size HS),Nat.min_l; [reflexivity|].
   pose proof (proj1 (proj2 Ha)). unfold T.active,T.depth in *; lia. }
 pose proof (cancel_stack_with_tail HS HM base frames (R.top S q) (T.pop M S q)
   (T.closes b-k) (T.opens b) Hsafe) as Hreplay.
 rewrite Hstack,Hlen in Hreplay.
 replace (k+(T.closes b-k)) with (T.closes b) in Hreplay by lia.
 rewrite (same_state_regions _ _ Hreplay).
 destruct (cancel_values M S frames (R.top S q) (T.pop M S q)) as [[v r]|].
 2: { cbn [option_map]. unfold continue_replay. rewrite T.replay_closes_none,T.replay_opens_none; reflexivity. }
 cbn [option_map fst snd].
 assert (Hunmatched : T.lo (T.append_region base v)=T.net (T.append_region base v) \/ T.closes b-k=0).
 { destruct (le_dec (T.opens a) (T.closes b)) as [Hle|Hle].
   - assert (Hz : T.opens base=0) by (unfold k in Hcount; rewrite Nat.min_l in Hcount by exact Hle; lia).
     left. change (T.lo base=T.net base).
     pose proof (proj1 Hb) as Hd. unfold CompactDepth.consistent,T.metadata in Hd; cbn in Hd.
     unfold T.opens in Hz; lia.
   - right. unfold k. rewrite Nat.min_r by lia; lia. }
 destruct (replay_unmatched_layout HS HM (T.opens b)
   (T.append_region base v) r Hunmatched) as [t [Ht Hr]].
 rewrite Ht. cbn [option_map fst]. rewrite Hr.
 unfold T.append_region; cbn [T.regions]. rewrite Hrest. reflexivity.
Qed.
Definition install_depth (d : CompactDepth.t) (r : R.carrier S) :=
 @T.mk Raw Value M S (CompactDepth.lo d) (CompactDepth.hi d) (CompactDepth.net d) r.

Theorem op_normal_form (a b : T.t M S) : T.Consistent a ->
 let d := CompactDepth.combine (T.metadata a) (T.metadata b) in
 T.op (Some a) (Some b) =
 if CompactDepth.valid (Z.of_nat (T.depth M S)) d then
   option_map (install_depth d) (operand_regions a b)
 else None.
Proof.
 intros Ha d. unfold T.op. fold d.
 destruct (CompactDepth.valid (Z.of_nat (T.depth M S)) d); [|reflexivity].
 change ((match operand_replay a b with
   | None => None | Some (s,_) => Some (install_depth d (T.regions s)) end) =
   option_map (install_depth d) (operand_regions a b)).
 rewrite <- (operand_replay_layout b Ha).
 destruct (operand_replay a b) as [[s q]|]; reflexivity.
Qed.
End OperandLayout.

(** Outstanding associativity obligation (not an axiom or admission):
    use [op_normal_form] to prove equality of the two region computations.
    In particular, when [opens a > closes b] and [closes c > opens b],
    cancellation propagates across both boundaries of b. The existing
    one-sided [cancel_values_app] and [cancel_values_boundary_associative]
    lemmas do not yet identify the residual queues in this two-sided case.
    No independent overall associativity theorem is claimed here. *)
End TupleDirect.
