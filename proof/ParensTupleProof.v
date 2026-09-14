From Stdlib Require Import List Bool ZArith Lia FunctionalExtensionality ProofIrrelevance.
Require Import Monoid Parens Parens_n PullArray ParensRegions ParensTuple.
Require Import ParensTupleDirect.
Import ListNotations.
Set Implicit Arguments.
Set Universe Polymorphism.
Module TupleProof.
Module T := ParensTuple.ParensTuple.
Module R := ParensRegions.ParensRegions.
Module A := ParensN.

Section Storage.
 Context {E} (S : R.regions E) (HS : R.Laws S) (e : E).
 Definition slot r j := nth j (R.view S r) e.
 Lemma at_top r : slot r 0 = R.top S r.
 Proof. unfold slot; rewrite (R.view_top HS r); reflexivity. Qed.
 Lemma at_out r j : 2*R.depth S+1 <= j -> slot r j = e.
 Proof. intro H; unfold slot; apply nth_overflow; rewrite (R.view_size HS); lia. Qed.
 Lemma at_replace r x j : slot (R.replace S r x) j =
   if Nat.eqb j 0 then x else slot r j.
 Proof.
   unfold slot; rewrite (R.view_replace HS).
   destruct j; cbn; [reflexivity|].
   rewrite (R.view_top HS r) at 2; reflexivity.
 Qed.
 Lemma at_push r x j : j < 2*R.depth S+1 ->
   slot (R.push S r x) j = match j with 0 => x | Datatypes.S k => slot r k end.
 Proof.
   intro Hj.
   pose proof (f_equal (fun xs => nth j xs e) (R.view_push HS r x)) as H.
   cbn beta in H.
   rewrite app_nth1 in H by (rewrite (R.view_size HS); exact Hj).
   destruct j; exact H.
 Qed.
 Lemma at_pop r j : slot (R.pop S r e) j = slot r (Datatypes.S j).
 Proof.
   destruct (lt_dec j (2*R.depth S+1)) as [Hj|Hj].
   - pose proof (f_equal (fun xs => nth (Datatypes.S j) xs e) (R.view_pop HS r e)) as H.
     cbn in H. unfold slot.
     destruct (lt_dec (Datatypes.S j) (length (R.view S r))) as [Hk|Hk].
     + rewrite app_nth1 in H by exact Hk; exact H.
     + rewrite app_nth2 in H by lia.
       rewrite (R.view_size HS) in *.
       replace (Datatypes.S j-(2*R.depth S+1)) with 0 in H by lia.
       cbn in H. rewrite H; symmetry; apply nth_overflow; rewrite (R.view_size HS); lia.
   - rewrite !at_out by lia; reflexivity.
 Qed.
 Lemma at_iter_pop k r j :
   slot (Nat.iter k (fun q => R.pop S q e) r) j = slot r (j+k).
 Proof.
   revert r j; induction k; intros r j.
   - rewrite Nat.add_0_r; reflexivity.
   - rewrite Nat.iter_succ, at_pop, IHk. f_equal; lia.
 Qed.
 Lemma at_reverse r j : j < 2*R.depth S+1 ->
   slot (R.reverse S r) j = slot r (2*R.depth S-j).
 Proof.
   intro Hj; unfold slot; rewrite (R.view_reverse HS).
   rewrite rev_nth by (rewrite (R.view_size HS); lia).
   rewrite (R.view_size HS); f_equal; lia.
 Qed.
 Lemma at_ext r s : (forall j, slot r j = slot s j) -> r=s.
 Proof.
   intro H; apply (R.view_injective HS).
   apply nth_ext with (d:=e) (d':=e).
   - rewrite !(R.view_size HS); reflexivity.
   - intros j Hj; apply H.
 Qed.
End Storage.

Section Correspondence.
 Context {Raw Value} (M : MonoidalOps (Nest Raw Value) Value).
 Context (S : R.regions (m_summary M)) (HS : R.Laws S).
 Let N := R.depth S.
 Let e := m_ne M.
 Definition index r j := slot S e r j.
 Definition encode (s : T.t M S) : A.t M :=
   A.mk (T.lo s) (T.hi s) (T.net s)
     (PullArray.mk (2*N+1) (fun i =>
        if i <=? T.active s then index (T.regions s) (T.active s-i) else e)).
 Definition encode_opt := @option_map _ _ encode.
 Definition Related (a : A.t M) (s : T.t M S) :=
   A.lo a = T.lo s /\ A.hi a = T.hi s /\ A.net a = T.net s /\
   forall j, index (T.regions s) j =
     if j <=? A.active a then A.region (A.regions_of a) (A.active a-j) else e.

 Lemma encode_closes s : A.closes (encode s) = T.closes s.
 Proof. reflexivity. Qed.
 Lemma encode_opens s : A.opens (encode s) = T.opens s.
 Proof. reflexivity. Qed.
 Lemma encode_active s : A.active (encode s) = T.active s.
 Proof. reflexivity. Qed.

 Lemma tuple_padding s j : T.Consistent s -> T.active s < j -> index (T.regions s) j=e.
 Proof.
   intros [_ [Hbound Hpad]] Hj.
   pose proof (f_equal (fun xs => nth (j-Datatypes.S (T.active s)) xs e) Hpad) as H.
   cbn beta in H.
   rewrite nth_skipn in H.
   replace (Datatypes.S (T.active s)+(j-Datatypes.S (T.active s))) with j in H by lia.
   rewrite nth_repeat in H; exact H.
 Qed.

 Lemma encode_consistent s : T.Consistent s -> A.Consistent N (encode s).
 Proof.
   intros [Hd [Hb Hp]]. split; [reflexivity|].
   split; [exact Hd|]. split; [rewrite encode_active; unfold T.depth in Hb; unfold N; lia|].
   intros i Hi; unfold A.region, encode; cbn [A.regions_of PullArray.index].
   rewrite encode_active in Hi.
   rewrite (proj2 (Nat.leb_gt i (T.active s)) Hi); reflexivity.
 Qed.

 Lemma related_encode s : T.Consistent s -> Related (encode s) s.
 Proof.
   intro Hs; repeat split; try reflexivity.
   intro j; rewrite encode_active.
   destruct (j <=? T.active s) eqn:Hj.
   - apply Nat.leb_le in Hj.
     unfold A.region, encode; cbn [A.regions_of PullArray.index].
     rewrite (proj2 (Nat.leb_le (T.active s-j) (T.active s))) by lia.
     replace (T.active s-(T.active s-j)) with j by lia; reflexivity.
   - apply Nat.leb_gt in Hj; now apply tuple_padding.
 Qed.

 Lemma related_counts a s : Related a s ->
   A.closes a=T.closes s /\ A.opens a=T.opens s /\ A.active a=T.active s.
 Proof. intros [Hl [Hh [Hn _]]]; unfold A.active,T.active,A.closes,T.closes,A.opens,T.opens; rewrite Hl,Hn; auto. Qed.

 Lemma related_injective a s t : Related a s -> Related a t -> s=t.
 Proof.
   intros [Hl [Hh [Hn Hr]]] [Hl' [Hh' [Hn' Hr']]].
   assert (Heq : T.regions s=T.regions t).
   { apply (at_ext HS e); intro j. change (index (T.regions s) j=index (T.regions t) j).
     rewrite Hr,Hr'; reflexivity. }
   destruct s,t; cbn in *; congruence.
 Qed.
 Lemma related_consistent a s : A.Consistent N a -> Related a s -> T.Consistent s.
 Proof.
   intros [Hsz [Hd [Hb Hp]]] Hr.
   pose proof (related_counts Hr) as [Hc [Ho Hk]].
   destruct Hr as [Hl [Hh [Hn Hr]]].
   split.
   - unfold CompactDepth.consistent,T.metadata; cbn.
     rewrite <-Hl,<-Hh,<-Hn; exact Hd.
   - split; [unfold T.depth; unfold N in Hb; lia|].
     apply nth_ext with (d:=e) (d':=e).
     + rewrite length_skipn,(R.view_size HS),repeat_length.
       unfold T.depth; unfold N in Hb; lia.
     + intros j Hj. rewrite nth_skipn,nth_repeat.
       change (index (T.regions s) (Datatypes.S (T.active s)+j)=e).
       rewrite Hr.
       rewrite (proj2 (Nat.leb_gt (Datatypes.S (T.active s)+j) (A.active a))) by lia.
       reflexivity.
 Qed.

 Lemma related_encode_eq a s : A.Consistent N a -> Related a s -> encode s=a.
 Proof.
   intros [Hsz [Hd [Hb Hp]]] Hr.
   pose proof (related_counts Hr) as [Hc [Ho Hk]].
   destruct Hr as [Hl [Hh [Hn Hr]]].
   assert (Hrs : A.regions_of (encode s)=A.regions_of a).
   { apply PullArray.ext.
     - symmetry; exact Hsz.
     - intro i. change ((if i <=? T.active s then index (T.regions s) (T.active s-i) else e) = A.region (A.regions_of a) i).
       destruct (i <=? T.active s) eqn:Hi.
       + apply Nat.leb_le in Hi. rewrite Hr, Hk.
         rewrite (proj2 (Nat.leb_le (T.active s-i) (T.active s))) by lia.
         replace (T.active s-(T.active s-i)) with i by lia; reflexivity.
       + apply Nat.leb_gt in Hi; symmetry; apply Hp; lia. }
   destruct a; cbn in *; unfold encode; cbn in *; congruence.
 Qed.

 Lemma related_append_region a s x : A.Consistent N a -> Related a s ->
   Related (A.append_region a x) (T.append_region s x).
 Proof.
   intros [Hsz [Hd [Hb Hp]]] [Hl [Hh [Hn Hr]]].
   unfold Related; cbn [A.append_region T.append_region A.lo A.hi A.net T.lo T.hi T.net].
   split; [exact Hl|]; split; [exact Hh|]; split; [exact Hn|].
   intro j; rewrite A.append_region_active.
   unfold index; cbn [T.append_region T.regions].
   rewrite (at_replace HS e).
   destruct j as [|j].
   - cbn [Nat.eqb Nat.leb Nat.sub].
     replace (A.active a-0) with (A.active a) by lia.
     change (m_op M (R.top S (T.regions s)) x = A.region (A.put_region (A.regions_of a) (A.active a) (m_op M (A.region (A.regions_of a) (A.active a)) x)) (A.active a)).
     rewrite A.region_put_same by (rewrite Hsz; exact Hb).
     rewrite <- (at_top HS e). fold (index (T.regions s) 0).
     rewrite Hr; cbn; rewrite Nat.sub_0_r; reflexivity.
   - cbn [Nat.eqb]. fold (index (T.regions s) (Datatypes.S j)).
     rewrite Hr. destruct (Datatypes.S j <=? A.active a) eqn:Hj; [|reflexivity].
     apply Nat.leb_le in Hj. cbn [A.append_region A.regions_of].
     rewrite A.region_put_other by lia; reflexivity.
 Qed.
 Definition MetaEq (a:A.t M) (s:T.t M S) := A.lo a=T.lo s /\ A.hi a=T.hi s /\ A.net a=T.net s.
 Lemma related_top a s : Related a s -> R.top S (T.regions s)=A.region (A.regions_of a) (A.active a).
 Proof.
   intros [_ [_ [_ Hr]]]. rewrite <- (at_top HS e).
   change (index (T.regions s) 0=A.region (A.regions_of a) (A.active a)).
   rewrite Hr; cbn; rewrite Nat.sub_0_r; reflexivity.
 Qed.

 Lemma related_push a s a' s' x :
   A.Sized N a -> Related a s -> MetaEq a' s' ->
   A.active a'=Datatypes.S (A.active a) -> A.active a'<2*N+1 ->
   A.regions_of a'=A.put_region (A.regions_of a) (A.active a') x ->
   T.regions s'=R.push S (T.regions s) x ->
   Related a' s'.
 Proof.
   intros Hsz [_ [_ [_ Hr]]] [Hl [Hh Hn]] Hk Hb Ha Hs.
   unfold Related; repeat split; try assumption.
   intro j; unfold index; rewrite Hs.
   destruct (lt_dec j (2*N+1)) as [Hj|Hj].
   - rewrite (at_push HS e) by exact Hj.
     destruct j as [|j].
     + cbn. rewrite Nat.sub_0_r,Ha,A.region_put_same.
       * reflexivity.
       * rewrite Hsz; exact Hb.
     + fold (index (T.regions s) j). rewrite Hr,Hk.
       cbn [Nat.leb]. destruct (j <=? A.active a) eqn:Hja; [|reflexivity].
       apply Nat.leb_le in Hja. rewrite Ha,Hk.
       rewrite A.region_put_other by lia.
       replace (Datatypes.S (A.active a)-Datatypes.S j) with (A.active a-j) by lia; reflexivity.
   - rewrite (at_out HS e) by (unfold N in *; lia).
     rewrite (proj2 (Nat.leb_gt j (A.active a'))) by lia; reflexivity.
 Qed.

 Lemma related_append_open a s : A.Consistent N a -> Related a s ->
   Datatypes.S (A.active a)<2*N+1 ->
   Related (A.append_open a) (T.append_open s).
 Proof.
   intros Ha Hr Hb.
   destruct Ha as [Hsz [[Hlo [Hhi [Hln [Hnh Hspan]]]] [Hk Hp]]].
   eapply related_push with (x:=e); try exact Hr; try exact Hsz.
   - destruct Hr as [Hl [Hh [Hn _]]]; unfold MetaEq; cbn; rewrite Hl,Hh,Hn; auto.
   - apply A.append_open_active; exact Hln.
   - rewrite A.append_open_active by exact Hln; exact Hb.
   - cbn [A.append_open A.regions_of]; rewrite A.append_open_active by exact Hln; unfold e; f_equal; lia.
   - reflexivity.
 Qed.
 Lemma related_pop a s a' s' x :
   A.Sized N a -> Related a s -> MetaEq a' s' ->
   Datatypes.S (A.active a')=A.active a -> A.active a<2*N+1 ->
   A.regions_of a'=A.put_region (A.put_region (A.regions_of a) (A.active a') x) (A.active a) e ->
   T.regions s'=R.replace S (R.pop S (T.regions s) e) x ->
   Related a' s'.
 Proof.
   intros Hsz [_ [_ [_ Hr]]] [Hl [Hh Hn]] Hk Hb Ha Hs.
   unfold Related; repeat split; try assumption.
   intro j; unfold index; rewrite Hs,(at_replace HS e).
   destruct j as [|j].
   - cbn [Nat.eqb Nat.leb]. rewrite Nat.sub_0_r,Ha.
     rewrite A.region_put_other by lia.
     rewrite A.region_put_same by (rewrite Hsz; lia); reflexivity.
   - cbn [Nat.eqb]. rewrite (at_pop HS e).
     fold (index (T.regions s) (Datatypes.S (Datatypes.S j))).
     rewrite Hr,<-Hk.
     change ((if Datatypes.S j <=? A.active a' then
       A.region (A.regions_of a) (A.active a'-Datatypes.S j) else e) =
       (if Datatypes.S j <=? A.active a' then
       A.region (A.regions_of a') (A.active a'-Datatypes.S j) else e)).
     destruct (Datatypes.S j <=? A.active a') eqn:Hj; [|reflexivity].
     apply Nat.leb_le in Hj. rewrite Ha,<-Hk.
     rewrite !A.region_put_other by lia.
     replace (Datatypes.S (A.active a')-Datatypes.S (Datatypes.S j)) with
       (A.active a'-Datatypes.S j) by lia; reflexivity.
 Qed.

 Lemma related_below_top a s : Related a s -> 0<A.active a ->
   R.top S (T.pop M S (T.regions s))=A.region (A.regions_of a) (A.active a-1).
 Proof.
   intros [_ [_ [_ Hr]]] Hk.
   unfold T.pop. rewrite <-(at_top HS e),(at_pop HS e).
   change (index (T.regions s) 1=A.region (A.regions_of a) (A.active a-1)).
   rewrite Hr,(proj2 (Nat.leb_le 1 (A.active a))) by lia; reflexivity.
 Qed.

 Definition RelatedOpt a s := match a,s with
   | Some a,Some s => Related a s | None,None => True | _,_ => False end.

 Lemma related_append_close a s :
   A.Consistent N a -> Related a s ->
   (A.opens a=0 -> Datatypes.S (A.active a)<2*N+1) ->
   RelatedOpt (A.append_close a) (T.append_close s).
 Proof.
   intros Ha Hr Hroom.
   pose proof (related_counts Hr) as [Hc [Ho Hk]].
   pose proof (related_top Hr) as Htop.
   destruct Ha as [Hsz [[Hlo [Hhi [Hln [Hnh Hspan]]]] [Hb Hp]]].
   unfold A.append_close,T.append_close; rewrite <-Ho,Htop.
   destruct (0 <? A.opens a) eqn:Hopen.
   - apply Nat.ltb_lt in Hopen.
     assert (Hpos:0<A.active a) by (unfold A.active; lia).
     unfold A.close. destruct (m_obs M (A.region (A.regions_of a) (A.active a))) as [v|] eqn:Hv; [|exact I].
     cbn zeta; cbn [RelatedOpt].
     pose proof (related_below_top Hr Hpos) as Hbelow.
     change (R.top S (T.pop M S (T.regions s)) = A.region (A.regions_of a) (A.active a-1)) in Hbelow.
     setoid_rewrite Hbelow.
     eapply related_pop with (a:=a) (s:=s); try exact Hsz; try exact Hr; try exact Hb.
     + destruct Hr as [Hl [Hh [Hn _]]]; unfold MetaEq; cbn; rewrite Hl,Hh,Hn; auto.
     + eapply A.append_close_active_open; eauto.
       unfold A.append_close,A.close; rewrite (proj2 (Nat.ltb_lt 0 (A.opens a)) Hopen),Hv; reflexivity.
     + cbn [A.regions_of].
       f_equal. f_equal.
       assert (Hcl : A.append_close a = Some (A.mk (Z.min (A.lo a) (A.net a-1)) (Z.max (A.hi a) (A.net a)) (A.net a-1)%Z
         (A.put_region (A.put_region (A.regions_of a) (A.active a-1) (m_op M (A.region (A.regions_of a) (A.active a-1)) (m_gen M (nested v)))) (A.active a) e))).
       { unfold A.append_close,A.close; rewrite (proj2 (Nat.ltb_lt 0 (A.opens a)) Hopen),Hv; reflexivity. }
       pose proof (A.append_close_active_open a Hlo Hln Hopen Hcl) as Hcount.
       unfold e in Hcount; lia.
     + reflexivity.
   - apply Nat.ltb_ge in Hopen. assert (Hz:A.opens a=0) by lia.
     cbn [RelatedOpt].
     eapply related_push with (a:=a) (s:=s) (x:=e); try exact Hsz; try exact Hr.
     + destruct Hr as [Hl [Hh [Hn _]]]; unfold MetaEq; cbn; rewrite Hl,Hh,Hn; auto.
     + eapply A.append_close_active_no_open; eauto.
       unfold A.append_close; rewrite Hz; reflexivity.
     + erewrite A.append_close_active_no_open; eauto.
       unfold A.append_close; rewrite Hz; reflexivity.
     + cbn [A.regions_of]. f_equal.
       assert (Hcl:A.append_close a = Some (A.mk (Z.min (A.lo a) (A.net a-1)) (Z.max (A.hi a) (A.net a)) (A.net a-1)%Z
         (A.put_region (A.regions_of a) (A.closes a+1) e))).
       { unfold A.append_close; rewrite Hz; reflexivity. }
       pose proof (A.append_close_active_no_open a Hlo Hln Hz Hcl) as Hcount.
       unfold e in Hcount. unfold A.active in Hcount; rewrite Hz in Hcount; unfold A.active; lia.
     + reflexivity.
 Qed.
 (* A fixed envelope bounds every intermediate replay state, not merely
    the result after the final metadata has been restored. *)
 Definition Envelope (L H : Z) (a : A.t M) :=
   A.Consistent N a /\ (L <= A.lo a)%Z /\ (A.hi a <= H)%Z.

 Lemma envelope_region L H a x : Envelope L H a ->
   Envelope L H (A.append_region a x).
 Proof.
   intros [[Hsz [Hd [Hb Hp]]] [Hl Hh]].
   split; [|split; assumption].
   split; [apply A.append_region_sized; exact Hsz|].
   split; [exact Hd|]. split; [exact Hb|].
   apply A.append_region_padding; exact Hp.
 Qed.

 Lemma envelope_open L H a : (H-L <= Z.of_nat N)%Z ->
   Envelope L H a -> (A.net a+1 <= H)%Z ->
   Envelope L H (A.append_open a).
 Proof.
   intros Hspan [[Hsz [Hd [Hb Hp]]] [Hl Hh]] Hnext.
   destruct Hd as [Hlo [Hhi [Hln [Hnh Hwidth]]]].
   assert (Hd : A.depth_consistent N (A.append_open a)).
   { unfold A.depth_consistent,A.append_open; cbn -[Z.mul].
     rewrite Z.min_l by lia.
     pose proof (Z.le_max_l (A.hi a) (A.net a+1)).
     pose proof (Z.le_max_r (A.hi a) (A.net a+1)).
     assert (Z.max (A.hi a) (A.net a+1) <= H)%Z by (apply Z.max_lub; lia).
     repeat split; lia. }
   split.
   - split; [apply A.append_open_sized; exact Hsz|].
     split; [exact Hd|]. split; [apply A.depth_consistent_active_bound; exact Hd|].
     apply A.append_open_padding; assumption.
   - unfold A.append_open; cbn -[Z.mul]. split.
     + rewrite Z.min_l by lia; exact Hl.
     + apply Z.max_lub; assumption.
 Qed.

 Lemma envelope_open_room L H a : (H-L <= Z.of_nat N)%Z ->
   Envelope L H a -> (A.net a+1 <= H)%Z ->
   Datatypes.S (A.active a) < 2*N+1.
 Proof.
   intros Hspan He Hnext.
   pose proof (envelope_open Hspan He Hnext) as [[_ [_ [Hb _]]] _].
   destruct He as [[_ [[_ [_ [Hln _]]] _]] _].
   rewrite A.append_open_active in Hb by exact Hln; exact Hb.
 Qed.

 Lemma close_metadata (a b : A.t M) : A.append_close a = Some b ->
   A.lo b = Z.min (A.lo a) (A.net a-1) /\
   A.hi b = Z.max (A.hi a) (A.net a) /\
   A.net b = (A.net a-1)%Z.
 Proof.
   unfold A.append_close. destruct (0 <? A.opens a).
   - destruct (A.close M (A.region (A.regions_of a) (A.active a)));
       intro H; inversion H; auto.
   - intro H; inversion H; auto.
 Qed.

 Lemma envelope_close L H a b : (H-L <= Z.of_nat N)%Z ->
   Envelope L H a -> (L <= A.net a-1)%Z ->
   A.append_close a = Some b -> Envelope L H b.
 Proof.
   intros Hspan [[Hsz [Hd [Hb Hp]]] [Hl Hh]] Hnext Hclose.
   pose proof (close_metadata a Hclose) as [Hbl [Hbh Hbn]].
   destruct Hd as [Hlo [Hhi [Hln [Hnh Hwidth]]]].
   assert (Hd : A.depth_consistent N b).
   { unfold A.depth_consistent; rewrite Hbl,Hbh,Hbn.
     rewrite Z.max_l by lia.
     pose proof (Z.le_min_l (A.lo a) (A.net a-1)).
     pose proof (Z.le_min_r (A.lo a) (A.net a-1)).
     assert (L <= Z.min (A.lo a) (A.net a-1))%Z by (apply Z.min_glb; lia).
     repeat split; lia. }
   split.
   - split; [eapply A.append_close_sized; eauto|].
     split; [exact Hd|]. split; [apply A.depth_consistent_active_bound; exact Hd|].
     eapply A.append_close_padding; eauto.
     unfold A.Sized in Hsz; rewrite Hsz; exact Hb.
   - rewrite Hbl,Hbh. split.
     + apply Z.min_glb; assumption.
     + rewrite Z.max_l by lia; exact Hh.
 Qed.

 Lemma envelope_close_room L H a : (H-L <= Z.of_nat N)%Z ->
   Envelope L H a -> (L <= A.net a-1)%Z ->
   A.opens a=0 -> Datatypes.S (A.active a) < 2*N+1.
 Proof.
   intros Hspan He Hnext Hz.
   assert (Hsome: exists b, A.append_close a=Some b).
   { unfold A.append_close; rewrite Hz; eexists; reflexivity. }
   destruct Hsome as [b Hb].
   pose proof (envelope_close Hspan He Hnext Hb) as [[_ [_ [Hbound _]]] _].
   destruct He as [[_ [[Hlo [_ [Hln _]]] _]] _].
   rewrite (A.append_close_active_no_open a Hlo Hln Hz Hb) in Hbound.
   exact Hbound.
 Qed.

 (* The replay queue exposes exactly the still-unconsumed source regions. *)
 Definition Queue q (source : A.t M) offset :=
   forall k, offset+k <= A.active source ->
     index q k = A.region (A.regions_of source) (offset+k).

 Lemma queue_pop q source offset : Queue q source offset ->
   Queue (T.pop M S q) source (offset+1).
 Proof.
   intros H k Hk. unfold index,T.pop.
   rewrite (at_pop HS e). unfold Queue,index in H.
   rewrite H by lia. f_equal; lia.
 Qed.

 Lemma queue_top q source offset : Queue q source offset ->
   offset <= A.active source ->
   R.top S q = A.region (A.regions_of source) offset.
 Proof.
   intros H Hb. rewrite <- (at_top HS e).
   specialize (H 0). rewrite Nat.add_0_r in H. apply H; exact Hb.
 Qed.

 Lemma queue_initial a s : A.Consistent N a -> Related a s ->
   Queue (Nat.iter (2*N-T.active s) (T.pop M S)
     (R.reverse S (T.regions s))) a 0.
 Proof.
   intros Hc Hr k Hk.
   pose proof (related_counts Hr) as [_ [_ Hactive]].
   destruct Hc as [_ [_ [Hb _]]].
   destruct Hr as [_ [_ [_ Hslots]]].
   unfold index,T.pop.
   rewrite (at_iter_pop HS e).
   rewrite (at_reverse HS e) by (unfold N in *; lia).
   fold (index (T.regions s) (2*R.depth S-(k+(2*N-T.active s)))).
   rewrite Hslots.
   assert (Heq: 2*R.depth S-(k+(2*N-T.active s))=A.active a-k)
     by (unfold N in *; lia).
   rewrite Heq.
   rewrite (proj2 (Nat.leb_le _ _) (Nat.le_sub_l _ _)).
   replace (A.active a-(A.active a-k)) with k by lia.
   reflexivity.
 Qed.
 Definition ReplayRelated L H source offset net_result a ts :=
   match a,ts with
   | Some a,Some (s,q) => Related a s /\ Envelope L H a /\
       Queue q source offset /\ A.net a=net_result
   | None,None => True
   | _,_ => False
   end.

 Lemma replay_opens_related n j source a s q L H :
   (H-L <= Z.of_nat N)%Z -> Envelope L H a -> Related a s ->
   A.closes source+j+n <= A.active source ->
   Queue q source (A.closes source+j+1) ->
   (A.net a+Z.of_nat n <= H)%Z ->
   ReplayRelated L H source (A.closes source+j+n+1)
     (A.net a+Z.of_nat n)%Z
     (A.replay_opens n j source (Some a))
     (T.replay_opens n (Some (s,q))).
 Proof.
   revert j a s q; induction n as [|n IH]; intros j a s q Hspan He Hr Hb Hq Hnet.
   - cbn [A.replay_opens T.replay_opens ReplayRelated].
     replace (A.closes source+j+0+1) with (A.closes source+j+1) by lia.
     split; [exact Hr|]. split; [exact He|]. split; [exact Hq|lia].
   - assert (Hnext:(A.net a+1<=H)%Z) by lia.
     assert (Hroom:Datatypes.S(A.active a)<2*N+1)
       by (eapply envelope_open_room; eauto).
     pose proof (related_append_open (proj1 He) Hr Hroom) as Hr'.
     pose proof (envelope_open Hspan He Hnext) as He'.
     pose proof (queue_top Hq ltac:(lia)) as Htop.
     replace (A.closes source+j+1) with (A.closes source+Datatypes.S j) in Htop by lia.
     cbn [A.replay_opens T.replay_opens]. rewrite Htop.
     specialize (IH (Datatypes.S j)
       (A.append_region (A.append_open a) (A.region (A.regions_of source) (A.closes source+Datatypes.S j)))
       (T.append_region (T.append_open s) (A.region (A.regions_of source) (A.closes source+Datatypes.S j)))
       (T.pop M S q) Hspan).
     assert (Hq': Queue (T.pop M S q) source (A.closes source+Datatypes.S j+1)).
     { replace (A.closes source+Datatypes.S j+1) with ((A.closes source+j+1)+1) by lia.
       apply queue_pop; exact Hq. }
     specialize (IH (envelope_region _ He') (related_append_region _ (proj1 He') Hr')
       ltac:(lia) Hq' ltac:(cbn -[Z.mul]; lia)).
     replace (A.closes source+j+Datatypes.S n+1) with
       (A.closes source+Datatypes.S j+n+1) by lia.
     replace (A.net a+Z.of_nat(Datatypes.S n))%Z with
       (A.net (A.append_region (A.append_open a) (A.region (A.regions_of source) (A.closes source+Datatypes.S j)))+Z.of_nat n)%Z
       by (cbn -[Z.mul]; lia).
     exact IH.
 Qed.
 Lemma replay_closes_related n j source a s q L H :
   (H-L <= Z.of_nat N)%Z -> Envelope L H a -> Related a s ->
   j+n <= A.active source -> Queue q source (j+1) ->
   (L <= A.net a-Z.of_nat n)%Z ->
   ReplayRelated L H source (j+n+1) (A.net a-Z.of_nat n)%Z
     (A.replay_closes n j source (Some a))
     (T.replay_closes n (Some (s,q))).
 Proof.
   revert j a s q; induction n as [|n IH]; intros j a s q Hspan He Hr Hb Hq Hnet.
   - cbn [A.replay_closes T.replay_closes ReplayRelated].
     replace (j+0+1) with (j+1) by lia.
     split; [exact Hr|]. split; [exact He|]. split; [exact Hq|lia].
   - assert (Hnext:(L<=A.net a-1)%Z) by lia.
     assert (Hroom:A.opens a=0 -> Datatypes.S(A.active a)<2*N+1)
       by (eapply envelope_close_room; eauto).
     pose proof (related_append_close (proj1 He) Hr Hroom) as Hstep.
     cbn [A.replay_closes T.replay_closes].
     destruct (A.append_close a) as [a'|] eqn:Ha;
       destruct (T.append_close s) as [s'|] eqn:Hs;
       cbn [RelatedOpt] in Hstep; try contradiction.
     2: exact I.
     pose proof (envelope_close Hspan He Hnext Ha) as He'.
     pose proof (close_metadata a Ha) as [_ [_ Hnet']].
     pose proof (queue_top Hq ltac:(lia)) as Htop.
     replace (j+1) with (Datatypes.S j) in Htop by lia. rewrite Htop.
     specialize (IH (Datatypes.S j)
       (A.append_region a' (A.region (A.regions_of source) (Datatypes.S j)))
       (T.append_region s' (A.region (A.regions_of source) (Datatypes.S j)))
       (T.pop M S q) Hspan).
     assert (Hq': Queue (T.pop M S q) source (Datatypes.S j+1)).
     { replace (Datatypes.S j+1) with ((j+1)+1) by lia.
       apply queue_pop; exact Hq. }
     specialize (IH (envelope_region _ He') (related_append_region _ (proj1 He') Hstep)
       ltac:(lia) Hq' ltac:(cbn -[Z.mul]; lia)).
     replace (j+Datatypes.S n+1) with (Datatypes.S j+n+1) by lia.
     replace (A.net a-Z.of_nat(Datatypes.S n))%Z with
       (A.net (A.append_region a' (A.region (A.regions_of source) (Datatypes.S j)))-Z.of_nat n)%Z
       by (cbn -[Z.mul]; lia).
     exact IH.
 Qed.
 Lemma replay_summary_related a b s t L H :
   A.Consistent N a -> A.Consistent N b -> Related a s -> Related b t ->
   L=Z.min (A.lo a) (A.net a+A.lo b) ->
   H=Z.max (A.hi a) (A.net a+A.hi b) ->
   (H-L<=Z.of_nat N)%Z ->
   RelatedOpt (A.replay_summary a b)
     (option_map fst
       (T.replay_opens (T.opens t)
         (T.replay_closes (T.closes t)
           (Some (T.append_region s
             (R.top S (Nat.iter (2*N-T.active t) (T.pop M S) (R.reverse S (T.regions t)))),
             T.pop M S (Nat.iter (2*N-T.active t) (T.pop M S) (R.reverse S (T.regions t)))))))).
 Proof.
   intros Ha Hb Hr Ht HL HH Hspan.
   pose proof (related_counts Ht) as [Hc [Ho Hactive]].
   pose proof Hb as [_ [[Hlo [_ [Hln [Hnh _]]]] _]].
   assert (Hcl:Z.of_nat(A.closes b)=(-A.lo b)%Z).
   { unfold A.closes; rewrite Z2Nat.id by lia; reflexivity. }
   assert (Hop:Z.of_nat(A.opens b)=(A.net b-A.lo b)%Z).
   { unfold A.opens; rewrite Z2Nat.id by lia; reflexivity. }
   assert (He:Envelope L H a).
   { split; [exact Ha|]. subst L H; split; [apply Z.le_min_l|apply Z.le_max_l]. }
   set (q:=Nat.iter (2*N-T.active t) (T.pop M S) (R.reverse S (T.regions t))).
   assert (Hq:Queue q b 0) by (apply queue_initial; assumption).
   pose proof (queue_top Hq (Nat.le_0_l _)) as Htop.
   rewrite Htop,<-Hc,<-Ho.
   pose proof (replay_closes_related (A.closes b) 0 (source:=b) (q:=T.pop M S q)
     Hspan (envelope_region (A.region (A.regions_of b) 0) He) (related_append_region _ Ha Hr)
     ltac:(unfold A.active; lia) (queue_pop Hq)
     ltac:(cbn -[Z.mul]; rewrite Hcl; subst L; pose proof (Z.le_min_r (A.lo a) (A.net a+A.lo b)); lia)) as Hclose.
   unfold A.replay_summary.
   destruct (A.replay_closes (A.closes b) 0 b
     (Some (A.append_region a (A.region (A.regions_of b) 0)))) as [a'|] eqn:Hac;
   destruct (T.replay_closes (A.closes b)
     (Some (T.append_region s (A.region (A.regions_of b) 0),T.pop M S q))) as [[s' q']|] eqn:Htc;
     cbn [ReplayRelated] in Hclose; try contradiction.
   - destruct Hclose as [Hr' [He' [Hq' Hnet]]].
     replace (0+A.closes b+1) with (A.closes b+0+1) in Hq' by lia.
     pose proof (replay_opens_related (A.opens b) 0 (source:=b) (q:=q')
       Hspan He' Hr' ltac:(unfold A.active; lia) Hq'
       ltac:(cbn -[Z.mul] in Hnet; rewrite Hcl in Hnet; rewrite Hop;
         subst H; pose proof (Z.le_max_r (A.hi a) (A.net a+A.hi b)); lia)) as Hopen.
     destruct (A.replay_opens (A.opens b) 0 b (Some a'));
       destruct (T.replay_opens (A.opens b) (Some (s',q'))) as [[r qr]|];
       cbn [ReplayRelated RelatedOpt] in *; tauto.
   - destruct (A.opens b); exact I.
 Qed.
 Lemma guard_related a b s t : N<50 ->
   A.Consistent N a -> A.Consistent N b -> Related a s -> Related b t ->
   CompactDepth.valid (Z.of_nat N) (CompactDepth.combine (T.metadata s) (T.metadata t)) =
     A.depth_supported_n N a b.
 Proof.
   intros HN Ha Hb Hr Ht.
   pose proof (proj1 (related_consistent Ha Hr)) as Hs.
   pose proof (proj1 (related_consistent Hb Ht)) as Ht'.
   pose proof (CompactDepth.combine_bounds (Zle_0_nat N) Hs Ht') as [Hbounds _].
   apply Bool.eq_true_iff_eq.
   rewrite CompactDepth.valid_spec.
   unfold A.depth_supported_n; rewrite Z.leb_le.
   destruct Hr as [Hal [Hah [Han _]]]; destruct Ht as [Hbl [Hbh [Hbn _]]].
   unfold A.combined_depth,A.array_depth,depth_op,depth_span.
   cbn -[Z.mul]. rewrite Hal,Hah,Han,Hbl,Hbh.
   unfold CompactDepth.consistent in *.
   cbn -[Z.mul] in *.
   tauto || (split; intros; intuition lia).
 Qed.

 Lemma op_related a b s t : N<50 ->
   A.Consistent N a -> A.Consistent N b -> Related a s -> Related b t ->
   RelatedOpt (A.parens_n_op N (Some a) (Some b)) (T.op (Some s) (Some t)).
 Proof.
   intros HN Ha Hb Hr Ht.
   pose proof (guard_related HN Ha Hb Hr Ht) as Hg.
   rewrite A.parens_n_op_as_guarded_replay.
   unfold T.op,T.depth; fold N. rewrite Hg.
   destruct (A.depth_supported_n N a b) eqn:Hsupported; [|exact I].
   assert (Hspan:(Z.max (A.hi a) (A.net a+A.hi b)-
     Z.min (A.lo a) (A.net a+A.lo b)<=Z.of_nat N)%Z).
   { apply Z.leb_le in Hsupported; exact Hsupported. }
   pose proof (replay_summary_related Ha Hb Hr Ht eq_refl eq_refl Hspan) as Hreplay.
   destruct (A.replay_summary a b) as [r|] eqn:Har.
   - destruct (T.replay_opens (T.opens t)
       (T.replay_closes (T.closes t)
         (Some (T.append_region s
           (R.top S (Nat.iter (2*N-T.active t) (T.pop M S) (R.reverse S (T.regions t)))),
           T.pop M S (Nat.iter (2*N-T.active t) (T.pop M S) (R.reverse S (T.regions t)))))))
       as [[u q]|] eqn:Htu; cbn [option_map fst RelatedOpt] in Hreplay; try contradiction.
     cbn [A.finish_replay_opt RelatedOpt].
     pose proof (A.replay_summary_result_invariants Ha Hb Hsupported Har) as [_ [_ Hactive]].
     destruct Hr as [Hal [Hah [Han _]]]; destruct Ht as [Hbl [Hbh [Hbn _]]].
     destruct Hreplay as [_ [_ [_ Hslots]]].
     unfold Related; cbn [T.lo T.hi T.net T.regions].
     split; [cbn; rewrite Hal,Han,Hbl; reflexivity|].
     split; [cbn; rewrite Hah,Han,Hbh; reflexivity|].
     split; [cbn; rewrite Han,Hbn; reflexivity|].
     intro j; rewrite Hslots,Hactive; reflexivity.
   - destruct (T.replay_opens (T.opens t)
       (T.replay_closes (T.closes t)
         (Some (T.append_region s
           (R.top S (Nat.iter (2*N-T.active t) (T.pop M S) (R.reverse S (T.regions t)))),
           T.pop M S (Nat.iter (2*N-T.active t) (T.pop M S) (R.reverse S (T.regions t)))))))
       as [[u q]|]; cbn [option_map fst RelatedOpt] in Hreplay; try contradiction.
     exact I.
 Qed.
 Lemma encode_opt_consistent x : T.ConsistentOpt x ->
   A.ConsistentOpt N (encode_opt x).
 Proof. destruct x; cbn; [apply encode_consistent|auto]. Qed.

 Lemma encode_opt_injective x y : T.ConsistentOpt x -> T.ConsistentOpt y ->
   encode_opt x=encode_opt y -> x=y.
 Proof.
   destruct x as [x|],y as [y|]; cbn; intros Hx Hy Heq; try discriminate; auto.
   assert (Henc:encode x=encode y) by congruence. f_equal.
   apply related_injective with (a:=encode x).
   - apply related_encode; exact Hx.
   - rewrite Henc; apply related_encode; exact Hy.
 Qed.

 Theorem op_preserves_consistency (x y : option (T.t M S)) : N<50 ->
   T.ConsistentOpt x -> T.ConsistentOpt y -> T.ConsistentOpt (T.op x y).
 Proof.
   intros _ Hx Hy.
   exact (TupleDirect.op_preserves_consistency HS x y Hx Hy).
 Qed.

 Lemma encode_op x y : N<50 -> T.ConsistentOpt x -> T.ConsistentOpt y ->
   encode_opt (T.op x y)=A.parens_n_op N (encode_opt x) (encode_opt y).
 Proof.
   destruct x as [x|],y as [y|]; intros HN Hx Hy; try reflexivity.
   pose proof (encode_consistent Hx) as Ha.
   pose proof (encode_consistent Hy) as Hb.
   pose proof (op_related HN Ha Hb (related_encode Hx) (related_encode Hy)) as Hr.
   pose proof (A.parens_n_op_preserves_consistency
     N (Some(encode x)) (Some(encode y)) Ha Hb) as Hc.
   unfold encode_opt; cbn [option_map].
   destruct (A.parens_n_op N (Some(encode x)) (Some(encode y)));
     destruct (T.op (Some x) (Some y)); cbn [RelatedOpt] in Hr; try contradiction; try reflexivity.
   cbn. f_equal. eapply related_encode_eq; eauto.
 Qed.

 Theorem op_associative : N<50 -> IsMonoid M ->
   forall (x y z : option (T.t M S)), T.ConsistentOpt x -> T.ConsistentOpt y -> T.ConsistentOpt z ->
     T.op (T.op x y) z=T.op x (T.op y z).
 Proof.
   intros HN HM x y z Hx Hy Hz.
   apply encode_opt_injective.
   - apply op_preserves_consistency; auto. apply op_preserves_consistency; auto.
   - apply op_preserves_consistency; auto. apply op_preserves_consistency; auto.
   - repeat rewrite encode_op by (auto; apply op_preserves_consistency; auto).
     apply A.parens_n_op_assoc; auto using encode_opt_consistent.
 Qed.
 Lemma encode_base x : encode (T.base M S x)=A.base N M x.
 Proof.
   unfold encode,A.base,T.base; cbn [T.lo T.hi T.net T.regions].
   f_equal. apply PullArray.ext.
   - unfold A.put_region; rewrite PullArray.size_put; reflexivity.
   - intro i.
     change ((if i<=?0 then index (R.replace S (R.fill S e) x) (0-i) else e)=
       A.region (A.put_region (A.empty_regions N M) 0 x) i).
     destruct i as [|i].
     + cbn. unfold index. rewrite (at_replace HS e); cbn.
       symmetry; apply A.region_put_same. cbn; lia.
     + cbn. rewrite A.region_put_other by lia; reflexivity.
 Qed.

 Lemma encode_ne : N<50 -> encode_opt (T.ne M S)=A.ne N M.
 Proof.
   intro HN. unfold T.ne,T.supported,T.depth; fold N.
   rewrite (proj2 (Nat.ltb_lt N 50) HN).
   unfold encode_opt; cbn [option_map]; rewrite encode_base; reflexivity.
 Qed.

 Theorem ne_left_neutral : N<50 -> IsMonoid M ->
   forall x, T.ConsistentOpt x -> T.op (T.ne M S) x=x.
 Proof.
   exact (TupleDirect.ne_left_neutral HS).
 Qed.

 Theorem monoid_laws : N<50 -> IsMonoid M ->
   T.ConsistentOpt (T.ne M S) /\
   (forall (x y : option (T.t M S)), T.ConsistentOpt x -> T.ConsistentOpt y -> T.ConsistentOpt(T.op x y)) /\
   (forall (x y z : option (T.t M S)), T.ConsistentOpt x -> T.ConsistentOpt y -> T.ConsistentOpt z ->
     T.op(T.op x y)z=T.op x(T.op y z)) /\
   (forall x, T.ConsistentOpt x -> T.op(T.ne M S)x=x) /\
   (forall x, T.ConsistentOpt x -> T.op x(T.ne M S)=x).
 Proof.
   intros HN HM. split; [apply T.ne_consistent; exact HS|].
   split; [intros; apply op_preserves_consistency; assumption|].
   split; [apply op_associative; assumption|].
   split; [apply ne_left_neutral; assumption|].
   apply T.ne_right_neutral; assumption.
 Qed.
 Lemma base_consistent x : T.Consistent (T.base M S x).
 Proof.
   split.
   - unfold CompactDepth.consistent,T.metadata,T.base; cbn; lia.
   - split; [unfold T.active,T.closes,T.opens,T.base; cbn; lia|].
     unfold T.base; cbn [T.regions]. rewrite (R.view_replace HS),(R.view_fill HS).
     change (tl (repeat e (2*N+1))=repeat e (2*N-0)).
     replace (2*N+1) with (Datatypes.S(2*N)) by lia.
     cbn; f_equal; lia.
 Qed.

 Lemma base_open_consistent : 0<N ->
   T.Consistent (T.append_open (T.base M S e)).
 Proof.
   intro HN. pose proof (base_consistent e) as Hbase.
   pose proof (encode_consistent Hbase) as Ha.
   assert (He:Envelope 0 1 (encode(T.base M S e))).
   { split; [exact Ha|]. cbn; lia. }
   pose proof (envelope_open (L:=0%Z) (H:=1%Z) ltac:(lia) He ltac:(cbn; lia)) as He'.
   eapply related_consistent; [exact (proj1 He')|].
   apply related_append_open; [exact Ha|apply related_encode; exact Hbase|].
   eapply envelope_open_room with (L:=0%Z) (H:=1%Z); [lia|exact He|cbn; lia].
 Qed.

 Lemma base_close_consistent : 0<N ->
   T.ConsistentOpt (T.append_close (T.base M S e)).
 Proof.
   intro HN. pose proof (base_consistent e) as Hbase.
   pose proof (encode_consistent Hbase) as Ha.
   assert (He:Envelope (-1) 0 (encode(T.base M S e))).
   { split; [exact Ha|]. cbn; lia. }
   pose proof (related_append_close Ha (related_encode Hbase)
     ltac:(eapply envelope_close_room with (L:=(-1)%Z) (H:=0%Z); [lia|exact He|cbn; lia])) as Hr.
   destruct (A.append_close (encode(T.base M S e))) as [a|] eqn:Ha';
     destruct (T.append_close(T.base M S e)); cbn [RelatedOpt] in Hr;
     try contradiction; try exact I.
   eapply related_consistent; [|exact Hr].
   exact (proj1 (envelope_close (L:=(-1)%Z) (H:=0%Z) ltac:(lia) He ltac:(cbn; lia) Ha')).
 Qed.

 Lemma gen_consistent {Delimiter} (left right:Delimiter->bool) x :
   T.ConsistentOpt(T.gen M S left right x).
 Proof.
   unfold T.gen. destruct (T.supported M S); [|exact I].
   destruct x as [r|c]; [apply base_consistent|].
   destruct (left c); [|destruct (right c)].
   - destruct (Nat.eqb (T.depth M S) 0) eqn:Hd; [exact I|].
     apply base_open_consistent; apply Nat.eqb_neq in Hd; unfold N,T.depth in *; lia.
   - destruct (Nat.eqb (T.depth M S) 0) eqn:Hd; [exact I|].
     apply base_close_consistent; apply Nat.eqb_neq in Hd; unfold N,T.depth in *; lia.
   - apply T.ne_consistent; exact HS.
 Qed.

 (* The consistent carrier makes the domain of the monoid laws explicit.
    Its operation and generator are exactly the direct tuple operations;
    proofs have no computational content. *)
 Section Carrier.
 Context (HN:N<50).
 Definition Summary := {s : option(T.t M S) | T.ConsistentOpt s}.
 Definition summary_ne : Summary := exist _ (T.ne M S) (T.ne_consistent M HS).
 Definition summary_op (x y:Summary) : Summary :=
   exist _ (T.op (proj1_sig x) (proj1_sig y))
     (op_preserves_consistency (proj1_sig x) (proj1_sig y) HN (proj2_sig x) (proj2_sig y)).
 Definition Make {Delimiter} (left right:Delimiter->bool) : MonoidalOps (del Raw Delimiter) Value :=
   {| m_summary:=Summary; m_ne:=summary_ne; m_op:=summary_op;
      m_gen:=fun x=>exist _ (T.gen M S left right x) (gen_consistent left right x);
      m_obs:=fun x=>T.obs (proj1_sig x) |}.

 Lemma summary_ext (x y:Summary) : proj1_sig x=proj1_sig y -> x=y.
 Proof.
   destruct x as [x Hx],y as [y Hy]; cbn; intro H; subst y.
   f_equal; apply proof_irrelevance.
 Qed.

 Theorem Make_is_monoid {Delimiter} (left right:Delimiter->bool) :
   IsMonoid M -> IsMonoid (Make left right).
 Proof.
   intro HM. split.
   - intros [x Hx] [y Hy] [z Hz]. apply summary_ext; cbn.
     apply op_associative; assumption.
   - split; intros [x Hx]; apply summary_ext; cbn.
     + apply ne_left_neutral; assumption.
     + apply T.ne_right_neutral; assumption.
 Qed.
 End Carrier.
End Correspondence.
End TupleProof.
