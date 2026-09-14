From Stdlib Require Import List Bool ZArith Lia.
Require Import Monoid Parens ParensRegions.
Require Export Delimiter.
Import ListNotations.
Set Implicit Arguments.
Set Universe Polymorphism.
Open Scope nat_scope.

(** The byte arithmetic is modelled over Z, with explicit representability
    theorems. This is not a formalisation of the Futhark compiler. *)
Module CompactDepth.
Open Scope Z_scope.
Record t := mk { lo : Z; hi : Z; net : Z }.
Definition consistent (d : Z) (s : t) :=
 lo s <= 0 /\ 0 <= hi s /\ lo s <= net s /\ net s <= hi s /\ hi s-lo s <= d.
Definition combine a b :=
 mk (Z.min (lo a) (net a+lo b))
    (Z.max (hi a) (net a+hi b)) (net a+net b).
Definition valid d s :=
 (0 <=? d) && (d <? 50) && (-d <=? lo s) && (lo s <=? 0) &&
 (0 <=? hi s) && (hi s <=? d) && (lo s <=? net s) &&
 (net s <=? hi s) && (hi s-lo s <=? d).

Lemma valid_spec d s : valid d s = true <-> 0 <= d < 50 /\ consistent d s.
Proof.
 unfold valid, consistent.
 repeat rewrite Bool.andb_true_iff; repeat rewrite Z.leb_le;
 rewrite Z.ltb_lt; lia.
Qed.

Lemma combine_bounds d a b :
 0 <= d -> consistent d a -> consistent d b ->
 let c := combine a b in
 consistent (2*d) c /\ -2*d <= lo c /\ hi c <= 2*d /\
 -2*d <= net c <= 2*d.
Proof.
 unfold consistent, combine; cbn -[Z.mul].
 intros Hd Ha Hb.
 destruct (Z.min_spec (lo a) (net a + lo b)) as [[H1 E1]|[H1 E1]];
 destruct (Z.max_spec (hi a) (net a + hi b)) as [[H2 E2]|[H2 E2]];
 rewrite E1, E2; lia.
Qed.

Definition signed_byte x := -128 <= x <= 127.
Theorem combine_fits_i8 d a b :
 0 <= d < 50 -> consistent d a -> consistent d b ->
 let c := combine a b in
 signed_byte (lo c) /\ signed_byte (hi c) /\ signed_byte (net c) /\
 signed_byte (hi c-lo c) /\ signed_byte (net a+lo b) /\
 signed_byte (net a+hi b).
Proof.
 intros Hd Ha Hb.
 pose proof (combine_bounds (proj1 Hd) Ha Hb) as H.
 unfold signed_byte, consistent in *; cbn -[Z.mul] in *; lia.
Qed.

Theorem counts_fit_i8 d s :
 0 <= d < 50 -> consistent d s ->
 0 <= -lo s <= 49 /\ 0 <= net s-lo s <= 49 /\
 0 <= net s-2*lo s <= 98 /\
 0 <= 2*d-(net s-2*lo s) <= 98.
Proof. unfold consistent; lia. Qed.
End CompactDepth.

(** Direct model of Parens.Make: active region at the head; reverse and
    discard source padding; replay closes, then opens, consuming a queue.
    Failures (including observation failure) are represented by option. *)
Module ParensTuple.
Module R := ParensRegions.ParensRegions.
Section Make.
 Context {Raw Value Delimiter : Type}.
 Context (M : MonoidalOps (Nest Raw Value) Value).
 Context (S : R.regions (m_summary M)).
 Context (is_left is_right : Delimiter -> bool).

 Record t := mk { lo : Z; hi : Z; net : Z; regions : R.carrier S }.
 Definition metadata s := CompactDepth.mk (lo s) (hi s) (net s).
 Definition depth := R.depth S.
 Definition supported := Nat.ltb depth 50.
 Definition base x := mk 0%Z 0%Z 0%Z (R.replace S (R.fill S (m_ne M)) x).
 Definition ne : option t := if supported then Some (base (m_ne M)) else None.
 Definition closes s := Z.to_nat (-lo s).
 Definition opens s := Z.to_nat (net s-lo s).
 Definition active s := closes s + opens s.
 Definition pop r := R.pop S r (m_ne M).
 Definition append_region s x :=
   mk (lo s) (hi s) (net s) (R.replace S (regions s) (m_op M (R.top S (regions s)) x)).
 Definition append_open s :=
   mk (Z.min (lo s) (net s)) (Z.max (hi s) (net s+1)) (net s+1)%Z
      (R.push S (regions s) (m_ne M)).
 Definition append_close s : option t :=
   if Nat.ltb 0 (opens s) then
     match m_obs M (R.top S (regions s)) with
     | None => None
     | Some v =>
       let rest := pop (regions s) in
       Some (mk (Z.min (lo s) (net s-1)) (Z.max (hi s) (net s)) (net s-1)%Z
         (R.replace S rest (m_op M (R.top S rest) (m_gen M (nested v)))))
     end
   else Some (mk (Z.min (lo s) (net s-1)) (Z.max (hi s) (net s)) (net s-1)%Z
                  (R.push S (regions s) (m_ne M))).

 Fixpoint replay_closes n (state : option (t * R.carrier S)) :=
   match n, state with
   | 0, _ => state
   | Datatypes.S k, Some (s,q) =>
     match append_close s with
     | None => None
     | Some s' => replay_closes k (Some (append_region s' (R.top S q), pop q))
     end
   | _, None => None
   end.
 Fixpoint replay_opens n (state : option (t * R.carrier S)) :=
   match n, state with
   | 0, _ => state
   | Datatypes.S k, Some (s,q) =>
     replay_opens k (Some (append_region (append_open s) (R.top S q), pop q))
   | _, None => None
   end.

 Definition op (a b : option t) : option t :=
   match a,b with
   | Some a,Some b =>
     let m := CompactDepth.combine (metadata a) (metadata b) in
     if CompactDepth.valid (Z.of_nat depth) m then
       let q := Nat.iter (2*depth-active b) pop (R.reverse S (regions b)) in
       let s0 := append_region a (R.top S q) in
       let s1 := replay_closes (closes b) (Some (s0,pop q)) in
       match replay_opens (opens b) s1 with
       | None => None
       | Some (s2,_) => Some (mk (CompactDepth.lo m) (CompactDepth.hi m)
                                (CompactDepth.net m) (regions s2))
       end
     else None
   | _,_ => None
   end.

 Definition gen (x : del Raw Delimiter) : option t :=
   if supported then
     match x with
     | E r => Some (base (m_gen M (raw r)))
     | Del c =>
       if is_left c then
         if Nat.eqb depth 0 then None else Some (append_open (base (m_ne M)))
       else if is_right c then
         if Nat.eqb depth 0 then None else append_close (base (m_ne M))
       else ne
     end
   else None.
 Definition obs (s : option t) : option Value :=
   match s with
   | Some s =>
     if (0 <=? lo s)%Z && (hi s <=? Z.of_nat depth)%Z && (net s =? 0)%Z
     then m_obs M (R.top S (regions s)) else None
   | None => None
   end.
 Definition Make : MonoidalOps (del Raw Delimiter) Value :=
   {| m_summary := option t; m_ne := ne; m_op := op; m_gen := gen; m_obs := obs |}.

 Definition Consistent s :=
   CompactDepth.consistent (Z.of_nat depth) (metadata s) /\
   active s <= 2*depth /\
   skipn (Datatypes.S (active s)) (R.view S (regions s)) =
     repeat (m_ne M) (2*depth-active s).
 Definition ConsistentOpt s := match s with Some s => Consistent s | None => True end.

 Lemma op_none_left x : op None x = None.
 Proof. reflexivity. Qed.
 Lemma op_none_right x : op x None = None.
 Proof. destruct x; reflexivity. Qed.
 Lemma replay_closes_none n : replay_closes n None = None.
 Proof. destruct n; reflexivity. Qed.
 Lemma replay_opens_none n : replay_opens n None = None.
 Proof. destruct n; reflexivity. Qed.

 Theorem op_success_depth a b s : op a b = Some s ->
   CompactDepth.consistent (Z.of_nat depth) (metadata s).
 Proof.
   destruct a as [a|], b as [b|]; try discriminate.
   unfold op.
   destruct (CompactDepth.combine (metadata a) (metadata b)) as [l h n] eqn:Hm.
   destruct (CompactDepth.valid (Z.of_nat depth) (CompactDepth.mk l h n)) eqn:Hv;
     [|discriminate].
   intro Hop.
   match type of Hop with
   | context [match ?q with Some _ => _ | None => _ end] =>
     destruct q as [[s0 q0]|] eqn:Hqueue
   end; try discriminate.
   inversion Hop; subst s.
   apply CompactDepth.valid_spec in Hv. exact (proj2 Hv).
 Qed.

 Context (HS : R.Laws S).
 Lemma base_ne_regions : regions (base (m_ne M)) = R.fill S (m_ne M).
 Proof.
   cbn [base regions].
   rewrite <- (R.top_fill HS (m_ne M)) at 2.
   apply (R.replace_top HS).
 Qed.

 Theorem ne_consistent : ConsistentOpt ne.
 Proof.
   unfold ne; destruct supported; cbn [ConsistentOpt]; [|exact I].
   unfold Consistent. split.
   - unfold CompactDepth.consistent, metadata, base; cbn; lia.
   - split; [unfold active, closes, opens, base; cbn; lia|].
     rewrite base_ne_regions, (R.view_fill HS).
     unfold active, closes, opens, base; cbn.
     change (skipn 1 (repeat (m_ne M) (2*depth+1)) = repeat (m_ne M) (2*depth-0)).
     replace (2*depth+1) with (Datatypes.S (2*depth)) by lia.
     cbn [skipn repeat]. f_equal; lia.
 Qed.

 Theorem metadata_combine_fits_i8 a b :
   depth < 50 -> Consistent a -> Consistent b ->
   let m := CompactDepth.combine (metadata a) (metadata b) in
   CompactDepth.signed_byte (CompactDepth.lo m) /\
   CompactDepth.signed_byte (CompactDepth.hi m) /\
   CompactDepth.signed_byte (CompactDepth.net m) /\
   CompactDepth.signed_byte (CompactDepth.hi m-CompactDepth.lo m).
 Proof.
   intros Hd [Ha _] [Hb _].
   pose proof (CompactDepth.combine_fits_i8 (d:=Z.of_nat depth)
     ltac:(lia) Ha Hb) as H.
   cbn in H |- *; tauto.
 Qed.

 Lemma iter_pop_fill k : Nat.iter k pop (R.fill S (m_ne M)) = R.fill S (m_ne M).
 Proof.
   induction k; [reflexivity|].
   rewrite Nat.iter_succ, IHk; unfold pop; apply (R.pop_fill HS).
 Qed.

 Lemma append_region_ne s : IsMonoid M -> append_region s (m_ne M) = s.
 Proof.
   intros [_ [_ Hright]]. unfold append_region.
   rewrite Hright, (R.replace_top HS). destruct s; reflexivity.
 Qed.

 Theorem ne_right_neutral : depth < 50 -> IsMonoid M ->
   forall x, ConsistentOpt x -> op x ne = x.
 Proof.
   intros Hd HM [s|] Hs; [|reflexivity].
   assert (Hsupported : supported = true) by (unfold supported; apply Nat.ltb_lt; exact Hd).
   unfold ne; rewrite Hsupported.
   unfold op.
   assert (Hmd : CompactDepth.combine (metadata s) (metadata (base (m_ne M))) = metadata s).
   { destruct Hs as [[Hlo [Hhi [Hln [Hnh Hspan]]]] _].
     unfold CompactDepth.combine, metadata, base; cbn [lo hi net CompactDepth.lo CompactDepth.hi CompactDepth.net].
     rewrite !Z.add_0_r, Z.min_l, Z.max_l; try assumption; reflexivity. }
   rewrite Hmd.
   assert (Hvalid : CompactDepth.valid (Z.of_nat depth) (metadata s) = true).
   { apply CompactDepth.valid_spec. split; [lia|exact (proj1 Hs)]. }
   rewrite Hvalid.
   change (closes (base (m_ne M))) with 0.
   change (opens (base (m_ne M))) with 0.
   change (active (base (m_ne M))) with 0.
   rewrite base_ne_regions, (R.reverse_fill HS), iter_pop_fill, (R.top_fill HS).
   cbn [replay_closes replay_opens].
   rewrite (append_region_ne s HM).
   destruct s; reflexivity.
 Qed.

 (** [ParensTupleProof] supplies the existing array-correspondence proof.
     [ParensTupleDirect] develops independent tuple replay laws; neither
     this definition file nor that direct development imports the array model. *)
End Make.
End ParensTuple.

(** Executable smoke tests of the direct replay definitions, including
    failure. These examples are not a substitute for the general laws. *)
Module TupleExamples.
 Definition Sum : MonoidalOps (Nest nat nat) nat :=
   {| m_summary := nat; m_ne := 0; m_op := Nat.add;
      m_gen := fun x => match x with raw n | nested n => n end;
      m_obs := fun n => Some n |}.
 Definition R2 := ParensRegions.Build nat 2.
 Definition token := @ParensTuple.gen nat nat bool Sum R2 (fun b => b) negb.
 Definition fold xs := fold_left (@ParensTuple.op nat nat Sum R2)
   (map token xs) (@ParensTuple.ne nat nat Sum R2).
 Definition eval xs := @ParensTuple.obs nat nat Sum R2 (fold xs).
 Example two_levels :
   eval [E 12; Del true; E 34; Del true; E 56; Del false; Del false; E 78] = Some 180.
 Proof. vm_compute; reflexivity. Qed.
 Example excessive_depth :
   eval [Del true; Del true; Del true; E 1; Del false; Del false; Del false] = None.
 Proof. vm_compute; reflexivity. Qed.
 Example malformed_order : eval [Del false; E 1; Del true] = None.
 Proof. vm_compute; reflexivity. Qed.
 Example split_replay :
   let a := fold [E 12; Del true] in
   let b := fold [E 34; Del true; E 56] in
   let c := fold [Del false; Del false; E 78] in
   @ParensTuple.op nat nat Sum R2 (@ParensTuple.op nat nat Sum R2 a b) c =
   @ParensTuple.op nat nat Sum R2 a (@ParensTuple.op nat nat Sum R2 b c).
 Proof. vm_compute; reflexivity. Qed.
End TupleExamples.
