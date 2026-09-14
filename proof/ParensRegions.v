From Stdlib Require Import List Arith Lia.
Import ListNotations.
Set Implicit Arguments.
Set Universe Polymorphism.

(** The public region interface. [view] is proof-only; the Futhark interface
    has no indexing or conversion to a list. *)
Module ParensRegions.
Record regions (A : Type) := {
  carrier : Type;
  depth : nat;
  fill : A -> carrier;
  top : carrier -> A;
  last : carrier -> A;
  replace : carrier -> A -> carrier;
  push : carrier -> A -> carrier;
  pop : carrier -> A -> carrier;
  reverse : carrier -> carrier;
  view : carrier -> list A
}.
Arguments carrier {_} _.
Arguments depth {_} _.
Arguments fill {_} _ _.
Arguments top {_} _ _.
Arguments last {_} _ _.
Arguments replace {_} _ _ _.
Arguments push {_} _ _ _.
Arguments pop {_} _ _ _.
Arguments reverse {_} _ _.
Arguments view {_} _ _.

Definition Zero (A : Type) : regions A :=
 {| carrier := A; depth := 0;
    fill := fun x => x; top := fun x => x; last := fun x => x;
    replace := fun _ x => x; push := fun _ x => x;
    pop := fun _ p => p; reverse := fun x => x;
    view := fun x => [x] |}.

Definition Succ {A} (R : regions A) : regions A :=
 {| carrier := (A * carrier R * A)%type; depth := S (depth R);
    fill := fun x => (x, fill R x, x);
    top := fun r => fst (fst r); last := fun r => snd r;
    replace := fun r x => (x, snd (fst r), snd r);
    push := fun r x => (x, push R (snd (fst r)) (fst (fst r)),
                        last R (snd (fst r)));
    pop := fun r p => (top R (snd (fst r)),
                       pop R (snd (fst r)) (snd r), p);
    reverse := fun r => (snd r, reverse R (snd (fst r)), fst (fst r));
    view := fun r => fst (fst r) :: view R (snd (fst r)) ++ [snd r] |}.

Record Laws {A} (R : regions A) : Prop := {
  view_size : forall r, length (view R r) = 2 * depth R + 1;
  view_injective : forall r s, view R r = view R s -> r = s;
  view_fill : forall x, view R (fill R x) = repeat x (2 * depth R + 1);
  view_top : forall r, view R r = top R r :: tl (view R r);
  view_last : forall r p, List.last (view R r) p = last R r;
  view_replace : forall r x, view R (replace R r x) = x :: tl (view R r);
  view_push : forall r x, view R (push R r x) ++ [last R r] = x :: view R r;
  view_pop : forall r p, top R r :: view R (pop R r p) = view R r ++ [p];
  view_reverse : forall r, view R (reverse R r) = rev (view R r)
}.

Theorem Zero_laws A : Laws (Zero A).
Proof. constructor; cbn; intros; try reflexivity; congruence. Qed.

Theorem Succ_laws {A} (R : regions A) : Laws R -> Laws (Succ R).
Proof.
 intros [Hsize Hinj Hfill Htop Hlast Hreplace Hpush Hpop Hrev].
 constructor; cbn.
 - intros [[a r] z]; cbn. rewrite length_app, Hsize; cbn; lia.
 - intros [[a r] z] [[b s] w]; cbn. intro H.
   injection H as Hab Hrest. subst b.
   apply app_inj_tail in Hrest as [Hrs Hzw].
   apply Hinj in Hrs; subst s w; reflexivity.
 - intro x. rewrite Hfill.
   change (x :: repeat x (2 * depth R + 1) ++ repeat x 1 =
           repeat x (2 * S (depth R) + 1)).
   rewrite <- repeat_app.
   change (repeat x (S ((2 * depth R + 1) + 1)) =
           repeat x (2 * S (depth R) + 1)).
   f_equal; lia.
 - intros [[a r] z]; reflexivity.
 - intros [[a r] z] p.
   change (List.last ((a :: view R r) ++ [z]) p = z).
   apply last_last.
 - intros [[a r] z] x; reflexivity.
 - intros [[a r] z] x; cbn.
   rewrite Hpush; reflexivity.
 - intros [[a r] z] p; cbn.
   change (a :: (top R r :: view R (pop R r z)) ++ [p] =
           a :: (view R r ++ [z]) ++ [p]).
   rewrite Hpop; reflexivity.
 - intros [[a r] z]; cbn.
   rewrite Hrev, rev_app_distr; reflexivity.
Qed.

Fixpoint Build (A : Type) (n : nat) : regions A :=
 match n with 0 => Zero A | S n => Succ (Build A n) end.

Theorem Build_laws A n : Laws (Build A n).
Proof. induction n; cbn; [apply Zero_laws|now apply Succ_laws]. Qed.

Theorem Build_depth A n : depth (Build A n) = n.
Proof. induction n; cbn; congruence. Qed.

Section Derived.
 Context {A} (R : regions A) (HR : Laws R).
 Lemma reverse_involutive r : reverse R (reverse R r) = r.
 Proof. apply (view_injective HR); rewrite ! (view_reverse HR), rev_involutive; reflexivity. Qed.
 Lemma top_fill x : top R (fill R x) = x.
 Proof.
   pose proof (view_top HR (fill R x)) as H.
   rewrite (view_fill HR) in H.
   destruct (2 * depth R + 1) eqn:E; [lia|]. cbn in H; congruence.
 Qed.
 Lemma replace_top r : replace R r (top R r) = r.
 Proof. apply (view_injective HR); rewrite (view_replace HR); symmetry; apply (view_top HR). Qed.
 Lemma reverse_fill x : reverse R (fill R x) = fill R x.
 Proof. apply (view_injective HR); rewrite (view_reverse HR), !(view_fill HR), rev_repeat; reflexivity. Qed.
 Lemma pop_fill x : pop R (fill R x) x = fill R x.
 Proof.
   apply (view_injective HR).
   pose proof (view_pop HR (fill R x) x) as H.
   rewrite top_fill, (view_fill HR) in H.
   replace (2 * depth R + 1) with (S (2 * depth R)) in * by lia.
   cbn in H. injection H as H. rewrite H.
   rewrite (view_fill HR).
   change (repeat x (2 * depth R) ++ repeat x 1 = repeat x (2 * depth R + 1)).
   rewrite <- repeat_app. f_equal; lia.
 Qed.
End Derived.
End ParensRegions.
