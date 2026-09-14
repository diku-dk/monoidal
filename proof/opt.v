Require Import Monoid.
Set Implicit Arguments.
Set Universe Polymorphism.
Module OptMonoid.
Definition op {T} (x y : option T) := match x with Some _ => x | None => y end.
(** The outer option is failure; Some None is successful absence.
    The summary's None is the neutral absence, NOT an absorbing failure. *)
Definition opt {I O} (M : MonoidalOps I O) : MonoidalOps (option I) (option O) :=
  {| m_summary := option (m_summary M); m_ne := None; m_op := op;
     m_gen := fun x => match x with Some v => Some (m_gen M v) | None => None end;
     m_obs := fun x => match x with
       | None => Some None
       | Some s => match m_obs M s with Some v => Some (Some v) | None => None end
       end |}.
(** Payload combination is never used, so IsMonoid M is unnecessary. *)
Theorem opt_is_monoid {I O} (M : MonoidalOps I O) : IsMonoid (opt M).
Proof.
  split.
  - intros [x|] [y|] [z|]; reflexivity.
  - split; intros [x|]; reflexivity.
Qed.
Lemma first_present {T} (x : T) y : op (Some x) y = Some x.
Proof. reflexivity. Qed.
Lemma absent_observation {I O} (M : MonoidalOps I O) :
  m_obs (opt M) None = Some None.
Proof. reflexivity. Qed.
Lemma payload_failure {I O} (M : MonoidalOps I O) s :
  m_obs M s = None -> m_obs (opt M) (Some s) = None.
Proof. intro H; cbn; now rewrite H. Qed.
End OptMonoid.
