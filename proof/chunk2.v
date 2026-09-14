Require Import Monoid chunk.
Set Implicit Arguments.
Set Universe Polymorphism.
Import ChunkMonoid.

Section Chunk2.
Context {I O P Q D : Type}.
Context (M1 : MonoidalOps I O) (M2 : MonoidalOps O P)
        (M3 : MonoidalOps (del P D) Q).
Context (ignore1 ignore2 : D -> bool).
Let inner := chunk M2 M3 ignore2.
Let reference := chunk M1 inner ignore1.

(** The Futhark carrier has A/B/C. Totalising chunk observations also
    requires outer failure and a failed middle chunk that has not yet been
    observed. The latter must NOT be collapsed to outer failure. *)
Inductive flat :=
| Failed : flat
| FA : m_summary M1 -> flat
| FB : m_summary M1 -> m_summary M2 -> m_summary M1 -> flat
| FC : m_summary M1 -> m_summary M2 -> m_summary M3 -> m_summary M2 -> m_summary M1 -> flat
| MiddleFailed : m_summary M1 -> m_summary M1 -> flat.

Definition decode (x:flat) : m_summary reference :=
  match x with
  | Failed => None
  | FA a => Some (A M1 inner a)
  | FB a b z => Some (C M1 inner a (Some (A M2 M3 b)) z)
  | FC a b c d z => Some (C M1 inner a (Some (C M2 M3 b c d)) z)
  | MiddleFailed a z => Some (C M1 inner a None z)
  end.

Definition encode (x:m_summary reference) : flat :=
  match x with
  | None => Failed
  | Some (A _ _ a) => FA a
  | Some (C _ _ a None z) => MiddleFailed a z
  | Some (C _ _ a (Some (A _ _ b)) z) => FB a b z
  | Some (C _ _ a (Some (C _ _ b c d)) z) => FC a b c d z
  end.

Lemma encode_decode x : encode (decode x) = x.
Proof. destruct x; reflexivity. Qed.
Lemma decode_encode x : decode (encode x) = x.
Proof.
  destruct x as [[a|a b z]|]; try reflexivity.
  destruct b as [[b|b c d]|]; reflexivity.
Qed.

Definition chunk2 : MonoidalOps (del I D) Q :=
  {| m_summary := flat;
     m_ne := encode (m_ne reference);
     m_op := fun x y => encode (m_op reference (decode x) (decode y));
     m_gen := fun x => encode (m_gen reference x);
     m_obs := fun x => m_obs reference (decode x) |}.

Theorem chunk2_is_monoid : IsMonoid M1 -> IsMonoid M2 -> IsMonoid M3 -> IsMonoid chunk2.
Proof.
  intros H1 H2 H3.
  assert (H : IsMonoid reference).
  { apply chunk_is_monoid; [exact H1|apply chunk_is_monoid; assumption]. }
  destruct H as [Ha [Hl Hr]].
  split; [|split].
  - intros x y z.
    change (encode (m_op reference (decode (encode (m_op reference (decode x) (decode y)))) (decode z)) =
            encode (m_op reference (decode x) (decode (encode (m_op reference (decode y) (decode z)))))).
    rewrite !decode_encode, Ha; reflexivity.
  - intro x.
    change (encode (m_op reference (decode (encode (m_ne reference))) (decode x)) = x).
    rewrite decode_encode, Hl, encode_decode; reflexivity.
  - intro x.
    change (encode (m_op reference (decode x) (decode (encode (m_ne reference)))) = x).
    rewrite decode_encode, Hr, encode_decode; reflexivity.
Qed.

Lemma operation_correspondence x y :
  decode (m_op chunk2 x y) = m_op reference (decode x) (decode y).
Proof. apply decode_encode. Qed.
Lemma generation_correspondence x : decode (m_gen chunk2 x) = m_gen reference x.
Proof. apply decode_encode. Qed.
Lemma observation_correspondence x : m_obs chunk2 x = m_obs reference (decode x).
Proof. reflexivity. Qed.
End Chunk2.
