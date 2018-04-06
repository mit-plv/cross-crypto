Require Import CrossCrypto.fmap.list_of_pairs.

Section WithKV.
  Context {K V : Type}.
  Context (Keqb : K -> K -> bool).

  Context (Kper : K -> K -> Prop) (Vper : V -> V -> Prop).
  (* TODO: require per transitive symmetric *)
  Context (Keqb_iff : forall k1 k2, Keqb k1 k2 = true <-> Kper k1 k2).
  Lemma ok : fmap.ok Kper Vper (list_of_pairs Keqb).
  Abort.
End WithKV.