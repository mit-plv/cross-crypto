Local Set Universe Polymorphism.
Require CrossCrypto.fmap.
From Coq Require Import List.

Section WithKV.
  Context {K V : Type}.
  Context (Keqb : K -> K -> bool).
  Definition list_of_pairs : @fmap.operations K V :=
    {|
      fmap.M := list (K * V);
      fmap.empty := nil;
      fmap.add := fun k v => cons (k, v);
      fmap.find := fun k m => option_map snd (List.find (fun '(k', _) => Keqb k' k) m);
      fmap.fold_ac := fun S f => List.fold_right (fun '(k, v) => f k v);
    |}.
End WithKV.