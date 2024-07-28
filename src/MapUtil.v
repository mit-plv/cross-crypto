From Coq Require Import MSetPositive FSetFacts MSetProperties.
From Coq Require Import FMapPositive FMapFacts.
Module PositiveMapFacts := FMapFacts.WFacts_fun PositiveMap.E PositiveMap.
Module PositiveMapProperties := FMapFacts.WProperties_fun PositiveMap.E PositiveMap.
Module PositiveSetProperties := MSetProperties.WPropertiesOn PositiveSet.E MSetPositive.PositiveSet.

Section FMapTODO.
  Lemma PosMap_add_commutes {A} x y (m : PositiveMap.t A) a b :
    (x <> y \/ a = b) ->
    PositiveMap.Equal (PositiveMap.add x a (PositiveMap.add y b m))
                      (PositiveMap.add y b (PositiveMap.add x a m)).
  Proof.
    cbv [PositiveMap.Equal]; destruct 1; intros;
      repeat match goal with
             | _ => rewrite PositiveMapFacts.add_o
             | |- context [if ?x then _ else _] =>
               destruct x; subst; try congruence
             end.
  Qed.

  Lemma subset_inter s1 s2 s3:
    PositiveSet.Subset s1 s3 ->
    PositiveSet.Subset s2 s3 ->
    PositiveSet.Subset (PositiveSet.inter s1 s2) s3.
  Admitted.
  
  Lemma subset_union s1 s2 s3 :
    PositiveSet.Subset (PositiveSet.union s2 s3) s1
    -> PositiveSet.Subset s2 s1 /\ PositiveSet.Subset s3 s1.
  Admitted.

  Lemma find_update_in {A} k (m1 m2 : PositiveMap.t A) :
    PositiveMap.In k m2 ->
    PositiveMap.find k (PositiveMapProperties.update m1 m2) =
    PositiveMap.find k m2.
  Admitted.

  Lemma find_update_not_in {A} k (m1 m2 : PositiveMap.t A) :
    ~PositiveMap.In k m2 ->
    PositiveMap.find k (PositiveMapProperties.update m1 m2) =
    PositiveMap.find k m1.
  Admitted.

  Lemma update_assoc {A} (m0 m1 m2 : PositiveMap.t A):
    PositiveMapProperties.update m0 (PositiveMapProperties.update m1 m2) =
    PositiveMapProperties.update (PositiveMapProperties.update m0 m1) m2.
  Admitted.

  Lemma update_add {A} (m0 m1:PositiveMap.t A) i a :
    PositiveMap.Equal
      (PositiveMapProperties.update m0 (PositiveMap.add i a m1))
      (PositiveMap.add i a (PositiveMapProperties.update m0 m1)).
  Proof.
  Admitted.
  
  Lemma union_remove_equal x s s' s1 s2
        (Hadd: PositiveSetProperties.Add x s s') :
    ~PositiveSet.In x s ->
    PositiveSet.Equal (PositiveSet.union s1 s2) s' ->
    PositiveSet.Equal (PositiveSet.union (PositiveSet.remove x s1)
                                         (PositiveSet.remove x s2)) s.
  Proof.
    cbv [PositiveSet.Equal PositiveSetProperties.Add] in *; intros.
    match goal with H: forall _, PositiveSet.In _ _ <-> PositiveSet.In _ _
                                 |- context [PositiveSet.In ?x] =>
                    specialize (H x) end.
    rewrite Hadd in *.
    rewrite PositiveSet.union_spec in *.
    rewrite !PositiveSet.remove_spec in *.
    (* asserts because tauto is bad at substituting *)
    assert (x = a <-> a = x) by (split; congruence).
    assert (x = a -> ~ PositiveSet.In a s) by congruence.
    repeat match goal with
           | _ => progress intros
           | H: _ /\ _ |- _ => destruct H
           | H: _ \/ _ |- _ => destruct H
           | _ => split
           | _ => tauto
           end.
  Qed.

  Lemma add_add_eq {A} x y (a b : A) m (H:x = y) :
    PositiveMap.Equal
      (PositiveMap.add x a (PositiveMap.add y b m))
      (PositiveMap.add x a m).
  Admitted.

  Lemma update_overwrite {A} x (m1 m2 : PositiveMap.t A) :
    PositiveMap.In x m2 ->
    PositiveMap.Equal 
      (PositiveMapProperties.update m1 m2)
      (PositiveMapProperties.update (PositiveMap.remove x m1) m2).
  Admitted.


  Lemma union_remove s1 s2 x :
    PositiveSet.Equal (PositiveSet.union s1 s2)
                      (PositiveSet.union s1 (PositiveSet.remove x s2)).
  Admitted.

  Lemma empty_not_in {A} m :
    @PositiveMap.Empty A m <-> forall x, ~PositiveMap.In x m.
  Proof.
    cbv [PositiveMap.Empty PositiveMap.MapsTo PositiveMap.In not Znat.neq].
    split; repeat match goal with
                  | _ => progress intro
                  | H: exists _, _ |- _ => destruct H
                  | _ => solve [eauto]
                  end.
  Qed.

  Lemma update_empty_r {A} (m1 m2: PositiveMap.t A) :
    PositiveMap.Empty m2 ->
    PositiveMap.Equal (PositiveMapProperties.update m1 m2) m1.
  Admitted.

  Lemma update_subset {A} (m1 m2 : PositiveMap.t A) :
    (forall k, PositiveMap.In k m1 -> PositiveMap.In k m2) ->
    PositiveMap.Equal (PositiveMapProperties.update m1 m2) m2.
  Admitted.

  Lemma empty_inter: forall s : PositiveSet.t, PositiveSet.eq (PositiveSet.inter s PositiveSet.empty) PositiveSet.empty.
    intros.
    apply PositiveSetProperties.empty_is_empty_1.
    apply PositiveSetProperties.empty_inter_2.
    apply PositiveSet.empty_spec.
  Qed.
End FMapTODO.

