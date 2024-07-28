Require CrossCrypto.fmap.
From Coq Require Import List.
From Coq Require Import Sorted.
From Coq Require Import Eqdep_dec.

Definition dec P := {P} + {~P}.
Definition uniq_pf P := forall p1 p2 : P, p1 = p2.
Definition eqdec (T : Type) := forall a b : T, dec (a = b).

Lemma eqdec_uip T (D : eqdec T) (a b : T) : uniq_pf (a = b).
  intros ??.
  eapply eq_proofs_unicity_on.
  intros c.
  edestruct (D a c); eauto.
Qed.

Section Sorted.
  Import EqNotations.

  Scheme HdRel_depind := Induction for HdRel Sort Prop.

  Context {T : Type}
          {R : T -> T -> Prop}
          (R_uniq : forall a b, uniq_pf (R a b)).

  Lemma HdRel_depinv {x l} (p : HdRel R x l) :
    match l as l0 return l0 = l -> Prop with
    | nil => fun e => p = rew e in (HdRel_nil _ _)
    | b :: l => fun e => exists (r : R x b),
                    p = rew e in (HdRel_cons _ _ _ _ r)
    end eq_refl.
  Proof. revert l p; apply HdRel_depind; cbn [eq_rect]; eauto. Qed.

  Lemma HdRel_uniq h l : uniq_pf (HdRel R h l).
    induction l; intros p1 p2.
    - rewrite (HdRel_depinv p1), (HdRel_depinv p2); eauto.
    - destruct (HdRel_depinv p1) as (r1&->).
      destruct (HdRel_depinv p2) as (r2&->).
      rewrite (R_uniq _ _ r1 r2).
      eauto.
  Qed.

  Scheme Sorted_depind := Induction for Sorted Sort Prop.

  Lemma Sorted_depinv {l} (p : Sorted R l) :
    match l as l0 return l0 = l -> Prop with
    | nil => fun e => p = rew e in Sorted_nil _
    | cons x l => fun e => exists s h,
                      p = rew e in Sorted_cons s h
    end eq_refl.
  Proof. revert l p; apply Sorted_depind; cbn [eq_rect]; eauto. Qed.

  Lemma Sorted_uniq l : uniq_pf (Sorted R l).
  Proof.
    induction l; intros p1 p2.
    - rewrite (Sorted_depinv p1), (Sorted_depinv p2); eauto.
    - destruct (Sorted_depinv p1) as (?&?&->).
      destruct (Sorted_depinv p2) as (?&?&->).
      cbn [eq_rect].
      rewrite IHl.
      rewrite HdRel_uniq.
      eauto.
  Qed.

  Context (R_dec : forall a b, dec (R a b)).

  Definition HdRel_dec x l : dec (HdRel R x l).
    destruct l as [|y l].
    - solve [econstructor; eauto].
    - destruct (R_dec x y).
      + solve [econstructor; eauto].
      + right; intros H.
        inversion_clear H.
        congruence.
  Defined.

  Local Hint Constructors NoDup.

  Context (R_trans : forall a b c, R a b -> R b c -> R a c)
          (R_antisym : forall a, R a a -> False).
  Lemma sorted_list_nodup (l : list T) :
    Sorted R l -> NoDup l.
  Proof.
    intros H.
    eapply Sorted_StronglySorted in H; eauto using R_trans.
    induction H as [|???? Hf]; eauto.
    econstructor; eauto.
    intro; eapply Forall_forall in Hf; eauto using R_antisym.
  Qed.

  Context (T_eq_lem : forall a b : T, a = b \/ a <> b).

  Lemma nodup_in_cons_extend {t} a (l1 l2 : list t) :
    NoDup (a :: l1) ->
    (forall x, In x (a :: l1) -> In x (a :: l2)) ->
    forall x, In x l1 -> In x l2.
  Proof.
    intros Hn H x ?.
    inversion_clear Hn.
    cbn [In] in H.
    destruct (H x); eauto.
    congruence.
  Qed.

  Lemma sorted_list_set (l1 l2 : list T) :
    Sorted R l1 -> Sorted R l2 ->
    (forall x, In x l1 <-> In x l2) ->
    l1 = l2.
  Proof.
    intros HS1 HS2 HIn.
    revert dependent l2.
    induction l1 as [|a1]; intros.
    - destruct l2; eauto.
      cbn [In] in HIn.
      exfalso.
      eapply HIn; eauto.
    - induction l2 as [|a2].
      { cbn [In] in HIn.
        exfalso.
        eapply HIn; eauto. }
      destruct (T_eq_lem a1 a2) as [<-|].
      + f_equal.
        apply IHl1; try solve [eapply Sorted_inv; eauto].
        intros.
        split; eapply nodup_in_cons_extend;
          repeat (eapply HIn || eauto using sorted_list_nodup).
      + exfalso.
        assert (In a1 l2).
        {
          cbn [In] in HIn.
          edestruct HIn.
          intuition congruence.
        }
        assert (In a2 l1).
        {
          cbn [In] in HIn.
          edestruct (HIn a2).
          intuition congruence.
        }
        assert (R a1 a2).
        {
          eapply Sorted_StronglySorted in HS1; eauto using R_trans.
          inversion_clear HS1.
          eapply Forall_forall; eauto.
        }
        assert (R a2 a1).
        {
          eapply Sorted_StronglySorted in HS2; eauto using R_trans.
          inversion_clear HS2.
          eapply Forall_forall; eauto.
        }
        eauto using R_trans, R_antisym.
  Qed.
End Sorted.

Section Extmap.
  Context {key value : Type}.
  Context {lt : key -> key -> Prop}.
  Local Notation "a < b" := (lt a b).
  Context {key_dec : eqdec key}
          {value_dec : eqdec value}
          {lt_dec : forall a b : key, dec (a < b)}
          {lt_uniq : forall a b : key, uniq_pf (a < b)}.

  Definition extmap := {l : list (key * value) | Sorted lt (map fst l)}.

  Lemma key_uniq : forall a b : key, uniq_pf (a = b).
  Proof. eauto using eqdec_uip. Qed.

  Lemma cond_uniq (l : list (key * value)) : uniq_pf (Sorted lt (map fst l)).
  Proof. eauto using Sorted_uniq. Qed.

  Definition l_dec : eqdec (list (key * value)).
    cbv [eqdec dec] in key_dec, value_dec |- *.
    intros.
    decide equality; decide equality; eauto.
  Defined.

  Definition extmap_dec : eqdec extmap.
    intros (l1&?) (l2&?).
    destruct (l_dec l1 l2) as [-> | NE].
    - left.
      rewrite Sorted_uniq by eapply lt_uniq.
      eauto.
    - right; intro H; inversion H.
      congruence.
  Defined.

  Definition empty : extmap := exist _ nil (Sorted_nil _).

  Fixpoint add' (k : key) (v : value) (l : list (key * value))
    : list (key * value) :=
    match l with
    | nil => (k, v) :: nil
    | cons (k', v') l =>
      match key_dec k k' with
      | left _ => ((k, v) :: l)
      | right _ =>
        match lt_dec k k' with
        | left _ => ((k, v) :: (k', v') :: l)
        | right _ => ((k', v') :: add' k v l)
        end
      end
    end.

  Context {trichotomy : forall a b : key, a <> b -> ~(a < b) -> b < a}.

  Lemma add_hdrel (k0 k : key) (v : value) (l : list (key * value)) :
    HdRel lt k0 (map fst l) ->
    k0 < k ->
    HdRel lt k0 (map fst (add' k v l)).
  Proof.
    intros H ?.
    induction l as [|[k' v']]; cbn [add'].
    - cbn [map fst]; eauto.
    - destruct (key_dec k k') as [->|];
        [|destruct (lt_dec k k')]; cbn [map fst] in H |- *;
          eauto; inversion H; eauto.
  Qed.

  Lemma add_sorted (k : key) (v : value) (l : list (key * value)) :
    Sorted lt (map fst l) -> Sorted lt (map fst (add' k v l)).
    intros H.
    induction l as [|[k' v']]; cbn [add'].
    - cbn [map fst]; eauto.
    - destruct (key_dec k k') as [->|];
        [|destruct (lt_dec k k')]; cbn [map fst] in H |- *;
          eauto; inversion H; eauto using add_hdrel.
  Qed.

  Definition add (k : key) (v : value) (m : extmap) : extmap.
    destruct m as [l s].
    exists (add' k v l).
    eauto using add_sorted.
  Defined.

  Fixpoint find' k l : option value :=
    match l with
    | nil => None
    | (k', v') :: l => match key_dec k k' with
                       | left _ => Some v'
                       | right _ => find' k l
                       end
    end.

  Definition find (k : key) (m : extmap) : option value :=
    let (l, _) := m in
    find' k l.

  Definition fold_ac (S : Type)
             (f : key -> value -> S -> S) (init : S) (m : extmap) : S :=
    let (l, _) := m in
    List.fold_right (fun '(k, v) => f k v) init l.

  Definition extensional : @fmap.operations key value :=
    {|
      fmap.M := extmap;
      fmap.empty := empty;
      fmap.add := add;
      fmap.find := find;
      fmap.fold_ac := fold_ac;
    |}.

  Context {lt_trans : forall a b c : key, a < b -> b < c -> a < c}
          {lt_antisym : forall a : key, a < a -> False}.

  Lemma find_in k (m : extmap) v :
    let (l, _) := m in
    In (k, v) l <-> match find' k l with
                    | Some v' => v = v'
                    | None => False
                    end.
  Proof.
    destruct m as [l s].
    induction l as [|[k' v']]; cbn [find'].
    - split; eauto.
    - cbn [map fst] in s.
      destruct (key_dec k k') as [<-|].
      + split.
        * intros [|]; try congruence.
          exfalso.
          eapply sorted_list_nodup in s; eauto.
          inversion_clear s.
          match goal with
          | H : ~ In k (map fst l) |- _ => change k with (fst (k, v)) in H
          end.
          eauto using in_map.
        * intros <-.
          eauto using in_eq.
      + rewrite <- IHl; try solve [inversion s; eauto].
        split; eauto using in_cons.
        intros [|]; congruence.
  Qed.

  Lemma find_keys_ext (m1 m2 : extmap) :
    let (l1, _) := m1 in
    let (l2, _) := m2 in
    (forall k, find' k l1 = find' k l2) ->
    map fst l1 = map fst l2.
  Proof.
    destruct m1 as [l1 s1].
    destruct m2 as [l2 s2].
    intros Hfind.
    eapply sorted_list_set; eauto;
      try solve [intros; edestruct key_dec; eauto].
    intros k.
    specialize (Hfind k).
    assert (forall v, In (k, v) l1 <-> In (k, v) l2) as Hf.
    {
      pose proof (find_in k (exist _ l1 s1)) as Hf1;
        cbv iota beta in Hf1;
        pose proof (find_in k (exist _ l2 s2)) as Hf2;
        cbv iota beta in Hf2.
      destruct (find' k l1) as [v1|];
        destruct (find' k l2) as [v2|];
        cbn [find']; try congruence;
          [inversion Hfind; subst v2|];
          setoid_rewrite Hf1;
          setoid_rewrite Hf2;
          intuition.
    }

    repeat rewrite in_map_iff.
    split;
      intros ((k'&?)&?&?);
      cbn [fst] in *;
      subst k';
      exists (k, v);
      (rewrite Hf || rewrite <- Hf); eauto.
  Qed.

  Lemma ext_cons k v l1 l2 :
    Sorted lt (map fst ((k, v) :: l1)) ->
    Sorted lt (map fst ((k, v) :: l2)) ->
    (forall k', find' k' ((k, v) :: l1) = find' k' ((k, v) :: l2)) ->
    forall k', find' k' l1 = find' k' l2.
  Proof.
    intros s1 s2 Hfind k'.
    cbn [find'] in Hfind.
    specialize (Hfind k').
    destruct (key_dec k' k) as [->|]; eauto.
    assert (Sorted lt (map fst l1)) as s1' by (inversion_clear s1; eauto).
    assert (Sorted lt (map fst l2)) as s2' by (inversion_clear s2; eauto).
    eapply sorted_list_nodup in s1; eauto.
    eapply sorted_list_nodup in s2; eauto.
    transitivity (None : option value);
      [pose proof (find_in k (exist _ l1 s1')) as Hf|
       pose proof (find_in k (exist _ l2 s2')) as Hf];
      cbv iota beta in Hf;
      destruct (find' k _) as [v'|]; eauto;
        exfalso;
        specialize (Hf v');
        destruct Hf as [_ Hf];
        specialize (Hf eq_refl);
        eapply in_map with (f:=fst) in Hf;
        cbn [map fst] in s1, s2, Hf;
        solve [(inversion s1 + inversion s2);
               congruence].
  Qed.

  Lemma extmap_extensional (m1 m2 : extmap) :
    (forall k, find k m1 = find k m2) ->
    m1 = m2.
  Proof.
    intros Hfind.
    destruct m1 as [l1 s1], m2 as [l2 s2].
    enough (l1 = l2) as <-.
    {
      f_equal.
      eapply Sorted_uniq; eauto.
    }
    assert (map fst l1 = map fst l2) as Hmap by
          (eapply (find_keys_ext (exist _ l1 s1) (exist _ l2 s2));
           eauto).

    cbn [find] in Hfind.
    revert dependent l2.
    induction l1 as [|[k1 v1]]; destruct l2 as [|[k2 v2]];
      intros;
      try solve [cbn [map] in Hmap; congruence].
    assert (k1 = k2) as <- by (cbn [map fst] in Hmap; congruence).
    assert (v1 = v2) as <-.
    {
      specialize (Hfind k1);
        cbn [find'] in Hfind.
      destruct (key_dec k1 k1); congruence.
    }
    f_equal.
    assert (Sorted lt (map fst l1)) as s1' by (inversion_clear s1; eauto).
    assert (Sorted lt (map fst l2)) as s2' by (inversion_clear s2; eauto).
    apply IHl1; eauto using ext_cons.
    eapply (find_keys_ext (exist _ l1 s1') (exist _ l2 s2')).
    eauto using ext_cons.
  Qed.
End Extmap.
