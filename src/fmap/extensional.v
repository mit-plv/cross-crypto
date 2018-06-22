Require CrossCrypto.fmap.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Logic.Eqdep_dec.

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

  Fixpoint add' (k : key) (v : value) (l : list (key * value)) : list (key * value) :=
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

  Lemma add_sort (k : key) (v : value) (l : list (key * value)) :
    Sorted lt (map fst l) -> Sorted lt (map fst (add' k v l)).
    intros H.
    induction l as [|[k' v']]; cbn [add'].
    - cbn [map fst]; eauto.
    - destruct (key_dec k k') as [->|];
        [|destruct (lt_dec k k')]; cbn [map fst] in H |- *;
          eauto; inversion H; eauto using add_hdrel.
  Qed.

  (* Definition extensional : @fmap.operations key value := *)
  (*   {| *)
  (*     fmap.M := extmap; *)
  (*     fmap.empty := empty; *)
  (*     fmap.add := add; *)
  (*     fmap.find := find; *)
  (*     fmap.fold_ac := fold_ac; *)
  (*   |}. *)

End Extmap.
