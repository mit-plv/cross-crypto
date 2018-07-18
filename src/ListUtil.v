Require Import Coq.Lists.List.

Module FromNil.
  Section WithElementType.
    Context {A : Type}.
    Definition nth_error_count l n : nat + A :=
      fold_right (fun a s => match s with
                             | inl n =>
                               match n with
                               | O => inr a
                               | S n => inl n
                               end
                             | inr a => inr a
                             end)
                 (inl n) l.
    Definition nth_error (l : list A) (n : nat) : option A :=
      match nth_error_count l n with
      | inl _ => None
      | inr a => Some a
      end.
  End WithElementType.

  Module _test.
    Local Definition t0 : nth_error (2::1::0::nil) 0 = Some 0 := eq_refl.
    Local Definition t1 : nth_error (2::1::0::nil) 1 = Some 1 := eq_refl.
    Local Definition t2 : nth_error (2::1::0::nil) 2 = Some 2 := eq_refl.
    Local Definition tx : nth_error (2::1::0::nil) 3 = None := eq_refl.
  End _test.
End FromNil.

Module Decompose.
  Section WithElementType.
    Context {A : Type}.

    Fixpoint decompose_find' (f : nat -> A -> bool) i acc l {struct l} :
      option (list A * A * list A) :=
      match l with
      | nil => None
      | cons x l => if f i x
                    then Some (acc, x, l)
                    else decompose_find' f (S i) (x :: acc) l
      end.

    Definition decompose_find f l := decompose_find' f 0 nil l.

    Definition found f l a (x : A) b :=
      l = rev_append a (x :: b) /\ f (length a) x = true.

    Local Create HintDb listutil discriminated.
    Local Hint Rewrite rev_append_rev
          app_length
          PeanoNat.Nat.add_1_r
          rev_app_distr
          rev_involutive : listutil.
    Local Hint Rewrite <- app_assoc : listutil.
    Local Ltac crush :=
      repeat match goal with
             | H : (_ :: _) = (_ :: _) |- _ => inversion H; clear H
             | H : (rev _ ++ _ :: nil) = (rev _ ++ _ :: nil) |- _ =>
               change (rev ?a ++ ?x :: nil) with (rev (x :: a)) in H;
               eapply (f_equal (@rev _)) in H;
               repeat rewrite rev_involutive in H
             | H : (rev _) = (rev _) |- _ =>
               eapply (f_equal (@rev _)) in H;
               repeat rewrite rev_involutive in H
             | _ => autorewrite with listutil in *;
                    cbn [rev_append rev length app] in *;
                    subst;
                    intuition idtac
             end.

    Lemma found_inv f y l a x b :
      found f (y :: l) a x b ->
      (a = nil /\ (f 0 y = true)) \/
      (exists a', a = (a' ++ y :: nil) /\
                  found (fun i => f (S i)) l a' x b).
    Proof.
      cbv [found].
      pattern a; eapply rev_ind.
      - crush.
      - right; eexists; crush.
    Qed.

    Lemma found_end_inv f y l a x b :
      found f (rev (y :: l)) a x b ->
      (b = nil /\ (f (length l) y = true)) \/
      (exists b', b = (b' ++ y :: nil) /\
                  found f (rev l) a x b').
    Proof.
      cbv [found].
      pattern b; eapply rev_ind.
      - crush.
      - intros z b' _ [H H'].
        replace (rev_append a (x :: b' ++ z :: nil)) with
            (rev (z :: rev b' ++ x :: a)) in H by crush.
        right; eexists; crush.
    Qed.

    Lemma decompose_find_spec f l :
      match decompose_find f l with
      | Some (a, x, b) => found f l a x b /\
                          ~ exists c y d, found f (rev a) c y d
      | None => ~ exists a x b, found f l a x b
      end.
    Proof.
      enough (forall acc,
                 (~ exists a x b, found f (rev acc) a x b) ->
                 match decompose_find' f (length acc) acc l with
                 | Some (a, x, b) =>
                   found f (rev_append acc l) a x b /\
                   ~ exists c y d, found f (rev a) c y d
                 | None => ~ exists a x b, found f (rev_append acc l) a x b
                 end) as H.
      {
        cbv [decompose_find].
        specialize (H nil); cbn [rev length] in H.
        refine ((fun H' => ltac:(clear H)) (H _)).
        - destruct (decompose_find' f 0 nil l) as [[[??]?]|];
            rewrite ?app_nil_r in H'; cbn [rev_append] in H'; intuition.
        - intros (?&?&?&Hnil).
          cbv [found rev] in Hnil.
          rewrite rev_append_rev in Hnil.
          eapply app_cons_not_nil; intuition eauto.
      }
      induction l as [|y l];
        intros acc Hacc; cbn [decompose_find' rev_append app].
      - rewrite rev_append_rev, app_nil_r; eauto.
      - cbv [found].
        remember (f (length acc) y) as b; destruct b;
          try solve [intuition eauto].
        eapply (IHl (y :: acc)).
        intros (?&?&?&Hyacc).
        eapply found_end_inv in Hyacc.
        destruct Hyacc as [|[? ?]].
        + intuition congruence.
        + eapply Hacc; do 3 eexists; intuition eauto.
    Qed.

    Definition decompose_at l n : option (list A * list A) :=
      match decompose_find (fun i _ => Nat.eqb i n) l with
      | Some (a, x, b) => Some (a, x :: b)
      | None => None
      end.

    Lemma decompose_at_correct l n : match decompose_at l n with
                                     | Some (a, b) => l = rev_append a b
                                     | None => True
                                     end.
    Proof.
      cbv [decompose_at].
      pose proof (decompose_find_spec (fun i _ => Nat.eqb i n) l) as H.
      destruct (decompose_find _ _) as [[[??]?]|];
        cbv [found] in H;
        intuition idtac.
    Qed.
  End WithElementType.
End Decompose.
