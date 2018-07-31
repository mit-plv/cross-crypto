Require Import Coq.Lists.List.

Create HintDb listrew discriminated.
Hint Rewrite
     PeanoNat.Nat.add_succ_r
     PeanoNat.Nat.add_0_r
     app_length
     app_nil_r
     rev_app_distr
     rev_append_rev
     rev_involutive
     rev_length
  : listrew.
Hint Rewrite <-
     app_assoc
     app_comm_cons
  : listrew.
Ltac listrew :=
  repeat (autorewrite with listrew in *;
          cbn [rev app length] in *).

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

    Fixpoint find' (f : nat -> A -> bool) i acc l {struct l} :
      option (list A * A * list A) :=
      match l with
      | nil => None
      | cons x l => if f i x
                    then Some (acc, x, l)
                    else find' f (S i) (x :: acc) l
      end.

    Definition find f l := find' f 0 nil l.

    Definition found f l a (x : A) b :=
      l = rev_append a (x :: b) /\ f (length a) x = true.

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
             | H : _ /\ _ |- _ => destruct H
             | H : exists _, _ |- _ => destruct H
             | _ => cbv [found] in *;
                    listrew;
                    subst;
                    intuition idtac
             end.

    Lemma found_inv f y l a x b :
      found f (y :: l) a x b ->
      (a = nil /\ (f 0 y = true)) \/
      (exists a', a = (a' ++ y :: nil) /\
                  found (fun i => f (S i)) l a' x b).
    Proof.
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
      pattern b; eapply rev_ind.
      - crush.
      - intros z b' _ [??].
        replace (rev_append a (x :: b' ++ z :: nil)) with
            (rev (z :: rev b' ++ x :: a)) in * by crush.
        right; eexists; crush.
    Qed.

    Lemma find_spec f l :
      match find f l with
      | Some (a, x, b) => found f l a x b /\
                          ~ exists c y d, found f (rev a) c y d
      | None => ~ exists a x b, found f l a x b
      end.
    Proof.
      enough (forall acc,
                 (~ exists a x b, found f (rev acc) a x b) ->
                 match find' f (length acc) acc l with
                 | Some (a, x, b) =>
                   found f (rev_append acc l) a x b /\
                   ~ exists c y d, found f (rev a) c y d
                 | None => ~ exists a x b, found f (rev_append acc l) a x b
                 end) as H.
      {
        cbv [find].
        specialize (H nil); cbn [rev length] in H.
        refine ((fun H' => ltac:(clear H)) (H _)).
        - destruct (find' f 0 nil l) as [[[??]?]|]; crush.
        - intros (?&?&?&?).
          crush.
          eapply app_cons_not_nil; intuition eauto.
      }
      induction l as [|y l];
        intros acc Hacc; cbn [find' rev_append app].
      - crush.
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

    Fixpoint find_all' (f : nat -> A -> bool)
             i results prefix l {struct l} :
      list (list A * A * list A) :=
      match l with
      | nil => results
      | cons x l => find_all' f (S i)
                                        (if f i x
                                         then (prefix, x, l) :: results
                                         else results)
                                        (x :: prefix)
                                        l
      end.

    Definition find_all f l := find_all' f 0 nil nil l.

    Lemma find_all_correct f l :
      Forall (fun '(a, x, b) => found f l a x b)
             (find_all f l).
    Proof.
      enough (forall results prefix,
                 Forall (fun '(a, x, b) => found f (rev_append prefix l)
                                                 a x b)
                        results ->
                 Forall (fun '(a, x, b) => found f (rev_append prefix l)
                                                 a x b)
                        (find_all' f (length prefix)
                                             results prefix l))
             by (eapply (H nil nil); eapply Forall_nil).
      induction l as [|y l]; cbn [find_all']; eauto.
      intros.
      eapply (IHl (if f (length prefix) y
                   then (prefix, y, l) :: results
                   else results)
                  (y :: prefix)).
      remember (f (length prefix) y) as fy.
      destruct fy; eauto.
      eapply Forall_cons; eauto.
      cbv [found]; eauto.
    Qed.

    Fixpoint index' acc l n {struct n} : option (list A * A * list A) :=
      match l with
      | nil => None
      | x :: l =>
        match n with
        | 0 => Some (acc, x, l)
        | S n => index' (x :: acc) l n
        end
      end.

    Definition index l n : option (list A * A * list A) :=
      index' nil l n.

    Lemma index_correct l n :
      match index l n with
      | Some (a, x, b) => l = rev_append a (x :: b) /\ length a = n
      | None => True
      end.
    Proof.
      enough (forall acc,
                 match index' acc l n with
                 | Some (a, x, b) =>
                   rev_append acc l = rev_append a (x :: b) /\
                   length a = length acc + n
                 | None => True
                 end) as H by eapply H.
      revert l; induction n; intros [|y l] acc; cbn [index']; eauto.
      specialize (IHn l (y :: acc)).
      destruct (index' _ _ _) as [[[??]?]|]; intuition crush.
    Qed.

    Section Prefix.
      Context (A_eqb : A -> A -> bool)
              (A_eqb_eq : forall a a' : A, A_eqb a a' = true <-> a = a').

      Fixpoint prefix pre l : option (list A) :=
        match pre with
        | nil => Some l
        | x :: pre =>
          match l with
          | nil => None
          | a :: l => if A_eqb x a
                      then prefix pre l
                      else None
          end
        end.

      Lemma prefix_correct pre l : match prefix pre l with
                                   | Some rest => l = pre ++ rest
                                   | None => True
                                   end.
      Proof.
        revert l; induction pre as [|x pre];
          intros l; cbn [prefix app]; eauto.
        destruct l as [|a l]; eauto.
        pose proof (A_eqb_eq x a); specialize (IHpre l).
        destruct (A_eqb x a), (prefix pre l); intuition congruence.
      Qed.
    End Prefix.
  End WithElementType.
End Decompose.

Module ListDec.
  Section WithElementType.
    Context {A : Type}.

    Section EqDec.
      Context (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'}).

      Definition list_eq_dec (l l' : list A) : {l = l'} + {l <> l'}.
        let t := (try solve [subst; eauto | right; intro; congruence]) in
        revert l'; induction l as [|a l]; destruct l' as [|a' l']; t;
        destruct (A_eq_dec a a'), (IHl l'); t.
      Defined.
    End EqDec.

    Section Eqb.
      Context (A_eqb : A -> A -> bool)
              (A_eqb_eq : forall a a' : A, A_eqb a a' = true <-> a = a').

      Fixpoint list_eqb (l l' : list A) : bool :=
        match l, l' with
        | nil, nil => true
        | a :: l, a' :: l' => A_eqb a a' && list_eqb l l'
        | _, _ => false
        end.

      Lemma list_eqb_eq (l l' : list A) : list_eqb l l' = true <-> l = l'.
      Proof.
        revert l'; induction l; destruct l'; cbn [list_eqb];
          rewrite ?Bool.andb_true_iff, ?A_eqb_eq, ?IHl in *;
          intuition congruence.
      Qed.
    End Eqb.
  End WithElementType.
End ListDec.
