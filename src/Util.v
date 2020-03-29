Require Import FCF.FCF.
Require Import FCF.SplitVector.
Require Import RewriteUtil.

Lemma Rnd_split_eq n1 n2 : Comp_eq
                                (x <-$ { 0 , 1 }^ n1 + n2; ret splitVector n1 n2 x)
                                (x1 <-$ { 0 , 1 }^ n1; x2 <-$ { 0 , 1 }^ n2; ret (x1, x2)).
Proof. intro z. eapply Rnd_split_equiv. Qed.

Lemma list_vector_split a b (T : Set) (x : Vector.t T _) : skipn (b) (Vector.to_list x) = Vector.to_list (snd (splitVector (b) a x)).
  induction b; simpl; intuition.
  destruct (splitVector b a (Vector.tl x)) eqn:?.
  specialize (IHb (Vector.tl x)).
  rewrite Heqp in IHb.
  simpl in *.
  rewrite <- IHb.
  rewrite (Vector.eta x).
  reflexivity.
Qed.
