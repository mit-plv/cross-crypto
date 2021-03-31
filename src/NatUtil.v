Require Import Lia.

Fixpoint optsub (n m : nat) {struct m} : option nat :=
  match m with
  | 0 => Some n
  | S m => match n with
           | 0 => None
           | S n => optsub n m
           end
  end.

Notation "a -? b" := (optsub a b) (left associativity, at level 50).

Lemma optsub_plus a b :
  match a -? b with
  | Some c => a = b + c
  | None => a < b
  end.
Proof.
  revert a; induction b; intros a; cbn [optsub plus]; eauto.
  destruct a; try lia.
  specialize (IHb a).
  destruct (a -? b); lia.
Qed.
