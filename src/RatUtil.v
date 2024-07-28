Require Import FCF.FCF.
From Coq Require Import Morphisms.

Create HintDb rat discriminated.
Create HintDb ratsimpl discriminated.

#[global]
Hint Extern 1 => simple eapply (@reflexivity Rat eqRat _) : rat.
#[global]
Hint Extern 1 => simple eapply (@reflexivity Rat leRat _) : rat.
#[global]
Hint Immediate rat0_le_all : rat.

Lemma maxRat_same r : maxRat r r = r.
Proof. intros; cbv [maxRat]; destruct (bleRat r r) eqn:?; trivial. Qed.
Lemma minRat_same r : minRat r r = r.
Proof. intros; cbv [minRat]; destruct (bleRat r r) eqn:?; trivial. Qed.

#[global]
Hint Rewrite ratSubtract_0 minRat_same maxRat_same : ratsimpl.

Lemma ratDistance_same r : ratDistance r r == 0.
Proof. cbv [ratDistance]; autorewrite with ratsimpl; auto with rat. Qed.

#[global]
Hint Rewrite ratDistance_same : ratsimpl.
