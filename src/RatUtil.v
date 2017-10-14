Require Import FCF.FCF.
Require Import Coq.Classes.Morphisms.

Create HintDb rat discriminated.
Create HintDb ratsimpl discriminated.

Hint Immediate (@reflexivity Rat eqRat _) : rat.
Hint Immediate (@reflexivity Rat leRat _) : rat.
Hint Immediate (rat0_le_all) : rat.

Lemma maxRat_same r : maxRat r r = r.
Proof. intros; cbv [maxRat]; destruct (bleRat r r) eqn:?; trivial. Qed.
Lemma minRat_same r : minRat r r = r.
Proof. intros; cbv [minRat]; destruct (bleRat r r) eqn:?; trivial. Qed.

Hint Rewrite ratSubtract_0 minRat_same maxRat_same : ratsimpl.

Lemma ratDistance_same r : ratDistance r r == 0.
Proof. cbv [ratDistance]; autorewrite with ratsimpl; auto with rat. Qed.

Hint Rewrite ratDistance_same : ratsimpl.
