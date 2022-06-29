Require Import FCF.FCF.
Require Import FCF.Asymptotic.
Require Import RatUtil.
Require Import Coq.Lists.SetoidList.

Global Instance Proper_negligible :
  Proper (pointwise_relation nat eqRat ==> iff) negligible.
Proof.
  cbv [pointwise_relation Proper respectful].
  split; pose (@symmetry _ eqRat _); eauto 10 using negligible_eq.
Qed.

Global Instance Proper_negligible_le :
  Proper (pointwise_relation nat leRat ==> Basics.flip Basics.impl) negligible.
Proof.
  cbv [pointwise_relation Proper respectful].
  intros ? ? ? ?; eauto using negligible_le.
Qed.

Lemma negligible_0 : negligible (fun _ => 0).
  eapply negligible_le with (f1 := fun n => 0 / expnat 2 n).
  { reflexivity. }
  { apply negligible_const_num. }
Qed.

Global Instance Reflexive_negligible_ratDistance :
  Reflexive (fun f g => negligible (fun eta => | f eta - g eta |)).
Proof.
  intros ?; setoid_rewrite ratDistance_same; eapply negligible_0.
Qed.

Global Instance Symmetric_negligible_ratDistance :
  Symmetric (fun f g => negligible (fun eta => | f eta - g eta |)).
Proof.
  intros ???; setoid_rewrite ratDistance_comm; assumption.
Qed.

Global Instance Transitive_negligible_ratDistance :
  Transitive (fun f g => negligible (fun eta => | f eta - g eta |)).
Proof.
  intros ?????; setoid_rewrite ratTriangleInequality; eauto using negligible_plus.
Qed.

Definition image_relation {T} (R:T->T->Prop) {A} (f:A->T) := fun x y => R (f x) (f y).
Global Instance Equivalence_image_relation {T R} {Equivalence_R:Equivalence R} {A} (f:A->T) :
  Equivalence (image_relation R f).
Proof. destruct Equivalence_R; split; cbv; eauto. Qed.

Definition Comp_eq {A} := image_relation (pointwise_relation _ eqRat) (@evalDist A).
Global Instance Equivalence_Comp_eq {A} : Equivalence (@Comp_eq A) := _.

Global Instance Proper_evalDist {A} : Proper (Comp_eq ==> Logic.eq ==> eqRat) (@evalDist A).
Proof. intros ?? H ?? ?; subst; apply H. Qed.

Global Instance Proper_getSupport {A} : Proper (Comp_eq ==> (@Permutation.Permutation _)) (@getSupport A).
Proof. intros ???; eapply evalDist_getSupport_perm_id; assumption. Qed.

Global Instance Proper_sumList {A:Set} {R:A->A->Prop} : Proper (eqlistA R  ==> (R ==> eqRat) ==> eqRat) (@sumList A).
Proof.
  repeat intro. cbv [sumList].
  rewrite <-!fold_left_rev_right.
  eapply eqlistA_rev in H.
  generalize dependent (rev x); generalize dependent (rev y).
  intros ? ?; induction 1; [reflexivity|].
  simpl; f_equiv; eauto.
Qed.

Global Instance Proper_sumList_permutation {A:Set} : Proper ((@Permutation.Permutation A) ==> (pointwise_relation _ eqRat) ==> eqRat) (@sumList A).
Proof.
  intros ? ? H; induction H; repeat intro; cbv [respectful] in *; rewrite ?sumList_cons.
  { eauto with rat. }
  { f_equiv; eauto. }
  { cbv [pointwise_relation] in H; repeat rewrite H.
    repeat rewrite <-ratAdd_assoc.
    rewrite (ratAdd_comm (y0 y)).
    f_equiv.
    eapply (Proper_sumList(R:=Logic.eq)); eauto; repeat intro; subst; auto; reflexivity. }
  { etransitivity; [eapply IHPermutation1 | eapply IHPermutation2];
      intros; subst; (try match goal with H1:_ |- _ => eapply H1 end;reflexivity). }
Qed.

Global Instance Proper_Ret {A} {R} : Proper (R ==> pointwise_relation _ Comp_eq) (@Ret A).
Proof.
  intros eq1 eq2 ? x1 x2.
  cbv [Comp_eq image_relation pointwise_relation evalDist].
  destruct (eq1 x1 x2), (eq2 x1 x2); (congruence||reflexivity).
Qed. 

Global Instance Proper_Bind {A B} : Proper (Comp_eq ==> (pointwise_relation _ Comp_eq) ==> Comp_eq) (@Bind A B).
Proof.
  intros ?? H ?? G ?. simpl evalDist.
  setoid_rewrite H. setoid_rewrite G. reflexivity.
Qed.

Lemma Comp_eq_bool (x y:Comp bool) :
  well_formed_comp x
  -> well_formed_comp y
  -> Pr [x] == Pr[y]
  -> Comp_eq x y.
  intros.
  intro b.
  destruct b; trivial.
  rewrite !evalDist_complement; trivial.
  f_equiv; trivial.
Qed.

Lemma Comp_eq_evalDist A (x y:Comp A) :
  (forall c, evalDist x c == evalDist y c)
  <-> Comp_eq x y.
Proof.
  split; intro.
  { cbv [Comp_eq pointwise_relation image_relation]; assumption. }
  { cbv [Comp_eq pointwise_relation image_relation] in H; assumption. }
Qed.

(* TODO: This should be a two-way lemma *)
Lemma comp_spec_impl_Comp_eq A (H: EqDec A) (x y: Comp A) :
  comp_spec eq x y
  -> Comp_eq x y.
Proof.
  intro.
  apply Comp_eq_evalDist.
  intro.
  fcf_to_prhl.
  cbv [comp_spec] in *.
  destruct H0.
  exists x0.
  destruct H0.
  destruct H1.
  split; try split; try assumption.
  intros.
  specialize (H2 p H3).
  rewrite H2.
  reflexivity.
Qed.


Lemma Bind_unused A B (a:Comp A) (b:Comp B) :
  Comp_eq (_ <-$ a; b) b.
Admitted. (* TODO: does FCF have something like this? *)

Lemma Bind_Ret_l {A B: Set} {H: EqDec A} (x: A) (f: A -> Comp B):
  Comp_eq (x' <-$ ret x; f x') (f x).
Proof.
  apply Comp_eq_evalDist.
  intros.
  apply evalDist_left_ident_eq.
Qed.

Lemma Bind_Ret_r {A : Set} {H: EqDec A} (cA : Comp A) :
  Comp_eq (x <-$ cA; ret x) cA.
Proof.
  apply Comp_eq_evalDist.
  intros.
  apply evalDist_right_ident.
Qed.

Lemma Bind_assoc {A B C: Set} (cA : Comp A)
      (f : A -> Comp B) (g : B -> Comp C) :
  Comp_eq (x <-$ cA; y <-$ f x; g y) (y <-$ (x <-$ cA; f x); g y).
Proof.
  intros.
  apply Comp_eq_evalDist.
  intros.
  fcf_inline_first.
  reflexivity.
Qed.

Lemma Bind_comm : forall (A B : Set)(c1 : Comp A)(c2 : Comp B)(C : Set)(c3 : A -> B -> Comp C),
  Comp_eq (a <-$ c1; b <-$ c2; (c3 a b)) (b <-$ c2; a <-$ c1; (c3 a b)). 
Proof.
  intros.
  apply Comp_eq_evalDist.
  intros.
  apply evalDist_commute_eq.
Qed.

(* TODO(jgross): explain these *)
Ltac solve_Proper_eqs :=
  idtac;
  lazymatch goal with
  | [ |- Proper _ _ ] => apply @reflexive_proper; solve_Proper_eqs
  | [ |- Reflexive (_ ==> _)%signature ]
    => apply @reflexive_eq_dom_reflexive; solve_Proper_eqs
  | [ |- Reflexive _ ] => try apply eq_Reflexive
  end.
Ltac is_evar_or_eq e :=
  first [ is_evar e
        | match e with
          | eq => idtac
          end ].
Ltac is_evar_or_eq_or_evar_free e :=
  first [ is_evar_or_eq e
        | try (has_evar e; fail 1) ].
#[global]
Hint Extern 1 (Proper ?e _) =>
is_evar_or_eq e; solve_Proper_eqs : typeclass_instances.
#[global]
Hint Extern 1 (Proper (?e1 ==> ?e2) _) =>
is_evar_or_eq e1; is_evar_or_eq_or_evar_free e2; solve_Proper_eqs : typeclass_instances.
#[global]
Hint Extern 1 (Proper (?e1 ==> ?e2 ==> ?e3) _) =>
is_evar_or_eq e1; is_evar_or_eq e2; is_evar_or_eq_or_evar_free e3; solve_Proper_eqs : typeclass_instances.
#[global]
Hint Extern 1 (Proper (?e1 ==> ?e2 ==> ?e3 ==> ?e4) _) =>
is_evar_or_eq e1; is_evar_or_eq e2; is_evar_or_eq e3; is_evar_or_eq_or_evar_free e4; solve_Proper_eqs : typeclass_instances.
#[global]
Hint Extern 1 (Proper (?e1 ==> ?e2 ==> ?e3 ==> ?e4 ==> ?e5) _) =>
is_evar_or_eq e1; is_evar_or_eq e2; is_evar_or_eq e3; is_evar_or_eq e4; is_evar_or_eq_or_evar_free e5; solve_Proper_eqs : typeclass_instances.
#[global]
Hint Extern 1 (Proper (?e1 ==> ?e2 ==> ?e3 ==> ?e4 ==> ?e5 ==> ?e6) _) =>
is_evar_or_eq e1; is_evar_or_eq e2; is_evar_or_eq e3; is_evar_or_eq e4; is_evar_or_eq e5; is_evar_or_eq_or_evar_free e6; solve_Proper_eqs : typeclass_instances.
