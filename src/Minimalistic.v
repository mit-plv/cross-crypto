Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Classes.Morphisms.
Require Import Coq.MSets.MSetPositive Coq.FSets.FMapPositive.
Require Import FCF.FCF FCF.Asymptotic FCF.EqDec.
Require Import CrossCrypto.Util CrossCrypto.RatUtil CrossCrypto.RewriteUtil CrossCrypto.MapUtil.
Require Import Coq.ZArith.ZArith.
Require Import Lia. (* TODO: remove after removing not_negligible_const *)
Require Import Coq.Init.Wf.
Require Import Coq.Relations.Relations.
Require Import Coq.Wellfounded.Transitive_Closure.
Require Import Coq.Wellfounded.Lexicographic_Product.
Require Import Coq.btauto.Btauto.

#[global] Instance compeq_rw A : RewriteRelation (@Comp_eq A) := {}.

#[global] Hint Mode Reflexive ! ! : typeclass_instances.
#[global] Hint Mode Symmetric ! ! : typeclass_instances.
#[global] Hint Mode Transitive ! ! : typeclass_instances.

Lemma eqb_bool a b : (a ?= b) = negb (xorb a b).
Proof.
  destruct a; destruct b;
    (rewrite eqb_leibniz || rewrite eqb_false_iff); congruence.
Qed.
Ltac btauto' := btauto.
Ltac btauto := cbv [implb] in *; rewrite ?eqb_bool; rewrite ?eqb_bool in *; btauto'.

(* TODO: move *)
Lemma or_refl P : or P P <-> P. Proof. tauto. Qed.
Lemma or_False_r P : or P False <-> P. Proof. tauto. Qed.
Lemma or_False_l P : or False P <-> P. Proof. tauto. Qed.

Section Language.
  Context {type  : Set} {eqdec_type : EqDec type}
          {interp_type : type -> nat -> Set}
          {eqdec_interp_type : forall {t eta}, EqDec (interp_type t eta)}
          {interp_type_inhabited : forall t eta, interp_type t eta}
          {tbool trand : type} {tprod : type -> type -> type}.
  Context {func : type -> type -> Set}.

  Bind Scope etype_scope with type.
  Delimit Scope etype_scope with etype.
  Local Notation "A * B" := (tprod A%etype B%etype) : etype_scope.
  Local Notation "A -> B" := (func A%etype B%etype) : etype_scope.

  Inductive expr : type -> Type :=
  | expr_const {t} (_:forall eta, interp_type t eta) : expr t
  | expr_random (idx:positive) : expr trand
  | expr_adversarial {t1 t2} (_:expr t1) : expr t2
  | expr_app {t1 t2} (_:(t1 -> t2)%etype) (_:expr t1) : expr t2
  | expr_pair {t1 t2} (_:expr t1) (_:expr t2) : expr (t1 * t2).

  Bind Scope expr_scope with expr.
  Delimit Scope expr_scope with expr.

  Local Notation "'#' x" := (expr_const x) (right associativity, at level 9, format "# x") : expr_scope.
  Local Notation "'$' x" := (expr_random x%positive) (right associativity, at level 79, x at next level, format "$ x") : expr_scope. (* FIXME: we want level 9, but it conflicts with fcf *)
  Local Notation "f @ x" := (expr_app f x%expr) (left associativity, at level 11, format "f @ x") : expr_scope.
  Local Notation "'!' t '@' x" := (@expr_adversarial _ t x%expr) (left associativity, at level 11, format "! t @ x", t at next level) : expr_scope.
  Local Notation "'!' '@' x" := (expr_adversarial x%expr) (left associativity, at level 11, format "! @ x") : expr_scope.
  Local Notation "( x , y , .. , z )" := (expr_pair .. (expr_pair x%expr y%expr) .. z%expr) : expr_scope.
  Local Notation "'#!'" := (expr_const (interp_type_inhabited _)) : expr_scope.

  Fixpoint randomness_indices {t:type} (e:expr t) : PositiveSet.t :=
    match e with
    | #_ => PositiveSet.empty
    | $i => PositiveSet.singleton i
    | !@x => randomness_indices x
    | f@x => randomness_indices x
    | (a, b) => PositiveSet.union (randomness_indices a) (randomness_indices b)
    end%expr.

  (* TODO: use a map with a canonical representation *)
  Global Instance randomness_map_eq_dec {eta} : EqDec (PositiveMap.tree (interp_type trand eta)). Admitted.

  Context (cast_rand : forall eta, Bvector eta -> interp_type trand eta).
  Section GenerateRandomness.
    Context (eta:nat).

    Definition genrand : Comp _ := (r <-$ {0,1}^eta; ret (cast_rand eta r)).
    (* TODO: use [genrand] in the remainder of this section *)

    Definition generate_randomness_single i (rndC : Comp (PositiveMap.tree _)) :=
      rnds' <-$ rndC;
        ri <-$ {0,1}^eta;
        ret (PositiveMap.add i (cast_rand eta ri) rnds' : PositiveMap.tree _).

    Definition generate_randomness idxs
      : Comp (PositiveMap.tree (interp_type trand eta))
      := PositiveSet.fold generate_randomness_single
                          idxs
                          (ret (PositiveMap.empty _ : PositiveMap.tree _)).

    Lemma empty_randomness :
      Comp_eq (generate_randomness PositiveSet.empty)
              (ret (PositiveMap.empty _ : PositiveMap.tree _)).
    Proof.
      intros; cbv [generate_randomness].
      rewrite PositiveSetProperties.fold_empty.
      reflexivity.
    Qed.

    Global Instance Proper_generate_randomness_single :
      Proper (eq ==> Comp_eq ==> Comp_eq) generate_randomness_single.
    Proof.
      cbv [Proper respectful generate_randomness_single]; intros; subst.
      match goal with H: Comp_eq _ _ |- _ => rewrite H; reflexivity end.
    Qed.

    (* TODO: This is unprovable; it is true if programs only use the
    map interface functions and never modify the map structurally. To
    prove this you need a canonical map.*)
    Lemma generate_randomness_single_transpose :
      SetoidList.transpose Comp_eq generate_randomness_single.
    Proof.
      cbv [SetoidList.transpose generate_randomness_single]; intros.
      repeat setoid_rewrite <-Bind_assoc.
      repeat setoid_rewrite Bind_Ret_l.

      destruct (Pos.eq_dec x y).
      {
        etransitivity.
        {
          do 3 (eapply Proper_Bind; [reflexivity|];
                cbv [pointwise_relation]; intros).

    (* Line below fails because Ret is not proper over
          PositiveMap.eq *)
          (* rewrite add_add_eq. *)

    Admitted.

    Lemma add_generate_randomness {A} (f:_->Comp A) x s s' :
      PositiveSetProperties.Add x s s' ->
      ~PositiveSet.In x s ->
      Comp_eq (a <-$ generate_randomness s'; f a)
              (a <-$ {0,1}^eta;
                 b <-$ generate_randomness s;
                 f (PositiveMap.add x (cast_rand eta a) b)).
    Proof.
      cbv [generate_randomness]; intros.
      rewrite PositiveSetProperties.fold_2 by
          (try eassumption; try (exact _);
           auto using generate_randomness_single_transpose).
      cbv [generate_randomness_single].
      repeat setoid_rewrite <-Bind_assoc;
        repeat setoid_rewrite Bind_Ret_l;
        rewrite Bind_comm with (c2 := {0,1}^_).
      reflexivity.
    Qed.

    Lemma generate_single i idxs:
      forall {A} (f:_->Comp A),
        PositiveSet.In i idxs ->
        Comp_eq
          (t <-$ generate_randomness idxs;
             f (PositiveMap.find i t))
          (r <-$ { 0 , 1 }^ eta; f (Some (cast_rand eta r))).
    Proof.
      intros.
      apply PositiveSetProperties.Add_remove in H.
      rewrite add_generate_randomness
        by eauto using PositiveSetProperties.Dec.F.remove_1.

      (* TODO: this should work but doesn't:
         setoid_rewrite PositiveMapProperties.F.add_eq_o *)
      f_equiv; cbv [pointwise_relation]; intros.
      etransitivity. {
        apply Proper_Bind; [reflexivity|].
        cbv [pointwise_relation]; intros.
        rewrite PositiveMapProperties.F.add_eq_o by reflexivity.
        eapply reflexivity. }
      rewrite Bind_unused; reflexivity.
    Qed.

    Lemma Proper_Bind_generate_randomness {A: Set} idxs :
      Proper (
          (fun f g =>
             forall m,
               (forall i, PositiveMap.In i m <-> PositiveSet.In i idxs) ->
               Comp_eq (f m) (g m))
            ==> Comp_eq)
             (Bind (A:=A) (generate_randomness idxs)).
    Proof.
      cbv [Proper respectful generate_randomness].
      match goal with |- context [PositiveSet.fold ?f _] =>
                      set (F:=f) end.
      apply PositiveSetProperties.fold_rec; [|subst F; simpl];
        repeat match goal with
               | _ => progress intros
               | _ => setoid_rewrite Bind_Ret_l
               | _ => setoid_rewrite <-Bind_assoc
               | _ => rewrite PositiveMapProperties.F.empty_in_iff
               | H: forall m, _ -> Comp_eq (_ m) (_ m) |- _ => apply H; intros
               | H: PositiveSet.Empty _ |- context[PositiveSet.In ?x _] =>
                 specialize (H x)
               | H: forall _ _, _ -> Comp_eq (Bind _ _) (Bind _ _)
                                |- _ => apply H; intros
               | H: forall m, _ -> Comp_eq (_ m) (_ m)
                              |- _ => apply H; intros
               | _ => rewrite PositiveMapFacts.add_in_iff
               | H: PositiveSetProperties.Add _ _ _ |- context [PositiveSet.In ?x] =>
                 cbv [PositiveSetProperties.Add] in H; specialize (H x)
               | |- Comp_eq (Bind ?x _) (Bind ?x _) =>
                 apply Proper_Bind;[reflexivity|];
                   cbv [pointwise_relation]; intros
               | H: _ |- _ => rewrite H; tauto
               | _ => tauto
               end.
    Qed.

    Global Instance Proper_generate_randomness :
      Proper (PositiveSet.Equal ==> Comp_eq) generate_randomness.
    Proof.
      cbv [Proper respectful generate_randomness].
      intros.
      cbv [PositiveSet.Equal] in H.
      apply PositiveSetProperties.fold_equal;
        auto using generate_randomness_single_transpose; try exact _.
    Qed.

    Lemma generate_twice idxs1 :
      forall idxs2 {A} (f:_->Comp A),
        Proper (PositiveMap.Equal ==> Comp_eq) f ->
        Comp_eq
          (a <-$ generate_randomness idxs1;
             b <-$ generate_randomness idxs2;
             f (PositiveMapProperties.update b a))
          (a <-$ generate_randomness (PositiveSet.union idxs1 idxs2);
             f a).
    Proof.
      apply PositiveSetProperties.set_induction with (s:=idxs1).
      {
        intros.
        etransitivity. {
          do 2 (eapply Proper_Bind_generate_randomness; intros).
          rewrite update_empty_r; [eapply reflexivity|].
          apply empty_not_in; intros; cbv [PositiveSet.Empty] in *.
          repeat match goal with
                 | H: forall _, _ |- context[PositiveMap.In ?x] =>
                   specialize (H x) end; tauto. }
        rewrite Bind_unused.
        rewrite PositiveSetProperties.empty_union_1 by assumption.
        reflexivity. }
      { intros until 1. intro new_elt; intros.
        rewrite @add_generate_randomness with (s':=s') by eassumption.
        rewrite @add_generate_randomness with
            (s:=PositiveSet.union s (PositiveSet.remove new_elt idxs2))
            (s':=PositiveSet.union s' idxs2) (x:=new_elt); cycle 1.
        {
          cbv [PositiveSetProperties.Add]; intros.
          rewrite (union_remove s' idxs2 new_elt).
          eapply PositiveSetProperties.union_Add.
          assumption. }
        {
          rewrite !PositiveSet.union_spec, PositiveSet.remove_spec.
          assert (new_elt = new_elt) by reflexivity.
          tauto. }

        setoid_rewrite update_add.
        f_equiv; cbv [pointwise_relation]; intros.
        match goal with H: _ |- context [PositiveMap.add ?i ?x] =>
                        rewrite H with (f:=fun m => f (PositiveMap.add i x m)) end.
        rewrite <-union_remove; try reflexivity.
        cbv [Proper respectful]; intros;
          match goal with H: PositiveMap.Equal _ _ |- _ => rewrite H end;
          reflexivity. }
    Qed.
  End GenerateRandomness.

  Context (interp_func : forall {t1 t2} (f:(t1->t2)%etype) {eta}, interp_type t1 eta -> interp_type t2 eta).
  Context (interp_pair : forall {t1 t2 eta}, interp_type t1 eta -> interp_type t2 eta -> interp_type (t1 * t2) eta).
  Arguments interp_func {_ _} _ {_}.
  Arguments interp_pair {_ _ _}.

  Fixpoint interp_fixed {t} (e:expr t) (eta : nat)
           (adv: forall t1 t2, interp_type t1 eta -> interp_type t2 eta)
           (rands: PositiveMap.t (interp_type trand eta))
    : interp_type t eta :=
    match e with
    | # c => c eta
    | $ i => match PositiveMap.find i rands with Some r => r | _ => cast_rand eta (Bvector_exists _) end
    | !@inputs => adv _ _ (interp_fixed inputs eta adv rands)
    | f@inputs => interp_func f (interp_fixed inputs eta adv rands)
    | (a, b) => interp_pair (interp_fixed a eta adv rands) (interp_fixed b eta adv rands)
    end%expr.

  Definition interp {t} (e:expr t) (eta:nat) adv : Comp (interp_type t eta)
    := rands <-$ generate_randomness eta (randomness_indices e); ret (interp_fixed e eta adv rands).

  Global Instance Proper_interp_fixed {t} (e:expr t) eta adv :
    Proper (PositiveMap.Equal ==> Logic.eq) (interp_fixed e eta adv).
  Proof.
    cbv [Proper respectful]; induction e; intros; simpl; try reflexivity.
    { cbv [PositiveMap.Equal] in *. rewrite H. reflexivity. }
    { erewrite IHe; eauto. }
    { erewrite IHe; eauto. }
    { erewrite IHe1, IHe2; eauto. }
  Qed.

  Section Security.
    (* the adversary is split into three parts for no particular reason. It first decides how much randomness it will need, then interacts with the protocol (repeated calls to [adversary] with all messages up to now as input), and then tries to claim victory ([distinguisher]). There is no explicit sharing of state between these procedures, but all of them get the same random inputs in the security game. The handling of state is a major difference between FCF [OracleComp] and this framework *)
    Definition universal_security_game {t}
               (evil_rand_indices: forall eta:nat, PositiveSet.t)
               (adv:forall (eta:nat) (rands: PositiveMap.t (interp_type trand eta)) t1 t2, interp_type t1 eta -> interp_type t2 eta)
               (distinguisher: forall (eta:nat) (rands: PositiveMap.t (interp_type trand eta)), interp_type t eta -> Datatypes.bool)
               (eta:nat) (e:expr t) : Comp Datatypes.bool :=
      evil_rands <-$ generate_randomness eta (evil_rand_indices eta);
        out <-$ interp e eta (adv eta (evil_rands));
        ret (distinguisher eta evil_rands out).

    Definition indist {t:type} (a b:expr t) : Prop :=  forall adl adv dst,
        (* TODO: insert bounds on coputational complexity of [adv] and [dst] here *)
        let game eta e := universal_security_game adl adv dst eta e in
        negligible (fun eta => | Pr[game eta a] -  Pr[game eta b] | ).

    Global Instance Equivalence_indist {t} : Equivalence (@indist t).
    Proof.
      split; cbv [Reflexive Symmetric Transitive indist]; intros;
        [ setoid_rewrite ratDistance_same (* Reflexive *)
        | setoid_rewrite ratDistance_comm (* Symmetric *)
        | setoid_rewrite ratTriangleInequality ]; (* Transitive *)
        eauto using negligible_0, negligible_plus.
    Qed.

    Global Instance Proper_indist_func {t1 t2} f : Proper (@indist t1 ==> @indist t2) (expr_app f).
    Proof.
      cbv [Proper respectful indist universal_security_game interp]; intros.
      cbn [interp_fixed].

      specialize (H adl adv
                    (fun eta rands v => dst eta rands (interp_func f v))).
      cbn [id] in *.

      setoid_rewrite <-Bind_assoc; setoid_rewrite Bind_Ret_l.
      setoid_rewrite <-Bind_assoc in H; setoid_rewrite Bind_Ret_l in H.
      eapply H.
    Qed.
  End Security.

  Local Infix "≈" := indist (at level 70). (* \approx *)
  Local Notation "a ≉ b" := (~ (a ≈ b)) (at level 70). (* \napprox *)

  Lemma interp_const {t} (c : forall eta, interp_type t eta) eta adv : Comp_eq (interp #c eta adv) (ret (c eta)).
  Proof. cbv -[Comp_eq]; setoid_rewrite Bind_unused; reflexivity. Qed.

  Lemma interp_rand i eta a : Comp_eq (interp ($i) eta a) (genrand eta).
  Admitted.

  Context (vtrue vfalse : forall eta, interp_type tbool eta)
          (inspect_vbool : forall eta, interp_type tbool eta -> bool)
          (case_tbool : forall eta (b:interp_type tbool eta), b = if inspect_vbool eta b then vtrue eta else vfalse eta)
          (inspect_vtrue : forall eta, inspect_vbool eta (vtrue eta) = true)
          (inspect_vfalse : forall eta, inspect_vbool eta (vfalse eta) = false).
  Arguments inspect_vbool {eta}.

  Context (feqb : forall {t}, (t*t -> tbool)%etype).
  Arguments feqb {_}.
  Local Notation "a == b" := (feqb@(a, b))%expr : expr_scope.
  Arguments feqb {_}.
  Context (interp_feqb : forall t eta (v1 v2:interp_type t eta),
              inspect_vbool (interp_func feqb (interp_pair v1 v2))
              = eqb v1 v2).

  Context (fand : (tbool * tbool -> tbool)%etype)
          (interp_fand : forall eta v1 v2,
              inspect_vbool (interp_func fand (interp_pair v1 v2)) =
              andb (inspect_vbool v1) (inspect_vbool (eta:=eta) v2)).
  Local Notation "a /\ b" := (fand@(a, b))%expr : expr_scope.
  Context (f_or : (tbool * tbool -> tbool)%etype)
          (interp_f_or : forall eta v1 v2,
              inspect_vbool (interp_func f_or (interp_pair v1 v2)) =
              orb (inspect_vbool v1) (inspect_vbool (eta:=eta) v2)).
  Local Notation "a \/ b" := (f_or@(a, b))%expr : expr_scope.
  Context (fimpl : (tbool * tbool -> tbool)%etype)
          (interp_fimpl : forall eta v1 v2,
              inspect_vbool (interp_func fimpl (interp_pair v1 v2)) =
              implb (inspect_vbool v1) (inspect_vbool (eta:=eta) v2)).
  Local Notation "a -> b" := (fimpl@(a, b))%expr : expr_scope.
  Context (fnegb : (tbool -> tbool)%etype)
          (interp_fnegb : forall eta v,
              inspect_vbool (interp_func fnegb v) =
              negb (inspect_vbool (eta:=eta) v)).
  Local Notation "~ a" := (fnegb@a)%expr : expr_scope.
  Context (ite : forall t, (tbool * t * t -> t)%etype).
  Arguments ite {_}.
  Context (interp_ite :
             forall t eta b (v1 v2:interp_type t eta),
               interp_func ite (interp_pair (interp_pair b v1) v2) =
               if inspect_vbool b then v1 else v2).
  Arguments interp_ite {_ _}.
  Local Notation "'eif' b 'then' x 'else' y" :=
    (ite@(b,x,y))%expr
      (at level 200, b at level 1000, x at level 1000, y at level 1000,
       format "'[hv' 'eif'  b  '/' '[' 'then'  x  ']' '/' '[' 'else'  y ']' ']'")
    : expr_scope.

  Section TBool.
    Definition tbool_rect eta
               (P : interp_type tbool eta -> Type)
               (f : P (vfalse eta)) (t : P (vtrue eta))
               (b : interp_type tbool eta) : P b.
      rewrite case_tbool; destruct (inspect_vbool b); eauto.
    Defined.

    Lemma inspect_vbool_inj : forall eta (x y : interp_type tbool eta),
        inspect_vbool x = inspect_vbool y -> x = y.
    Proof.
      intros ? x; pattern x; eapply tbool_rect; clear x;
        intro y; pattern y; eapply tbool_rect; clear y;
          repeat rewrite inspect_vfalse; repeat rewrite inspect_vtrue;
            intros; congruence.
    Qed.
  End TBool.

  Section WHP.
    Definition whp (e:expr tbool) := e ≈ #vtrue.

    Global Instance Proper_whp_indist : Proper (indist ==> iff) whp.
    Proof.
      intros ? ? H.
      cbv [whp].
      rewrite H.
      reflexivity.
    Qed.

    Definition whp_game evil_rand_indices adversary eta e : Comp Datatypes.bool :=
      evil_rands <-$ generate_randomness eta (evil_rand_indices eta);
        out <-$ interp e eta (adversary eta (evil_rands));
        ret negb (inspect_vbool out).

    Definition whp_simple (e : expr tbool) :=
      forall adl adv,
        (* TODO: insert bounds on coputational complexity of [adv] and [dst] here *)
        negligible (fun eta : nat => Pr[whp_game adl adv eta e]).
  End WHP.

  Definition always (e : expr tbool) :=
    forall eta adv rands, interp_fixed e eta adv rands = vtrue eta.

  Lemma always_impl a b : always (a -> b) -> (always a -> always b).
  Proof.
    intros Hab Ha eta adv rands; specialize (Hab eta adv rands); specialize (Ha eta adv rands).
    cbv [always] in *.
    cbn [interp_fixed] in *.
    rewrite Ha in Hab; clear Ha.
    rewrite <- Hab; clear Hab.
    apply inspect_vbool_inj.
    rewrite interp_fimpl, inspect_vtrue; reflexivity.
  Qed.

  Lemma eqb_tbool eta (v1 v2 : interp_type tbool eta) :
    (v1 ?= v2) = (inspect_vbool v1 ?= inspect_vbool v2).
  Proof.
    destruct (v1 ?= v2) eqn:HL;
      destruct (inspect_vbool v1 ?= inspect_vbool v2) eqn:HR;
      try congruence; [|].
    { rewrite eqb_false_iff in HR.
      rewrite eqb_leibniz in HL; subst; congruence. }
    { rewrite eqb_false_iff in HL.
      rewrite eqb_leibniz in HR; subst.
      apply inspect_vbool_inj in HR; congruence. }
  Qed.

  Lemma commute_inspect_if {eta} (b : bool) (v1 v2 : interp_type tbool eta) :
    inspect_vbool (if b then v1 else v2) =
    if b then inspect_vbool v1 else inspect_vbool v2.
  Proof. destruct b; reflexivity. Qed.

  Create HintDb push_interp discriminated.
  Hint Rewrite
       @interp_fnegb
       @interp_fand
       @interp_f_or
       @interp_fimpl
       @interp_feqb
       @eqb_tbool
       @interp_ite
       @commute_inspect_if
       @inspect_vtrue
       @inspect_vfalse
       : push_interp.

  Section PushIsTrue.
    Lemma is_true_implb a b :
      is_true (implb a b) <-> (is_true a -> is_true b).
      destruct a; destruct b; subst; cbv; eauto.
    Qed.

    Lemma is_true_eqb {T} {e : EqDec T} (a b : T) :
      is_true (a ?= b) <-> a = b.
      destruct e as [? e].
      cbv.
      rewrite e.
      eauto.
    Qed.

    Lemma is_true_andb a b : is_true (andb a b) <-> (is_true a /\ is_true b).
      destruct a; destruct b; intuition congruence.
    Qed.

    Lemma is_true_orb a b : is_true (orb a b) <-> (is_true a \/ is_true b).
      destruct a; destruct b; intuition congruence.
    Qed.

    Lemma is_true_negb a : is_true (negb a) <-> ~is_true a.
      destruct a; cbv; intuition congruence.
    Qed.
  End PushIsTrue.

  Create HintDb push_is_true discriminated.
  Hint Rewrite
       is_true_implb
       @is_true_eqb (* TODO COQBUG does removing this @ cause an anomaly? *)
       is_true_andb
       is_true_orb
       is_true_negb : push_is_true.

  Ltac goal_always_to_inspect_interp_fixed_true :=
    lazymatch goal with
    | |- always _ =>
      progress cbv [always];
      let eta := fresh "eta" in
      let adv := fresh "adv" in
      let rands := fresh "rands" in
      intros eta adv rands;
      apply inspect_vbool_inj;
      rewrite inspect_vtrue
    end.

  Ltac remember_inspect_vbool :=
    repeat match goal with
           | [ |- context[inspect_vbool (interp_fixed ?e _ _ _)] ] =>
             is_var e;
             let v := fresh e in
             rename e into v;
             remember (inspect_vbool (interp_fixed v _ _ _)) as e
           end.

  Ltac goal_unpack_always :=
    goal_always_to_inspect_interp_fixed_true;
    cbn [interp_fixed];
    autorewrite with push_interp;
    remember_inspect_vbool.


  Ltac merge_always_step :=
    match goal with
    | |- always _ -> _ => intros ?
    | H : always _ |- always _ => revert H; apply always_impl
    end.
  Ltac merge_always := repeat merge_always_step.

  Ltac unpack_always := merge_always; goal_unpack_always.

  Section WHPLemmas.
    Lemma pr_false : Pr[ret false] = 0.
    Proof.
      cbn; destruct (EqDec_dec bool_EqDec false true); congruence.
    Qed.

    Lemma whp_game_wins_indist_game :
      forall adl adv e,
      exists dst,
      forall eta,
        let game :=
            universal_security_game adl adv dst eta in
        Pr[whp_game adl adv eta e] <=
    |Pr[game e] - Pr[game (expr_const vtrue)]|.
    Proof.
      intros.
      exists (fun _ _ out => negb (inspect_vbool out)).
      intro.
      cbv [universal_security_game whp_game interp].
      cbn [interp_fixed].
      repeat rewrite Bind_unused.
      repeat rewrite Bind_Ret_l.
      rewrite inspect_vtrue.
      cbv [negb].
      rewrite pr_false.
      rewrite ratDistance_comm.
      rewrite ratDistance_from_0.
      auto with rat.
    Qed.

    Lemma whp_to_whp_simple :
      forall e, whp e -> whp_simple e.
    Proof.
      cbv [whp_simple whp indist].
      intros e H adl adv.
      destruct (whp_game_wins_indist_game adl adv e) as [dst ?].
      eapply negligible_le; try eapply (H adl adv dst).
      auto.
    Qed.

    Lemma pr_weaken :
      forall T (X : Comp T) Y1 Y2,
        (forall x, In x (getSupport X) -> Bool.leb (Y1 x) (Y2 x)) ->
        Pr[x <-$ X; ret Y1 x] <= Pr[x <-$ X; ret Y2 x].
    Proof.
      intros.
      cbv [evalDist].
      eapply sumList_le.
      intros.
      eapply ratMult_leRat_compat; eauto with rat.
      repeat
        match goal with
        | [ |- context[EqDec_dec bool_EqDec (?f ?b) true] ] =>
          destruct (EqDec_dec bool_EqDec (f b) true); auto with rat
        | [ H : context[In _ _ -> _], H1 : In ?b _, e : ?f a = true |- _ ] =>
          specialize (H b H1);
            rewrite e in H; simpl in H
        end.
      exfalso; auto.
    Qed.

    Lemma pr_dist_bound_helper :
      forall {WT : Set} T (eT : EqDec T)
             (XY : WT -> Comp (T * T)) (W : Comp WT) Z,
        Pr[w <-$ W; xy <-$ XY w; ret Z w (fst xy)] <=
        Pr[w <-$ W; xy <-$ XY w; ret Z w (snd xy)] +
        Pr[w <-$ W; xy <-$ XY w; ret negb (fst xy ?= snd xy)].
    Proof.
      intros.
      cbn [evalDist].
      rewrite <- sumList_sum.
      eapply sumList_le.
      intros.
      rewrite <- ratMult_distrib.
      eapply ratMult_leRat_compat; eauto with rat.
      rewrite <- sumList_sum.
      eapply sumList_le.
      intros [x y] _.
      rewrite <- ratMult_distrib.
      eapply ratMult_leRat_compat; eauto with rat.
      cbv [fst snd].
      repeat match goal with
             | [ |- context[EqDec_dec ?X ?Y ?Z] ] => destruct (EqDec_dec X Y Z)
             end;
        pose proof (eqb_leibniz x y);
        destruct (x ?= y); intuition; subst; try congruence.
    Qed.

    Lemma sum_dist :
      forall a b c,
        a <= b + c ->
        b <= a + c ->
    |a - b| <= c.
    Proof.
      intros.
      eapply ratDistance_leRat_both;
        rewrite <- ratSubtract_ratAdd_inverse with (r2 := c);
        eauto using ratSubtract_leRat_l.
    Qed.

    Definition swapcomp {T1 T2 : Set} {e1 : EqDec T1} {e2 : EqDec T2}
               (XY : Comp (T1 * T2)) : Comp (T2 * T1) :=
      xy <-$ XY; ret (snd xy, fst xy).

    Lemma swapcomp_compat :
      forall {T1 T2 T3 : Set} {e1 : EqDec T1} {e2 : EqDec T2}
             (XY : Comp (T1 * T2)) (f : T1 -> T2 -> Comp T3),
        Comp_eq
          (xy <-$ XY; f (fst xy) (snd xy))
          (yx <-$ swapcomp XY; f (snd yx) (fst yx)).
    Proof.
      intros.
      cbv [swapcomp].
      rewrite <- Bind_assoc.
      setoid_rewrite Bind_Ret_l.
      cbn [fst snd].
      reflexivity.
    Qed.

    Lemma pr_dist_bound :
      forall WT (W : Comp WT) T (eT : EqDec T) (XY : WT -> Comp (T * T)) Z,
    |Pr[w <-$ W; xy <-$ XY w; ret Z w (fst xy)] -
     Pr[w <-$ W; xy <-$ XY w; ret Z w (snd xy)]|
    <=
    Pr[w <-$ W; xy <-$ XY w; ret negb (fst xy ?= snd xy)].
    Proof.
      intros.
      eapply sum_dist.
      - eapply pr_dist_bound_helper.
      - assert (forall w,
                   Comp_eq
                     (xy <-$ XY w; ret Z w (snd xy))
                     (yx <-$ swapcomp (XY w); ret Z w (fst yx))) as E.
        {
          intros.
          eapply swapcomp_compat with (f := fun _ y => ret Z w y).
        }
        setoid_rewrite E; clear E.

        assert (forall w,
                   Comp_eq
                     (xy <-$ XY w; ret Z w (fst xy))
                     (yx <-$ swapcomp (XY w); ret Z w (snd yx))) as E.
        {
          intros.
          eapply swapcomp_compat with (f := fun x _ => ret Z w x).
        }
        setoid_rewrite E; clear E.


        assert (forall w,
                   Comp_eq
                     (xy <-$ XY w; ret negb (fst xy ?= snd xy))
                     (yx <-$ swapcomp (XY w); ret negb (fst yx ?= snd yx)))
          as E.
        {
          intros.
          setoid_rewrite eqb_symm at 2.
          eapply swapcomp_compat with (f := fun x y => ret negb (x ?= y)).
        }
        setoid_rewrite E; clear E.
        eapply pr_dist_bound_helper.
    Qed.

    Lemma Bind_assoc_in_Bind :
      forall T1 T2 T3 T4
             (a : Comp T1) (b : T1 -> Comp T2)
             (c : T1 -> T2 -> Comp T3) (d : T1 -> T3 -> Comp T4),
        Comp_eq
          (x <-$ a; y <-$ (z <-$ b x; c x z); d x y)
          (x <-$ a; z <-$ b x; y <-$ c x z; d x y).
      intros.
      setoid_rewrite <- Bind_assoc.
      reflexivity.
    Qed.

    Lemma Bind_beta_fst :
      forall {T1 T2 T3} {e1 : EqDec T1} {e2 : EqDec T2}
             (X : Comp T1) (Y : Comp T2) (f : T1 -> Comp T3),
        Comp_eq (x <-$ X; f x)
                (xy <-$ (x <-$ X; y <-$ Y; ret (x, y)); f (fst xy)).
    Proof.
      intros.
      repeat setoid_rewrite <- Bind_assoc.
      setoid_rewrite Bind_Ret_l.
      cbv [fst snd].
      setoid_rewrite Bind_unused.
      reflexivity.
    Qed.

    Lemma Bind_beta_snd :
      forall {T1 T2 T3} {e1 : EqDec T1} {e2 : EqDec T2}
             (X : Comp T1) (Y : Comp T2) (g : T2 -> Comp T3),
        Comp_eq (y <-$ Y; g y)
                (xy <-$ (x <-$ X; y <-$ Y; ret (x, y)); g (snd xy)).
    Proof.
      intros.
      repeat setoid_rewrite <- Bind_assoc.
      setoid_rewrite Bind_Ret_l.
      cbv [fst snd].
      setoid_rewrite Bind_unused.
      reflexivity.
    Qed.

    Lemma vfalse_eq_vbool_false eta :
      (vfalse eta ?= vtrue eta) = false.
    Proof.
      eapply eqb_false_iff.
      intros H;
        apply f_equal with (f := inspect_vbool) in H;
        revert H.
      rewrite inspect_vfalse, inspect_vtrue.
      congruence.
    Qed.

    Lemma inspect_vbool_equality :
      forall eta b, inspect_vbool b = (b ?= vtrue eta).
    Proof.
      intros.
      eapply tbool_rect with
          (P := fun b => inspect_vbool b = (b ?= vtrue eta));
        repeat match goal with
               | [ |- context[inspect_vbool]] =>
                 rewrite inspect_vfalse || rewrite inspect_vtrue
               | [ |- context[_ ?= _]] =>
                 rewrite vfalse_eq_vbool_false || rewrite eqb_refl
               end; reflexivity.
    Qed.

    Lemma indist_game_wins_whp_game :
      forall adl adv dst eta e,
        let game :=
            universal_security_game adl adv dst eta in
    |Pr[game e] - Pr[game (expr_const vtrue)]|
    <= Pr[whp_game adl adv eta e].
    Proof.
      intros adl adv dst eta e.
      cbv [universal_security_game whp_game interp].
      cbn [interp_fixed].
      setoid_rewrite Bind_unused.

      set (ER := generate_randomness eta (adl eta)).
      set (XR := (fun evil_rands =>
                    rands <-$ generate_randomness eta (randomness_indices e);
                    ret interp_fixed e eta (adv eta evil_rands) rands)).
      set (Y' := ret vtrue eta).
      set (XY :=
             (fun evil_rands =>
                x <-$ XR evil_rands;
                y <-$ (ret vtrue eta);
                ret (x, y))).
      set (Z := dst eta).

      enough (|Pr [er <-$ ER;
                   x <-$ XR er;
                   ret Z er x] -
               Pr [er <-$ ER; y <-$ Y'; ret Z er y]|
              <=
              Pr [er <-$ ER;
                  x <-$ XR er;
                  ret negb (inspect_vbool x)]) by (intuition idtac).

      assert (forall er,
                 Comp_eq
                   (x <-$ XR er;
                    ret Z er x)
                   (xy <-$ XY er;
                    ret Z er (fst xy))) as E.
      {
        intro er.
        eapply Bind_beta_fst with (X := XR er) (Y := Y').
      }
      setoid_rewrite E; clear E.

      assert (forall er,
                 Comp_eq
                   (y <-$ Y';
                    ret Z er y)
                   (xy <-$ XY er;
                    ret Z er (snd xy))) as E.
      {
        intro er.
        eapply Bind_beta_snd with (X := XR er) (Y := Y').
      }
      setoid_rewrite E; clear E.

      assert (forall er,
                 Comp_eq
                   (x <-$ XR er; ret negb (inspect_vbool x))
                   (xy <-$ XY er; ret negb (fst xy ?= snd xy))) as E.
      {
        intro er.
        subst XR XY; cbv beta.
        repeat rewrite <- Bind_assoc.
        setoid_rewrite <- Bind_assoc.
        repeat setoid_rewrite Bind_Ret_l.
        cbv [fst snd].

        assert (forall x,
                   Comp_eq
                     (ret negb (inspect_vbool
                                  (interp_fixed e eta (adv eta er) x)))
                     (ret negb (interp_fixed e eta (adv eta er) x
                                             ?= vtrue eta))) as E1.
        {
          intro.
          rewrite inspect_vbool_equality.
          reflexivity.
        }
        setoid_rewrite E1; clear E1.
        reflexivity.
      }
      setoid_rewrite E; clear E.

      eapply pr_dist_bound.
    Qed.

    Lemma whp_simple_to_whp :
      forall e, whp_simple e -> whp e.
    Proof.
      cbv [whp_simple whp indist].
      intros.
      eapply negligible_le.
      intros.
      eapply indist_game_wins_whp_game.
      auto.
    Qed.

    Lemma whp_whp_simple :
      forall e, whp e <-> whp_simple e.
    Proof.
      intuition eauto using whp_simple_to_whp, whp_to_whp_simple.
    Qed.

    Lemma Bind_assoc_2 :
      forall {A B C : Set} {e : EqDec (A * B)}
             (cA : Comp A) (f : A -> Comp B) (g : A -> B -> Comp C),
        Comp_eq (x <-$ cA; y <-$ f x; g x y)
                (xy <-$ (x <-$ cA; y <-$ f x; ret (x, y));
                   g (fst xy) (snd xy)).
    Proof.
      intros.
      repeat setoid_rewrite <- Bind_assoc.
      setoid_rewrite Bind_Ret_l.
      reflexivity.
    Qed.

    Lemma find_trivial_filter :
      forall {T} (m : PositiveMap.t T)
             (s : PositiveSet.t)
             (x : positive),
        PositiveSet.In x s ->
        PositiveMap.find x m =
        PositiveMap.find x
                         (PositiveMapProperties.filter
                            (fun k _ => PositiveSet.mem k s) m).
    Proof.
      intros.
      assert (forall e,
                 PositiveMap.MapsTo x e m <->
                 PositiveMap.MapsTo x e
                                    (PositiveMapProperties.filter
                                       (fun k _ => PositiveSet.mem k s) m))
        as M.
      - intros.
        split.
        + intros.
          eapply PositiveMapProperties.filter_iff; intuition.
        + intros MF.
          eapply PositiveMapProperties.filter_iff in MF; intuition.
      - pose proof (PositiveMapProperties.F.find_mapsto_iff m x) as F.
        remember (PositiveMap.find x m) as o.
        destruct o as [t|].
        + assert (PositiveMap.MapsTo x t m).
          {
            eapply F; eauto.
          }
          assert (PositiveMap.MapsTo
                    x t
                    (PositiveMapProperties.filter
                       (fun k _ => PositiveSet.mem k s) m)).
          {
            eapply M.
            eauto.
          }
          symmetry.
          eapply PositiveMapProperties.filter_iff; intuition.
        + remember (PositiveMap.find
                      x
                      (PositiveMapProperties.filter
                         (fun k _ => PositiveSet.mem k s) m)) as p.
          destruct p; eauto.
          exfalso.
          symmetry in Heqp.
          rewrite <- PositiveMapProperties.F.find_mapsto_iff in Heqp.
          rewrite <- M in Heqp.
          rewrite F in Heqp.
          congruence.
    Qed.

    Lemma interp_less_randomness :
      forall {t} eta adv (e : expr t)
             (r : PositiveMap.t (interp_type trand eta))
             (s : PositiveSet.t),
        PositiveSet.Subset (randomness_indices e) s ->
        interp_fixed e eta adv r =
        interp_fixed e eta adv
                     (PositiveMapProperties.filter
                        (fun k _ => PositiveSet.mem k s)
                        r).
    Proof.
      intros ? ? ? e ?; induction e.
      - reflexivity.
      - cbn [interp_fixed randomness_indices] in *.
        intros s S.
        assert (PositiveMap.find idx r =
                PositiveMap.find idx
                                 (PositiveMapProperties.filter
                                    (fun k _  =>
                                       PositiveSet.mem k s) r)) as E.
        {
          eapply find_trivial_filter.
          eapply S.
          eapply PositiveSetProperties.Dec.F.singleton_iff.
          eauto.
        }
        rewrite E; eauto.
      - cbn [interp_fixed randomness_indices] in *.
        intros.
        erewrite IHe; eauto.
      - cbn [interp_fixed randomness_indices] in *.
        intros.
        erewrite IHe; eauto.
      - cbn [interp_fixed randomness_indices].
        intros.
        edestruct subset_union; eauto.
        erewrite IHe1; eauto.
        erewrite IHe2; eauto.
    Qed.

    Lemma generate_randomness_single_support :
      forall eta m i r,
        In m (getSupport (generate_randomness_single eta i r)) ->
        forall x,
          PositiveMap.In x m -> x = i \/ (exists m',
                                             In m' (getSupport r) /\
                                             PositiveMap.In x m').
    Proof.
      intros ? ? ? ? I ? ? .
      cbn [generate_randomness_single getSupport] in I.
      repeat
        match goal with
        | [ H : In _ (getUnique _ _) |- _ ] =>
          eapply in_getUnique_if in H
        | [ H : In _ (flatten _) |- _ ] =>
          eapply in_flatten in H; destruct H as [? [? ?]]
        | [ H : In _ (map _ _) |- _ ] =>
          eapply in_map_iff in H; destruct H as [? [? ?]]; subst
        | [ H : In m (_ :: nil) |- _ ] => destruct H as [? | []]; subst
        | [ H : PositiveMap.In ?y (PositiveMap.add ?x ?e ?m) |- _ ] =>
          let H' := fresh in
          destruct (@PositiveMapProperties.F.add_in_iff _ m x y e) as [H' _];
            specialize (H' H); clear H; destruct H'; eauto
        end.
    Qed.

    Lemma generate_randomness_support :
      forall eta s m,
        In m (getSupport (generate_randomness eta s)) ->
        forall x,
          PositiveMap.In x m -> PositiveSet.In x s.
      cbv [generate_randomness] in *.
      intros eta s.
      eapply PositiveSetProperties.fold_rec with
          (A := Comp (PositiveMap.tree (interp_type trand eta)))
          (P := fun s r =>
                  forall m,
                    In m (getSupport r) ->
                    forall x,
                      PositiveMap.In x (m : PositiveMap.tree _) -> PositiveSet.In x s)
          (f := generate_randomness_single eta)
          (i := ret (PositiveMap.empty (interp_type trand eta) : PositiveMap.tree _)).
      - intros.
        exfalso.
        cbv [In getSupport] in *.
        intuition.
        subst.
        eapply PositiveMapProperties.F.empty_in_iff; eauto.
      - intros.
        clear H0.
        edestruct generate_randomness_single_support as [|[? []]]; eauto.
        + subst.
          eapply H1; eauto.
        + assert (PositiveSet.In x0 s') by eauto.
          eapply H1; eauto.
    Qed.

    Lemma restrict_irrelevant :
      forall {T} (m : PositiveMap.t T) (f : PositiveMap.key -> T -> bool),
        (forall x y, PositiveMap.MapsTo x y m -> f x y = true) ->
        PositiveMap.Equal m (PositiveMapProperties.filter f m).
      intros.
      eapply PositiveMapProperties.F.Equal_mapsto_iff.
      intros.
      rewrite PositiveMapProperties.filter_iff; intuition.
    Qed.

    Lemma mapsto_in :
      forall {T} (m : PositiveMap.t T) x y,
        PositiveMap.MapsTo x y m -> PositiveMap.In x m.
      intros.
      cbv [PositiveMap.MapsTo] in *.
      eapply PositiveMapFacts.in_find_iff.
      congruence.
    Qed.

    Lemma generate_empty :
      forall eta s,
        PositiveSet.Empty s ->
        Comp_eq (generate_randomness eta s)
                (ret (PositiveMap.empty (interp_type trand eta) : PositiveMap.tree _)).
    Proof.
      intros; eapply PositiveSetProperties.fold_1; intuition.
    Qed.

    (* TODO Need a canonical map *)
    Axiom positive_map_equal_eq : forall {T} (m m' : PositiveMap.t T),
        PositiveMap.Equal m m' -> m = m'.

    Lemma filter_empty :
      forall {T} f,
        PositiveMapProperties.filter f (PositiveMap.empty T) =
        PositiveMap.empty T.
    Proof.
      intros T f.
      eapply positive_map_equal_eq.
      eapply PositiveMapProperties.F.Equal_mapsto_iff.
      intros k e.
      rewrite PositiveMapProperties.filter_iff; intuition.
      exfalso; eapply PositiveMapProperties.F.empty_mapsto_iff; eauto.
    Qed.

    Lemma filter_add :
      forall {T} (m : PositiveMap.t T) f x y,
        PositiveMapProperties.filter f (PositiveMap.add x y m) =
        let fm := PositiveMapProperties.filter f m in
        match f x y with
        | true => PositiveMap.add x y fm
        | false => PositiveMap.remove x fm
        end.
    Proof.
      intros ? ? f x y.
      remember (f x y) as b.
      destruct b;
        eapply positive_map_equal_eq;
        eapply PositiveMapProperties.F.Equal_mapsto_iff; intros;
          repeat rewrite PositiveMapProperties.filter_iff;
          repeat rewrite PositiveMapProperties.F.add_mapsto_iff;
          repeat rewrite PositiveMapProperties.F.remove_mapsto_iff;
          repeat rewrite PositiveMapProperties.filter_iff;
          intuition; congruence.
    Qed.

    Lemma remove_notin : forall {T} x (s : PositiveMap.t T),
        ~PositiveMap.In x s ->
        PositiveMap.remove x s = s.
    Proof.
      intros.
      eapply positive_map_equal_eq.
      eapply PositiveMapProperties.F.Equal_mapsto_iff; intros.
      rewrite PositiveMapProperties.F.remove_mapsto_iff.
      intuition.
      subst; eauto using mapsto_in.
    Qed.

    Lemma remove_randomness eta x s :
      ~PositiveSet.In x s ->
      Comp_eq (generate_randomness eta s)
              (r <-$ generate_randomness eta s;
                 ret (PositiveMap.remove x r : PositiveMap.tree _)).
      intros.
      rewrite <- Bind_Ret_r with (cA := generate_randomness eta s) at 1.
      cbv [Comp_eq image_relation pointwise_relation].
      cbn [evalDist].
      intros.
      eapply sumList_body_eq.
      intros r I.
      assert (PositiveMap.remove x r = r) as E.
      {
        eapply remove_notin; eauto.
        intro.
        eauto using generate_randomness_support.
      }
      rewrite E; clear E.

      reflexivity.
    Qed.

    Lemma restrict_randomness :
      forall eta s mask,
        (Comp_eq (generate_randomness eta (PositiveSet.inter s mask))
                 (r <-$ (generate_randomness eta s);
                    ret (PositiveMapProperties.filter
                        (fun k _ =>
                           PositiveSet.mem k mask) r : PositiveMap.tree _))).
    Proof.
      intros eta s.
      pattern s.
      eapply PositiveSetProperties.set_induction; clear s.
      - intros.
        repeat rewrite generate_empty;
          eauto using PositiveSetProperties.empty_inter_1.
        rewrite Bind_Ret_l.
        rewrite filter_empty.
        reflexivity.
      - intros s s' IHs x nI A mask.
        rewrite add_generate_randomness; eauto.
        setoid_rewrite filter_add.

        assert (forall a,
                   Comp_eq
                     (r <-$ generate_randomness eta s;
                      ret (let fm :=
                               PositiveMapProperties.filter
                                 (fun k _ => PositiveSet.mem k mask) r in
                           if PositiveSet.mem x mask
                           then PositiveMap.add x (cast_rand eta a) fm : PositiveMap.tree _
                           else PositiveMap.remove x fm))
                     (fm <-$ (r <-$ generate_randomness eta s;
                              ret (PositiveMapProperties.filter
                                  (fun k _ => PositiveSet.mem k mask) r : PositiveMap.tree _));
                      ret if PositiveSet.mem x mask
                          then (PositiveMap.add x (cast_rand eta a) fm : PositiveMap.tree _)
                          else PositiveMap.remove x fm)) as E.
        {
          intros.
          rewrite <- Bind_assoc.
          setoid_rewrite Bind_Ret_l.
          reflexivity.
        }
        setoid_rewrite E; clear E.
        setoid_rewrite <- IHs.
        remember (PositiveSet.mem x mask) as b.
        destruct b.
        + rewrite <- Bind_Ret_r with
              (cA := generate_randomness eta (PositiveSet.inter s' mask)).
          eapply add_generate_randomness;
            eauto using PositiveSetProperties.Dec.F.inter_1.
          eapply PositiveSetProperties.inter_Add; eauto.
          eapply PositiveSetProperties.Dec.F.mem_iff; eauto.
        + rewrite Bind_unused.
          rewrite <- remove_randomness.
          * rewrite PositiveSetProperties.inter_Add_2 with
                (s := s) (s' := s') (s'' := mask) (x := x); eauto.
            -- reflexivity.
            -- eapply PositiveSetProperties.Dec.F.not_mem_iff; congruence.
          * eauto using PositiveSetProperties.Dec.F.inter_1.
    Qed.

    Corollary restrict_randomness_subset :
      forall eta s s',
        PositiveSet.Subset s s' ->
        (Comp_eq (generate_randomness eta s)
                 (r <-$ (generate_randomness eta s');
                    ret (PositiveMapProperties.filter
                        (fun k _ =>
                           PositiveSet.mem k s) r : PositiveMap.tree _))).
    Proof.
      intros.
      rewrite <- PositiveSetProperties.inter_subset_equal with
          (s := s) (s' := s'); eauto.
      rewrite PositiveSetProperties.inter_sym.
      eapply restrict_randomness.
    Qed.

    Lemma generate_more_randomness :
      forall {t} eta adv (e : expr t) (s : PositiveSet.t),
        PositiveSet.Subset (randomness_indices e) s ->
        Comp_eq (r <-$ generate_randomness eta (randomness_indices e);
                   ret interp_fixed e eta adv r)
                (r <-$ generate_randomness eta s;
                   ret interp_fixed e eta adv r).
      intros.
      assert (forall r,
                 Comp_eq
                   (ret interp_fixed e eta adv r)
                   (ret interp_fixed e eta adv
                        (PositiveMapProperties.filter
                           (fun k _ =>
                              PositiveSet.mem k (randomness_indices e)) r)))
        as E.
      {
        intro r.
        erewrite interp_less_randomness.
        - reflexivity.
        - reflexivity.
      }
      setoid_rewrite E at 2; clear E.

      setoid_rewrite <- Bind_Ret_l with
          (f := fun r => ret interp_fixed e eta adv (r : PositiveMap.tree _)) at 2.

      rewrite Bind_assoc.

      rewrite <- restrict_randomness_subset; eauto.
      reflexivity.
    Qed.

    Lemma leb_negb : forall b1 b2,
        Bool.leb b1 b2 ->
        Bool.leb (negb b2) (negb b1).
    Proof.
      destruct b1; destruct b2; intuition.
    Qed.

    Lemma weak_whp_impl_dist_always a b : always (a -> b) -> (whp a -> whp b)%core.
    Proof.
      repeat rewrite whp_whp_simple.
      cbv [whp_simple whp_game always interp].
      intros Himpl A adl adv.
      cbn [interp_fixed] in Himpl.
      assert (forall eta adv rands,
                 inspect_vbool
                   (interp_func fimpl
                                (interp_pair (interp_fixed a eta adv rands)
                                             (interp_fixed b eta adv rands))) =
                 inspect_vbool (vtrue eta)) as Himpl'.
      {
        intros; erewrite Himpl; reflexivity.
      }
      clear Himpl.
      setoid_rewrite inspect_vtrue in Himpl'.
      setoid_rewrite interp_fimpl in Himpl'.

      eapply negligible_le; try eapply (A adl adv).
      cbv beta.
      intro eta.

      set (u := PositiveSet.union (randomness_indices a)
                                  (randomness_indices b)).
      assert (forall adv,
                 Comp_eq
                   (rands <-$ generate_randomness eta (randomness_indices a);
                    ret interp_fixed a eta adv rands)
                   (rands <-$ generate_randomness eta u;
                    ret interp_fixed a eta adv rands)) as E.
      {
        intro.
        apply generate_more_randomness.
        apply PositiveSetProperties.union_subset_1.
      }
      setoid_rewrite E; clear E.
      assert (forall adv,
                 Comp_eq
                   (rands <-$ generate_randomness eta (randomness_indices b);
                    ret interp_fixed b eta adv rands)
                   (rands <-$ generate_randomness eta u;
                    ret interp_fixed b eta adv rands)) as E.
      {
        intro.
        apply generate_more_randomness.
        apply PositiveSetProperties.union_subset_2.
      }
      setoid_rewrite E; clear E.

      rewrite Bind_assoc_in_Bind.
      setoid_rewrite Bind_Ret_l.
      rewrite Bind_assoc_in_Bind.
      setoid_rewrite Bind_Ret_l.

      rewrite Bind_assoc_2 with
          (g := (fun e r =>
                   ret negb (inspect_vbool
                               (interp_fixed b eta (adv eta e) (r : PositiveMap.tree _))))).
      rewrite Bind_assoc_2 with
          (g := (fun e r =>
                   ret negb (inspect_vbool
                               (interp_fixed a eta (adv eta e) (r : PositiveMap.tree _))))).

      eapply pr_weaken.
      intros x _.
      specialize (Himpl' eta (adv eta (fst x)) (snd x)).
      eapply leb_negb.
      eapply leb_implb.
      eauto.
    Qed.

    Corollary whp_or_inl a b : whp a -> whp (a \/ b).
    Proof.
      eapply weak_whp_impl_dist_always; goal_unpack_always; btauto.
    Qed.

    Corollary whp_or_inr a b : whp b -> whp (a \/ b).
    Proof.
      eapply weak_whp_impl_dist_always; goal_unpack_always; btauto.
    Qed.

    Lemma whp_and a b : whp a /\ whp b -> whp (a /\ b).
    Proof.
      rewrite 3 whp_whp_simple.
      cbv [whp_simple whp_game interp].
      setoid_rewrite <-Bind_assoc.
      setoid_rewrite Bind_Ret_l.
      intros [A B].
      intros adl adv.
      setoid_rewrite interp_fand.
      fold (@interp_fixed tbool).
      eapply negligible_le with
          (f1 :=
             (fun eta =>
                Pr [evil_rands <-$ generate_randomness eta (adl eta);
                    x <-$
                      generate_randomness eta
                      (randomness_indices (a /\ b));
                    ret negb
                        (inspect_vbool
                           (interp_fixed a eta (adv eta evil_rands) x))]
                +
                Pr [evil_rands <-$ generate_randomness eta (adl eta);
                    x <-$
                      generate_randomness eta
                      (randomness_indices (a /\ b));
                    ret negb
                        (inspect_vbool
                           (interp_fixed b eta (adv eta evil_rands) x))])).
      - intro eta.
        set (E := generate_randomness eta (adl eta)).
        set (R := generate_randomness eta
                                      (randomness_indices
                                         (a /\ b))).
        set (I := fun e er r =>
                    inspect_vbool (interp_fixed e eta (adv eta er) r)).

        assert
          (Comp_eq
             (er <-$ E;
              r <-$ R;
              ret negb
                  (I a er r && I b er r))
             (xy <-$ (er <-$ E;
                      r <-$ R;
                      ret (I a er r, I b er r));
              ret negb (fst xy && snd xy))) as E0.
        {
          repeat setoid_rewrite <- Bind_assoc.
          setoid_rewrite Bind_Ret_l.
          cbv [fst snd].
          reflexivity.
        }
        cbv [I] in E0; rewrite E0; clear E0.

        setoid_rewrite negb_andb.

        assert (Comp_eq
                  (er <-$ E;
                   r <-$ R;
                   ret negb (I a er r))
                  (xy <-$ (er <-$ E;
                           r <-$ R;
                           ret (I a er r, I b er r));
                   ret negb (fst xy))) as E0.
        {
          repeat setoid_rewrite <- Bind_assoc.
          setoid_rewrite Bind_Ret_l.
          cbv [fst snd].
          reflexivity.
        }
        cbv [I] in E0; rewrite E0; clear E0.

        assert (Comp_eq
                  (er <-$ E;
                   r <-$ R;
                   ret negb (I b er r))
                  (xy <-$ (er <-$ E;
                           r <-$ R;
                           ret (I a er r, I b er r));
                   ret negb (snd xy))) as E0.
        {
          repeat setoid_rewrite <- Bind_assoc.
          setoid_rewrite Bind_Ret_l.
          cbv [fst snd].
          reflexivity.
        }
        cbv [I] in E0; rewrite E0; clear E0.

        eapply evalDist_orb_le.
      - cbn [randomness_indices].
        set (u := PositiveSet.union
                    (randomness_indices a) (randomness_indices b)).
        eapply negligible_plus.
        + assert (forall eta er,
                     Comp_eq
                       (r <-$ generate_randomness eta u;
                        ret negb (inspect_vbool
                                    (interp_fixed a eta (adv eta er) r)))
                       (r <-$ generate_randomness eta (randomness_indices a);
                        ret negb (inspect_vbool
                                    (interp_fixed a eta (adv eta er) r)))) as E.
          {
            intros.
            setoid_rewrite <- Bind_Ret_l with
                (f := fun b => ret negb (inspect_vbool b)).
            rewrite 2 Bind_assoc.
            rewrite generate_more_randomness.
            - reflexivity.
            - eapply PositiveSetProperties.union_subset_1.
          }
          setoid_rewrite E; clear E.
          eauto.
        + assert (forall eta er,
                     Comp_eq
                       (r <-$ generate_randomness eta u;
                        ret negb (inspect_vbool
                                    (interp_fixed b eta (adv eta er) r)))
                       (r <-$ generate_randomness eta (randomness_indices b);
                        ret negb (inspect_vbool
                                    (interp_fixed b eta (adv eta er) r)))) as E.
          {
            intros.
            setoid_rewrite <- Bind_Ret_l with
                (f := fun b => ret negb (inspect_vbool b)).
            rewrite 2 Bind_assoc.
            rewrite generate_more_randomness.
            - reflexivity.
            - eapply PositiveSetProperties.union_subset_2.
          }
          setoid_rewrite E; clear E.
          eauto.
    Qed.

    Lemma whp_true : whp (#vtrue).
    Proof. cbv [whp]. reflexivity. Qed.

    Lemma always_whp e : always e -> whp e.
    Proof.
      intros A.
      eapply (fun pf => weak_whp_impl_dist_always ((#vtrue)%expr) _ pf whp_true).
      cbv [always] in A.
      goal_always_to_inspect_interp_fixed_true.
      cbn[interp_fixed].
      rewrite A; autorewrite with push_interp; reflexivity.
    Qed.

    Lemma whp_impl a b : whp (a -> b) -> (whp a -> whp b)%core.
    Proof.
      intros I A.
      eapply weak_whp_impl_dist_always with (a := (a /\ (a -> b))%expr).
      - goal_unpack_always.
        destruct a; destruct b; reflexivity.
      - eauto using whp_and.
    Qed.
  End WHPLemmas.

  Ltac merge_whp_step :=
    match goal with
    | |- whp _ -> _ => intros ?
    | H : whp _ |- whp _ => revert H; apply whp_impl
    end.
  Ltac merge_whp := repeat merge_whp_step.

  Ltac unpack_whp := merge_whp; apply always_whp; unpack_always.

  Ltac unpack_whp_push :=
    unpack_whp;
    match goal with
    | |- ?x = true => change (is_true x)
    end;
    autorewrite with push_is_true.

  Section WHPCorollaries.
    Lemma whp_contract a b : whp b -> whp (a -> b).
    Proof. unpack_whp; btauto. Qed.

    Lemma whp_mp_cond a b c :
      whp (a -> b) -> whp (a -> b -> c) -> whp (a -> c).
    Proof. unpack_whp; btauto. Qed.

    Lemma whp_impl_trans a b c :
      whp (a -> b) -> whp (b -> c) -> whp (a -> c).
      intros.
      assert (whp (a -> b -> c)) by (eapply whp_contract; eauto).
      eapply whp_mp_cond with (a := a) (b := b) (c := c); eauto.
    Qed.

    Lemma whp_impl_refl e : whp (e -> e).
    Proof.
      unpack_whp; btauto.
    Qed.
  End WHPCorollaries.

  Ltac compose_impl :=
    lazymatch goal with
    | H : whp (?a -> ?b) |- whp (?a -> ?c) =>
      apply (whp_impl_trans a b c); [exact H|]
    | H : whp (?b -> ?c) |- whp (?a -> ?c) =>
      apply (whp_impl_trans a b c); [|exact H]
    end.

  Section Equality.
    Definition eqwhp {t} (e1 e2:expr t) : Prop := whp (e1 == e2).

    Global Instance subrelation_eqwhp_indist {t} : subrelation (@eqwhp t) (@indist t).
    Proof.
      intros ? ? H.
    Admitted.

    Global Instance Proper_whp_eqwhp : Proper (eqwhp ==> iff) whp.
    Proof.
      intros ? ? H.
      apply subrelation_eqwhp_indist in H.
      apply Proper_whp_indist.
      exact H.
    Qed.

    Global Instance Reflexive_eqwhp {t} : Reflexive (@eqwhp t).
    Proof.
      cbv [Reflexive indist universal_security_game eqwhp]; intros.
      unpack_whp.
      apply eqb_refl.
    Qed.

    Global Instance Symmetric_eqwhp {t} : Symmetric (@eqwhp t).
    Proof.
      cbv [Symmetric indist universal_security_game eqwhp].
      intros x y; unpack_whp.
      repeat match goal with
             | |- context [?a ?= ?b] => destruct (a ?= b) eqn:?
             | H:_|-_ => rewrite eqb_leibniz in H; rewrite H in *; clear H
             | H:_|-_ => rewrite eqb_refl in H; discriminate H
             | _ => reflexivity
             end.
    Qed.

    Global Instance Transitive_eqwhp {t} : Transitive (@eqwhp t).
    Proof.
      cbv [Transitive eqwhp].
      intros; unpack_whp.
      repeat match goal with
             | |- context [?a ?= ?b] => destruct (a ?= b) eqn:?
             | H:_|-_ => rewrite eqb_leibniz in H; rewrite H in *; clear H
             | H:_|-_ => rewrite eqb_refl in H; discriminate H
             | _ => reflexivity
             end.
    Qed.

    Lemma Proper_eqwhp_pair_internal {t1 t2}
          (e1 e1' : expr t1) (e2 e2' : expr t2) :
        whp (e1 == e1' -> e2 == e2' -> (e1, e2) == (e1', e2')).
    Proof.
      unpack_whp.
      repeat match goal with
             | |- context [?a ?= ?b] => destruct (a ?= b) eqn:?
             | H : _ = _ |- _ =>
               rewrite eqb_leibniz in H; rewrite H in *; clear H
             | H : _ = _ |- _ => rewrite eqb_refl in H; discriminate H
             | _ => reflexivity
             end.
    Qed.

    Global Instance Proper_eqwhp_pair {t1 t2} :
      Proper (eqwhp ==> eqwhp ==> eqwhp) (@expr_pair t1 t2).
    Proof.
      intros ?????. cbv [eqwhp] in *; merge_whp.
      eapply Proper_eqwhp_pair_internal.
    Qed.

    Lemma Proper_eqwhp_adversarial_internal {t1 t2} (e e' : expr t1) :
      whp (e == e' -> !t2@e == !t2@e').
    Proof.
      unpack_whp.
      repeat match goal with
             | |- context [?a ?= ?b] => destruct (a ?= b) eqn:?
             | H : _ = _ |- _ =>
               rewrite eqb_leibniz in H; rewrite H in *; clear H
             | H : _ = _ |- _ => rewrite eqb_refl in H; discriminate H
             | _ => reflexivity
             end.
    Qed.

    Global Instance Proper_eqwhp_adversarial {t1 t2} : Proper (eqwhp ==> eqwhp) (@expr_adversarial t1 t2).
    Proof.
      intros ??; cbv [eqwhp] in *; merge_whp.
      eapply Proper_eqwhp_adversarial_internal.
    Qed.

    Lemma Proper_eqwhp_func_internal {t1 t2} (f : func t1 t2) e e' :
      whp (e == e' -> f@e == f@e').
    Proof.
      unpack_whp.
      repeat match goal with
             | |- context [?a ?= ?b] => destruct (a ?= b) eqn:?
             | H : _ = _ |- _ =>
               rewrite eqb_leibniz in H; rewrite H in *; clear H
             | H : _ = _ |- _ => rewrite eqb_refl in H; discriminate H
             | _ => reflexivity
             end.
    Qed.

    Global Instance Proper_eqwhp_func {t1 t2} f : Proper (eqwhp ==> eqwhp) (@expr_app t1 t2 f).
    Proof.
      intros ??; cbv [eqwhp] in *; merge_whp.
      eapply Proper_eqwhp_func_internal.
    Qed.
  End Equality.

  Lemma feqb_refl {t} (x : expr t) : eqwhp (x == x) #vtrue.
  Proof. unpack_whp; rewrite eqb_refl; btauto. Qed.

  Lemma feqb_symm {t} (a b : expr t) : eqwhp (a == b) (b == a).
  Proof. unpack_whp_push; rewrite eqb_symm; btauto. Qed.

  Ltac echange t :=
    refine (_ : t).

  Ltac echangein t H :=
    let H' := fresh in
    refine ((fun H' : t => _) H);
    clear H;
    rename H' into H.

  Ltac fold_eqwhp :=
    repeat match goal with
           | H : context[whp (?a == ?b)] |- _ =>
             change (whp (a == b)) with (eqwhp a b) in H
           | |- context[whp (?a == ?b)] =>
             change (whp (a == b)) with (eqwhp a b)
           end.

  Section LateInterp.
    Fixpoint interp_late
             {t} (e:expr t) (eta : nat)
             (adv: forall t1 t2, interp_type t1 eta -> interp_type t2 eta)
             (fixed_rand: PositiveMap.t (interp_type trand eta))
    : Comp (interp_type t eta) :=
      match e with
      | #c => ret (c eta)
      | $i =>
        match PositiveMap.find i fixed_rand with
        | Some r => ret r
        | _ => r <-$ {0,1}^eta; ret (cast_rand eta r)
        end
      | !@ctx =>
        ctx <-$ interp_late ctx eta adv fixed_rand; ret (adv _ _ ctx)
      | f@x =>
        x <-$ interp_late x eta adv fixed_rand; ret (interp_func f x)
      | (a, b) =>
        common_rand <-$ generate_randomness eta (PositiveSet.inter (randomness_indices b) (randomness_indices a));
          let rands := PositiveMapProperties.update common_rand fixed_rand in
          b <-$ interp_late b eta adv rands;
            a <-$ interp_late a eta adv rands;
            ret (interp_pair a b)
      end%expr.

    Lemma interp_late_correct' {t} (e:expr t) eta adv :
      forall univ (H:PositiveSet.Subset (randomness_indices e) univ) fixed,
        Comp_eq (interp_late e eta adv fixed)
                (rands <-$ generate_randomness eta univ;
                   ret (interp_fixed e eta adv
                                     (PositiveMapProperties.update rands fixed))).
    Proof.
      induction e; intros;
        simpl interp_late; simpl interp_fixed.
      { rewrite Bind_unused. reflexivity. }
      {
        simpl randomness_indices in *.
        match goal with |- context[match ?x with | _ => _ end] =>
                        case_eq x; intros end.
        {
          etransitivity; cycle 1.
          {
            apply Proper_Bind_generate_randomness.
            intros.
            rewrite find_update_in
              by (apply PositiveMapProperties.F.in_find_iff; congruence).
            eapply reflexivity. }
          rewrite Bind_unused.
          rewrite H0; reflexivity. }
        {
          etransitivity; cycle 1.
          {
            apply Proper_Bind_generate_randomness.
            intros.
            rewrite find_update_not_in
              by (apply PositiveMapProperties.F.not_find_in_iff; congruence).
            eapply reflexivity. }

          remember (fun m => ret (match m with | Some r => r | None => cast_rand eta (Bvector_exists eta) end)) as G.
          transitivity (Bind (generate_randomness eta univ)
                             (fun t => G (PositiveMap.find idx t)));
            [|subst G; reflexivity].
          rewrite generate_single.
          subst G; reflexivity.
          cbv [PositiveSet.Subset] in H.
          apply H; apply PositiveSet.singleton_spec; reflexivity.
      } }
      { simpl randomness_indices in *.
        rewrite IHe by eassumption.
        repeat setoid_rewrite <-Bind_assoc.
        repeat setoid_rewrite Bind_Ret_l.
        reflexivity. }
      { simpl randomness_indices in *.
        rewrite IHe by eassumption.
        repeat setoid_rewrite <-Bind_assoc.
        repeat setoid_rewrite Bind_Ret_l.
        reflexivity. }
      {
        match goal with H : _ |- _ =>
                        simpl randomness_indices in H;
                          apply subset_union in H; destruct H end.

        setoid_rewrite IHe2; [|eassumption].
        setoid_rewrite IHe1; [|eassumption].
        repeat setoid_rewrite <-Bind_assoc.
        repeat setoid_rewrite Bind_Ret_l.

        (* FIXME: this assertion is false - andreser, ikdc *)
        assert (bind_twice : forall {A B:Set} (x: Comp B) (f : B -> B -> Comp A),
                   Comp_eq (Bind x (fun y => Bind x (f y)))
                           (Bind x (fun y => f y y))) by admit.
        repeat setoid_rewrite bind_twice.
        clear bind_twice.

        repeat setoid_rewrite update_assoc.

        match goal with
          |- Comp_eq (Bind ?y (fun a => Bind ?x _)) (Bind ?x ?g) =>
          rewrite generate_twice with (f:=g) end.
        { f_equiv; apply Proper_generate_randomness.
          auto using PositiveSetProperties.union_subset_equal, subset_inter. }
        { cbv [Proper respectful]; intros;
            match goal with H: PositiveMap.Equal _ _ |- _ => rewrite H end;
            reflexivity. } }
    Admitted.

    Lemma interp_late_correct {t} (e:expr t) eta adv:
      Comp_eq
        (interp_late e eta adv (PositiveMap.empty _))
        (interp e eta adv).
    Proof.
      rewrite interp_late_correct'; cbv [interp]; reflexivity.
    Qed.
  End LateInterp.

  Lemma indist_rand x y : ($x) ≈ ($y).
  Proof.
    cbv [indist universal_security_game]; intros.
    setoid_rewrite <-interp_late_correct.
    cbv [interp_late].
    setoid_rewrite PositiveMap.gempty.
    setoid_rewrite ratDistance_same.
    trivial using negligible_0.
  Qed.

  Lemma inequal_rand x y : x <> y -> whp (~ ($x) == ($y)).
  Admitted.

  Definition independent {T} {U} (x : expr T) (y : expr U) :=
    PositiveSet.eq (PositiveSet.inter (randomness_indices x) (randomness_indices y))
                   PositiveSet.empty.

  (* TODO: do we need explicit substitution to define [interact]? *)

  (* TODO: contribute to FCF *)
  Lemma not_negligible_const c (Hc: ~ c == 0) : ~ negligible (fun _ => c).
  Proof.
    destruct c as [num [den Hden]].
    assert (Hnum : num > 0). {
      cbv [eqRat beqRat ratCD] in Hc; simpl in Hc.
      match goal with [ Hc : context [PeanoNat.Nat.eq_dec ?a ?b] |- _ ]
                      => destruct (PeanoNat.Nat.eq_dec a b) in Hc
      end; solve [ contradiction | nia ].
    }
    intros H; cbv [negligible] in *; specialize (H 1%nat); destruct H as [n0 H].
    eapply (H (den + n0)%nat ltac:(constructor; lia) ltac:(lia)); clear H.
    cbv [leRat bleRat ratCD]; simpl.
    match goal with |- context [le_gt_dec ?a ?b] =>
                    destruct (le_gt_dec a b)
    end; solve [ trivial | nia ].
  Qed.

  Lemma tfdist : #vtrue ≉ #vfalse.
  Proof.
    cbv [indist universal_security_game interp].
    intro H.
    specialize (H (fun _ => PositiveSet.empty)
                  (fun n _ _ t _ => interp_type_inhabited t n)
                  (fun eta rands v => inspect_vbool v)).
    cbv [id] in *.
    setoid_rewrite Bind_unused in H.
    setoid_rewrite <-Bind_assoc in H.
    do 2 setoid_rewrite Bind_Ret_l in H.
    cbn [interp_fixed] in *.
    setoid_rewrite inspect_vtrue in H; setoid_rewrite inspect_vfalse in H.
    rewrite ?evalDist_ret_1, ?evalDist_ret_0 in H by congruence.
    setoid_rewrite ratDistance_comm in H; setoid_rewrite ratDistance_from_0 in H.
    eapply not_negligible_const; eauto using rat1_ne_rat0.
  Qed.

  Close Scope rat_scope.
  Close Scope vector_scope.

  Section MoreLemmas.
    Lemma if_same b t (e:expr t) : eqwhp (eif b then e else e) e.
    Proof.
      cbv [eqwhp]; unpack_whp. destruct b; rewrite eqb_refl; reflexivity.
    Qed.

    Lemma if_true_internal {t} b (e1 e2 : expr t) :
      whp (b -> (eif b then e1 else e2) == e1).
    Proof. unpack_whp; destruct b; eauto using eqb_refl. Qed.

    Corollary if_true_whp t (b : expr tbool) (e1 e2:expr t) :
      whp b -> eqwhp (eif b then e1 else e2) e1.
    Proof. cbv [eqwhp]; merge_whp; eapply if_true_internal. Qed.

    Corollary if_true t (e1 e2:expr t) : eqwhp (eif #vtrue then e1 else e2) e1.
    Proof. eapply if_true_whp. eapply whp_true. Qed.

    Lemma if_false_internal {t} b (e1 e2 : expr t) :
      whp (~b -> (eif b then e1 else e2) == e2).
    Proof. unpack_whp; destruct b; cbn; eauto using eqb_refl. Qed.

    Corollary if_false_whp t (b : expr tbool) (e1 e2:expr t) :
      whp (~b) -> eqwhp (eif b then e1 else e2) e2.
    Proof. cbv [eqwhp]; merge_whp; eapply if_false_internal. Qed.

    Corollary if_false t (e1 e2:expr t) : eqwhp (eif #vfalse then e1 else e2) e2.
    Proof. eapply if_false_whp. unpack_whp; reflexivity. Qed.

    Lemma impl_if a b :
      eqwhp (a -> b) (eif a then b else #vtrue).
    Proof. cbv [eqwhp]; unpack_whp. btauto. Qed.

    Lemma or_if a b :
      eqwhp (a \/ b) (eif a then #vtrue else b).
    Proof. cbv [eqwhp]; unpack_whp. btauto. Qed.

    Lemma and_if a b :
      eqwhp (a /\ b) (eif a then b else #vfalse).
    Proof. cbv [eqwhp]; unpack_whp. btauto. Qed.

    Lemma whp_split a b : whp (a -> b) -> whp (~a -> b) -> whp b.
    Proof. unpack_whp. btauto. Qed.

    Lemma whp_switch_cond a b c : eqwhp (a -> b -> c) (b -> a -> c).
    Proof. unpack_whp. btauto. Qed.

    Lemma whp_impl_eq a b c : eqwhp (a -> b == c) ((a -> b) == (a -> c)).
    Proof. unpack_whp. btauto. Qed.

    Corollary whp_cond_rew a b c :
      whp (a -> b == c) ->
      eqwhp (a -> b) (a -> c).
    Proof.
      cbv [eqwhp].
      merge_whp.
      rewrite <-whp_impl_eq.
      eapply whp_impl_refl.
    Qed.

    Lemma whp_explosion e : whp (#vfalse -> e).
    Proof. unpack_whp. btauto. Qed.

    Lemma not_impl_false x : eqwhp (~x) (x -> #vfalse).
    Proof. cbv [eqwhp]; unpack_whp; btauto. Qed.
  End MoreLemmas.

  Context {tunit : type}
          {funit : forall {t}, (t -> tunit)%etype}
          {f_id : forall {t}, (t -> t)%etype}.
  Global Arguments f_id {t}.
  Global Arguments funit {t}.
  Context {unit_eq : forall a b : expr tunit, eqwhp a b}.
  Context {f_id_eq : forall {t} (x : expr t), eqwhp (f_id@x) x}.
  Global Arguments f_id_eq {t}.

  Context {ffst : forall t1 t2, (t1 * t2 -> t1)%etype}
          {fsnd : forall t1 t2, (t1 * t2 -> t2)%etype}.
  Global Arguments ffst {t1 t2}.
  Global Arguments fsnd {t1 t2}.
  Context {ffst_pair : forall t1 t2 (e1 : expr t1) (e2 : expr t2),
              eqwhp (ffst@(e1, e2)) e1}
          {fsnd_pair : forall t1 t2 (e1 : expr t1) (e2 : expr t2),
              eqwhp (fsnd@(e1, e2)) e2}.
  Global Arguments ffst_pair {t1 t2}.
  Global Arguments fsnd_pair {t1 t2}.

  Context {tlist : type -> type}
          {cnil : forall t eta, interp_type (tlist t) eta}
          {fcons : forall t, func (t * tlist t) (tlist t)}.
  Global Arguments cnil {t}.
  Global Arguments fcons {t}.

  Context {f_in : forall t, (t * (tlist t) -> tbool)%etype}.
  Global Arguments f_in {t}.
  Context {f_in_nil : forall {t} x, eqwhp (f_in@(x, #(@cnil t)))
                                        #vfalse}
          {f_in_cons : forall {t} x y (l : expr (tlist t)),
              eqwhp (f_in@(x, fcons@(y, l)))
                    (x == y \/ f_in@(x, l))}.
  Global Arguments f_in_nil {t}.
  Global Arguments f_in_cons {t}.

  Context {tmessage : type}
          {encode : forall t, (t -> tmessage)%etype}
          {decode : forall t, (tmessage -> t)%etype}
          {decode_encode : forall t (x : expr t),
              eqwhp (decode t @ (encode t @ x)) x}
          {tnat : type}
          {len : (tmessage -> tnat)%etype}.
  Global Arguments encode {t}.
  Global Arguments decode {t}.
  Global Arguments decode_encode {t}.

  Definition expr_in {t} (x : expr t) : list (expr t) -> expr tbool :=
    (fold_right (fun m acc => x == m \/ acc)%expr #vfalse)%expr.

  Section Holes.
    Inductive expr_with_hole {hole : type} : type -> Type :=
    | ewh_const {t} (_:forall eta, interp_type t eta) : expr_with_hole t
    | ewh_random (idx:positive) : expr_with_hole trand
    | ewh_adversarial {t1 t2} (_:expr_with_hole t1) : expr_with_hole t2
    | ewh_app {t1 t2} (_:(t1 -> t2)%etype) (_:expr_with_hole t1)
      : expr_with_hole t2
    | ewh_pair {t1 t2} (_:expr_with_hole t1) (_:expr_with_hole t2)
      : expr_with_hole (t1 * t2)
    | ewh_hole : expr_with_hole hole.
    Global Arguments expr_with_hole : clear implicits.

    Fixpoint fill_hole {hole t}
             (E : expr_with_hole hole t) (e : expr hole) : expr t :=
      match E with
      | ewh_hole => e
      (* recurse *)
      | ewh_const c => #c
      | ewh_random i => $i
      | ewh_adversarial x => !@(fill_hole x e)
      | ewh_app f x => f@(fill_hole x e)
      | ewh_pair a b => (fill_hole a e, fill_hole b e)
      end.

    Fixpoint without_holes {hole t} (e : expr t)
      : @expr_with_hole hole t :=
      match e with
      | expr_const c => ewh_const c
      | expr_random i => ewh_random i
      | expr_adversarial e => ewh_adversarial (without_holes e)
      | expr_app f e => ewh_app f (without_holes e)
      | expr_pair e1 e2 =>
        ewh_pair (without_holes e1) (without_holes e2)
      end.

    Lemma fill_without_holes {hole} {t} (x : expr hole) (e : expr t) :
      fill_hole (without_holes e) x = e.
    Proof.
      induction e; cbn [without_holes fill_hole]; try reflexivity.
      - rewrite IHe; reflexivity.
      - rewrite IHe; reflexivity.
      - rewrite IHe1; rewrite IHe2; reflexivity.
    Qed.

    Lemma fill_eqwhp_internal {hole t} (e1 e2 : expr hole)
          (E : expr_with_hole hole t) :
      whp (e1 == e2 -> fill_hole E e1 == fill_hole E e2).
    Proof.
      unpack_whp_push.
      intros.
      induction E; cbn [fill_hole interp_fixed]; congruence.
    Qed.

    Corollary rewrite_eqwhp_internal {hole} (e1 e2 : expr hole)
              (E : expr_with_hole hole tbool) :
      eqwhp (e1 == e2 -> fill_hole E e1) (e1 == e2 -> fill_hole E e2).
    Proof.
      eapply whp_cond_rew.
      eapply fill_eqwhp_internal.
    Qed.

    Global Instance Proper_fill_hole {t1 t2} (C : expr_with_hole t1 t2)
      : Proper (eqwhp ==> eqwhp) (fill_hole C).
    Proof.
      intros x y.
      eapply whp_impl.
      eapply fill_eqwhp_internal.
    Qed.

    Lemma fill_cond_true a (C : expr_with_hole tbool tbool) :
      eqwhp (a -> fill_hole C a) (a -> fill_hole C #vtrue).
    Proof.
      cbv [eqwhp].
      rewrite <-whp_impl_eq.
      apply (whp_impl_trans _ (a == #vtrue)).
      - unpack_whp; btauto.
      - apply fill_eqwhp_internal.
    Qed.

    Lemma fill_cond_false a (C : expr_with_hole tbool tbool) :
      eqwhp (~a -> fill_hole C a) (~a -> fill_hole C #vfalse).
    Proof.
      cbv [eqwhp].
      rewrite <-whp_impl_eq.
      apply (whp_impl_trans _ (a == #vfalse)).
      - unpack_whp; btauto.
      - apply fill_eqwhp_internal.
    Qed.

    Fixpoint refine_hole {t1 t2 t3}
             (A : expr_with_hole t1 t2) (B : expr_with_hole t2 t3)
      : expr_with_hole t1 t3 :=
      match B with
      | ewh_hole => A
      (* recurse *)
      | ewh_const c => ewh_const c
      | ewh_random i => ewh_random i
      | ewh_adversarial x => ewh_adversarial (refine_hole A x)
      | ewh_app f x => ewh_app f (refine_hole A x)
      | ewh_pair a b => ewh_pair (refine_hole A a) (refine_hole A b)
      end.

    Lemma fill_refine_hole {t1 t2 t3}
          (A : expr_with_hole t1 t2) (B : expr_with_hole t2 t3)
          (e : expr t1) :
      fill_hole (refine_hole A B) e = fill_hole B (fill_hole A e).
    Proof.
      revert A e; induction B; intros A e; cbn [fill_hole refine_hole];
        try reflexivity.
      - rewrite IHB; reflexivity.
      - rewrite IHB; reflexivity.
      - rewrite IHB1; rewrite IHB2; reflexivity.
    Qed.
  End Holes.

  Bind Scope ewh_scope with expr_with_hole.
  Delimit Scope ewh_scope with ewh.
  Local Notation "'#' x" := (ewh_const x) : ewh_scope.
  Local Notation "'$' x" := (ewh_random x%positive) : ewh_scope.
  Local Notation "f @ x" := (ewh_app f x%ewh) : ewh_scope.
  Local Notation "'!' t '@' x" := (@ewh_adversarial _ t x%ewh) : ewh_scope.
  Local Notation "'!' '@' x" := (ewh_adversarial x%ewh) : ewh_scope.
  Local Notation "( x , y , .. , z )" := (ewh_pair .. (ewh_pair x%ewh y%ewh) .. z%ewh) : ewh_scope.
  Local Notation "'#!'" := (ewh_const (interp_type_inhabited _)) : ewh_scope.
  Local Notation "'eif' b 'then' x 'else' y" :=
    (ite@(b,x,y))%ewh
      (at level 200, b at level 1000, x at level 1000, y at level 1000,
       format "'[hv' 'eif'  b  '/' '[' 'then'  x  ']' '/' '[' 'else'  y ']' ']'")
    : ewh_scope.
  Local Notation "a [ b ]" := (refine_hole b a)%ewh
                                               (at level 10) : ewh_scope.

  Ltac build_context x e :=
    match type of x with
    | expr ?hole =>
      match e with
      | x => uconstr:(@ewh_hole hole)
      | @expr_const ?t ?c => uconstr:(@ewh_const hole t c)
      | expr_random ?i => uconstr:(@ewh_random hole i)
      | @expr_adversarial ?t1 ?t2 ?e => let E := build_context x e in
                                        uconstr:(@ewh_adversarial hole t1 t2 E)
      | @expr_app ?t1 ?t2 ?f ?e => let E := build_context x e in
                                   uconstr:(@ewh_app hole t1 t2 f E)
      | @expr_pair ?t1 ?t2 ?e1 ?e2 => let E1 := build_context x e1 in
                                      let E2 := build_context x e2 in
                                      uconstr:(@ewh_pair hole t1 t2 E1 E2)
      | fill_hole ?B ?e => let A := build_context x e in
                           uconstr:(refine_hole A B)
      | _ => uconstr:(without_holes e)
      end
    end.

  Ltac internal_rewrite :=
    match goal with
    | |- context[(?e == ?e' -> ?b)%expr] =>
      let C := build_context e b in
      let H := fresh in
      pose proof (rewrite_eqwhp_internal e e' C) as H;
      cbn [fill_hole refine_hole] in H;
      repeat ((rewrite fill_without_holes in H) +
              (rewrite fill_refine_hole in H));
      rewrite H; clear H
    end.

  Ltac rewrite_fill_cond_true :=
    match goal with
    | |- context[(?a -> ?b)%expr] =>
      lazymatch b with
      | context[a] => idtac
      end;
      let C := build_context a b in
      let H := fresh in
      pose proof (fill_cond_true a C) as H;
      repeat ((cbn [fill_hole refine_hole] in H) ||
              (rewrite fill_without_holes in H) ||
              (rewrite fill_refine_hole in H));
      rewrite H; clear H
    end.

  Ltac rewrite_fill_cond_false :=
    match goal with
    | |- context[(~ ?a -> ?b)%expr] =>
      lazymatch b with
      | context[a] => idtac
      end;
      let C := build_context a b in
      let H := fresh in
      pose proof (fill_cond_false a C) as H;
      repeat ((cbn [fill_hole refine_hole] in H) ||
              (rewrite fill_without_holes in H) ||
              (rewrite fill_refine_hole in H));
      rewrite H; clear H
    end.

  Ltac deny_cond :=
    match goal with
    | |- whp (?a -> ?b)%expr =>
      cut (whp (~ a));
      [solve [apply whp_impl;
              rewrite_fill_cond_false;
              apply whp_contract;
              apply whp_explosion]|]
    end.

  Ltac external_change e e' :=
    let H := fresh in
    assert (whp (e == e')) as H;
    [|
     revert H;
     apply whp_impl;
     internal_rewrite;
     apply whp_contract
    ].

  Lemma fill_cond_if_true a {t} (e e' : expr t) (C : expr_with_hole _ tbool) :
    eqwhp (a -> fill_hole C (eif a then e else e')) (a -> fill_hole C e).
  Proof.
    rewrite_fill_cond_true.
    rewrite if_true.
    reflexivity.
  Qed.

  Lemma fill_cond_if_false a {t} (e e' : expr t) (C : expr_with_hole _ tbool) :
    eqwhp (~a -> fill_hole C (eif a then e else e')) (~a -> fill_hole C e').
  Proof.
    rewrite_fill_cond_false.
    rewrite if_false.
    reflexivity.
  Qed.

  Ltac rewrite_fill_cond_if_true :=
    match goal with
    | |- context[(?a -> ?d)%expr] =>
      lazymatch d with
      | context[(eif a then ?b else ?c)%expr] =>
        let C := build_context (eif a then b else c)%expr d in
        let H := fresh in
        pose proof (fill_cond_if_true a b c C) as H;
        repeat ((cbn [fill_hole refine_hole] in H) ||
                (rewrite fill_without_holes in H) ||
                (rewrite fill_refine_hole in H));
        rewrite H; clear H
      end
    end.

  Ltac rewrite_fill_cond_if_false :=
    match goal with
    | |- context[(~ ?a -> ?d)%expr] =>
      match d with
      | context[(eif a then ?b else ?c)%expr] =>
        let C := build_context (eif a then b else c)%expr d in
        let H := fresh in
        pose proof (fill_cond_if_false a b c C) as H;
        repeat ((cbn [fill_hole refine_hole] in H) ||
                (rewrite fill_without_holes in H) ||
                (rewrite fill_refine_hole in H));
        rewrite H; clear H
      end
    end.

  (* TODO either fill these in concretely,
     or allow arbitrary types as randomness indices *)
  Context (pos_pair : nat * positive -> positive)
          (pos_pair_inv : positive -> nat * positive)
          (pos_pair_inv_l : forall x, pos_pair (pos_pair_inv x) = x)
          (pos_pair_inv_r : forall x, pos_pair_inv (pos_pair x) = x).

  Section renumber.
    Context (n : nat).

    Fixpoint renumber {t} (e : expr t) : expr t :=
      match e with
      | expr_random i => expr_random (pos_pair (n, i))
      (* recurse *)
      | expr_const c => expr_const c
      | expr_adversarial e => expr_adversarial (renumber e)
      | expr_app f e => expr_app f (renumber e)
      | expr_pair e1 e2 => expr_pair (renumber e1) (renumber e2)
      end.

    Fixpoint renumber_h {t1 t2} (C : expr_with_hole t1 t2) : expr_with_hole t1 t2 :=
      match C with
      | ewh_random i => ewh_random (pos_pair (n, i))
      (* recurse *)
      | ewh_const c => ewh_const c
      | ewh_adversarial e => ewh_adversarial (renumber_h e)
      | ewh_app f e => ewh_app f (renumber_h e)
      | ewh_pair e1 e2 => ewh_pair (renumber_h e1) (renumber_h e2)
      | ewh_hole => ewh_hole
      end.
  End renumber.

  Definition fill_alpha {t1 t2} n (C:expr_with_hole t1 t2) (e:expr t1) : expr t2 :=
    fill_hole (renumber_h n C) e.

  Section interaction.
    Context
      {i o s}
      (init : expr (tlist o * s))
      (step : expr_with_hole (i*s) (o*s)).
    Fixpoint interaction (n : nat) {struct n} : expr (tlist o * s)
      := match n with
         | O => renumber 0 init
         | S n' =>
           let outs'_s' := interaction n' in
             let outs' := ffst@outs'_s' in
             let s' := fsnd@outs'_s' in
           let o_s := fill_alpha n step (!@outs', s') in
           (fcons@(ffst@o_s, outs'), fsnd@o_s)
         end%expr.
  End interaction.

  Section Old.
    Context (n : nat).

    Definition index_old i :=
      let '(n', _) := pos_pair_inv i in
      n' <= n.

    Fixpoint expr_old {t} (e : expr t) :=
      match e with
      | $i => index_old i
      (* recurse *)
      | #_ => True
      | _@e => expr_old e
      | !@e => expr_old e
      | (e1, e2) => (expr_old e1 /\ expr_old e2)%type
      end%expr.
  End Old.

  Lemma pos_pair_old n m x : n <= m -> index_old m (pos_pair (n, x)).
  Proof.
    cbv [index_old]; rewrite pos_pair_inv_r.
    eauto.
  Qed.

  Lemma pos_pair_old_conv n m x : n > m -> index_old m (pos_pair (n, x)) -> False.
  Proof.
    cbv [index_old]; rewrite pos_pair_inv_r.
    lia.
  Qed.

  Lemma old_different i n x : index_old n i -> i <> pos_pair (S n, x).
  Proof.
    intros ??; subst; eauto using pos_pair_old_conv, gt_Sn_n.
  Qed.

  Lemma pos_pair_inj_left n m x y : pos_pair (n, x) = pos_pair (m, y) ->
                                    n = m.
    intros H.
    eapply (f_equal pos_pair_inv) in H.
    repeat rewrite pos_pair_inv_r in H.
    inversion H.
    eauto.
  Qed.

  Lemma renumber_old {t} n (e : expr t) :
    expr_old n (renumber n e).
    induction e; cbn [renumber expr_old]; eauto using pos_pair_old.
  Qed.

  Lemma fill_alpha_old {t1 t2} n (C : expr_with_hole t1 t2) e :
    expr_old n e ->
    expr_old n (fill_alpha n C e).
  Proof.
    revert e.
    induction C; intros e H;
      cbn [fill_alpha fill_hole renumber_h expr_old]; eauto using pos_pair_old.
  Qed.

  Lemma old_S {t} n (e : expr t) :
    expr_old n e -> expr_old (S n) e.
  Proof.
    induction e; eauto; cbn [expr_old].
    - cbv [index_old].
      destruct (pos_pair_inv _).
      eauto.
    - intuition idtac.
  Qed.

  Lemma interaction_old {i o s} init step n :
    expr_old n (@interaction i o s init step n).
  Proof.
    intros; induction n; cbn [interaction]; eauto;
    repeat (progress (cbn [expr_old]) ||
            split ||
            eapply fill_alpha_old ||
            solve [eauto using old_S, renumber_old]).
  Qed.

  Section Authenticity.
    Context {ttag tskey tvkey tpkey : type}
            {skeygen : (trand -> tskey)%etype}
            {vkeygen : (tskey -> tvkey)%etype}
            {pkeygen : (tskey -> tpkey)%etype}
            {auth : (tskey * tmessage -> ttag)%etype}
            {verify : (tvkey * tmessage * ttag -> tbool)%etype}.

    Inductive auth_safe' (sk : positive) :
      forall {t}, expr t -> list (expr tmessage) -> Prop :=
    | asauth m l : auth_safe' sk m l ->
                   auth_safe' sk (auth@(skeygen@$sk, m)) (m :: l)
    | asverify m t : auth_safe' sk (verify@(vkeygen@(skeygen@$sk), m, t)) nil
    | aspkey : auth_safe' sk (pkeygen@(skeygen@$sk)) nil
    | asrand_neq (i : positive) : i <> sk -> auth_safe' sk ($i) nil
    (* boring recursion: *)
    | asconst t v : @auth_safe' sk t #v nil
    | asfunc {t1 t2} (f : func t1 t2) e l :
        auth_safe' sk e l -> auth_safe' sk (f@e) l
    | asadv  {t1 t2} (e : expr t1) l :
        auth_safe' sk e l -> auth_safe' sk (!t2@e) l
    | aspair {t1 t2} (e1 : expr t1) (e2 : expr t2) l1 l2 :
        auth_safe' sk e1 l1 ->
        auth_safe' sk e2 l2 ->
        auth_safe' sk (e1, e2) (l1 ++ l2).

    Definition auth'_conclusion :=
      forall (sk : positive)
             (s : expr ttag)
             (l : list (expr tmessage))
             (m : expr tmessage),
        auth_safe' sk s l ->
        (* It's okay if the key was leaked at the time we got the message,
           just not the signature; hence no "auth_safe" for m. *)
        let ve := (verify@(vkeygen@(skeygen@$sk), m, s))%expr in
        whp (ve -> expr_in m l).

    Definition auth_safe (sk : positive)
               {t} (m : expr t) (l : list (expr tmessage)) : Prop :=
      exists l', auth_safe' sk m l' /\
                 (forall x, In x l' -> In x l) .

    Definition auth_conclusion :=
      forall (sk : positive)
             (s : expr ttag)
             (l : list (expr tmessage))
             (m : expr tmessage),
        auth_safe sk s l ->
        let ve := (verify@(vkeygen@(skeygen@$sk), m, s))%expr in
        whp (ve -> expr_in m l).

    Lemma expr_in_eq {t} (m x : expr t) l :
      In x l ->
      whp (m == x -> expr_in m l).
    Proof.
      induction l as [|y l].
      - intros [].
      - cbn [expr_in fold_right].
        intros [H|H].
        + subst.
          unpack_whp; btauto.
        + specialize (IHl H); clear H.
          unpack_whp; btauto.
    Qed.

    Lemma expr_in_extend {t} (m : expr t) l l' :
      (forall x, In x l -> In x l') ->
      whp (expr_in m l -> expr_in m l').
    Proof.
      revert l'.
      induction l as [|x l]; intros l' H; cbn [expr_in fold_right].
      - eapply whp_explosion.
      - cbn [In] in H.
        eapply (whp_split (m == x)).
        + rewrite whp_switch_cond.
          eapply whp_contract.
          assert (In x l') by (eapply H; eauto); clear H.
          eapply expr_in_eq; eauto.
        + rewrite or_if.
          rewrite_fill_cond_if_false.
          eapply whp_contract.
          eauto.
    Qed.

    Lemma auth'_auth : auth'_conclusion -> auth_conclusion.
    Proof.
      cbv [auth'_conclusion auth_conclusion].
      intros Hcon ??? m (? & Hauth_safe' & Hsub).
      specialize (Hcon _ _ _ m Hauth_safe').
      compose_impl.
      eapply expr_in_extend; eauto.
    Qed.
  End Authenticity.

  Section AuthRewriting.
    Lemma expr_in_singleton {t} (a b:expr t)
      : eqwhp (expr_in a (b :: nil)) (a == b).
    Proof. cbn [expr_in fold_right]; unpack_whp; btauto. Qed.

    Fixpoint choice {t} (m l0 : expr t) (l : list (expr t)) :=
      match l with
      | nil => l0
      | cons l1 l => (eif m == l0 then l0 else choice m l1 l)%expr
      end.

    Lemma choice_eq {t : type} (m l0 : expr t) (l : list (expr t)) :
      whp (expr_in m (cons l0 l) -> m == choice m l0 l).
    Proof.
      revert l0.
      induction l as [|l1 l]; intros l0.
      - cbn [choice].
        rewrite expr_in_singleton.
        eapply whp_impl_refl.
      - cbn [expr_in fold_right choice] in IHl |- *.
        specialize (IHl l1).
        eapply (whp_split (m == l0)).
        + rewrite whp_switch_cond.
          eapply whp_contract.
          rewrite_fill_cond_if_true.
          eapply whp_impl_refl.
        + assert (forall a b c,
                     whp (~a -> b -> c) ->
                     whp (~a -> a \/ b -> c))
            as disj_hyp_false
            by (intros; unpack_whp; btauto).
          eapply disj_hyp_false; clear disj_hyp_false.
          rewrite_fill_cond_if_false.
          eapply whp_contract.
          eauto.
    Qed.

    Lemma rewrite_condition {t : type} b (e1 e1' e2 : expr t) :
      whp ((b -> e1 == e1') ->
           (eif b then e1 else e2) == (eif b then e1' else e2)).
      rewrite (impl_if b).
      eapply (whp_split b).
      - repeat rewrite_fill_cond_if_true.
        eapply whp_contract.
        eapply whp_impl_refl.
      - repeat rewrite_fill_cond_if_false.
        do 2 eapply whp_contract.
        fold_eqwhp; reflexivity.
    Qed.

    Context {ttag tskey tvkey tpkey : type}
            {skeygen : (trand -> tskey)%etype}
            {vkeygen : (tskey -> tvkey)%etype}
            {pkeygen : (tskey -> tpkey)%etype}
            {auth : (tskey * tmessage -> ttag)%etype}
            {verify : (tvkey * tmessage * ttag -> tbool)%etype}
            (auth_correct : @auth_conclusion ttag tskey tvkey tpkey
                                             skeygen vkeygen pkeygen
                                             auth verify).

    Fixpoint choice_ctx {t1 t2} m (C : expr_with_hole _ t2)
             (l0 : expr t1) (l : list (expr t1)) :=
      match l with
      | nil => fill_hole C l0
      | cons l1 l => (eif m == l0
                      then fill_hole C l0
                      else choice_ctx m C l1 l)%expr
      end.

    Lemma fill_if_comm {t1 t2} (C : expr_with_hole _ t2) a (b c : expr t1) :
      eqwhp (fill_hole C (eif a then b else c))
            (eif a then fill_hole C b else fill_hole C c).
    Proof.
      eapply (whp_split a);
        [do 2 rewrite_fill_cond_if_true | do 2 rewrite_fill_cond_if_false];
        eapply whp_contract; fold_eqwhp; reflexivity.
    Qed.

    Lemma app_if {t1 t2} f b (x y : expr t1) :
      @eqwhp t2 (f@(eif b then x else y)) (eif b then f@x else f@y).
    Proof.
      lazymatch goal with
        |- context [(?app@(eif ?b then ?t else ?f))%expr]
        => let br := constr:((eif b then t else f)%expr) in
           let rhs := open_constr:(fill_hole (app@ewh_hole) br) in
           erewrite (_ : (app@_)%expr = rhs) by
               (cbn [fill_hole]; rewrite ?fill_without_holes; reflexivity);
             setoid_rewrite fill_if_comm;
             cbn [fill_hole]; rewrite ?fill_without_holes
      end.
      Unshelve. (* using [unshelve] before the lazymatch gives anomaly *)
      all : reflexivity.
    Qed.

    Lemma choice_ctx_as_fill {t1 t2}
          m (C : expr_with_hole _ t2) l0 (l : list (expr t1)) :
      eqwhp (choice_ctx m C l0 l)
            (fill_hole C (choice m l0 l)).
    Proof.
      revert l0.
      induction l; intros l0.
      - reflexivity.
      - cbn [choice_ctx choice].
        rewrite IHl.
        rewrite fill_if_comm; reflexivity.
    Qed.

    Local Notation auth_safe :=
      (@auth_safe ttag tskey tvkey tpkey
                  skeygen vkeygen pkeygen auth verify).

    (* make an opaque copy of verify so that we don't rewrite this lemma
       repeatedly. *)
    Lemma hide_verify : { v | verify = v }.
    Proof.
      exists verify.
      reflexivity.
    Qed.
    Definition verify' := proj1_sig hide_verify.
    Definition verify_verify' : verify = verify' := proj2_sig hide_verify.
    Lemma rewrite_verify
          sk {tag m}
          {t e} {C : expr_with_hole _ t} (Hhandler : eqwhp e (fill_hole C m))
          {choice0 choices} (_ : auth_safe sk tag (cons choice0 choices ))
          {err : expr t}
      : let ve := (verify@(vkeygen@(skeygen@($sk)), m, tag))%expr in
        let ve' := (verify'@(vkeygen@(skeygen@($sk)), m, tag))%expr in
        eqwhp (eif ve then e else err)
              (eif ve' then choice_ctx m C choice0 choices else err).
    Proof.
      rewrite <- verify_verify'; intros ve ve'; change ve' with ve; clear ve'.
      rewrite Hhandler; clear Hhandler.

      assert (whp (ve -> fill_hole C m == choice_ctx m C choice0 choices)).
      {
        rewrite choice_ctx_as_fill.
        apply (whp_impl_trans _ (m == choice m choice0 choices)).
        - apply (whp_impl_trans _ (expr_in m (cons choice0 choices))).
          + eauto using auth_correct.
          + apply choice_eq.
        - apply fill_eqwhp_internal.
      }
      eapply whp_impl.
      - eapply rewrite_condition.
      - eauto.
    Qed.
  End AuthRewriting.

  Section WHPFunction.
    Definition whp_compatible {t1 t2} (l1 l2 : list (expr t1 * expr t2))
      : Prop :=
      forall x1 y1 x2 y2, In (x1, y1) l1 -> In (x2, y2) l2 ->
                          whp (x1 == x2 -> y1 == y2).

    Definition whp_function {t1 t2} (l : list (expr t1 * expr t2)) : Prop :=
      whp_compatible l l.

    Lemma compatible_app {t1 t2} (l1 l2 : list (expr t1 * expr t2)) :
      whp_function l1 ->
      whp_function l2 ->
      whp_compatible l1 l2 ->
      whp_function (l1 ++ l2).
    Proof.
      cbv [whp_function whp_compatible].
      intros.
      repeat match goal with
             | H : _ |- _ => eapply in_app_or in H; destruct H
             end; eauto.
      external_change (x1 == x2)%expr (x2 == x1)%expr;
        [fold_eqwhp; eapply feqb_symm|].
      external_change (y1 == y2)%expr (y2 == y1)%expr;
        [fold_eqwhp; eapply feqb_symm|].
      eauto.
    Qed.

    Lemma nil_fn {t1 t2} : whp_function (nil : list (expr t1 * expr t2)).
    Proof. intros ????[]. Qed.

    Lemma singleton_fn {t1 t2} (x : expr t1) (y : expr t2) :
      whp_function ((x, y) :: nil).
    Proof. intros ????[][];
             repeat match goal with
                    | H : (_, _) = (_, _) |- _ => inversion H; clear H
                    | H : In _ nil |- _ => destruct H
                    end.
           subst; unpack_whp_push; reflexivity.
    Qed.

    Lemma whp_function_weaken {t1 t2} (l l' : list (expr t1 * expr t2)) :
      (forall x, In x l -> In x l') ->
      whp_function l' ->
      whp_function l.
    Proof. cbv [whp_function whp_compatible]; eauto. Qed.
  End WHPFunction.

  Section SymmetricEncrypt.
    Context {tkey tnonce : type}
            {keygen : (trand -> tkey)%etype}
            {encrypt : (tkey * tnonce * tmessage -> tmessage)%etype}.

    Inductive encrypt_pair_nonces (sk : positive) :
      forall {t}, expr t -> expr t ->
                  list (expr tnonce * expr tmessage) ->
                  list (expr tnonce * expr tmessage) -> Prop :=
    (* I believe the "safety" existentials are not easily removable,
       because they affect the nonce calculation. -ikdc *)
    | ep_encrypt n nl
                 lml lm'l
                 m m_safety ml m_safetyl
                 m' m'_safety m'_safetyl m'l :
        encrypt_pair_nonces sk n n nl nl ->
        encrypt_pair_nonces sk (len@m) (len@m') lml lm'l ->
        encrypt_pair_nonces sk m m_safety ml m_safetyl ->
        encrypt_pair_nonces sk m'_safety m' m'_safetyl m'l ->
        encrypt_pair_nonces sk
                            (encrypt@(keygen@($sk), n, m))
                            (encrypt@(keygen@($sk), n, m'))
                            ((n, m) :: nl ++ lml ++ ml ++ m'_safetyl)
                            ((n, m') :: nl ++ lm'l ++ m_safetyl ++ m'l)
    | ep_const {t} v : @encrypt_pair_nonces sk t (#v) (#v) nil nil
    | ep_rand (i : positive) :
        i <> sk ->
        encrypt_pair_nonces sk ($i) ($i) nil nil
    (* recurse *)
    | ep_app {t1 t2} (f : func t1 t2) a b al bl :
        encrypt_pair_nonces sk a b al bl ->
        encrypt_pair_nonces sk (f@a) (f@b) al bl
    | ep_adv {t1 t2} (a b : expr t1) al bl :
        encrypt_pair_nonces sk a b al bl ->
        encrypt_pair_nonces sk (!t2@a) (!t2@b) al bl
    | ep_pair {t1 t2} (a1 b1 : expr t1) al1 bl1 (a2 b2 : expr t2) al2 bl2 :
        encrypt_pair_nonces sk a1 b1 al1 bl1 ->
        encrypt_pair_nonces sk a2 b2 al2 bl2 ->
        encrypt_pair_nonces sk (a1, a2) (b1, b2) (al1 ++ al2) (bl1 ++ bl2)
    (* weaken *)
    | ep_transport {t} (a a' b b' : expr t) al bl :
        eqwhp a a' ->
        eqwhp b b' ->
        encrypt_pair_nonces sk a b al bl ->
        encrypt_pair_nonces sk a' b' al bl
    | ep_nonce_set {t} (a b : expr t) al bl al' bl' :
        (forall x, In x al -> In x al') ->
        (forall x, In x bl -> In x bl') ->
        encrypt_pair_nonces sk a b al bl ->
        encrypt_pair_nonces sk a b al' bl'
    .

    Lemma epn_symm sk {t} (a b : expr t) al bl :
      encrypt_pair_nonces sk a b al bl ->
      encrypt_pair_nonces sk b a bl al.
    Proof.
      induction 1.
      - eapply ep_nonce_set; [| |eapply ep_encrypt; eauto];
          cbn [In]; intros ?;
          repeat setoid_rewrite in_app_iff;
          intuition idtac.
      - eapply ep_const.
      - eapply ep_rand; eauto.
      - eapply ep_app; eauto.
      - eapply ep_adv; eauto.
      - eapply ep_pair; eauto.
      - eapply ep_transport; eassumption.
      - eapply ep_nonce_set; eauto.
    Qed.

    Definition encrypt_pair sk {t} (a b : expr t) : Prop :=
      exists al bl,
        encrypt_pair_nonces sk a b al bl /\
        whp_function al /\
        whp_function bl.

    Global Instance Proper_encrypt_pair_nonces sk {t : type} :
      Proper (eqwhp ==> eqwhp ==> eq ==> eq ==> iff)
             (@encrypt_pair_nonces sk t).
    Proof.
      intros ?? H ?? H' ??????; subst.
      split; (intros Hepn; eapply ep_transport;
              solve [eassumption | symmetry; eassumption]).
    Qed.

    (* If:
     * - allowing for eqwhp transports
     * - the secret key is used correctly
     * - nonces aren't reused
     * - both sides are syntactically the same,
     *   except for the inputs to encrypt
     * - the inputs to encrypt have lengths which correspond in the same way
     * Then:
     * - the two sides are indistinguishable *)
    Definition confidentiality_conclusion :=
      forall (sk : positive) {t} (a b : expr t),
        encrypt_pair sk a b ->
        a ≈ b.

    Context (conf : confidentiality_conclusion).

    Lemma fill_confidentiality sk nonce msg1 msg2 {t}
          (eh : expr_with_hole tmessage t) e1 :
      e1 = fill_hole eh (encrypt@(keygen@$sk, nonce, msg1)) ->
      let e2 := fill_hole eh (encrypt@(keygen@$sk, nonce, msg2)) in
      encrypt_pair sk e1 e2 ->
      e1 ≈ e2.
    Proof. eauto using conf. Qed.
  End SymmetricEncrypt.

  Lemma NoDup_nth_error_Some_neq {T} l
        (Hl : NoDup l)
        i j
        (x y : T)
        (Hix : nth_error l i = Some x)
        (Hjy : nth_error l j = Some y)
        (Hij : i <> j)
    : x <> y.
    pose proof proj1 (NoDup_nth_error l) Hl i j ltac:(eapply nth_error_Some; congruence) as H.
    assert (nth_error l i <> nth_error l j) by (intuition congruence).
    congruence.
  Qed.

  Ltac indexof x l :=
    lazymatch l with
    | nil => fail "element does not appear in the list"
    | cons x _ => constr:(O)
    | cons _ ?tl =>
      let i := indexof x tl in
      constr:(S i)
    end.

  Ltac solve_neq_from_NoDup :=
    lazymatch goal with
    | H : NoDup ?l |- ?x <> ?y
      =>
      let i := indexof x l in
      let j := indexof y l in
      refine (NoDup_nth_error_Some_neq l H i j x y _ _ _);
      [ cbv [nth_error]; reflexivity ..
      | refine (proj1 (Nat.eqb_neq _ _) _); reflexivity ]
    end.

  Create HintDb auth_safe' discriminated.
  Hint Extern 0 (_ <> _) => solve_neq_from_NoDup : auth_safe'.
  Hint Constructors auth_safe' : auth_safe'.
  Ltac solve_auth_safe :=
    lazymatch goal with
    | |- auth_safe' _ _ _ =>
      typeclasses eauto with auth_safe'
    | |- auth_safe _ _ _
      =>
      (* todo deduplicate? *)
      cbv [auth_safe];
      eexists;
      split;
      [ typeclasses eauto with auth_safe'
      | cbv [app];
        typeclasses eauto with nocore ]
    end.

  Ltac solve_eq_fill_hole_r :=
    try lazymatch goal with
        | |- eqwhp _ _ => apply (eq_subrelation Reflexive_eqwhp)
        end;
    lazymatch goal with
    | |- ?LHS = (fill_hole ?e ?x) =>
      is_evar e;
      let C := build_context x LHS in
      unify e C; reflexivity
    end.

  Ltac destruct_In H :=
    match type of H with
    | In _ ?l =>
      match l with
      | nil => solve [destruct H]
      | cons _ _ => let H' := fresh in destruct H as [H' | H'];
                                       [try match type of H' with
                                            | _ = ?a => subst a
                                            end
                                       |
                                       destruct_In H']
      | _ => fail
      end
    end.

  Ltac solve_whp_compatible :=
    lazymatch goal with
    | |- whp_function _ => cbv [whp_function]
    | |- whp_compatible => idtac
    end;
    let H1 := fresh in
    let H2 := fresh in
    intros ???? H1 H2;
    cbn [app] in H1, H2;
    destruct_In H1; destruct_In H2;
    repeat lazymatch goal with
           | H : (_, _) = (_, _) |- _ => inversion_clear H
           | |- whp (?x1 == ?x2 -> ?y1 == ?y2) =>
             lazymatch y1 with
             | y2 => apply whp_contract; fold_eqwhp; reflexivity
             | _ => idtac "todo: handle case where nonces are different"
             end
           end.

  Ltac dedup_cons x l :=
    lazymatch type of l with
    | list ?T =>
      let rec dedup_cons' x l' acc :=
          lazymatch l' with
          | nil => constr:(cons x acc)
          | cons ?y ?l' =>
            lazymatch y with
            | x => constr:(l)
            | _ => dedup_cons' x l' (cons y acc)
            end
          end
      in dedup_cons' x l (@nil T)
    end.

  Ltac dedup l :=
    lazymatch type of l with
    | list ?T =>
      let rec dedup' l acc :=
          lazymatch l with
          | nil => acc
          | cons ?x ?l => dedup' l ltac:(dedup_cons x acc)
          end
      in dedup' l (@nil T)
    end.

  Ltac dedup_whp_function :=
    lazymatch goal with
      |- whp_function ?l =>
      let k := dedup l in
      eapply (whp_function_weaken _ k);
      [
        let H := fresh in
        intros ? H;
        destruct_In H;
        solve [econstructor; eauto]
       |]
    end.

  Ltac ep_econstructor :=
    (* avoid weakening, which loops; this is faster than eapply *)
    (econstructor 1 ||
     econstructor 2 ||
     econstructor 3 ||
     econstructor 4 ||
     econstructor 5 ||
     econstructor 6).

  (* TODO use ep_nonce_set to dedup the list as it's constructed *)
  Ltac solve_encrypt_pair' nongreed nongreedy :=
    repeat lazymatch goal with
           | |- encrypt_pair _ _ _ => eexists; eexists; split; [|split]
           | |- encrypt_pair_nonces ?sk ?x ?y ?al ?bl =>
             tryif nongreed sk x y al bl
             then nongreedy sk x y al bl
             else ep_econstructor
           | |- _ <> _ => solve_neq_from_NoDup
           | |- whp_function _ =>
             cbv [app]; dedup_whp_function; solve_whp_compatible
           end.

  Tactic Notation "solve_encrypt_pair" tactic3(nongreed) tactic3(nongreedy) :=
    solve_encrypt_pair' nongreed nongreedy.

  Section Example1AuthConf.
    Context {tsignature tskey tpkey : type}.

    Context {skeygen : (trand -> tskey)%etype} (* secret key generation  *)
            {pkeygen : (tskey -> tpkey)%etype} (* public part of key *)
            {sign : (tskey * tmessage -> tsignature)%etype}
            {sverify : (tpkey * tmessage * tsignature -> tbool)%etype}
            {signature_correct :
               @auth_conclusion tsignature tskey tpkey tpkey
                                skeygen pkeygen pkeygen sign sverify}.

    Context {tmac tmkey : type}
            {mkeygen : (trand -> tmkey)%etype}
            {mac : (tmkey * tmessage -> tmac)%etype}
            {mverify : (tmkey * tmessage * tmac -> tbool)%etype}
            {mac_correct :
               @auth_conclusion tmac tmkey tmkey tunit
                                mkeygen f_id funit mac mverify}.

    Context {tkey tnonce : type}
            {ekeygen : (trand -> tkey)%etype}
            {encrypt : (tkey * tnonce * tmessage -> tmessage)%etype}
            {decrypt : (tkey * tmessage -> tmessage)%etype}
            (decrypt_encrypt : forall k n m,
                eqwhp (decrypt@(ekeygen@($k), encrypt@(ekeygen@($k), n, m))) m)
            {confidentiality :
               @confidentiality_conclusion tkey tnonce
                                           ekeygen encrypt}.

    Context {len_encode_skeygen : forall i j,
                eqwhp (len@(encode@(skeygen@($i))))
                      (len@(encode@(skeygen@($j))))}.

    (* hardcoded nonce *)
    Context {N : forall eta, interp_type tnonce eta}.

    Context (skn1 skn2 Kn irrelevant : positive)
            (nodup : NoDup (skn1 :: skn2 :: Kn :: irrelevant :: nil)%list).

    Example example_1_auth_from_conf :
      whp (
          let sk1 := ekeygen@($skn1) in
          let sk2 := mkeygen@($skn2) in
          let sK := skeygen@($Kn) in
          let msK := encode@sK in
          let pK := pkeygen@sK in
          let enc_out := encrypt@(sk1, #N, msK) in
          let mac_out := mac@(sk2, enc_out) in
          let net_in_1 := (pK, (enc_out, mac_out))%expr in

          let adv_out_1 := !(tmessage * tmac * tmessage)@net_in_1 in
          let adv_out_enc := ffst@(ffst@adv_out_1) in
          let adv_out_mac := fsnd@(ffst@adv_out_1) in
          let adv_out_msg := fsnd@adv_out_1 in
          let check_out := mverify@(f_id@sk2, adv_out_enc, adv_out_mac) in
          let dec_out := decrypt@(sk1, adv_out_enc) in
          let dec_msg := dec_out in
          let sK' : expr tskey := decode@dec_msg in
          let sign_out := sign@(sK', adv_out_msg) in
          let pK' := pkeygen@sK' in
          let net_in_good := (pK', (sign_out, (adv_out_msg, net_in_1)))%expr in
          let net_in_2 := (eif check_out
                           then net_in_good
                           else (#!, (#!, (#!, net_in_1))))%expr in

          let adv_out_2 := !(tmessage * tsignature)@net_in_2 in
          let adv_out_2_msg := ffst@adv_out_2 in
          let adv_out_2_sig := fsnd@adv_out_2 in
          let verify_out := sverify@(pK, adv_out_2_msg, adv_out_2_sig) in
          verify_out -> adv_out_2_msg == adv_out_msg)%expr.
    Proof.
      repeat
        match goal with
        | |- whp #vtrue => exact whp_true
        | _ => progress cbv [fill_hole refine_hole without_holes choice_ctx]
        | _ => progress rewrite ?decrypt_encrypt, ?decode_encode, ?impl_if, ?if_same, ?feqb_refl
        | _ => rewrite (rewrite_verify mac_correct)       by (solve_eq_fill_hole_r || solve_auth_safe)
        | _ => rewrite (rewrite_verify signature_correct) by (solve_eq_fill_hole_r || solve_auth_safe)
        | |- context[(encrypt@(ekeygen@($?sk), ?nonce, ?msg1))%expr] =>
          progress ( (* speedup: instead of progress, just check that msg2 and msg1 are not syntactically equal *)
              let msg2 := constr:((encode@(skeygen@($ irrelevant)))%expr) in
              rewrite (fill_confidentiality confidentiality sk nonce msg1 msg2)
                by
                  (solve_eq_fill_hole_r ||
                   solve_encrypt_pair
                     (fun _ x _ _ _ =>
                        lazymatch x with
                        | (len@_)%expr => idtac
                        end)
                     (fun _ _ _ _ _ =>
                        eapply ep_transport;
                        [reflexivity |
                         eapply len_encode_skeygen |
                         eapply ep_app]));
              cbv [fill_hole refine_hole without_holes choice_ctx])
        end.
    Qed.
  End Example1AuthConf.

  Section Example2Confidentiality.
    Context {tkey tnonce : type}
            {ekeygen : (trand -> tkey)%etype}
            {random_nonce : (trand -> tnonce)%etype}
            {random_nonce_inj : forall x y,
                whp (random_nonce@x == random_nonce@y -> x == y)}
            {encrypt : (tkey * tnonce * tmessage -> tmessage)%etype}
            {confidentiality :
               @confidentiality_conclusion tkey tnonce
                                           ekeygen encrypt}
            {erase_message : (tmessage -> tmessage)%etype}
            {erase_message_len :
               forall m, eqwhp (len@m) (len@(erase_message@m))}.

    Local Notation encrypt_pair_nonces :=
      (fun k => @encrypt_pair_nonces tkey tnonce ekeygen encrypt k _).

    Definition E2_input : type := tmessage.
    Definition E2_output : type := tmessage.
    Definition E2_state : type := tkey.

    Let K := 1%positive.
    Let rK := pos_pair (0%nat, K)%core.

    Definition E2_init : expr (tlist E2_output * E2_state) :=
      (#cnil, ekeygen@($K))%expr.

    Definition E2_step : expr_with_hole (E2_input * E2_state) (E2_output * E2_state) :=
      (
        let i_s := ewh_hole in
        let msg := ffst@i_s in
        let key := fsnd@i_s in
        (encrypt@(key, random_nonce@($1), msg), key)
      )%ewh.

    Definition E2_step_erase : expr_with_hole (E2_input * E2_state) (E2_output * E2_state) :=
      (
        let i_s := ewh_hole in
        let msg := ffst@i_s in
        let key := fsnd@i_s in
        (encrypt@(key, random_nonce@($1), erase_message@msg), key)
      )%ewh.

    Example example_2_confidentiality n :
        let e := interaction E2_init E2_step n in
        let outputs := (ffst@(e))%expr in
        let e_erase := interaction E2_init E2_step_erase n in
        let outputs_erase := (ffst@e_erase)%expr in
        outputs ≈ outputs_erase.
    Proof.
      intros.
      enough (eqwhp (fsnd@e) (ekeygen@($rK)) /\
              eqwhp (fsnd@e_erase) (ekeygen@($rK)) /\
              exists l l_erase,
                encrypt_pair_nonces rK outputs outputs_erase l l_erase /\
                whp_function l /\
                whp_function l_erase /\
                forall nce msg,
                  (In (nce, msg) l \/ In (nce, msg) l_erase) ->
                  exists i,
                    nce = (random_nonce@($i))%expr /\
                    expr_old n nce) as (_&_&?&?&?&?&?&_)
          by (eapply confidentiality; cbv [encrypt_pair]; eauto).
      revert e outputs e_erase outputs_erase.
      induction n.
      { cbn; cbv [E2_init].
        let r := repeat (setoid_rewrite ffst_pair || setoid_rewrite fsnd_pair) in
        split; [|split];
          [r; reflexivity ..|r].
        do 2 eexists; split; [|split; [|split]].
        - solve_encrypt_pair (fail) idtac.
        - solve_encrypt_pair (fail) idtac.
        - solve_encrypt_pair (fail) idtac.
        - intros; exfalso; intuition eauto using in_nil.
      }
      { cbn [interaction].
        generalize dependent (interaction E2_init E2_step n); intro e.
        generalize dependent (interaction E2_init E2_step_erase n); intro e_erase.
        intros.
        cbv [E2_step E2_step_erase fill_alpha renumber renumber_h fill_hole].
        destruct IHn as
            (Hstate & Hstate_erase &
             l' & l_erase' & Hepn & Hl' & Hl_erase' & Hnms).
        let r :=
            repeat (setoid_rewrite ffst_pair || setoid_rewrite fsnd_pair
                    || setoid_rewrite if_same || setoid_rewrite app_if
                    || setoid_rewrite Hstate
                    || setoid_rewrite Hstate_erase) in
        split; [|split];
          [r; reflexivity ..|r].
        do 2 eexists; split; [|split; [|split]].
        (* TODO clean this part up with better tactics *)
        {
          eapply ep_app.
          eapply ep_pair.
          { eapply ep_encrypt.
            - solve_encrypt_pair (fail) idtac.
              let H := fresh in
              intros H; apply pos_pair_inj_left in H; congruence.
            - eapply ep_transport;
                [reflexivity|eapply erase_message_len|eapply ep_app].
              eapply ep_adv.
              eapply Hepn.
            - eapply ep_adv.
              eapply Hepn.
            - eapply ep_app.
              eapply ep_adv.
              eapply Hepn.
          }
          { eapply Hepn. } }
        { cbv [whp_function].
          intros ????.
          cbn [app In].
          Local Opaque app.
          repeat
            (setoid_rewrite or_False_l || setoid_rewrite or_False_r
             || setoid_rewrite or_refl || setoid_rewrite or_assoc
             || setoid_rewrite app_nil_l || setoid_rewrite app_nil_r
             || setoid_rewrite in_app_iff).
          Local Transparent app.
          intros [] [];
            repeat lazymatch goal with
                   | H : (_, _) = (_, _) |- _ => inversion_clear H
                   end;
            [ apply whp_contract; fold_eqwhp; reflexivity | | |
              solve [eauto] ];
            deny_cond;
            repeat lazymatch goal with
                   | H : _ \/ _ |- _ => destruct H
                   | H : In (?x, ?y) _ |- _ =>
                     destruct (Hnms _ _ (ltac:(eauto using H))) as (?&?&?);
                       clear H;
                       subst;
                       cbn [expr_old] in *
                   | |- whp (~ random_nonce@?x1 == random_nonce@?x2) =>
                     rewrite not_impl_false;
                       apply (whp_impl_trans _ (x1 == x2));
                       [ solve [apply random_nonce_inj]
                       | rewrite <-not_impl_false;
                         apply inequal_rand ]
                   | |- pos_pair _ <> _ => solve [intro; eapply old_different; eauto]
                   | |- _ <> pos_pair _ => solve [intro; eapply old_different; eauto]
                   end.
        }
        { cbv [whp_function].
          intros ????.
          cbn [app In].
          Local Opaque app.
          repeat
            (setoid_rewrite or_False_l || setoid_rewrite or_False_r
             || setoid_rewrite or_refl || setoid_rewrite or_assoc
             || setoid_rewrite app_nil_l || setoid_rewrite app_nil_r
             || setoid_rewrite in_app_iff).
          Local Transparent app.
          intros [] [];
            repeat lazymatch goal with
                   | H : (_, _) = (_, _) |- _ => inversion_clear H
                   end;
            [ apply whp_contract; fold_eqwhp; reflexivity | | |
              solve [eauto] ];
            deny_cond;
            repeat lazymatch goal with
                   | H : _ \/ _ |- _ => destruct H
                   | H : In (?x, ?y) _ |- _ =>
                     destruct (Hnms _ _ (ltac:(eauto using H))) as (?&?&?);
                       clear H;
                       subst;
                       cbn [expr_old] in *
                   | |- whp (~ random_nonce@?x1 == random_nonce@?x2) =>
                     rewrite not_impl_false;
                       apply (whp_impl_trans _ (x1 == x2));
                       [ solve [apply random_nonce_inj]
                       | rewrite <-not_impl_false;
                         apply inequal_rand ]
                   | |- pos_pair _ <> _ => solve [intro; eapply old_different; eauto]
                   | |- _ <> pos_pair _ => solve [intro; eapply old_different; eauto]
                   end.
        }
        { intros n' m'.
          cbn [app In].

          assert (forall A B, (A \/ A \/ B) <-> (A \/ B)) as or_refl_l
              by (intuition idtac).
          Local Opaque app.
          repeat (setoid_rewrite or_False_l || setoid_rewrite or_False_r
                  || setoid_rewrite or_refl || setoid_rewrite or_assoc
                  || setoid_rewrite or_refl_l
                  || setoid_rewrite app_nil_l || setoid_rewrite app_nil_r
                  || setoid_rewrite in_app_iff).
          Local Transparent app.

          intros [Hnm|[Hnm|[Hnm|Hnm]]];
            solve [ inversion Hnm;
                    subst n' m';
                    eexists; split; [reflexivity|];
                    cbv [expr_old index_old]; rewrite pos_pair_inv_r; eauto
                  | edestruct (Hnms _ _ (ltac:(eauto using Hnm)))
                    as (?&?&?); eauto using old_S ]. } }
    Qed.
  End Example2Confidentiality.

  Section Example3HonestKerberos.
    Context {tmac tmkey : type}
            {mkeygen : (trand -> tmkey)%etype}
            {mac : (tmkey * tmessage -> tmac)%etype}
            {mverify : (tmkey * tmessage * tmac -> tbool)%etype}
            {mac_correct :
               @auth_conclusion tmac tmkey tmkey tunit
                                mkeygen f_id funit mac mverify}.

    Context {tkey tnonce : type}
            {ekeygen : (trand -> tkey)%etype}
            {random_nonce : (trand -> tnonce)%etype}
            {random_nonce_inj : forall x y,
                whp (random_nonce@x == random_nonce@y -> x == y)}
            {encrypt : (tkey * tnonce * tmessage -> tmessage)%etype}
            {decrypt : (tkey * tmessage -> tmessage)%etype}
            (decrypt_encrypt : forall k n m,
                eqwhp (decrypt@(ekeygen@($k), encrypt@(ekeygen@($k), n, m))) m)
            {confidentiality :
               @confidentiality_conclusion tkey tnonce
                                           ekeygen encrypt}
            {erase_message : (tmessage -> tmessage)%etype}
            {erase_message_len :
               forall m, eqwhp (len@m) (len@(erase_message@m))}.

    Local Notation encrypt_pair_nonces :=
      (fun k => @encrypt_pair_nonces tmessage tnat len tkey tnonce
                                     ekeygen encrypt k _).

    Definition E3_id := tbool. (* client id *)

    Definition E3_state : type :=
      ((tkey * tmkey) * (tkey * tmkey)) * (* client keys *)
      ((tlist (E3_id * tmessage)) * (* attacker-input (sender, message) log *)
       (tlist (E3_id * tmessage))) (* verified (sender, message) log *)
    .

    Let eK1 := 1%positive.
    Let eK2 := 2%positive.
    Let reK1 := pos_pair (0%nat, eK1)%core.
    Let reK2 := pos_pair (0%nat, eK2)%core.

    Let mK1 := 1%positive.
    Let mK2 := 2%positive.
    Let rmK1 := pos_pair (0%nat, mK1)%core.
    Let rmK2 := pos_pair (0%nat, mK2)%core.

    Definition E3_server_input : type := E3_id * E3_id. (* parties *)
    Definition E3_server_output : type :=
      (tmessage * tmac) * (tmessage * tmac). (* tickets for both parties *)

    Definition E3_server : expr_with_hole (E3_server_input * E3_state)
                                          (E3_server_output * E3_state) :=
      (
        let input := ffst@ewh_hole in
        let state := fsnd@ewh_hole in
        let i := ffst@input in
        let j := fsnd@input in
        let keys := ffst@state in
        let k1 := ffst@keys in
        let k2 := fsnd@keys in
        let ki := (eif i then k1 else k2) in
        let eki := ffst@ki in
        let mki := fsnd@ki in
        let session_key := mkeygen@($1) in
        let ticketi := encode@(j, session_key) in
        let msgi := encrypt@(eki, random_nonce@($2), ticketi) in
        let mmsgi := mac@(mki, msgi) in
        let kj := (eif j then k1 else k2) in
        let ekj := ffst@kj in
        let mkj := fsnd@kj in
        let ticketj := encode@(i, session_key) in
        let msgj := encrypt@(ekj, random_nonce@($3), ticketj) in
        let mmsgj := mac@(mkj, msgj) in
        (((msgi, mmsgi), (msgj, mmsgj)), state)
      )%ewh.

    Definition E3_client_input : type :=
      tbool * (* self *)
      (tmessage * tmac) * (* encrypted ticket *)
      (tbool * (* sign/verify *)
       tmessage * (* message to sign or verify *)
       tmac). (* (verify: tag) *)

    Definition E3_client_output : type := tmac. (* (sign) *)

    Local Notation "'require' a 'fail' b ; c" :=
      (eif a then c else b)%ewh
                            (right associativity,
                             only parsing,
                             at level 100) : ewh_scope.

    Definition E3_client : expr_with_hole (E3_client_input * E3_state)
                                          (E3_client_output * E3_state) :=
      (
        let input := ffst@ewh_hole in
        let state := fsnd@ewh_hole in
        let self := ffst@(ffst@input) in
        let mticket := fsnd@(ffst@input) in
        let operation := fsnd@input in
        let keys := ffst@state in
        let k1 := ffst@keys in
        let k2 := fsnd@keys in
        let kself := (eif self then k1 else k2) in
        let ekself := ffst@kself in
        let mkself := fsnd@kself in
        let eticket := ffst@mticket in
        let ticket_tag := fsnd@mticket in
        require mverify@(mkself, eticket, ticket_tag) fail (#!, state);
          let ticket : expr_with_hole _ (E3_id * tmkey) :=
              decode@(decrypt@(ekself, eticket)) in
          let other := ffst@ticket in
          let session_key := fsnd@ticket in
          let op_type := ffst@(ffst@operation) in
          (eif op_type
           then (* sign *)
             let message := fsnd@(ffst@operation) in
             let log := fsnd@state in
             let input_log := ffst@log in
             let output_log := fsnd@log in
             let new_state := (keys, (fcons@((self, message), input_log),
                                      output_log)) in
             (mac@(session_key, message), new_state)
           else (* verify *)
             let message := fsnd@(ffst@operation) in
             let message_tag := fsnd@operation in
             require mverify@(session_key, message, message_tag)
                     fail (#!, state);
               let log := fsnd@state in
               let input_log := ffst@log in
               let output_log := fsnd@log in
               let new_state :=
                   (keys, (input_log,
                           (fcons@((other, message), output_log)))) in
               (#!, new_state)
          )
      )%ewh.

    Definition E3_input : type := tbool * (E3_server_input * E3_client_input).
    Definition E3_output : type := E3_server_output * E3_client_output.

    Definition E3_init : expr (tlist E3_output * E3_state) :=
      (#cnil, (((ekeygen@($eK1), mkeygen@($mK1)),
                (ekeygen@($eK2), mkeygen@($mK2))),
               (#cnil, #cnil))).

    Definition E3_step : expr_with_hole (E3_input * E3_state)
                                        (E3_output * E3_state) :=
      (
        let input := ffst@ewh_hole in
        let state := fsnd@ewh_hole in
        let server_client := ffst@input in
        (eif server_client
         then
           let server_input := ffst@(fsnd@input) in
           let server := E3_server[(server_input, state)] in
           ((ffst@server, #!), fsnd@server)
         else
           let client_input := fsnd@(fsnd@input) in
           let client := E3_client[(client_input, state)] in
           ((#!, ffst@client), fsnd@client)
        )
      )%ewh.

    Example example_3_authenticity n :
      (
        let e := interaction E3_init E3_step n in
        let log := fsnd@(fsnd@e) in
        let input_log := ffst@log in
        let output_log := fsnd@log in
        forall x,
          whp (f_in@(x, output_log) ->
               f_in@(x, input_log))
      )%expr.
    Proof.
      induction n.
      {
        cbn; cbv [E3_init].
        intros.
        repeat (setoid_rewrite ffst_pair || setoid_rewrite fsnd_pair).
        setoid_rewrite f_in_nil.
        eapply whp_explosion.
      }
      { cbn [interaction].
        generalize dependent (interaction E3_init E3_step n); intro e.
        intros.
        cbv [E3_step E3_server E3_client
                     fill_alpha renumber renumber_h
                     fill_hole refine_hole].
        (* Resulting term is too large to do even a single
           setoid_rewrite ffst_pair in reasonable time.
           We need to exploit sharing in the term structure somehow. *)
    Abort.
  End Example3HonestKerberos.
End Language.
