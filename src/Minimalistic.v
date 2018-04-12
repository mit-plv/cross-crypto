Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Classes.Morphisms.
Require Import Coq.MSets.MSetPositive Coq.FSets.FMapPositive.
Require Import FCF.FCF FCF.Asymptotic FCF.EqDec.
Require Import CrossCrypto.Util CrossCrypto.RatUtil CrossCrypto.RewriteUtil CrossCrypto.MapUtil.
Require Import Lia. (* TODO: remove after removing not_negligible_const *)

Require Import Coq.btauto.Btauto.
Lemma eqb_bool a b : (a ?= b) = negb (xorb a b). Admitted.
Ltac btauto' := btauto.
Ltac btauto := cbv [implb] in *; rewrite ?eqb_bool; rewrite ?eqb_bool in *; btauto'.

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
  Local Notation "f @ x" := (expr_app f x) (left associativity, at level 11, format "f @ x").
  Local Notation "'!' t '@' x" := (@expr_adversarial _ t x%expr) (left associativity, at level 11, format "! t @ x", t at next level).
  Local Notation "'!' '@' x" := (expr_adversarial x%expr) (left associativity, at level 11, format "! @ x").
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
  Global Instance randomness_map_eq_dec {eta} : EqDec (PositiveMap.t (interp_type trand eta)). Admitted.

  Context (cast_rand : forall eta, Bvector eta -> interp_type trand eta).
  Section GenerateRandomness.
    Context (eta:nat).

    Definition genrand : Comp _ := (r <-$ {0,1}^eta; ret (cast_rand eta r)).
    (* TODO: use [genrand] in the remainder of this section *)

    Definition generate_randomness_single i rndC :=
      rnds' <-$ rndC;
        ri <-$ {0,1}^eta;
        ret (PositiveMap.add i (cast_rand eta ri) rnds').

    Definition generate_randomness idxs
      : Comp (PositiveMap.t (interp_type trand eta))
      := PositiveSet.fold generate_randomness_single
                          idxs
                          (ret (PositiveMap.empty _)).

    Lemma empty_randomness :
      Comp_eq (generate_randomness PositiveSet.empty)
              (ret (PositiveMap.empty _)).
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
        rewrite add_generate_randomness with (s'0:=s') by eassumption.
        rewrite add_generate_randomness with
            (s0:=PositiveSet.union s (PositiveSet.remove new_elt idxs2))
            (s'0:=PositiveSet.union s' idxs2) (x:=new_elt).
        Focus 2. {
          cbv [PositiveSetProperties.Add]; intros.
          rewrite (union_remove s' idxs2 new_elt).
          eapply PositiveSetProperties.union_Add.
          assumption. } Unfocus.
        Focus 2. {
          rewrite !PositiveSet.union_spec, PositiveSet.remove_spec.
          assert (new_elt = new_elt) by reflexivity.
          tauto. } Unfocus.

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
  Local Notation "a == b" := (feqb@(a, b)) : expr_scope.
  Arguments feqb {_}.
  Context (interp_feqb : forall t eta (v1 v2:interp_type t eta),
              inspect_vbool (interp_func feqb (interp_pair v1 v2))
              = eqb v1 v2).

  Context (fand : (tbool * tbool -> tbool)%etype)
          (interp_fand : forall eta v1 v2,
              inspect_vbool (interp_func fand (interp_pair v1 v2)) =
              andb (inspect_vbool v1) (inspect_vbool (eta:=eta) v2)).
  Local Notation "a /\ b" := (fand@(a, b)) : expr_scope.
  Context (f_or : (tbool * tbool -> tbool)%etype)
          (interp_f_or : forall eta v1 v2,
              inspect_vbool (interp_func f_or (interp_pair v1 v2)) =
              orb (inspect_vbool v1) (inspect_vbool (eta:=eta) v2)).
  Local Notation "a \/ b" := (f_or@(a, b)) : expr_scope.
  Context (fimpl : (tbool * tbool -> tbool)%etype)
          (interp_fimpl : forall eta v1 v2,
              inspect_vbool (interp_func fimpl (interp_pair v1 v2)) =
              implb (inspect_vbool v1) (inspect_vbool (eta:=eta) v2)).
  Local Notation "a -> b" := (fimpl@(a, b)) : expr_scope.
  Context (fnegb : (tbool -> tbool)%etype)
          (interp_fnegb : forall eta v,
              inspect_vbool (interp_func fnegb v) =
              negb (inspect_vbool (eta:=eta) v)).
  Local Notation "~ a" := (fnegb@a) : expr_scope.
  Context (ite : forall t, (tbool * t * t -> t)%etype).
  Arguments ite {_}.
  Context (interp_ite :
             forall t eta b (v1 v2:interp_type t eta),
               interp_func ite (interp_pair (interp_pair b v1) v2) =
               if inspect_vbool b then v1 else v2).
  Arguments interp_ite {_ _}.
  Local Notation "'eif' b 'then' x 'else' y" :=
    (ite@(b,x,y))
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


  Local Existing Instance eq_subrelation | 5.

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
          assert (forall xy,
                     Comp_eq (ret negb (fst xy ?= snd xy))
                             (ret negb (snd xy ?= fst xy))) as E1.
          {
            intros.
            setoid_rewrite eqb_symm at 2.
            reflexivity.
          }
          setoid_rewrite E1 at 2; clear E1.
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
      intro.
      assert (false = true).
      {
        rewrite <- inspect_vfalse with (eta := eta).
        rewrite <- inspect_vtrue with (eta := eta).
        f_equal; eauto.
      }
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

      cut (|Pr [er <-$ ER;
                x <-$ XR er;
                ret Z er x] -
            Pr [er <-$ ER; y <-$ Y'; ret Z er y]|
           <=
           Pr [er <-$ ER;
               x <-$ XR er;
               ret negb (inspect_vbool x)]); try solve [intuition].

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
          (A := Comp (PositiveMap.t (interp_type trand eta)))
          (P := fun s r =>
                  forall m,
                    In m (getSupport r) ->
                    forall x,
                      PositiveMap.In x m -> PositiveSet.In x s)
          (f := generate_randomness_single eta)
          (i := ret PositiveMap.empty (interp_type trand eta)).
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
                (ret PositiveMap.empty (interp_type trand eta)).
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
                 ret PositiveMap.remove x r).
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
                    ret PositiveMapProperties.filter
                        (fun k _ =>
                           PositiveSet.mem k mask) r)).
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
                           then PositiveMap.add x (cast_rand eta a) fm
                           else PositiveMap.remove x fm))
                     (fm <-$ (r <-$ generate_randomness eta s;
                              ret PositiveMapProperties.filter
                                  (fun k _ => PositiveSet.mem k mask) r);
                      ret if PositiveSet.mem x mask
                          then PositiveMap.add x (cast_rand eta a) fm
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
                    ret PositiveMapProperties.filter
                        (fun k _ =>
                           PositiveSet.mem k s) r)).
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
          (f := fun r => ret interp_fixed e eta adv r) at 2.

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
                               (interp_fixed b eta (adv eta e) r)))).
      rewrite Bind_assoc_2 with
          (g := (fun e r =>
                   ret negb (inspect_vbool
                               (interp_fixed a eta (adv eta e) r)))).

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

  Ltac contract_trans_whp :=
    repeat
      match goal with
      | H0 : whp (?a -> ?b) |- _ =>
        match goal with
        | H1 : whp (b -> ?c) |- _ =>
          assert (whp (a -> c)) by
              (eapply (whp_impl_trans _ _ _ H0 H1));
          clear H0; clear H1
        | H1 : whp (a -> b -> ?c) |- _ =>
          assert (whp (a -> c)) by
              (eapply (whp_mp_cond _ _ _ H0 H1));
          clear H0; clear H1
        end
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
          etransitivity.
          Focus 2. {
            apply Proper_Bind_generate_randomness.
            intros.
            rewrite find_update_in
              by (apply PositiveMapProperties.F.in_find_iff; congruence).
            eapply reflexivity. } Unfocus.
          rewrite Bind_unused.
          rewrite H0; reflexivity. }
        {
          etransitivity.
          Focus 2. {
            apply Proper_Bind_generate_randomness.
            intros.
            rewrite find_update_not_in
              by (apply PositiveMapProperties.F.not_find_in_iff; congruence).
            eapply reflexivity. } Unfocus.

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

        (* FIXME: this might be false ~ andreser *)
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
    eapply (H (den + n0)%nat ltac:(constructor; omega) ltac:(omega)); clear H.
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

    Lemma if_comm a b c :
      eqwhp (a -> b -> c) (b -> a -> c).
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
  End MoreLemmas.

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

    Fixpoint fill_hole {hole t}
             (E : @expr_with_hole hole t) (e : expr hole) : expr t :=
      match E with
      | ewh_hole => e
      (* recurse *)
      | ewh_const c => #c
      | ewh_random i => $i
      | ewh_adversarial x => !@(fill_hole x e)
      | ewh_app f x => f@(fill_hole x e)
      | ewh_pair a b => (fill_hole a e, fill_hole b e)
      end.

    Fixpoint fill_hole_section {hole t} (e : expr t)
      : @expr_with_hole hole t :=
      match e with
      | expr_const c => ewh_const c
      | expr_random i => ewh_random i
      | expr_adversarial e => ewh_adversarial (fill_hole_section e)
      | expr_app f e => ewh_app f (fill_hole_section e)
      | expr_pair e1 e2 =>
        ewh_pair (fill_hole_section e1) (fill_hole_section e2)
      end.

    Lemma fill_hole_section_section {hole} {t} (x : expr hole) (e : expr t) :
      fill_hole (fill_hole_section e) x = e.
    Proof.
      induction e; cbn [fill_hole_section fill_hole]; try reflexivity.
      - rewrite IHe; reflexivity.
      - rewrite IHe; reflexivity.
      - rewrite IHe1; rewrite IHe2; reflexivity.
    Qed.

    Lemma fill_eqwhp_internal {hole t} (e1 e2 : expr hole)
          (E : @expr_with_hole hole t) :
      whp (e1 == e2 -> fill_hole E e1 == fill_hole E e2).
    Proof.
      unpack_whp.
      match goal with
      | |- ?x = true => change (is_true x)
      end.
      autorewrite with push_is_true.
      intros.
      induction E; cbn [fill_hole interp_fixed]; congruence.
    Qed.

    Corollary rewrite_eqwhp_internal {hole} (e1 e2 : expr hole)
              (E : @expr_with_hole hole tbool) :
      eqwhp (e1 == e2 -> fill_hole E e1) (e1 == e2 -> fill_hole E e2).
    Proof.
      eapply whp_cond_rew.
      eapply fill_eqwhp_internal.
    Qed.

    Global Instance Proper_fill_hole {t1 t2} (C : @expr_with_hole t1 t2)
      : Proper (eqwhp ==> eqwhp) (fill_hole C).
    Proof.
      intros x y.
      eapply whp_impl.
      eapply fill_eqwhp_internal.
    Qed.

    Lemma fill_cond_true a {t} (e e' : expr t) (C : expr_with_hole tbool) :
      eqwhp (a -> fill_hole C (eif a then e else e')) (a -> fill_hole C e).
    Proof.
      cbv [eqwhp].
      rewrite <-whp_impl_eq.
      assert (whp (a -> (eif a then e else e') == e)) by eapply if_true_internal.
      pose proof (@fill_eqwhp_internal t _ (eif a then e else e') e C).
      contract_trans_whp.
      eauto.
    Qed.

    Lemma fill_cond_false a {t} (e e' : expr t) (C : expr_with_hole tbool) :
      eqwhp (~a -> fill_hole C (eif a then e else e')) (~a -> fill_hole C e').
    Proof.
      cbv [eqwhp].
      rewrite <-whp_impl_eq.
      assert (whp (~a -> (eif a then e else e') == e')) by eapply if_false_internal.
      pose proof (@fill_eqwhp_internal t _ (eif a then e else e') e' C).
      contract_trans_whp.
      eauto.
    Qed.

    Fixpoint compose_hole {t1 t2 t3}
             (A : @expr_with_hole t1 t2) (B : @expr_with_hole t2 t3)
      : @expr_with_hole t1 t3 :=
      match B with
      | ewh_hole => A
      (* recurse *)
      | ewh_const c => ewh_const c
      | ewh_random i => ewh_random i
      | ewh_adversarial x => ewh_adversarial (compose_hole A x)
      | ewh_app f x => ewh_app f (compose_hole A x)
      | ewh_pair a b => ewh_pair (compose_hole A a) (compose_hole A b)
      end.

    Lemma fill_compose_hole {t1 t2 t3}
          (A : @expr_with_hole t1 t2) (B : @expr_with_hole t2 t3)
          (e : expr t1) :
      eqwhp (fill_hole (compose_hole A B) e) (fill_hole B (fill_hole A e)).
    Proof.
      revert A e; induction B; intros A e; cbn [fill_hole compose_hole];
        try reflexivity.
      - rewrite IHB; reflexivity.
      - rewrite IHB; reflexivity.
      - rewrite IHB1; rewrite IHB2; reflexivity.
    Qed.
  End Holes.

  Ltac build_context x e :=
    match e with
    | x => uconstr:(ewh_hole)
    | expr_const ?c => uconstr:(ewh_const c)
    | expr_random ?i => uconstr:(ewh_random i)
    | expr_adversarial ?e => let E := build_context x e in
                             uconstr:(ewh_adversarial E)
    | expr_app ?f ?e => let E := build_context x e in uconstr:(ewh_app f E)
    | expr_pair ?e1 ?e2 => let E1 := build_context x e1 in
                           let E2 := build_context x e2 in
                           uconstr:(ewh_pair E1 E2)
    | fill_hole ?B ?e => let A := build_context x e in
                         uconstr:(compose_hole A B)
    | _ => uconstr:(fill_hole_section e)
    end.

  Ltac internal_rewrite :=
    match goal with
    | |- context[(?e == ?e' -> ?b)%expr] =>
      let C := build_context e b in
      let H := fresh in
      pose proof (rewrite_eqwhp_internal e e' C) as H;
      cbn [fill_hole compose_hole] in H;
      repeat ((rewrite fill_hole_section_section in H) +
              (rewrite fill_compose_hole in H));
      rewrite H; clear H
    end.

  Ltac rewrite_fill_cond_true :=
    match goal with
    | |- context[(?a -> ?d)%expr] =>
      match d with
      | context[(eif ?a then ?b else ?c)%expr] =>
        let C := build_context (eif a then b else c)%expr d in
        let H := fresh in
        pose proof (fill_cond_true a b c C) as H;
        cbn [fill_hole compose_hole] in H;
        repeat ((rewrite fill_hole_section_section in H) +
                (rewrite fill_compose_hole in H));
        rewrite H; clear H
      end
    end.

  Ltac rewrite_fill_cond_false :=
    match goal with
    | |- context[(~ ?a -> ?d)%expr] =>
      match d with
      | context[(eif ?a then ?b else ?c)%expr] =>
        let C := build_context (eif a then b else c)%expr d in
        let H := fresh in
        pose proof (fill_cond_false a b c C) as H;
        cbn [fill_hole compose_hole] in H;
        repeat ((rewrite fill_hole_section_section in H) +
                (rewrite fill_compose_hole in H));
        rewrite H; clear H
      end
    end.

  Section Authenticity.
    Context {tmessage ttag tskey tvkey : type}
            {skeygen : (trand -> tskey)%etype}
            {vkeygen : (tskey -> tvkey)%etype}
            {auth : (tskey * tmessage -> ttag)%etype}
            {verify : (tvkey * tmessage * ttag -> tbool)%etype}.

    Inductive auth_safe' (sk : positive) :
      forall {t}, expr t -> list (expr tmessage) -> Prop :=
    | asauth m l : auth_safe' sk m l ->
                   auth_safe' sk (auth@(skeygen@$sk, m)) (m :: l)
    | asverify m t : auth_safe' sk (verify@(vkeygen@(skeygen@$sk), m, t)) nil
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
        let ve := verify@(vkeygen@(skeygen@$sk), m, s) in
        whp (ve -> expr_in m l).

    Definition auth_safe (sk : positive)
               {t} (m : expr t) (l' : list (expr tmessage)) : Prop :=
      exists l, auth_safe' sk m l /\ (forall x, In x l -> In x l').

    Definition auth_conclusion :=
      forall (sk : positive)
             (s : expr ttag)
             (l : list (expr tmessage))
             (m : expr tmessage),
        auth_safe sk s l ->
        let ve := verify@(vkeygen@(skeygen@$sk), m, s) in
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
        + rewrite if_comm.
          eapply whp_contract.
          assert (In x l') by (eapply H; eauto); clear H.
          eapply expr_in_eq; eauto.
        + rewrite or_if.
          rewrite_fill_cond_false.
          eapply whp_contract.
          eauto.
    Qed.

    Lemma auth'_auth : auth'_conclusion -> auth_conclusion.
    Proof.
      cbv [auth'_conclusion auth_conclusion].
      intros A'C sk s l' m [l [AS' I]].
      specialize (A'C sk s l m AS').
      pose proof (expr_in_extend m l l' I).
      contract_trans_whp; eauto.
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
          rewrite_fill_cond_true.
          eapply whp_impl_refl.
        + assert (forall a b c,
                     whp (~a -> b -> c) ->
                     whp (~a -> a \/ b -> c))
            as disj_hyp_false
            by (intros; unpack_whp; btauto).
          eapply disj_hyp_false; clear disj_hyp_false.
          rewrite_fill_cond_false.
          eapply whp_contract.
          eauto.
    Qed.

    Lemma rewrite_condition {t : type} b (e1 e1' e2 : expr t) :
      whp ((b -> e1 == e1') ->
           (eif b then e1 else e2) == (eif b then e1' else e2)).
      rewrite (impl_if b).
      eapply (whp_split b).
      - repeat rewrite_fill_cond_true.
        eapply whp_contract.
        eapply whp_impl_refl.
      - repeat rewrite_fill_cond_false.
        do 2 eapply whp_contract.
        fold_eqwhp; reflexivity.
    Qed.

    Context {tmessage ttag tskey tvkey : type}
            {skeygen : (trand -> tskey)%etype}
            {vkeygen : (tskey -> tvkey)%etype}
            {auth : (tskey * tmessage -> ttag)%etype}
            {verify : (tvkey * tmessage * ttag -> tbool)%etype}
            {auth_correct : @auth_conclusion tmessage ttag tskey tvkey
                                             skeygen vkeygen auth verify}.
    Fixpoint choice_ctx {t1 t2} m (C : expr_with_hole t2)
             (l0 : expr t1) (l : list (expr t1)) :=
      match l with
      | nil => fill_hole C l0
      | cons l1 l => (eif m == l0
                      then fill_hole C l0
                      else choice_ctx m C l1 l)%expr
      end.

    Lemma fill_if_comm {t1 t2} (C : expr_with_hole t2) a (b c : expr t1) :
      eqwhp (fill_hole C (eif a then b else c))
            (eif a then fill_hole C b else fill_hole C c).
    Proof.
      eapply (whp_split a);
        [do 2 rewrite_fill_cond_true | do 2 rewrite_fill_cond_false];
        eapply whp_contract; fold_eqwhp; reflexivity.
    Qed.

    Lemma choice_ctx_as_fill {t1 t2}
          m (C : expr_with_hole t2) l0 (l : list (expr t1)) :
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

    Let auth_safe := @auth_safe tmessage ttag tskey tvkey
                                skeygen vkeygen auth verify.

    Lemma rewrite_verify sk (s : expr ttag) l0 l m {t}
          (A : expr_with_hole t) (B : expr t) :
      auth_safe sk _ s (cons l0 l) ->
      let ve := verify@(vkeygen@(skeygen@($sk)), m, s) in
      eqwhp (eif ve then fill_hole A m else B)
            (eif ve then choice_ctx m A l0 l else B).
    Proof.
      intros.

      assert (whp (ve -> fill_hole A m == choice_ctx m A l0 l)).
      {
        rewrite choice_ctx_as_fill.
        assert (whp (ve -> m == choice m l0 l)).
        {
          assert (whp (ve -> expr_in m (cons l0 l)))
            by eauto using auth_correct.
          pose proof choice_eq m l0 l.
          contract_trans_whp; eauto.
        }
        assert (whp (m == choice m l0 l ->
                     fill_hole A m == fill_hole A (choice m l0 l)))
          by eapply fill_eqwhp_internal.
        contract_trans_whp; eauto.
      }
      eapply whp_impl.
      - eapply rewrite_condition.
      - eauto.
    Qed.

    (* if we have a term of the form
     * eif verify pkey m s then A(m) else B
     * and we have all the side conditions so that
     * m in l given verify
     * we can rewrite this to
     * eif verify pkey m s then A(choice(l)) else B
     * where choice(l) is
     * choice([x]) => x
     * choice(x::l) => eif m == x then x else choice(l)
     *
     * finally, we should further rewrite it to commute A past the choice
     *
     * if l is empty, we can rewrite the whole thing to B
    *)
  End AuthRewriting.

  Section Encrypt.
    Context {tmessage : type}
            {eq_len : (tmessage * tmessage -> tbool)%etype}
            {tkey tnonce : type}
            {keygen : (trand -> tkey)%etype}
            {encrypt : (tkey * tnonce * tmessage -> tmessage)%etype}.

    (* The secret key is used only as the input to encrypt *)
    Inductive encrypt_safe (sk : positive) : forall {t}, expr t -> Prop :=
    | esencrypt n m :
        encrypt_safe sk n ->
        encrypt_safe sk m -> (* No key cycles *)
        encrypt_safe sk (encrypt@(keygen@($sk), n, m))
    | esrand_neq (i:positive) : i <> sk -> encrypt_safe sk ($i)
    (* boring recursion: *)
    | esconst t v : @encrypt_safe sk t #v
    | esfunc {t1 t2} (f : func t1 t2) e : encrypt_safe sk e -> encrypt_safe sk (f@e)
    | esadv  {t1 t2} (e : expr t1) : encrypt_safe sk e -> encrypt_safe sk (!t2@e)
    | espair {t1 t2} (e1: expr t1) (e2: expr t2) :
        encrypt_safe sk e1 ->
        encrypt_safe sk e2 ->
        encrypt_safe sk (e1, e2).

    (* This proposition says that message m is encrypted using
       secret key sk under nonce n somewhere in an expression. *)
    Inductive encrypts (sk : positive)
              (n : expr tnonce) (m : expr tmessage) : forall {t}, expr t -> Prop :=
    | encs_encrypt : encrypts sk n m (encrypt@(keygen@($sk), n, m))
    (* boring recursion: *)
    | encs_func {t1 t2} (f : func t1 t2) e : encrypts sk n m e -> encrypts sk n m (f@e)
    | encs_adv  {t1 t2} (e : expr t1) : encrypts sk n m e -> encrypts sk n m (!t2@e)
    | encs_pair_l {t1 t2} (e1 : expr t1) (e2 : expr t2) :
        encrypts sk n m e1 -> encrypts sk n m (e1, e2)
    | encs_pair_r {t1 t2} (e1 : expr t1) (e2 : expr t2) :
        encrypts sk n m e2 -> encrypts sk n m (e1, e2).

    (* Whenever nonces are equal, the corresponding messages are also
       equal.

       Note that this definition doesn't account for birthday attacks. *)
    Definition no_nonce_reuse (sk : positive) {t} (e : expr t) : Prop :=
      forall n1 m1 n2 m2, encrypts sk n1 m1 e -> encrypts sk n2 m2 e -> whp (n1 == n2 -> m1 == m2).

    (* Equality except for equal-length inputs to encrypt *)
    Inductive eq_mod_enc (sk : positive) : forall {t}, expr t -> expr t -> Prop :=
    | eqe_refl {t} e : @eq_mod_enc sk t e e
    | eqe_encrypt n m m' :
        whp (eq_len@(m, m')) ->
        eq_mod_enc sk
                   (encrypt@(keygen@($sk), n, m ))
                   (encrypt@(keygen@($sk), n, m'))
    (* boring recursion: *)
    | eqe_func {t1 t2} (f : func t1 t2) e e' : eq_mod_enc sk e e' -> eq_mod_enc sk (f@e) (f@e')
    | eqe_adv {t1 t2} (e e' : expr t1) : eq_mod_enc sk e e' -> eq_mod_enc sk (!t2@e) (!t2@e')
    | eqe_pair {t1 t2} (e1 e1' : expr t1) (e2 e2' : expr t2) :
        eq_mod_enc sk e1 e1' ->
        eq_mod_enc sk e2 e2' ->
        eq_mod_enc sk (e1, e2) (e1', e2').

    (* If the secret key is used correctly, and nonces aren't reused,
       then we can replace the inputs to encryptions with anything. *)
    Definition confidentiality_conclusion :=
      forall (sk : positive) {t} (e e' : expr t),
        encrypt_safe sk e ->
        encrypt_safe sk e' ->
        no_nonce_reuse sk e ->
        no_nonce_reuse sk e' ->
        eq_mod_enc sk e e' ->
        indist e e'.

    (* Syntactic structure of compliant terms *)
    Inductive enc_holes (sk : positive) {hole : Type} : type -> Type :=
    | ench_const {t} (_:forall eta, interp_type t eta) : enc_holes sk t
    | ench_random (idx:positive) : idx <> sk -> enc_holes sk trand
    | ench_adversarial t1 t2 (_:enc_holes sk t1) : enc_holes sk t2
    | ench_func {t1 t2} (_:func t1 t2) (_:enc_holes sk t1) :
        enc_holes sk t2
    | ench_pair {t1 t2} (_:enc_holes sk t1) (_:enc_holes sk t2) :
        enc_holes sk (t1 * t2)
    | ench_encrypt (_:hole) : enc_holes sk tmessage.

    Fixpoint fill_enc_holes {sk : positive} {hole : Type}
             (nonce : hole -> expr tnonce)
             (message : hole -> expr tmessage)
             {t} (eh : @enc_holes sk hole t) : expr t :=
      match eh with
      | ench_const _ x => #x
      | ench_random _ idx _ => $idx
      | ench_adversarial _ t1 t2 eh' => !t2@(fill_enc_holes nonce message eh')
      | ench_func _ f      eh' => f@(fill_enc_holes nonce message eh')
      | ench_pair _ eh1 eh2 => (fill_enc_holes nonce message eh1, fill_enc_holes nonce message eh2)
      | ench_encrypt _ h => encrypt@(keygen@($sk), nonce h, message h)
      end.

    Lemma fill_safe :
      forall sk {hole} nonce message {t} (eh : @enc_holes sk hole t),
        (forall h, encrypt_safe sk (nonce h)) ->
        (forall h, encrypt_safe sk (message h)) ->
        encrypt_safe sk (fill_enc_holes nonce message eh).
    Proof.
      induction eh;
        cbn [fill_enc_holes];
        econstructor; eauto.
    Qed.

    Lemma fill_enc_holes_ind {sk hole}
          nonce message
          (P : forall {t}, expr t -> Prop) :
      (forall h, encrypt_safe sk (nonce h)) ->
      (forall h, encrypt_safe sk (message h)) ->
      (forall {t} x, @P t (#x)%expr) -> (* WHY do we need a scope annotation here *)
      (forall idx, idx <> sk -> P ($idx)%expr) -> (* and here? *)
      (forall t1 t2 (e' : expr t1), P e' ->  P (!t2@e')) ->
      (forall t1 t2 (f : func t1 t2) e', encrypt_safe sk e' -> P e' -> P (f@e')) ->
      (forall t1 e1 t2 e2, @P t1 e1 -> @P t2 e2 -> P (e1, e2)%expr) -> (* and here? *)
      (forall h, P (encrypt@(keygen@($sk), nonce h, message h))) ->
      forall {t} (eh : @enc_holes sk hole t),
        P (fill_enc_holes nonce message eh).
    Proof.
      induction eh; eauto using fill_safe.
    Qed.

    Ltac expr_head x :=
      match x with
      | expr_const _ => idtac
      | expr_random _ => idtac
      | expr_adversarial _ => idtac
      | expr_app _ _ => idtac
      | expr_pair _ _ => idtac
      | _ => fail
      end.

    Lemma encrypts_fill :
      forall sk {hole} nonce message {t} (eh : @enc_holes sk hole t) n m,
        (forall h, encrypt_safe sk (nonce h)) ->
        (forall h, encrypt_safe sk (message h)) ->
        (forall h, encrypts sk n m (nonce h) ->
                   exists h', n = nonce h' /\ m = message h') ->
        (forall h, encrypts sk n m (message h) ->
                   exists h', n = nonce h' /\ m = message h') ->
        encrypts sk n m (fill_enc_holes nonce message eh) ->
        exists h, n = nonce h /\ m = message h.
    Proof.
      intros ? ? ? ? t eh ? ? ? ? ? ? E.
      revert t eh E.
      refine (@fill_enc_holes_ind
                _ _
                nonce message (fun _ e =>
                                 encrypts sk n m e ->
                                 exists h, _)
                _ _ _ _ _ _ _ _); eauto;
        intros;
        repeat match goal with
               | [ H : @existT type _ ?x ?y = @existT type _ ?x ?y' |- _ ] =>
                 assert (y = y') by
                     (eapply inj_pair2_eq_dec;
                      eauto using EqDec_dec, eqdec_type);
                   (subst y || subst y');
                   clear H
               | [ H : encrypts _ _ _ ?e |- _ ] =>
                 expr_head e;
                   inversion H; clear H
               | [ H : encrypt_safe _ ?e |- _ ] =>
                 expr_head e;
                   inversion H; clear H
               | [ _ : _ = ?t |- _ ] => subst t
               | [ _ : ?x <> ?x |- _ ] => congruence
               | _ => eauto
               end.
    Qed.

    Lemma fill_no_reuse :
      forall sk {hole} nonce message {t} (eh : @enc_holes sk hole t),
        (forall h, encrypt_safe sk (nonce h)) ->
        (forall h, encrypt_safe sk (message h)) ->
        (forall n m h, encrypts sk n m (nonce h) ->
                   exists h', n = nonce h' /\ m = message h') ->
        (forall n m h, encrypts sk n m (message h) ->
                   exists h', n = nonce h' /\ m = message h') ->
        (forall h1 h2, whp (nonce h1 == nonce h2 -> message h1 == message h2)) ->
        no_nonce_reuse sk (fill_enc_holes nonce message eh).
    Proof.
      unfold no_nonce_reuse.
      intros.
      repeat match goal with
             | [ H : encrypts _ ?n' ?m' _ |- _ ] =>
               edestruct encrypts_fill with (n := n') (m := m')
                 as [? []]; eauto; clear H
             end.
      subst; eauto.
    Qed.

    Lemma fill_mod_enc :
      forall sk {hole} nonce msg1 msg2 {t} (eh : @enc_holes sk hole t),
        (forall h, whp (eq_len@(msg1 h, msg2 h))) ->
        eq_mod_enc sk
                   (fill_enc_holes nonce msg1 eh)
                   (fill_enc_holes nonce msg2 eh).
    Proof.
      induction eh; cbn [fill_enc_holes]; econstructor; eauto.
    Qed.

    Lemma fill_confidentiality sk {hole} nonce msg1 msg2 {t}
          (eh : @enc_holes sk hole t) :
      (forall h, encrypt_safe sk (nonce h)) ->
      (forall h, encrypt_safe sk (msg1 h)) ->
      (forall h, encrypt_safe sk (msg2 h)) ->
      (forall n m h, encrypts sk n m (nonce h) ->
                     exists h', n = nonce h' /\ m = msg1 h') ->
      (forall n m h, encrypts sk n m (nonce h) ->
                     exists h', n = nonce h' /\ m = msg2 h') ->
      (forall n m h, encrypts sk n m (msg1 h) ->
                     exists h', n = nonce h' /\ m = msg1 h') ->
      (forall n m h, encrypts sk n m (msg2 h) ->
                     exists h', n = nonce h' /\ m = msg2 h') ->
      (forall h1 h2, whp (nonce h1 == nonce h2 -> msg1 h1 == msg1 h2)) ->
      (forall h1 h2, whp (nonce h1 == nonce h2 -> msg2 h1 == msg2 h2)) ->
      (forall h, whp (eq_len@(msg1 h, msg2 h))) ->
      confidentiality_conclusion ->
      indist (fill_enc_holes nonce msg1 eh)
             (fill_enc_holes nonce msg2 eh).
    Proof.
      intros;
        repeat match goal with
               | [ H : confidentiality_conclusion |- indist _ _ ] =>
                 eapply H
               | [ |- encrypt_safe _ _ ] => eauto using fill_safe
               | [ |- no_nonce_reuse _ _ ] => eauto using fill_no_reuse
               | [ |- eq_mod_enc _ _ _ ] => eauto using fill_mod_enc
               end.
    Qed.

    (* A nonce scheme that always picks constant nonces is safe from reuse:
       In the formula
           whp (nonce_i = nonce_j -> message_i = message_j)
       the antecedent is false with high probability unless i = j
       in which case the consequent is true with high probability. *)
    Lemma constant_nonce_no_reuse {hole}
          (n : hole -> expr tnonce)
          (N : hole -> _) (m : hole -> expr tmessage) :
      (forall h, n h = expr_const (N h)) ->
      (forall h1 h2 : hole, h1 = h2 \/ h1 <> h2) ->
      (forall (h1 h2 : hole) eta, N h1 eta = N h2 eta -> h1 = h2) ->
      forall h1 h2, whp (n h1 == n h2 -> m h1 == m h2).
    Proof.
      intros C hole_dec NI h1 h2.
      destruct (hole_dec h1 h2).
      - subst h2.
        unpack_whp.
        repeat match goal with
               | |- context [?a ?= ?b] => destruct (a ?= b) eqn:?
               | H : _ = _ |- _ =>
                 rewrite eqb_leibniz in H; rewrite H in *; clear H
               | H : _ = _ |- _ => rewrite eqb_refl in H; discriminate H
               | _ => reflexivity
               end.
      - unpack_whp.
        repeat match goal with
               | |- context [?a ?= ?b] =>
                 destruct (a ?= b) eqn:?
               | H : _ = _ |- _ => rewrite eqb_leibniz in H
               | H : context[n _] |- _ => rewrite C in H; cbv in H
               | H : N _ _ = N _ _ |- _ =>
                 apply NI in H; rewrite H in *; clear H
               | H: _ = _ |- _ => rewrite eqb_refl in H; discriminate H
               | _ => reflexivity
               end.
    Qed.
  End Encrypt.

  Section ExampleProtocol1.
    Context {tmessage : type}
            {eq_len : (tmessage * tmessage -> tbool)%etype}.
    Context {tsignature tskey tpkey : type}.

    Context {skeygen : (trand -> tskey)%etype} (* secret key generation  *)
            {pkeygen : (tskey -> tpkey)%etype} (* public part of key *)
            {sign : (tskey * tmessage -> tsignature)%etype}
            {sverify : (tpkey * tmessage * tsignature -> tbool)%etype}.

    Context {signature_correct :
               @auth_conclusion
                 tmessage
                 tsignature tskey tpkey skeygen pkeygen sign sverify}.

    Context {tmac tmkey : type}
            {mkeygen : (trand -> tmkey)%etype}
            {idmkey : (tmkey -> tmkey)%etype}
            {mac : (tmkey * tmessage -> tmac)%etype}
            {mverify : (tmkey * tmessage * tmac -> tbool)%etype}.

    Context {mac_correct :
               @auth_conclusion tmessage tmac tmkey tmkey
                                mkeygen idmkey mac mverify}.
    Context {tkey tnonce : type}
            {ekeygen : (trand -> tkey)%etype}
            {encrypt : (tkey * tnonce * tmessage -> tmessage)%etype}
            {decrypt : (tkey * tmessage -> tmessage)%etype}.

    Context {confidentiality :
               @confidentiality_conclusion tmessage eq_len
                                           tkey tnonce ekeygen encrypt}.

    Context {skey2message : (tskey -> tmessage)%etype}
            {message2skey : (tmessage -> tskey)%etype}.

    (* constant nonce *)
    Context {N : forall eta, interp_type tnonce eta}.
    Context  {tlist : type -> type}
             {cnil : forall t eta, interp_type (tlist t) eta}
             {fcons : forall t, (t * tlist t -> tlist t)%etype}.
    Arguments cnil {_}.
    Arguments fcons {_}.

    Context {ffst : forall t1 t2, (t1 * t2 -> t1)%etype}
            {fsnd : forall t1 t2, (t1 * t2 -> t2)%etype}.
    Arguments ffst {_ _}.
    Arguments fsnd {_ _}.

    Local Open Scope list_scope.
    Context (skn1 skn2 Kn : positive)
            (nodup : NoDup (skn1 :: skn2 :: Kn :: nil)).

    Section Protocol1Rewrite.
      (* FIXME lots of definitions here get leaked.  It's nice to be
         able to talk about them outside this section for proving things
         about them, so the best thing to do here may be to move the
         whole thing inside its own module later. *)

      Inductive protocol1_rewrite_state :=
      | Actual
      | ElimDec
      | RewriteEnc.

      Variable (s : protocol1_rewrite_state).

      Definition sk1 := ekeygen@($skn1).
      Definition sk2 := mkeygen@($skn2).
      Definition sK := skeygen@($Kn).
      Definition msK := skey2message@sK.
      Definition enc_out :=
        encrypt@(sk1, #N, match s with
                          | RewriteEnc => #!
                          | _ => msK
                          end).
      Definition mac_out := mac@(sk2, enc_out).
      Definition net_in_1 := (enc_out, mac_out)%expr.
      Definition adv_out_1 := !(tmessage * tmac * tmessage)@net_in_1.

      Definition adv_out_enc := ffst@(ffst@adv_out_1).
      Definition adv_out_mac := fsnd@(ffst@adv_out_1).
      Definition adv_out_msg := fsnd@adv_out_1.
      Definition check_out := mverify@(idmkey@sk2, adv_out_enc, adv_out_mac).
      Definition dec_out :=
        match s with
        | Actual => decrypt@(sk1, adv_out_enc)
        | _ => msK
        end%expr.
      Definition dec_msg := dec_out.
      Definition sK' := message2skey@dec_msg.
      Definition sign_out := sign@(sK', adv_out_msg).

      Definition net_in_good := (sign_out, (adv_out_msg, net_in_1))%expr.
      Definition net_in_2 := (eif check_out
                              then net_in_good
                              else (#!, (#!, net_in_1)))%expr.

      Definition adv_out_2 := !(tmessage * tsignature)@net_in_2.
      Definition adv_out_2_msg := ffst@adv_out_2.
      Definition adv_out_2_sig := fsnd@adv_out_2.
      Definition pK := pkeygen@sK.
      Definition verify_out := sverify@(pK, adv_out_2_msg, adv_out_2_sig).

      Definition auth_goal := (verify_out -> adv_out_2_msg == adv_out_msg)%expr.
    End Protocol1Rewrite.

    Example mac_integrity : whp (check_out Actual ->
                               adv_out_enc Actual == enc_out Actual).
    Proof.
      rewrite <-(expr_in_singleton (adv_out_enc Actual) (enc_out Actual)).
      cbv [check_out].
      eapply mac_correct.
      eexists.
      split.
      - cbv.
        repeat
          match goal with
          | |- auth_safe' _ _ _ => econstructor
          | [ |- _ <> _ ] =>
            intro;
              repeat (subst;
                      match goal with
                      | [ H : NoDup _ |- _ ] =>
                        inversion_clear H
                      end;
                      cbv [In] in *;
                      eauto)
          end.
      - eauto.
    Qed.

    Example rewrite_actual : exists e, whp (auth_goal Actual == e).
      eexists.
      cbv beta iota delta -[whp].
      (* note that we have decrypt(!encrypt(...))
       * with the adversary in between *)
      lazymatch goal with
      | |- whp ?x =>
        lazymatch x with
        | context[(eif mverify@(idmkey@(mkeygen@($?sk)), ?m, ?s) then ?T else ?E)%expr] =>
          let c := constr:(mverify@(idmkey@(mkeygen@($sk)), m, s)) in
          let i := constr:((eif c then T else E)%expr) in
            let Ti := type of i in
            let i' := fresh "i" in
            evar (i' : Ti);
              let H := fresh in
              assert (eqwhp i i') as H;
              [
                subst i';
                let A := build_context m T in
                let H := fresh in
                assert (eqwhp T (fill_hole A m)) as H
                by (cbn [fill_hole compose_hole];
                    repeat ((rewrite fill_hole_section_section) +
                            (rewrite fill_compose_hole));
                    reflexivity);
                rewrite H; clear H;
                eapply rewrite_verify
              |
              let C := build_context i x in
              let H' := fresh in
              assert (eqwhp x (fill_hole C i)) as H'
                  by (cbn [fill_hole compose_hole];
                      repeat ((rewrite fill_hole_section_section) +
                              (rewrite fill_compose_hole));
                      reflexivity);
              rewrite H'; clear H';
              rewrite H; clear H
              ]
        end
      end.
      {
        eexists.
        split.
        - repeat econstructor;
            match goal with
            | |- _ <> _ => admit
            end.
        - cbn [app].
          intros.
          eauto.
          (* todo deduplicate *)
      }
      subst i.
      cbn [fill_hole compose_hole choice_ctx];
        repeat ((rewrite fill_hole_section_section) +
                (rewrite fill_compose_hole)).

      (* victory! we now have decrypt(encrypt) instead of decrypt(!encrypt) *)
      (* todo wip *)
    Abort.

    Lemma elimdec_verify :
      whp (check_out Actual -> verify_out Actual == verify_out ElimDec).
    Admitted.
    Lemma elimdec_adv_msg :
      whp (check_out Actual -> adv_out_msg Actual == adv_out_msg ElimDec).
    Admitted.
    Lemma elimdec_adv_msg_2 :
      whp (check_out Actual -> adv_out_2_msg Actual == adv_out_2_msg ElimDec).
    Admitted.

    Lemma rewrite_enc :
      auth_goal ElimDec ≈ auth_goal RewriteEnc.
      etransitivity.
      cbv beta iota delta -[indist].

      (* TODO change definitions to let-ins *)
      (* TODO implement build enc_holes *)

    Admitted.

    (* Goal Proper (whp ==> whp) indist. *)

    Lemma authenticity_after_rewrite :
      whp (auth_goal RewriteEnc).
      cbv beta iota delta -[whp].
    Admitted.

    Lemma verify_impl_check : whp (verify_out Actual -> check_out Actual).
    Admitted.

    Theorem example_proto_1_authenticity :
      whp (verify_out Actual -> adv_out_2_msg Actual == adv_out_msg Actual).
    Admitted.
  End ExampleProtocol1.
End Language.
