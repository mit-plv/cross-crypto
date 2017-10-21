Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Classes.Morphisms.
Require Import Coq.MSets.MSetPositive Coq.FSets.FMapPositive.
Require Import FCF.FCF FCF.Asymptotic FCF.EqDec.
Require Import CrossCrypto.Util CrossCrypto.RatUtil CrossCrypto.RewriteUtil CrossCrypto.MapUtil.
Require Import Lia. (* TODO: remove after removing not_negligible_const *)

Section Language.
  Context {type  : Set} {eqdec_type : EqDec type}
          {interp_type : type -> nat -> Set} {eqdec_interp_type : forall {t eta}, EqDec (interp_type t eta)}
          {tbool trand tmessage : type} {tlist : type -> type} {tprod : type -> type -> type}.
  Context {func : type -> type -> Set}.

  Inductive expr : type -> Type :=
  | expr_const {t} (_:forall eta, interp_type t eta) : expr t
  | expr_random (idx:positive) : expr trand
  | expr_adversarial (_:expr (tlist tmessage)) : expr tmessage
  | expr_func {t1 t2} (_:func t1 t2) (_:expr t1) : expr t2
  | expr_pair {t1 t2} (_:expr t1) (_:expr t2) : expr (tprod t1 t2).

  Bind Scope expr_scope with expr.
  Delimit Scope expr_scope with expr.
  Local Open Scope expr_scope.

  Fixpoint randomness_indices {t:type} (e:expr t) : PositiveSet.t :=
    match e with
    | expr_const _ => PositiveSet.empty
    | expr_random idx => PositiveSet.singleton idx
    | expr_adversarial x => randomness_indices x
    | expr_func f x => randomness_indices x
    | expr_pair a b => PositiveSet.union (randomness_indices a) (randomness_indices b)
    end.

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

  Context (interp_func : forall {t1 t2} (f:func t1 t2) {eta}, interp_type t1 eta -> interp_type t2 eta).
  Context (interp_pair : forall {t1 t2 eta}, interp_type t1 eta -> interp_type t2 eta -> interp_type (tprod t1 t2) eta).
  Arguments interp_func {_ _} _ {_}.
  Arguments interp_pair {_ _ _}.

  Fixpoint interp_fixed {t} (e:expr t) (eta : nat)
           (adv: interp_type (tlist tmessage) eta -> interp_type tmessage eta)
           (rands: PositiveMap.t (interp_type trand eta))
    : interp_type t eta :=
    match e with
    | expr_const c => c eta
    | expr_random i => match PositiveMap.find i rands with Some r => r | _ => cast_rand eta (Bvector_exists _) end
    | expr_adversarial inputs => adv (interp_fixed inputs eta adv rands)
    | expr_func f inputs => interp_func f (interp_fixed inputs eta adv rands)
    | expr_pair a b => interp_pair (interp_fixed a eta adv rands) (interp_fixed b eta adv rands)
    end.
  Definition interp {t} (e:expr t) (eta:nat)
             (adv: interp_type (tlist tmessage) eta -> interp_type tmessage eta)
    : Comp (interp_type t eta)
    := rands <-$ generate_randomness eta (randomness_indices e); ret (interp_fixed e eta adv rands).

  Global Instance Proper_interp_term_fixed {t} (e:expr t) eta adv :
    Proper (PositiveMap.Equal ==> Logic.eq) (interp_fixed e eta adv).
  Proof.
    cbv [Proper respectful]; induction e; intros; simpl; try reflexivity.
    { cbv [PositiveMap.Equal] in *. rewrite H. reflexivity. }
    { erewrite IHe; eauto. }
    { erewrite IHe; eauto. }
    { erewrite IHe1, IHe2; eauto. }
  Qed.

  Section Security.
    (* the adversary is split into three parts for no particular reason. It first decides how much randomness it will need, then interacts with the protocol (repeated calls to [adverary] with all messages up to now as input), and then tries to claim victory ([distinguisher]). There is no explicit sharing of state between these procedures, but all of them get the same random inputs in the security game. The handling of state is a major difference between FCF [OracleComp] and this framework *)
    Definition universal_security_game {t}
               (evil_rand_indices: forall eta:nat, PositiveSet.t)
               (adversary:forall (eta:nat) (rands: PositiveMap.t (interp_type trand eta)), interp_type (tlist tmessage) eta -> interp_type tmessage eta)
               (distinguisher: forall (eta:nat) (rands: PositiveMap.t (interp_type trand eta)), interp_type t eta -> Datatypes.bool)
               (eta:nat) (e:expr t) : Comp Datatypes.bool :=
      evil_rands <-$ generate_randomness eta (evil_rand_indices eta);
        out <-$ interp e eta (adversary eta (evil_rands));
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

    Global Instance Proper_indist_func {t1 t2} f : Proper (@indist t1 ==> @indist t2) (expr_func f).
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
  Infix "≈" := indist (at level 70).

  Lemma interp_term_const {t} e eta a : Comp_eq (interp (@expr_const t e) eta a) (ret (e eta)).
  Proof. cbv -[Comp_eq]; setoid_rewrite Bind_unused; reflexivity. Qed.

  Lemma interp_term_rand i eta a : Comp_eq (interp (@expr_random i) eta a) (genrand eta).
  Admitted.

  Context (vtrue vfalse : forall eta, interp_type tbool eta)
          (inspect_vbool : forall eta, interp_type tbool eta -> bool)
          (case_tbool : forall eta (b:interp_type tbool eta), b = if inspect_vbool eta b then vtrue eta else vfalse eta)
          (inspect_vtrue : forall eta, inspect_vbool eta (vtrue eta) = true)
          (inspect_vfalse : forall eta, inspect_vbool eta (vfalse eta) = false).

  Arguments inspect_vbool {eta}.

  Definition whp (e:expr tbool) := e ≈ (expr_const vtrue).

  Definition whp_game
             (evil_rand_indices: forall eta:nat, PositiveSet.t)
             (adversary:forall (eta:nat) (rands: PositiveMap.t (interp_type trand eta)), interp_type (tlist tmessage) eta -> interp_type tmessage eta)
             (eta:nat) (e:expr tbool) : Comp Datatypes.bool :=
    evil_rands <-$ generate_randomness eta (evil_rand_indices eta);
    out <-$ interp e eta (adversary eta (evil_rands));
    ret negb (inspect_vbool out).

  Definition whp_simple (e : expr tbool) :=
    forall adl adv,
      negligible (fun eta : nat => Pr[whp_game adl adv eta e]).

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
    repeat match goal with
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
    intros [x y] ?.
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
                   (yx <-$ swapcomp (XY w); ret negb (fst yx ?= snd yx))) as E.
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

  Definition tbool_rect eta
             (P : interp_type tbool eta -> Type)
             (f : P (vfalse eta)) (t : P (vtrue eta))
             (b : interp_type tbool eta) : P b.
    rewrite case_tbool; destruct (inspect_vbool b); eauto.
  Defined.

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
    eapply tbool_rect with (P := fun b => inspect_vbool b = (b ?= vtrue eta));
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

  Local Existing Instance eq_subrelation | 5.
  (* Local Instance subrelation_eq_Comp_eq {A} : subrelation eq (Comp_eq(A:=A)) | 2 := eq_subrelation _. *)

  Context (feqb : forall t, func (tprod t t) tbool).
  Arguments feqb {_}.
  Context (interp_feqb : forall t eta (v1 v2:interp_type t eta),
              interp_func feqb (interp_pair v1 v2) = if eqb v1 v2 then vtrue eta else vfalse eta).

  Context (fand : func (tprod tbool tbool) tbool).
  Context (interp_fand : forall eta v1 v2, inspect_vbool (interp_func fand (interp_pair v1 v2)) =
                                           andb (inspect_vbool v1) (inspect_vbool (eta:=eta) v2)).
  Context (f_or : func (tprod tbool tbool) tbool).
  Context (interp_f_or : forall eta v1 v2,
              inspect_vbool (interp_func f_or (interp_pair v1 v2)) =
              orb (inspect_vbool v1) (inspect_vbool (eta:=eta) v2)).
  Context (fimpl : func (tprod tbool tbool) tbool).
  Context (interp_fimpl : forall eta v1 v2,
              inspect_vbool (interp_func fimpl (interp_pair v1 v2)) =
              implb (inspect_vbool v1) (inspect_vbool (eta:=eta) v2)).

  Definition always (e : expr tbool) :=
    forall eta adv rands, interp_fixed e eta adv rands = vtrue eta.

  Definition impl (e1 e2 : expr tbool) :=
    always (expr_func fimpl (expr_pair e1 e2)).

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
                                     (fun k _ => PositiveSet.mem k s) m)) as M.
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
    intros ? ? ? ? ?.
    induction e.
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
    intros ? ? ? ? I ? ?.
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

  Lemma whp_impl a b : impl a b -> whp a -> whp b.
  Proof.
    repeat rewrite whp_whp_simple.
    cbv [whp_simple whp_game impl always interp].
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
    setoid_rewrite inspect_vtrue in Himpl'.
    setoid_rewrite interp_fimpl in Himpl'.

    eapply negligible_le; try eapply (A adl adv).
    cbv beta.
    intro eta.

    set (u := PositiveSet.union (randomness_indices a) (randomness_indices b)).
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
                 ret negb (inspect_vbool (interp_fixed b eta (adv eta e) r)))).
    rewrite Bind_assoc_2 with
        (g := (fun e r =>
                 ret negb (inspect_vbool (interp_fixed a eta (adv eta e) r)))).

    eapply pr_weaken.
    intros x _.
    specialize (Himpl' eta (adv eta (fst x)) (snd x)).
    eapply leb_negb.
    eapply leb_implb.
    eauto.
  Qed.

  Lemma whp_and a b : whp a /\ whp b -> whp (expr_func fand (expr_pair a b)).
  Proof.
    SearchAbout whp iff.
    rewrite 3whp_whp_simple.
    cbv [whp_simple whp_game interp] in *.
    setoid_rewrite <-Bind_assoc.
    intros [A B].
  Admitted.

  Section Equality.
    Definition eqwhp {t} (e1 e2:expr t) : Prop := whp (expr_func feqb (expr_pair e1 e2)).

    Global Instance Reflexive_eqwhp {t} : Reflexive (@eqwhp t).
    Proof.
      cbv [Reflexive indist universal_security_game eqwhp whp interp]; intros.
      cbn [interp_fixed].
      (* TODO: report inlined setoid rewrite *)
      eapply Proper_negligible.
      {
        intro eta.
        setoid_rewrite interp_feqb.
        setoid_rewrite eqb_refl.
        setoid_rewrite Bind_unused.
        eapply reflexivity.
      }
      setoid_rewrite ratDistance_same.
      eapply negligible_0.
    Qed.

    Global Instance Symmetric_eqwhp {t} : Symmetric (@eqwhp t).
    Proof.
      cbv [Symmetric indist universal_security_game eqwhp whp interp]; intros.
      cbn [interp_fixed] in *.
      (* TODO: report inlined setoid rewrite *)
      eapply Proper_negligible.
      {
        intro eta.

        setoid_rewrite interp_feqb.
        setoid_rewrite eqb_symm.
        setoid_rewrite <-interp_feqb.

        cbn [randomness_indices].
        setoid_rewrite PositiveSetProperties.union_sym.

        eapply reflexivity.
      }
      eapply H.
    Qed.

    Global Instance Transitive_eqwhp {t} : Transitive (@eqwhp t).
    Proof.
      cbv [Transitive eqwhp]; intros ??? A B.
      refine (whp_impl _ _ _ (whp_and _ _ (conj A B))).
      cbv [impl always]; intros; cbn.
      etransitivity; [eapply case_tbool|].
      repeat match goal with
             | _ => solve [trivial]
             | _ => setoid_rewrite interp_fimpl
             | _ => setoid_rewrite interp_fand
             | _ => setoid_rewrite interp_feqb
             | _ => setoid_rewrite inspect_vtrue
             | _ => setoid_rewrite inspect_vfalse
             | |- context [if ?a ?= ?b then _ else _] => destruct (a ?= b) eqn:?
             | H:_|-_ => rewrite eqb_leibniz in H; rewrite H in *; clear H
             | H:_|-_ => rewrite eqb_refl in H; discriminate H
             | _ => progress cbn
             end.
    Qed.
      
    Global Instance Proper_eqwhp_pair {t1 t2} : Proper (eqwhp ==> eqwhp ==> eqwhp) (@expr_pair t1 t2).
    Admitted.

    Global Instance Proper_eqwhp_adversarial : Proper (eqwhp ==> eqwhp) expr_adversarial.
    Admitted.
  End Equality.

  Section LateInterp.
    Fixpoint interp_late
             {t} (e:expr t) (eta : nat)
             (adv: interp_type (tlist tmessage) eta -> interp_type tmessage eta)
             (fixed_rand: PositiveMap.t (interp_type trand eta))
    : Comp (interp_type t eta) :=
      match e with
      | expr_const c => ret (c eta)
      | expr_random i =>
        match PositiveMap.find i fixed_rand with
        | Some r => ret r
        | _ => r <-$ {0,1}^eta; ret (cast_rand eta r)
        end
      | expr_adversarial ctx =>
        ctx <-$ interp_late ctx eta adv fixed_rand; ret (adv ctx)
      | expr_func f x =>
        x <-$ interp_late x eta adv fixed_rand; ret (interp_func f x)
      | expr_pair a b =>
        common_rand <-$ generate_randomness eta (PositiveSet.inter (randomness_indices b) (randomness_indices a));
          let rands := PositiveMapProperties.update common_rand fixed_rand in
          b <-$ interp_late b eta adv rands;
            a <-$ interp_late a eta adv rands;
            ret (interp_pair a b)
      end.

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

  Lemma indist_rand x y : expr_random x ≈ expr_random y.
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

  Context (ite : forall t, func (tprod tbool (tprod t t)) t).
  Arguments ite {_}.
  Context (interp_ite : forall t eta b (v1 v2:interp_type t eta), interp_func ite (interp_pair b (interp_pair v1 v2)) = if inspect_vbool b then v1 else v2).
  Arguments interp_ite {_ _}.

  Lemma if_same b t (e:expr t) : eqwhp (expr_func ite (expr_pair b (expr_pair e e))) e.
  Proof.
    cbv [eqwhp whp indist universal_security_game interp]; intros.
    cbn [interp_fixed].
    eapply Proper_negligible; [intro eta|].
    {
      setoid_rewrite interp_feqb.
      setoid_rewrite interp_ite.
      assert (if_same : forall (x:bool) {T} (Y:T), (if x then Y else Y) = Y) by (destruct x; reflexivity).
      setoid_rewrite if_same at 1.
      setoid_rewrite eqb_refl.
      setoid_rewrite Bind_unused.
      eapply reflexivity.
    }
    setoid_rewrite ratDistance_same.
    eapply negligible_0.
  Qed.

  Context (vmessage_exists : forall eta, interp_type tmessage eta).

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

  Lemma tfdist : ~ expr_const vtrue ≈ expr_const vfalse.
  Proof.
    cbv [indist universal_security_game interp].
    intro H.
    specialize (H (fun _ => PositiveSet.empty)
                  (fun _ _ _ => (vmessage_exists _))
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

  Lemma if_true t (e1 e2:expr t) : eqwhp (expr_func ite (expr_pair (expr_const vtrue) (expr_pair e1 e2))) e1.
  Proof.
    cbv [eqwhp whp indist universal_security_game interp]; intros.
    cbn [interp_fixed].
    eapply Proper_negligible; [intro eta|].
    {
      setoid_rewrite interp_ite.
      setoid_rewrite inspect_vtrue.
      setoid_rewrite interp_feqb.
      setoid_rewrite eqb_refl.
      setoid_rewrite Bind_unused.
      eapply reflexivity.
    }
    setoid_rewrite ratDistance_same.
    eapply negligible_0.
  Qed.

  Lemma if_false t (e1 e2:expr t) : eqwhp (expr_func ite (expr_pair (expr_const vfalse) (expr_pair e1 e2))) e2.
  Proof.
    cbv [eqwhp whp indist universal_security_game interp]; intros.
    cbn [interp_fixed].
    eapply Proper_negligible; [intro eta|].
    {
      setoid_rewrite interp_ite.
      setoid_rewrite inspect_vfalse.
      setoid_rewrite interp_feqb.
      setoid_rewrite eqb_refl.
      setoid_rewrite Bind_unused.
      eapply reflexivity.
    }
    setoid_rewrite ratDistance_same.
    eapply negligible_0.
  Qed.

End Language.
