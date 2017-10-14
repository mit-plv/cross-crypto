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
          (case_tbool : forall eta (b:interp_type tbool eta), b = if inspect_vbool eta b then vtrue eta else vfalse eta).
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

  Lemma whp_game_wins_indist_game :
    forall adl adv eta e,
    exists dst,
      let game :=
          universal_security_game adl adv dst eta in
      Pr[whp_game adl adv eta e] <= |Pr[game e] - Pr[game (expr_const vtrue)]|.
  Admitted.

  Lemma whp_simple_to_whp :
    forall e, whp_simple e -> whp e.
  Admitted.

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

  Lemma whp_impl a b : impl a b -> whp a -> whp b.
  Proof.
    cbv [whp indist universal_security_game interp]; intros.
    cbn [interp_fixed] in H0 |- *.
    repeat setoid_rewrite Bind_unused.
    repeat setoid_rewrite <-Bind_assoc.
    repeat setoid_rewrite Bind_Ret_l.
    repeat setoid_rewrite Bind_unused in H0.
    repeat setoid_rewrite <-Bind_assoc in H0.
    repeat setoid_rewrite Bind_Ret_l in H0.
    eapply negligible_le; try eapply (H0 adl adv dst).
    cbv beta.
    intro n.
  Admitted.

  Lemma whp_and a b : whp a /\ whp b -> whp (expr_func fand (expr_pair a b)).
  Proof.
      cbv [indist universal_security_game whp interp]; intros.
      cbn [interp_fixed].
      eapply Proper_negligible. 
      {
        intro eta.
        setoid_rewrite (case_tbool eta
                          (interp_func fand
                                       (interp_pair (interp_fixed a eta (adv eta _) _)
                                                    (interp_fixed b eta (adv eta _) _)))).
        setoid_rewrite interp_fand.
        repeat setoid_rewrite Bind_unused.
        repeat setoid_rewrite <-Bind_assoc.
        repeat setoid_rewrite Bind_Ret_l.
        repeat setoid_rewrite <-Bind_assoc in H.
        repeat setoid_rewrite Bind_Ret_l in H.
        destruct H as [Ha Hb].
        cbv [andb].
        Lemma if_if (b t f:bool) {T} (x y:T) :
          (if (if b then t else f) then x else y)
          = 
          (if b then (if t then x else y) else (if f then x else y)).
        Proof. destruct b, t, f; trivial. Qed.
        setoid_rewrite if_if.
        setoid_rewrite <-case_tbool.
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

    Global Instance Transitive_eqwhp {t} : Transitive (@eqwhp t). Admitted.

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

  Context (inspect_vtrue : forall eta, inspect_vbool (vtrue eta) = true).
  Context (inspect_vfalse : forall eta, inspect_vbool (vfalse eta) = false).
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
