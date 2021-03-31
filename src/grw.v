Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Strings.String.
Require Import Coq.derive.Derive.
Require Import ZArith Lia.

Require Import Coq.Lists.List.

Require CrossCrypto.fmap.
Require Import CrossCrypto.ListUtil.
Require Import CrossCrypto.NatUtil.

Require Import FCF.EqDec.

Set Primitive Projections.
Unset Printing Primitive Projection Parameters.

Notation "x ?= y" := (eqb x y) (at level 70,
                                right associativity,
                                y at next level).

Ltac destruct_decider k comparison lemma a b :=
  let H := fresh in
  pose proof (lemma a b) as H; destruct (comparison a b);
  try k a;
  try k b;
  let Ht := type of H in
  try k Ht.

Ltac crush_deciders_in x :=
  lazymatch x with
  | context[(@eqb ?T ?E ?a ?b)] =>
    destruct_decider crush_deciders_in (@eqb T E) (@eqb_leibniz T E) a b
  | context[?a -? ?b] =>
    destruct_decider crush_deciders_in optsub optsub_plus a b
  | context[?a =? ?b] =>
    destruct_decider crush_deciders_in Nat.eqb Nat.eqb_eq a b
  | context[?a <=? ?b] =>
    destruct_decider crush_deciders_in Nat.leb Nat.leb_le a b
  | context[?a <? ?b] =>
    destruct_decider crush_deciders_in Nat.ltb Nat.ltb_lt a b
  end.

Ltac use_boolean_equalities :=
  repeat match goal with
         | H : true = true -> ?x |- _ => specialize (H eq_refl)
         | H : _ -> true = true |- _ => clear H
         | H : false = true -> _ |- _ => clear H
         | H : ?x -> false = true |- _ =>
           assert (~ x) by (let H' := fresh in
                            intro H'; specialize (H H');
                            congruence);
           clear H
         | H : _ = true <-> _ |- _ => destruct H
         end.

Ltac crush_deciders' t :=
  repeat (multimatch goal with
          | |- ?x => crush_deciders_in x
          | _ => use_boolean_equalities
          | _ => cbn [andb orb negb] in *
          | _ => intuition idtac
          | _ => congruence
          | _ => lia
          | _ => t
          end).

Tactic Notation "crush_deciders" tactic3(t) :=
  crush_deciders' t.

Section Language.
  Local Existing Instance eq_subrelation | 5.

  Record Basetype :=
    {
      basetype : Set;
      basetype_eqdec : EqDec basetype;
      interp_basetype : basetype -> Set;
      interp_basetype_eqdec : forall t, EqDec (interp_basetype t);
      interp_basetype_inhabited : forall {t}, interp_basetype t;
      basetype_transport :
        forall {P : basetype -> Type} {t : basetype} (u : basetype),
          P t -> option (P u);
      basetype_transport_same :
        forall {P t} (x : P t),
          basetype_transport t x = Some x;
      basetype_transport_different :
        forall {P t u} (x : P t),
          u <> t -> basetype_transport u x = None;
    }.
  Arguments interp_basetype_inhabited _ {t}.
  Arguments basetype_transport _ {P t}.
  Arguments basetype_transport_same _ {P t}.
  Arguments basetype_transport_different _ {P t u}.
  Context {B : Basetype}.
  Local Existing Instance basetype_eqdec.
  Local Existing Instance interp_basetype_eqdec.

  Inductive type : Set :=
  | tbase : B.(basetype) -> type
  | tunit : type
  | tprod : type -> type -> type.

  Bind Scope etype_scope with type.
  Delimit Scope etype_scope with etype.
  Local Notation "A * B" := (tprod A%etype B%etype) : etype_scope.

  Fixpoint type_eqb (t1 t2 : type) : bool :=
    match t1, t2 with
    | tbase b1, tbase b2 => b1 ?= b2
    | tunit, tunit => true
    | tprod t1a t1b, tprod t2a t2b =>
      (type_eqb t1a t2a) && (type_eqb t1b t2b)
    | _, _ => false
    end.
  Lemma type_eqb_eq t1 t2 : type_eqb t1 t2 = true <-> t1 = t2.
  Proof.
    revert t2; induction t1; intros []; cbn [type_eqb];
      crush_deciders rewrite ?andb_true_iff, ?IHt1_1, ?IHt1_2 in *.
  Qed.
  Local Instance type_eqdec : EqDec type := Build_EqDec type_eqb type_eqb_eq.
  Lemma type_eq_or (t1 t2 : type) : t1 = t2 \/ t1 <> t2.
  Proof. destruct (EqDec_dec _ t1 t2); eauto. Qed.

  Fixpoint interp_type (t : type) : Set :=
    match t with
    | tbase b => B.(interp_basetype) b
    | tunit => unit
    | tprod t1 t2 => interp_type t1 * interp_type t2
    end.

  Fixpoint interp_type_eqb {t} (x y : interp_type t) : bool :=
    match t return interp_type t -> interp_type t -> bool with
    | tbase b => fun x y => x ?= y
    | tunit => fun _ _ => true
    | tprod t1 t2 => fun x y =>
                       match x, y with
                       | (x1, x2), (y1, y2) =>
                         interp_type_eqb x1 y1 && interp_type_eqb x2 y2
                       end
    end x y.
  Lemma interp_type_eqb_eq {t} (x y : interp_type t) :
    interp_type_eqb x y = true <-> x = y.
  Proof.
    induction t; cbn [interp_type interp_type_eqb] in *;
      try solve [crush_deciders idtac];
      destruct x, y; rewrite ?andb_true_iff, ?IHt1, ?IHt2;
        intuition congruence.
  Qed.
  Definition interp_type_eqdec {t} : EqDec (interp_type t) :=
    Build_EqDec interp_type_eqb interp_type_eqb_eq.

  Fixpoint interp_type_inhabited {t : type} : interp_type t :=
    match t with
    | tbase _ => B.(interp_basetype_inhabited)
    | tunit => tt
    | tprod t1 t2 => (interp_type_inhabited, interp_type_inhabited)
    end.

  Record Monad :=
    {
      MM : type -> Type;
      Ret : forall {t}, interp_type t -> MM t;
      Bind : forall {t1 t2}, MM t1 -> (interp_type t1 -> MM t2) -> MM t2;
      MMequiv : forall {t}, MM t -> MM t -> Prop;
      MMequiv_equiv : forall {t}, Equivalence (@MMequiv t);
      Proper_Bind :
        forall {t1 t2},
          Proper
            (MMequiv ==> (pointwise_relation _ MMequiv) ==> MMequiv)
            (@Bind t1 t2);
      Bind_assoc :
        forall {t1 t2 t3}
               (f : MM t1)
               (g : interp_type t1 -> MM t2)
               (h : interp_type t2 -> MM t3),
          MMequiv (Bind (Bind f g) h)
                  (Bind f (fun x => Bind (g x) h));
      Bind_Ret_l :
        forall {t1 t2} x (f : interp_type t1 -> MM t2),
          MMequiv (Bind (Ret x) f) (f x);
      Bind_Ret_r :
        forall {t} (x : MM t),
          MMequiv (Bind x Ret) x;
      Bind_comm :
        forall {t1 t2 t3}
               (c1 : MM t1) (c2 : MM t2)
               (c3 : interp_type t1 -> interp_type t2 -> MM t3),
          MMequiv (Bind c1 (fun a => Bind c2 (fun b => c3 a b)))
                  (Bind c2 (fun b => Bind c1 (fun a => c3 a b)));
    }.
  Arguments Ret _ {t}.
  Arguments Bind _ {t1 t2}.
  Arguments MMequiv _ {t}.
  Arguments MMequiv_equiv _ {t}.
  Arguments Proper_Bind _ {t1 t2}.
  Arguments Bind_assoc _ {t1 t2 t3}.
  Arguments Bind_Ret_l _ {t1 t2}.
  Arguments Bind_Ret_r _ {t}.
  Arguments Bind_comm _ {t1 t2 t3}.
  Context {Mon : Monad}.
  Local Existing Instance MMequiv_equiv.
  Local Existing Instance Proper_Bind.
  Local Create HintDb mbind discriminated.
  Hint Rewrite
       (@Bind_assoc Mon)
       (@Bind_Ret_l Mon)
       (@Bind_Ret_r Mon)
    : mbind.
  Notation M := (MM Mon).
  Notation Mret := (Ret Mon).
  Notation Mbind := (Bind Mon).
  Notation Mequiv := (MMequiv Mon).

  Ltac step_Mequiv :=
    repeat multimatch goal with
           | |- Mequiv (Mbind _ _) (Mbind _ _) =>
             eapply Mon.(Proper_Bind); [try reflexivity | intros ?]
           | |- Mequiv ?x ?y => change x with y; reflexivity
           | |- _ => autorewrite with mbind
           end.

  Record Const :=
    {
      const : Set;
      const_eqdec : EqDec const;
      cdom; ccod : const -> type;
      interp_const : forall c, interp_type (cdom c) -> M (ccod c);
      retconst : Set;
      retconst_eqdec : EqDec retconst;
      rcdom; rccod : retconst -> type;
      interp_retconst : forall c,
          interp_type (rcdom c) -> interp_type (rccod c)
    }.
  Local Existing Instance const_eqdec.
  Local Existing Instance retconst_eqdec.
  Context {C : Const}.

  (* De bruijn indices which can be paired together to get a tuple *)
  Inductive ref : Type :=
  | ref_index : nat -> ref
  | ref_pair : ref -> ref -> ref.

  Fixpoint ref_eqb (r r' : ref) : bool :=
    match r, r' with
    | ref_index i, ref_index i' => i =? i'
    | ref_pair r1 r2, ref_pair r1' r2' => ref_eqb r1 r1' && ref_eqb r2 r2'
    | _, _ => false
    end.
  Lemma ref_eqb_eq r r' : ref_eqb r r' = true <-> r = r'.
  Proof.
    revert r'; induction r; destruct r'; cbn [ref_eqb];
      let t := (rewrite ?IHr1, ?IHr2, ?andb_true_iff, ?Nat.eqb_eq in * ) in
      repeat (intuition idtac; t); congruence.
  Qed.
  Local Instance ref_eqdec : EqDec ref := Build_EqDec ref_eqb ref_eqb_eq.

  Inductive op : Type :=
  | op_unit : op
  | op_app (c : C.(const)) : ref -> op
  | op_retapp (c : C.(retconst)) : ref -> op.

  Definition op_eqb (o o' : op) : bool :=
    match o, o' with
    | op_unit, op_unit => true
    | op_app c r, op_app c' r'
    | op_retapp c r, op_retapp c' r' => (c ?= c') && (r ?= r')
    | _, _ => false
    end.
  Lemma op_eqb_eq o o' : op_eqb o o' = true <-> o = o'.
  Proof. destruct o, o'; cbn [op_eqb]; crush_deciders idtac. Qed.
  Local Instance op_eqdec : EqDec op := Build_EqDec op_eqb op_eqb_eq.

  Definition op_type o : type :=
    match o with
    | op_unit => tunit
    | op_app c _ => ccod _ c
    | op_retapp c _ => rccod _ c
    end.

  Fixpoint transport {P : type -> Type} {a : type} (b : type) :
    P a -> option (P b) :=
    match a, b with
    | tbase a, tbase b => @basetype_transport
                            _ (fun bt => P (tbase bt)) _ b
    | tunit, tunit => Some
    | tprod a1 a2, tprod b1 b2 =>
      fun p =>
        match @transport (fun t => P (t * a2)%etype) _ b1 p with
        | Some p' => @transport (fun t => P (b1 * t)%etype) _ b2 p'
        | None => None
        end
    | _, _ => fun _ => None
    end.

  Fixpoint lookup (ctxt : type) (ctx : interp_type ctxt)
           (n : nat) (t : type) {struct n} : option (interp_type t) :=
    match ctxt return interp_type ctxt -> _ with
    | (_ * _)%etype =>
      fun ctx =>
        match n, ctx with
        | 0, (x, _) => transport t x
        | S n, (_, ctx) => lookup _ ctx n t
        end
    | _ => fun _ => None
    end ctx.

  Fixpoint lookup_ref ctxt ctx (r : ref) (t : type) {struct r}
    : option (interp_type t) :=
    match r with
    | ref_index n => lookup ctxt ctx n t
    | ref_pair r1 r2 =>
      match t with
      | (t1 * t2)%etype =>
        match lookup_ref ctxt ctx r1 t1, lookup_ref ctxt ctx r2 t2 with
        | Some x, Some y => Some (x, y)
        | _, _ => None
        end
      | _ => None
      end
    end.

  Definition interp_op ctxt ctx o : option (M (op_type o)) :=
    match o with
    | op_unit => Some (Mret (tt : interp_type tunit))
    | op_app c r => match lookup_ref ctxt ctx r (cdom _ c) with
                    | Some x => Some (interp_const _ c x)
                    | None => None
                    end
    | op_retapp c r => match lookup_ref ctxt ctx r (rcdom _ c) with
                       | Some x => Some (Mret (interp_retconst _ c x))
                       | None => None
                       end
    end.

  Definition cast {a : type} (b : type) (x : interp_type a) : interp_type b :=
    match transport b x with
    | Some x => x
    | None => interp_type_inhabited
    end.

  Lemma transport_same {P t} (x : P t) : transport t x = Some x.
  Proof.
    revert P x; induction t; intros P x; cbn [transport].
    - eapply (@basetype_transport_same _ (fun b => P (tbase b))).
    - eauto.
    - rewrite IHt1, IHt2; eauto.
  Qed.

  Lemma cast_same {t} (x : interp_type t) : cast t x = x.
  Proof. cbv [cast]; rewrite transport_same; eauto. Qed.

  Lemma transport_different {P t u} (x : P t) : u <> t -> transport u x = None.
  Proof.
    revert P x u; induction t as [| |t1 ? t2 ?]; intros P x [| |u1 u2];
      intros NE; cbn [transport];
      try congruence.
    - eapply (@basetype_transport_different _ (fun b => P (tbase b))).
      congruence.
    - destruct (type_eq_or t1 u1).
      + destruct (type_eq_or t2 u2).
        * congruence.
        * destruct transport; eauto.
          rewrite IHt2; eauto.
      + rewrite IHt1; eauto.
  Qed.

  Lemma cast_different {t u} (x : interp_type t) :
    u <> t -> cast u x = interp_type_inhabited.
  Proof. intros; cbv [cast]; rewrite transport_different; eauto. Qed.

  Definition interp_op_silent ctxt ctx o : M (op_type o) :=
    match interp_op ctxt ctx o with
    | Some m => m
    | None => Mret interp_type_inhabited
    end.

  Definition expr : Set := (list op) * op.

  Definition expr_type '((_, p2) : expr) : type := op_type p2.

  (* Interpreter in continuation-passing style. This has several
   * advantages over direct style:
   * - No need to rewrite Bind_Ret_l (very slowly!) on binds of the
   *   contexts to get the correct form and to eliminate
   *   lookups/transports
   * - Good commutation relation with List.app
   * - Can refer to universally-quantified variables as free de Bruijn indices
   *)
  Fixpoint interp_bindings (ctxt : type) (ctx : interp_type ctxt)
           (p : list op)
           (tk : type) (k : forall ctxt : type, interp_type ctxt -> M tk)
           {struct p} : (M tk) :=
    match p with
    | nil => k ctxt ctx
    | cons o p =>
      Mbind (interp_op_silent ctxt ctx o)
            (fun x => interp_bindings (op_type o * ctxt) (x, ctx) p tk k)
    end.

  Definition interp_expr ctxt ctx e : M (expr_type e) :=
    let '(p, o) := e in
    interp_bindings ctxt ctx p (op_type o)
                    (fun ctxt ctx => interp_op_silent ctxt ctx o).

  Definition interp_expr_cast ctxt ctx e t : M t :=
    Mbind (interp_expr ctxt ctx e)
          (fun x => Mret (cast t x)).

  Lemma Mequiv_Mbind_cast {t1 t1' t2} (c1 : M t1) (c1' : M t1')
        (c2 c2' : forall t, interp_type t -> M t2) :
    t1 = t1' ->
    (forall t, Mequiv (Mbind c1 (fun x => Mret (cast t x)))
                      (Mbind c1' (fun x => Mret (cast t x)))) ->
    (forall t (x : interp_type t), Mequiv (c2 _ x) (c2' _ x)) ->
    Mequiv (Mbind c1 (c2 _)) (Mbind c1' (c2' _)).
  Proof.
    intros ? Hc1 Hc2; subst t1'.
    step_Mequiv; cbv [pointwise_relation]; eauto.
    specialize (Hc1 t1).
    setoid_rewrite cast_same in Hc1.
    setoid_rewrite Bind_Ret_r in Hc1.
    eauto.
  Qed.

  Lemma interp_expr_cast_expr_type ctxt ctx e :
    Mequiv (interp_expr_cast ctxt ctx e (expr_type e))
           (interp_expr ctxt ctx e).
  Proof.
    cbv [interp_expr_cast].
    setoid_rewrite <-(Bind_Ret_r _ (interp_expr ctxt ctx e)) at 2.
    step_Mequiv.
    rewrite cast_same; reflexivity.
  Qed.

  Definition equiv_under ctxt ctx e1 e2 :=
    forall t, Mequiv (interp_expr_cast ctxt ctx e1 t)
                     (interp_expr_cast ctxt ctx e2 t).

  Definition equiv e1 e2 := forall ctxt ctx, equiv_under ctxt ctx e1 e2.

  Instance equiv_equiv : Equivalence equiv.
  Proof.
    split; cbv [equiv equiv_under Reflexive Symmetric Transitive];
      [reflexivity|symmetry; eauto|etransitivity; eauto].
  Qed.

  Lemma interp_bindings_app ctxt (ctx : interp_type ctxt)
        (p1 p2 : list op) tk (k : forall ctxt, interp_type ctxt -> M tk) :
    Mequiv
      (interp_bindings ctxt ctx (p1 ++ p2) tk k)
      (interp_bindings ctxt ctx p1 tk
                       (fun ctxt ctx => interp_bindings ctxt ctx p2 tk k)).
  Proof.
    revert ctxt ctx p2 tk k;
      induction p1 as [|o p1]; intros ctxt ctx p2 tk k;
        [reflexivity|].
    cbn [interp_bindings app].
    step_Mequiv; eauto.
  Qed.

  Lemma bind_interp_bindings ctxt ctx p tk k
        tf (f : interp_type tk -> M tf) :
    Mequiv (Mbind (interp_bindings ctxt ctx p tk k) f)
           (interp_bindings ctxt ctx p tf (fun ctxt ctx =>
                                             Mbind (k ctxt ctx) f)).
  Proof.
    revert ctxt ctx; induction p as [|o p]; intros ctxt ctx;
      cbn [interp_bindings]; [reflexivity|].
    step_Mequiv; eauto.
  Qed.

  Definition continuation_compat tk
             (k k' : forall ctxt : type, interp_type ctxt -> M tk) : Prop :=
    forall ctxt (ctx : interp_type ctxt),
      Mequiv (k ctxt ctx) (k' ctxt ctx).

  Fixpoint renumber_ref (f : nat -> nat) (r : ref) : ref :=
    match r with
    | ref_index n => ref_index (f n)
    | ref_pair r1 r2 => ref_pair (renumber_ref f r1) (renumber_ref f r2)
    end.

  Definition renumber_op (f : nat -> nat) (o : op) : op :=
    match o with
    | op_unit => op_unit
    | op_app c r => op_app c (renumber_ref f r)
    | op_retapp c r => op_retapp c (renumber_ref f r)
    end.

  Definition offset_renumbering (offset : nat)
             (f : nat -> nat) (n : nat) : nat :=
    match n -? offset with
    | Some k => offset + (f k)
    | None => n
    end.

  Lemma offset_id k i :
    offset_renumbering k (fun x => x) i = i.
  Proof.
    cbv [offset_renumbering].
    crush_deciders idtac.
  Qed.

  Fixpoint renumber_bindings (f : nat -> nat) (p : list op)
    : list op :=
    match p with
    | nil => nil
    | cons o p =>
      cons (renumber_op f o)
           (renumber_bindings (offset_renumbering 1 f) p)
    end.

  Fixpoint renumber_expr' acc f p o' :=
    match p with
    | nil => (rev acc, renumber_op f o')
    | o :: p => renumber_expr' (renumber_op f o :: acc)
                               (offset_renumbering 1 f) p o'
    end.

  Definition renumber_expr (f : nat -> nat) '((p, o') : expr) : expr :=
    renumber_expr' nil f p o'.

  Fixpoint refs (r : ref) (n : nat) :=
    match r with
    | ref_index k => n = k
    | ref_pair r1 r2 => refs r1 n \/ refs r2 n
    end.

  Definition op_refs (o : op) (n : nat) :=
    match o with
    | op_unit => False
    | op_app _ r | op_retapp _ r => refs r n
    end.

  Fixpoint bindings_ref (p : list op) (n : nat) :=
    match p with
    | nil => False
    | o :: p => op_refs o n \/ bindings_ref p (S n)
    end.

  Definition expr_refs '((p, o) : expr) (n : nat) :=
    bindings_ref p n \/ op_refs o (length p + n).

  Fixpoint refsb (r : ref) (n : nat) :=
    match r with
    | ref_index k => n =? k
    | ref_pair r1 r2 => refsb r1 n || refsb r2 n
    end.

  Definition op_refsb (o : op) (n : nat) :=
    match o with
    | op_unit => false
    | op_app _ r | op_retapp _ r => refsb r n
    end.

  Fixpoint bindings_refb (p : list op) (n : nat) :=
    match p with
    | nil => false
    | o :: p => op_refsb o n || bindings_refb p (S n)
    end.

  Definition expr_refsb '((p, o) : expr) (n : nat) :=
    bindings_refb p n || op_refsb o (length p + n).

  Lemma refsb_ref r i :
    refsb r i = true <-> refs r i.
  Proof.
    induction r; cbn [refs refsb].
    - crush_deciders idtac.
    - rewrite orb_true_iff; intuition idtac.
  Qed.

  Lemma op_refsb_ref o i :
    op_refsb o i = true <-> op_refs o i.
  Proof.
    destruct o; cbn [op_refs op_refsb];
      eauto using refsb_ref;
      intuition congruence.
  Qed.

  Lemma bindings_refb_ref p i :
    bindings_refb p i = true <-> bindings_ref p i.
  Proof.
    revert i; induction p as [|o p]; intros i;
      cbn [bindings_refb bindings_ref];
      try intuition congruence.
    rewrite orb_true_iff;
      rewrite op_refsb_ref;
      specialize (IHp (S i));
      intuition idtac.
  Qed.

  Fixpoint all_refsb (f : nat -> bool) (r : ref) : bool :=
    match r with
    | ref_index n => f n
    | ref_pair r1 r2 => all_refsb f r1 && all_refsb f r2
    end.

  Definition op_all_refsb (f : nat -> bool) (o : op) : bool :=
    match o with
    | op_unit => true
    | op_app _ r | op_retapp _ r => all_refsb f r
    end.

  Fixpoint bindings_all_refb (f : nat -> bool) (p : list op) : bool :=
    match p with
    | nil => true
    | o :: p =>
      op_all_refsb f o && bindings_all_refb (fun n => match n with
                                                      | 0 => true
                                                      | S n => f n
                                                      end) p
    end.

  Definition expr_all_refsb (f : nat -> bool) '((p, o) : expr) : bool :=
    (bindings_all_refb f p)
      && op_all_refsb (fun n => match n -? length p with
                                | Some k => f k
                                | None => true
                                end) o.

  Lemma all_refsb_correct f r :
    all_refsb f r = true ->
    forall n, refs r n -> f n = true.
  Proof.
    intros.
    induction r; cbn [all_refsb refs] in *.
    - congruence.
    - rewrite andb_true_iff in *; intuition idtac.
  Qed.

  Lemma op_all_refsb_correct f o :
    op_all_refsb f o = true ->
    forall n, op_refs o n -> f n = true.
  Proof.
    intros; destruct o; cbn [op_all_refsb op_refs] in *;
      rewrite ?andb_true_iff in *; intuition idtac;
        eapply all_refsb_correct; eauto with nocore.
  Qed.

  Lemma bindings_all_refb_correct f p :
    bindings_all_refb f p = true ->
    forall n, bindings_ref p n -> f n = true.
  Proof.
    intros; revert dependent f; revert dependent n; induction p;
      intros n Hn f Hf;
      cbn [bindings_all_refb bindings_ref] in *;
      intuition idtac;
      rewrite ?andb_true_iff in *;
      solve [(eapply op_all_refsb_correct +
              eapply (IHp (S n) ltac:(eauto) (fun n => match n with
                                                       | 0 => true
                                                       | S n => f n
                                                       end)));
             intuition eauto with nocore].
  Qed.

  Lemma expr_all_refsb_correct f e :
    expr_all_refsb f e = true ->
    forall n, expr_refs e n -> f n = true.
  Proof.
    destruct e as [p o];
      cbn [expr_refs expr_all_refsb] in *;
      rewrite ?andb_true_iff in *;
      intros [? Ho] ? [?|?].
    - eapply bindings_all_refb_correct; eauto with nocore.
    - eapply op_all_refsb_correct in Ho; eauto with nocore.
      match goal with
      | _ : context[?a + ?b -? ?a] |- _ =>
        replace (a + b -? a) with (Some b) in * by
            (crush_deciders f_equal)
      end; eauto with nocore.
  Qed.

  Lemma bindings_ref_app (p1 p2 : list op) n :
    bindings_ref (p1 ++ p2) n <->
    bindings_ref p1 n \/ bindings_ref p2 (length p1 + n).
  Proof.
    revert n; induction p1; intros n; cbn [bindings_ref length plus app].
    - intuition idtac.
    - replace (S (length p1 + n)) with (length p1 + S n) by lia.
      setoid_rewrite IHp1; intuition idtac.
  Qed.

  Lemma renumber_ref_ext_relevant f f' r :
    (forall i, refs r i -> f i = f' i) ->
    renumber_ref f r = renumber_ref f' r.
  Proof.
    intros Hf; induction r; cbn [renumber_ref refs] in *.
    - rewrite Hf; eauto.
    - rewrite IHr1, IHr2; eauto.
  Qed.

  Lemma renumber_ref_ext f f' r :
    (forall i, f i = f' i) ->
    renumber_ref f r = renumber_ref f' r.
  Proof. eauto using renumber_ref_ext_relevant. Qed.

  Lemma renumber_op_ext_relevant f f' o :
    (forall i, op_refs o i -> f i = f' i) ->
    renumber_op f o = renumber_op f' o.
  Proof.
    intros Hf; induction o; cbn [renumber_op];
      try erewrite renumber_ref_ext_relevant; eauto.
  Qed.

  Lemma renumber_op_ext f f' o :
    (forall i, f i = f' i) ->
    renumber_op f o = renumber_op f' o.
  Proof. eauto using renumber_op_ext_relevant. Qed.

  Lemma renumber_bindings_ext_relevant f f' p :
    (forall i, bindings_ref p i -> f i = f' i) ->
    renumber_bindings f p = renumber_bindings f' p.
  Proof.
    revert f f'; induction p as [|o p]; eauto.
    intros; cbn [renumber_bindings bindings_ref] in *.
    f_equal; try (erewrite renumber_op_ext_relevant; eauto).
    apply IHp.
    intros []; cbv [offset_renumbering optsub]; eauto.
  Qed.

  Lemma renumber_bindings_ext f f' p :
    (forall i, f i = f' i) ->
    renumber_bindings f p = renumber_bindings f' p.
  Proof. eauto using renumber_bindings_ext_relevant. Qed.

  Lemma offset_renumbering_plus a b n f :
    offset_renumbering (a + b) f n =
    offset_renumbering a (offset_renumbering b f) n.
  Proof.
    cbv [offset_renumbering] in *.
    crush_deciders idtac.
    subst.
    match goal with
    | _ : (_ + _ + ?x) = (_ + (_ + ?y)) |- _ => assert (x = y) by lia
    end.
    subst; lia.
  Qed.

  Lemma renumber_expr'_renumber_bindings acc f p o' :
    renumber_expr' acc f p o' =
    (rev acc ++ renumber_bindings f p,
     renumber_op (offset_renumbering (length p) f) o').
  Proof.
    revert acc f; induction p; intros acc f;
      cbn [renumber_expr' renumber_bindings length].
    - setoid_rewrite renumber_op_ext with (f' := f) at 2;
        [|reflexivity].
      listrew; eauto.
    - rewrite IHp.
      listrew.
      f_equal.
      eapply renumber_op_ext.
      intros;
        rewrite <-offset_renumbering_plus;
        f_equal; lia.
  Qed.

  Lemma renumber_expr_renumber_bindings f p o' :
    renumber_expr f (p, o') =
    (renumber_bindings f p,
     renumber_op (offset_renumbering (length p) f) o').
  Proof. eapply renumber_expr'_renumber_bindings. Qed.

  Lemma renumber_expr_ext_relevant f f' e :
    (forall i, expr_refs e i -> f i = f' i) ->
    renumber_expr f e = renumber_expr f' e.
  Proof.
    destruct e as [p o];
      repeat rewrite renumber_expr_renumber_bindings;
      cbn [expr_refs].
    intros.
    rewrite renumber_bindings_ext_relevant with (f' := f') by
        intuition eauto.
    rewrite renumber_op_ext_relevant with
        (f' := (offset_renumbering (length p) f')); eauto.
    intros.
    cbv [offset_renumbering];
      crush_deciders (subst; eauto).
  Qed.

  Lemma renumber_expr_ext f f' e :
    (forall i, f i = f' i) ->
    renumber_expr f e = renumber_expr f' e.
  Proof. eauto using renumber_expr_ext_relevant. Qed.

  Lemma renumber_bindings_app (f : nat -> nat) (p1 p2 : list op) :
    renumber_bindings f (p1 ++ p2) =
    (renumber_bindings f p1)
      ++ renumber_bindings (offset_renumbering (length p1) f) p2.
  Proof.
    revert f; induction p1; intros f; eauto.
    listrew.
    cbn [renumber_bindings offset_renumbering optsub length].
    listrew.
    f_equal.
    rewrite <-(Nat.add_1_r (length p1)).
    erewrite (renumber_bindings_ext (offset_renumbering (length p1 + 1) f));
      eauto using offset_renumbering_plus.
  Qed.

  Definition context_renumbered (f : nat -> nat)
             ctxt (ctx : interp_type ctxt)
             ctxt' (ctx' : interp_type ctxt') : Prop :=
    forall i t, lookup ctxt' ctx' (f i) t = lookup ctxt ctx i t.

  Lemma context_renumbered_ext f1 f2 ctxt ctx ctxt' ctx' :
    (forall n, f1 n = f2 n) ->
    context_renumbered f1 ctxt ctx ctxt' ctx' <->
    context_renumbered f2 ctxt ctx ctxt' ctx'.
  Proof. intuition congruence. Qed.

  Definition continuation_renumbered (f : nat -> nat) tk
             (k k' : forall ctxt : type, interp_type ctxt -> M tk) :=
    forall ctxt (ctx : interp_type ctxt) ctxt' (ctx' : interp_type ctxt'),
      context_renumbered f ctxt ctx ctxt' ctx' ->
      Mequiv (k ctxt ctx) (k' ctxt' ctx').

  Lemma continuation_renumbered_ext f1 f2 tk k k' :
    (forall i, f1 i = f2 i) ->
    continuation_renumbered f1 tk k k' ->
    continuation_renumbered f2 tk k k'.
  Proof. intros ???????; rewrite context_renumbered_ext in *; eauto. Qed.

  Local Instance continuation_renumbered_Mequiv f tk :
    Proper ((forall_relation
               (fun ctxt => pointwise_relation (interp_type ctxt) Mequiv)
               ==>
               (forall_relation
                  (fun ctxt => pointwise_relation (interp_type ctxt) Mequiv))
               ==> iff)) (continuation_renumbered f tk).
  Proof.
    cbv [Proper respectful forall_relation pointwise_relation Basics.impl].
    cbv [continuation_renumbered].
    intros k1 k1' Hk1 k2 k2' Hk2.
    split; intros H ctxt ctx ctxt' ctx';
      (etransitivity; [|etransitivity];
       [|eapply H|]);
      solve [eauto | symmetry; eauto].
  Qed.

  Lemma context_renumbered_1 f ctxt ctx ctxt' ctx' t
        (x : interp_type t) :
    context_renumbered f ctxt ctx ctxt' ctx' ->
    context_renumbered (offset_renumbering 1 f)
                       (t * ctxt) (x, ctx) (t * ctxt') (x, ctx').
  Proof.
    cbv [context_renumbered].
    intros ? n u.
    destruct n; cbn [lookup offset_renumbering optsub].
    - reflexivity.
    - rewrite Nat.add_1_l.
      cbn [lookup].
      eauto.
  Qed.

  Lemma lookup_renumbered_ref ctxt ctx ctxt' ctx' f r t :
    context_renumbered f ctxt ctx ctxt' ctx' ->
    lookup_ref ctxt' ctx' (renumber_ref f r) t =
    lookup_ref ctxt ctx r t.
  Proof.
    cbv [context_renumbered].
    intros ?.
    revert t; induction r; intros t;
      cbn [lookup_ref renumber_ref] in *; eauto.
    destruct t; eauto.
    rewrite IHr1, IHr2; reflexivity.
  Qed.

  Lemma interp_renumbered_op f o tk
        (k k' : forall ctxt, interp_type ctxt -> M tk) :
    continuation_renumbered (offset_renumbering 1 f) tk k k' ->
    continuation_renumbered
      f tk
      (fun ctxt ctx =>
         (Mbind (interp_op_silent ctxt ctx o)
                (fun x => k (op_type o * ctxt)%etype (x, ctx))))
      (fun ctxt ctx =>
         (Mbind
            (interp_op_silent ctxt ctx
                              (renumber_op f o))
            (fun x => k'
                        (op_type (renumber_op f o) *
                         ctxt)%etype (x, ctx)))).
  Proof.
    intros Hk ?????.
    destruct o; cbn [renumber_op op_type op_refs] in *;
      (step_Mequiv; [..|eapply Hk; eapply context_renumbered_1; eauto]);
      cbv [interp_op_silent interp_op];
      erewrite lookup_renumbered_ref by eauto;
      reflexivity.
  Qed.

  Lemma interp_renumbered_op_no_ctx f o tk
        (k k' : forall t, interp_type t -> M tk) :
    (forall t x, Mequiv (k t x) (k' t x)) ->
    continuation_renumbered
      f tk
      (fun ctxt ctx =>
         (Mbind (interp_op_silent ctxt ctx o)
                (fun x => k (op_type o) x)))
      (fun ctxt ctx =>
         (Mbind
            (interp_op_silent ctxt ctx
                              (renumber_op f o))
            (fun x => k'
                        (op_type (renumber_op f o)) x))).
  Proof.
    intros Hk ?????.
    destruct o; cbn [renumber_op op_type op_refs] in *;
      (step_Mequiv; [..|eapply Hk]);
      cbv [interp_op_silent interp_op];
      erewrite lookup_renumbered_ref by eauto;
      reflexivity.
  Qed.

  Lemma interp_renumbered_bindings (f : nat -> nat)
        (p : list op)
        tk (k k' : forall ctxt : type, interp_type ctxt -> M tk) :
    continuation_renumbered (offset_renumbering (length p) f) tk k k' ->
    continuation_renumbered
      f tk
      (fun ctxt ctx => interp_bindings ctxt ctx p tk k)
      (fun ctxt ctx => interp_bindings ctxt ctx (renumber_bindings f p) tk k').
  Proof.
    revert tk k k'.
    pattern p; revert p; eapply rev_ind;
      cbn [renumber_bindings interp_bindings length offset_renumbering
                             optsub plus]; eauto.
    intros o p IHp tk k k' Hkk'.
    rewrite renumber_bindings_app.
    cbn [renumber_bindings].
    setoid_rewrite interp_bindings_app.
    eapply IHp; eauto.
    cbn [interp_bindings].
    intros ?????.
    eapply interp_renumbered_op; eauto.
    listrew.
    replace (S (length p)) with (1 + length p) in * by lia.
    eapply (continuation_renumbered_ext
              _ _ _ _ _
              ltac:(intros; eapply offset_renumbering_plus)) in Hkk'; eauto.
  Qed.

  Lemma interp_renumbered_expr (f : nat -> nat) t (e : expr) :
    continuation_renumbered
      f t
      (fun ctxt ctx => interp_expr_cast ctxt ctx e t)
      (fun ctxt ctx => interp_expr_cast ctxt ctx (renumber_expr f e) t).
  Proof.
    intros ?????.
    destruct e as [p o].
    rewrite renumber_expr_renumber_bindings.
    cbv [interp_expr_cast interp_expr].
    setoid_rewrite bind_interp_bindings.
    eapply interp_renumbered_bindings; eauto.
    refine (interp_renumbered_op_no_ctx
              _ _ _
              (fun _ x => Mret (cast t x))
              (fun _ x => Mret (cast t x)) _); reflexivity.
  Qed.

  Lemma lookup_unref_0 ctxt (ctx : interp_type ctxt)
        t (x : interp_type t) r u :
    ~refs r 0 ->
    lookup_ref (t * ctxt) (x, ctx) r u =
    lookup_ref ctxt ctx (renumber_ref pred r) u.
  Proof.
    intros.
    revert u; induction r; intros u; cbn [refs] in *.
    - destruct n; cbn [lookup_ref lookup renumber_ref pred];
        congruence.
    - cbn [lookup_ref lookup renumber_ref].
      destruct u; try reflexivity.
      rewrite IHr1, IHr2 by intuition idtac.
      reflexivity.
  Qed.

  Lemma lookup_ref_S ctxt (ctx : interp_type ctxt)
        t (x : interp_type t) r u :
    lookup_ref (t * ctxt) (x, ctx) (renumber_ref S r) u =
    lookup_ref ctxt ctx r u.
  Proof.
    intros.
    revert u; induction r; intros u.
    - reflexivity.
    - cbn [renumber_ref lookup_ref lookup].
      destruct u; try reflexivity.
      rewrite IHr1, IHr2.
      reflexivity.
  Qed.

  Lemma commute_ops ctxt (ctx : interp_type ctxt)
        (o1 o2 : op)
        tk (k k' : forall ctxt, interp_type ctxt -> M tk) :
    ~op_refs o2 0 ->
    continuation_renumbered (fun n => match n with
                                      | 0 => 1
                                      | 1 => 0
                                      | _ => n
                                      end) tk k k' ->
    Mequiv (interp_bindings ctxt ctx (o1 :: o2 :: nil) tk k)
           (interp_bindings ctxt ctx
                            (renumber_op pred o2 :: renumber_op S o1 :: nil)
                            tk k').
  Proof.
    intros Ho2 Hk.
    cbn [interp_bindings].

    transitivity
      (Mbind (interp_op_silent ctxt ctx o1)
             (fun x =>
                Mbind (interp_op_silent (op_type o1 * ctxt) (x, ctx) o2)
                      (fun y =>
                         k' (op_type o1 * (op_type o2 * ctxt))%etype
                            (x, (y, ctx))))).
    { step_Mequiv.
      eapply Hk.
      intros [|[]] ?; reflexivity. }

    transitivity
    (Mbind (interp_op_silent ctxt ctx o1)
           (fun x =>
              Mbind (interp_op_silent ctxt ctx (renumber_op pred o2))
                    (fun y =>
                       k' (op_type o1 *
                           (op_type (renumber_op pred o2) * ctxt))%etype
                          (x, (y, ctx))))).
    { step_Mequiv.
      destruct o2; cbn [op_type renumber_op];
        step_Mequiv;
        cbn [op_refs] in Ho2; cbv [interp_op_silent interp_op];
          rewrite lookup_unref_0 by eauto;
          reflexivity. }

    transitivity
    (Mbind (interp_op_silent ctxt ctx (renumber_op pred o2))
           (fun y =>
              Mbind (interp_op_silent ctxt ctx o1)
                    (fun x =>
                       k' (op_type o1 *
                           (op_type (renumber_op pred o2) * ctxt))%etype
                          (x, (y, ctx))))).
    { eapply Bind_comm. }

    { step_Mequiv.
      destruct o1; cbn [op_type renumber_op];
        step_Mequiv; try reflexivity;
          cbv [interp_op_silent interp_op];
          rewrite lookup_ref_S;
          reflexivity. }
  Qed.

  Section RenumberRenumber.
    Context (h g f : nat -> nat)
            (Ih : forall x, h x = g (f x)).
    Lemma renumber_renumber_ref r :
      renumber_ref h r = renumber_ref g (renumber_ref f r).
    Proof. induction r; cbn [renumber_ref]; congruence. Qed.
    Lemma renumber_renumber_op o :
      renumber_op h o = renumber_op g (renumber_op f o).
    Proof. destruct o; cbn [renumber_op];
             repeat rewrite renumber_renumber_ref; eauto. Qed.
  End RenumberRenumber.

  Lemma renumber_renumber_bindings (h g f : nat -> nat) p :
    (forall x, h x = g (f x)) ->
    renumber_bindings h p = renumber_bindings g (renumber_bindings f p).
  Proof.
    revert h g f; induction p; intros h g f Ih; cbn [renumber_bindings]; eauto.
    erewrite (renumber_renumber_op h); eauto.
    erewrite IHp; eauto.
    intros []; cbn [offset_renumbering optsub plus]; eauto.
  Qed.

  Lemma length_renumber f p : length (renumber_bindings f p) = length p.
  Proof. revert f; induction p; cbn [renumber_bindings length]; congruence. Qed.

  Lemma offset_renumbering_ext n f f' :
    (forall i, f i = f' i) ->
    (forall i, offset_renumbering n f i = offset_renumbering n f' i).
  Proof. cbv [offset_renumbering]; crush_deciders eauto. Qed.

  Lemma renumber_renumber_expr (h g f : nat -> nat) e :
    (forall x, h x = g (f x)) ->
    renumber_expr h e = renumber_expr g (renumber_expr f e).
  Proof.
    intros Hh; destruct e.
    repeat rewrite renumber_expr_renumber_bindings.
    f_equal.
    - eapply renumber_renumber_bindings; eauto.
    - eapply renumber_renumber_op.
      intros; rewrite length_renumber.
      erewrite offset_renumbering_ext by eapply Hh.
      cbv [offset_renumbering]; crush_deciders idtac.
      match goal with
      | H : ?a + ?b = ?a + ?c |- _ => assert (b = c) by lia
      end;
        subst; eauto.
  Qed.

  Lemma refs_renumber f r j :
    refs (renumber_ref f r) j <-> exists i, f i = j /\ refs r i.
  Proof.
    induction r; cbn [renumber_ref refs];
      intuition repeat match goal with
                       | H : exists _, _ |- _ => destruct H as (?&<-&?)
                       | _ => intuition eauto
                       end.
  Qed.

  Lemma op_refs_renumber f o j :
    op_refs (renumber_op f o) j <-> exists i, f i = j /\ op_refs o i.
  Proof.
    destruct o; cbn [renumber_op op_refs];
      intuition repeat match goal with
                       | H : exists _, _ |- _ => destruct H as (?&<-&?)
                       | H : _ |- _ => setoid_rewrite refs_renumber in H
                       | _ => setoid_rewrite refs_renumber
                       | _ => intuition eauto
                       end.
  Qed.

  Lemma bindings_ref_renumber f p j :
    bindings_ref (renumber_bindings f p) j <->
    exists i, f i = j /\ bindings_ref p i.
  Proof.
    revert f j; induction p; intros;
      intuition repeat multimatch goal with
                       | H : exists _, _ |- _ => destruct H as (?&<-&?)
                       | H : _ |- _ => setoid_rewrite op_refs_renumber in H
                       | _ => setoid_rewrite op_refs_renumber
                       | _ => cbn [bindings_ref renumber_bindings] in *
                       | _ => intuition eauto
                       end.
    - rewrite IHp in *;
        repeat match goal with
               | H : exists _, _ |- _ =>
                 let x := fresh in
                 destruct H as ([]&?&?);
                   cbv [offset_renumbering optsub] in *
               | _ => congruence
               | _ => intuition eauto
               end.
    - rewrite IHp;
        right; eexists (S _); cbv [offset_renumbering optsub]; eauto.
  Qed.

  Lemma offset_eq_inv a f i j :
    offset_renumbering a f i = a + j ->
    i >= a /\ f (i - a) = j.
  Proof.
    cbv [offset_renumbering]; crush_deciders subst.
    match goal with
    | |- context[?a + ?b - ?a] => replace (a + b - a) with b by lia
    end; lia.
  Qed.

  Lemma expr_refs_renumber f e j :
    expr_refs (renumber_expr f e) j <->
    exists i, f i = j /\ expr_refs e i.
  Proof.
    destruct e; rewrite renumber_expr_renumber_bindings;
      cbn [expr_refs].
    rewrite length_renumber.
    setoid_rewrite bindings_ref_renumber.
    setoid_rewrite op_refs_renumber.
    split.
    - intros [(?&?&?)|(?&?&?)].
      + eexists.
        intuition eauto.
      + match goal with
        | H : offset_renumbering _ _ _ = _ |- _ => eapply offset_eq_inv in H
        end.
        eexists; intuition eauto.
        match goal with
        | |- context[?a + (?b - ?a)] =>
          replace (a + (b - a)) with b by lia
        end; eauto.
    - intros (?&?&[?|?]); eauto.
      right.
      eexists; split; eauto.
      cbv [offset_renumbering].
      crush_deciders (idtac; match goal with
                             | H : ?a + ?x = ?a + ?y |- _ =>
                               assert (x = y) by lia; subst
                             end).
  Qed.

  Lemma renumber_id_ref r :
    renumber_ref (fun x => x) r = r.
  Proof. induction r; cbn [renumber_ref]; congruence. Qed.

  Lemma renumber_id_op o :
    renumber_op (fun x => x) o = o.
  Proof.
    destruct o; cbn [renumber_op]; try rewrite renumber_id_ref; congruence.
  Qed.

  Lemma renumber_id_bindings p :
    renumber_bindings (fun x => x) p = p.
  Proof.
    induction p; cbn [renumber_bindings]; eauto.
    rewrite renumber_id_op.
    erewrite renumber_bindings_ext by (eapply offset_id).
    rewrite IHp; eauto.
  Qed.

  Lemma renumber_id_expr e :
    renumber_expr (fun x => x) e = e.
  Proof.
    destruct e; rewrite renumber_expr_renumber_bindings.
    rewrite renumber_id_bindings.
    erewrite renumber_op_ext by (eapply offset_id);
      rewrite renumber_id_op; eauto.
  Qed.

  Lemma commute_many ctxt (ctx : interp_type ctxt)
        (o : op) (p : list op)
        tk (ks : nat -> forall ctxt, interp_type ctxt -> M tk) :
    ~bindings_ref p 0 ->
    (forall j,
        j < length p ->
        continuation_renumbered
          (offset_renumbering
             j (fun n => match n with
                         | 0 => 1
                         | 1 => 0
                         | _ => n
                         end)) tk (ks (S j)) (ks j)) ->
    Mequiv (interp_bindings ctxt ctx (o :: p) tk (ks (length p)))
           (interp_bindings ctxt ctx
                            ((renumber_bindings pred p)
                               ++ renumber_op (plus (length p)) o :: nil)
                            tk (ks 0)).
  Proof.
    remember (length p) as lenp.
    revert ctxt ctx o p Heqlenp;
      induction lenp;
      intros ctxt ctx o p Heqlenp Hp Hks;
      destruct p as [|o' p]; try (cbn [length] in Heqlenp; congruence).
    - cbn [interp_bindings renumber_bindings length plus].
      rewrite renumber_id_op.
      reflexivity.
    - inversion Heqlenp; clear Heqlenp.
      subst lenp.
      cbn [bindings_ref] in *.
      replace (o :: o' :: p) with ((o :: o' :: nil) ++ p)
        by (eapply app_comm_cons).
      rewrite interp_bindings_app.
      etransitivity.
      {
        eapply commute_ops.
        - cbn [bindings_ref] in Hp; eauto.
        - eapply interp_renumbered_bindings.
          eapply Hks; eauto.
      }

      cbn [renumber_bindings length interp_bindings app] in IHlenp |- *.
      step_Mequiv.

      etransitivity.
      {
        eapply IHlenp; eauto.
        - rewrite length_renumber; eauto.
        - setoid_rewrite bindings_ref_renumber.
          intros ([|[]]&?&?); intuition congruence.
      }

      replace (renumber_op (plus (S (length p))) o) with
          (renumber_op (plus (length p)) (renumber_op S o)) by
          (erewrite <-renumber_renumber_op; eauto; intros; lia).
      erewrite <-renumber_renumber_bindings by (intros; reflexivity).
      rewrite renumber_bindings_ext_relevant with
          (f' := (offset_renumbering 1 pred)); try reflexivity.
      intros [|[]] ?; intuition idtac.
  Qed.

  Definition continuation_equiv tk
             (k k' : forall ctxt, interp_type ctxt -> M tk) :=
    forall ctxt ctx, Mequiv (k ctxt ctx) (k' ctxt ctx).

  Local Instance interp_bindings_Mequiv ctxt ctx p tk :
    Proper (continuation_equiv tk ==> Mequiv)
           (interp_bindings ctxt ctx p tk).
  Proof.
    revert ctxt ctx; induction p;
      cbn [interp_bindings]; intros ctxt ctx k k' ?; eauto.
    step_Mequiv.
    eapply IHp; eauto.
  Qed.

  Ltac crush_Mequiv :=
    repeat multimatch goal with
           | |- Mequiv (interp_bindings _ _ _ _ _)
                       (interp_bindings _ _ _ _ _) =>
             eapply interp_bindings_Mequiv; intros ??
           | |- context[interp_bindings _ _ (_ ++ _) _ _] =>
             rewrite interp_bindings_app
           | |- context[Mbind (interp_bindings _ _ _ _ _) _] =>
             rewrite bind_interp_bindings
           | |- _ => cbn [interp_bindings]
           | |- _ => step_Mequiv
           end.

  Definition cycle_to_here_renumbering (from j : nat) : nat :=
    if j =? from
    then 0
    else if j <? from
         then S j
         else j.

  Definition cycle (from to j : nat) : nat :=
    if j =? from
    then to
    else if (to <=? j) && (j <? from)
         then S j
         else j.

  Lemma cycle_trivial n j :
    cycle n n j = j.
  Proof.
    cbv [cycle].
    crush_deciders idtac.
  Qed.

  Lemma offset_cycle a b c j :
    offset_renumbering b (cycle a c) j =
    cycle (a + b) (c + b) j.
  Proof.
    cbv [offset_renumbering cycle].
    crush_deciders cbn [andb].
  Qed.

  Lemma cycle_S from to :
    to < from ->
    forall i,
      cycle from to i =
      offset_renumbering to
                         (fun n => match n with
                                   | 0 => 1
                                   | 1 => 0
                                   | _ => n
                                   end)
                         (cycle from (S to) i).
  Proof.
    cbv [cycle offset_renumbering].
    intros.
    crush_deciders (cbn [andb] in * );
      repeat match goal with
             | |- context[match ?x with _ => _ end] => destruct x
             end;
      crush_deciders idtac.
  Qed.

  Definition cycle_expr_continuation ncommute e t j ctxt ctx :=
    interp_expr_cast ctxt ctx
                     (renumber_expr (cycle ncommute j) e)
                     t.

  Lemma cycle_continuation_renumbered ncommute e t j :
    j < ncommute ->
    continuation_renumbered
      (offset_renumbering j
                          (fun n : nat => match n with
                                          | 0 => 1
                                          | 1 => 0
                                          | S (S _) => n
                                          end)) t
      (cycle_expr_continuation ncommute e t (S j))
      (cycle_expr_continuation ncommute e t j).
  Proof.
    intros.
    cbv [cycle_expr_continuation].
    erewrite (renumber_expr_ext
                _ _ _
                ltac:(eapply (cycle_S ncommute j
                                      ltac:(eauto)))).
    rewrite renumber_renumber_expr with
        (h :=
           fun i =>
             offset_renumbering j
                                (fun n =>
                                   match n with
                                   | 0 => 1
                                   | 1 => 0
                                   | S (S _) => n
                                   end)
                                (cycle ncommute (S j) i))
        (g := offset_renumbering j
                                 (fun n : nat => match n with
                                                 | 0 => 1
                                                 | 1 => 0
                                                 | S (S _) => n
                                                 end))
        (f := cycle ncommute (S j))
      by reflexivity.
    eapply interp_renumbered_expr.
  Qed.

  Definition context_omits (f : nat -> option nat)
             ctxt (ctx : interp_type ctxt)
             ctxt' (ctx' : interp_type ctxt') : Prop :=
    forall i t,
      match f i with
      | Some j => lookup ctxt' ctx' j t = lookup ctxt ctx i t
      | None => True
      end.

  Definition continuation_omits (f : nat -> option nat)
             tk (k k' : forall ctxt, interp_type ctxt -> M tk) : Prop :=
    forall ctxt (ctx : interp_type ctxt) ctxt' (ctx' : interp_type ctxt'),
      context_omits f ctxt ctx ctxt' ctx' ->
      Mequiv (k ctxt ctx) (k' ctxt' ctx').

  Lemma assoc_op ctxt (ctx : interp_type ctxt) o
        tm (m : interp_type (op_type o * ctxt) -> M tm)
        tk (k k' : forall ctxt, interp_type ctxt -> M tk) :
    continuation_omits (fun n =>
                          match n with
                          | 0 => Some 0
                          | 1 => None
                          | S n => Some n
                          end) tk k k' ->
    Mequiv
      (Mbind (interp_op_silent ctxt ctx o)
             (fun x =>
                Mbind (m (x, ctx))
                      (fun y => k (tm * (op_type o * ctxt))%etype
                                  (y, (x, ctx)))))
      (Mbind (Mbind (interp_op_silent ctxt ctx o)
                    (fun x => m (x, ctx)))
             (fun y => k' (tm * ctxt)%etype
                          (y, ctx))).
  Proof.
    intros Hkk'; crush_Mequiv; eapply Hkk'.
    intros [|[|[]]] ?; reflexivity.
  Qed.

  Definition offset_omission offset f n :=
    match n -? offset with
    | Some k => match f k with
                | Some k' => Some (offset + k')
                | None => None
                end
    | None => Some n
    end.

  Lemma assoc_many ctxt (ctx : interp_type ctxt) p
        tm (m : forall ctxt, interp_type ctxt -> M tm)
        tk (ks : nat -> forall ctxt, interp_type ctxt -> M tk) :
    (forall j,
        j < length p ->
        continuation_omits
          (fun n => match n with
                    | 0 => Some 0
                    | 1 => None
                    | S n => Some n
                    end) tk (ks (S j)) (ks j)) ->
    Mequiv
      (interp_bindings
         ctxt ctx p tk
         (fun ctxt ctx =>
            Mbind (m ctxt ctx)
                  (fun y => (ks (length p) (tm * ctxt)%etype (y, ctx)))))
      (Mbind (interp_bindings ctxt ctx p tm m)
             (fun y => ks 0 (tm * ctxt)%etype (y, ctx))).
  Proof.
    intros Hk.
    rewrite bind_interp_bindings.
    revert Hk m;
      pattern p; revert p; eapply rev_ind; [|intros o p IHp];
        intros Hk m.
    { reflexivity. }
    listrew.
    specialize (IHp (ltac:(intros; eapply Hk; lia))
                    (fun _ ctx =>
                       Mbind (interp_op_silent _ ctx o)
                             (fun x => m (_ * _)%etype (x, ctx)))).
    specialize (Hk (length p) ltac:(lia)).
    repeat rewrite interp_bindings_app; cbn [interp_bindings].
    etransitivity; [|etransitivity]; [|eapply IHp|]; clear IHp;
      [|solve [crush_Mequiv]].
    eapply interp_bindings_Mequiv; intros ??.
    eapply assoc_op; eauto.
  Qed.

  Definition ref_omits (f : nat -> option nat) r :=
    forall i, refs r i -> f i <> None.

  Definition op_omits (f : nat -> option nat) o :=
    forall i, op_refs o i -> f i <> None.

  Definition bindings_omit (f : nat -> option nat) p :=
    forall i, bindings_ref p i -> f i <> None.

  Definition expr_omits (f : nat -> option nat) e :=
    forall i, expr_refs e i -> f i <> None.

  Definition expr_omits_range n e :=
    forall i, expr_refs e i -> i = 0 \/ S n <= i.

  Definition expr_omits_rangeb n e :=
    expr_all_refsb (fun i => (i =? 0) ||
                             (S n <=? i)) e.

  Lemma expr_omits_rangeb_correct n e :
    expr_omits_rangeb n e = true -> expr_omits_range n e.
  Proof.
    cbv [expr_omits_rangeb expr_omits_range]; intros He ??.
    eapply expr_all_refsb_correct in He; eauto.
    revert He; crush_deciders idtac.
  Qed.

  Definition silence_omission (f : nat -> option nat) j :=
    match f j with
    | Some x => x
    | None => 0
    end.

  Lemma lookup_omitted_ref ctxt ctx ctxt' ctx' f r t :
    context_omits f ctxt ctx ctxt' ctx' ->
    ref_omits f r ->
    lookup_ref ctxt' ctx' (renumber_ref (silence_omission f) r) t =
    lookup_ref ctxt ctx r t.
  Proof.
    cbv [context_omits ref_omits silence_omission].
    intros Hctx Hr.
    revert t; induction r as [i|r1 IHr1 r2 IHr2]; intros t;
      cbn [lookup_ref renumber_ref refs] in *.
    - specialize (Hctx i t).
      specialize (Hr _ ltac:(eauto)).
      destruct (f i); congruence.
    - destruct t; eauto.
      erewrite IHr1, IHr2 by eauto; reflexivity.
  Qed.

  Lemma context_omits_1 f ctxt ctx ctxt' ctx' t (x : interp_type t) :
    context_omits f ctxt ctx ctxt' ctx' ->
    context_omits (offset_omission 1 f) (_ * _) (x, ctx) (_ * _) (x, ctx').
  Proof.
    cbv [context_omits offset_omission]; intros Hf.
    crush_deciders (idtac;
                    multimatch goal with
                    | |- context[f ?x] => specialize (Hf x); destruct (f x)
                    | _ => change (1 + ?y) with (S y)
                    | H : ?x < 1 |- _ => assert (x = 0) by lia; clear H
                    | _ => cbn [lookup]
                    | _ => subst
                    end).
  Qed.

  Lemma interp_omitted_op f o tk
        (k k' : forall ctxt, interp_type ctxt -> M tk) :
    op_omits f o ->
    continuation_omits (offset_omission 1 f) tk k k' ->
    continuation_omits
      f tk
      (fun _ ctx =>
         (Mbind (interp_op_silent _ ctx o)
                (fun x => k (_ * _)%etype (x, ctx))))
      (fun _ ctx =>
         (Mbind
            (interp_op_silent _ ctx
                              (renumber_op (silence_omission f) o))
            (fun x => k' (_ * _)%etype (x, ctx)))).
  Proof.
    intros ? Hk ?????.
    destruct o; cbn [renumber_op op_type op_refs] in *;
      (step_Mequiv; [..|eapply Hk; eapply context_omits_1; eauto]);
      cbv [interp_op_silent interp_op];
      erewrite lookup_omitted_ref by eauto;
      reflexivity.
  Qed.

  Lemma interp_omitted_op_no_ctx f o tk
        (k k' : forall t, interp_type t -> M tk) :
    op_omits f o ->
    (forall t x, Mequiv (k t x) (k' t x)) ->
    continuation_omits
      f tk
      (fun ctxt ctx =>
         (Mbind (interp_op_silent ctxt ctx o)
                (fun x => k (op_type o) x)))
      (fun ctxt ctx =>
         (Mbind
            (interp_op_silent ctxt ctx
                              (renumber_op (silence_omission f) o))
            (fun x => k'
                        (op_type (renumber_op (silence_omission f) o)) x))).
  Proof.
    intros ? Hk ?????.
    destruct o; cbn [renumber_op op_type op_refs] in *;
      (step_Mequiv; [..|eapply Hk; eapply context_omits_1; eauto]);
      cbv [interp_op_silent interp_op];
      erewrite lookup_omitted_ref by eauto;
      reflexivity.
  Qed.

  Lemma offset_omission_0 f i : offset_omission 0 f i = f i.
  Proof.
    cbv [offset_omission].
    crush_deciders idtac.
    subst; cbn [plus].
    destruct (f _); eauto.
  Qed.

  Lemma context_omits_ext f1 f2 ctxt ctx ctxt' ctx' :
    (forall i, f1 i = f2 i) ->
    context_omits f1 ctxt ctx ctxt' ctx' <->
    context_omits f2 ctxt ctx ctxt' ctx'.
  Proof. intros H; cbv [context_omits]; setoid_rewrite H; reflexivity. Qed.

  Lemma continuation_omits_ext f1 f2 tk k k' :
    (forall i, f1 i = f2 i) ->
    continuation_omits f1 tk k k' ->
    continuation_omits f2 tk k k'.
  Proof.
    intros H Hk ?????.
    eapply Hk.
    erewrite context_omits_ext; eauto.
  Qed.

  Local Instance continuation_omits_Mequiv f tk :
    Proper
      (forall_relation
         (fun ctxt => pointwise_relation (interp_type ctxt) Mequiv) ==>
         forall_relation
         (fun ctxt => pointwise_relation (interp_type ctxt) Mequiv) ==>
         iff) (continuation_omits f tk).
  Proof.
    cbv [Proper respectful forall_relation pointwise_relation Basics.impl].
    cbv [continuation_omits].
    intros k1 k1' Hk1 k2 k2' Hk2.
    split; intros H ctxt ctx ctxt' ctx';
      (etransitivity; [|etransitivity];
       [|eapply H|]);
      solve [eauto | symmetry; eauto].
  Qed.

  Lemma bindings_omit_app_invl f p1 p2 :
    bindings_omit f (p1 ++ p2) -> bindings_omit f p1.
  Proof.
    cbv [bindings_omit].
    intros Ha.
    setoid_rewrite bindings_ref_app in Ha.
    intuition eauto.
  Qed.

  Lemma bindings_omit_app_invr f p1 p2 :
    bindings_omit f (p1 ++ p2) ->
    bindings_omit (offset_omission (length p1) f) p2.
  Proof.
    cbv [bindings_omit offset_omission].
    intros Ha.
    setoid_rewrite bindings_ref_app in Ha.
    intros i ?.
    crush_deciders idtac.
    match goal with
    | _ : context[f ?x] |- _ => specialize (Ha x)
    end.
    subst.
    destruct (f _); eauto; congruence.
  Qed.

  Lemma offset_silence n f i :
    offset_omission n f i <> None ->
    offset_renumbering n (silence_omission f) i =
    silence_omission (offset_omission n f) i.
  Proof.
    intros.
    cbv [offset_renumbering silence_omission offset_omission] in *.
    crush_deciders (destruct (f _)).
  Qed.

  Lemma offset_offset_omission a b f i :
    offset_omission (a + b) f i =
    offset_omission a (offset_omission b f) i.
  Proof.
    cbv [offset_omission].
    crush_deciders idtac.
    subst.
    match goal with
    | H : ?x + ?y + ?z = ?x + (?y + ?z') |- _ =>
      assert (z = z') by lia; clear H; subst
    end.
    destruct (f _); f_equal; lia.
  Qed.

  Lemma interp_omitted_bindings f p
        tk (k k' : forall ctxt : type, interp_type ctxt -> M tk) :
    bindings_omit f p ->
    continuation_omits (offset_omission (length p) f) tk k k' ->
    continuation_omits
      f tk
      (fun ctxt ctx => interp_bindings ctxt ctx p tk k)
      (fun ctxt ctx =>
         interp_bindings ctxt ctx
                         (renumber_bindings (silence_omission f) p) tk k').
  Proof.
    revert tk k k'.
    pattern p; revert p; eapply rev_ind;
      cbn [renumber_bindings interp_bindings length offset_renumbering
                             optsub plus]; [|intros o p IHp];
        intros tk k k' Hp Hkk'.
    { eapply continuation_omits_ext in Hkk';
        try solve [eapply offset_omission_0].
      eapply Hkk'. }
    rewrite renumber_bindings_app.
    cbn [renumber_bindings].
    setoid_rewrite interp_bindings_app.
    pose proof (bindings_omit_app_invl _ _ _ Hp).
    pose proof (bindings_omit_app_invr _ _ _ Hp).
    cbv [bindings_omit] in *; cbn [bindings_ref] in *.
    clear Hp.
    eapply IHp; eauto; cbn [interp_bindings].
    intros ?????.
    rewrite renumber_op_ext_relevant with
        (f := (offset_renumbering (length p) (silence_omission f)))
        (f' := (silence_omission (offset_omission (length p) f)))
      by (eauto using offset_silence).

    eapply interp_omitted_op; try solve [eauto |
                                         cbv [op_omits]; intuition eauto].
    listrew.
    eapply continuation_omits_ext;
      try eapply offset_offset_omission; eauto.
  Qed.

  Lemma interp_omitted_expr f t (e : expr) :
    expr_omits f e ->
    continuation_omits
      f t
      (fun ctxt ctx => interp_expr_cast ctxt ctx e t)
      (fun ctxt ctx =>
         interp_expr_cast ctxt ctx (renumber_expr (silence_omission f) e) t).
  Proof.
    intros He ?????.
    destruct e as [p o].
    cbv [expr_omits expr_refs] in *.
    rewrite renumber_expr_renumber_bindings.
    erewrite renumber_op_ext_relevant; cycle 1.
    { intros i ?.
      eapply offset_silence.
      cbv [offset_omission].
      crush_deciders subst.
      match goal with
      | _ : context[f ?x] |- _ => specialize (He x)
      end.
      destruct (f _); eauto; congruence. }
    cbv [interp_expr_cast interp_expr].
    setoid_rewrite bind_interp_bindings.
    eapply interp_omitted_bindings;
      try solve [eauto | cbv [bindings_omit]; intuition eauto].
    refine (interp_omitted_op_no_ctx
              _ _ _
              (fun _ x => Mret (cast t x))
              (fun _ x => Mret (cast t x))
              _ _).
    { intros i ?.
      cbv [offset_omission].
      crush_deciders subst.
      intros.
      match goal with
      | _ : context[f ?x] |- _ => specialize (He x)
      end.
      destruct (f _); eauto; congruence. }
    reflexivity.
  Qed.

  Definition shift from to i := if i <? from
                                then 0
                                else i - from + to.

  Definition shift_expr_continuation e t total j ctxt ctx :=
    interp_expr_cast ctxt ctx (renumber_expr (shift (S (total - j)) 1) e) t.

  Lemma shift_S from i :
    shift (S from) 1 i =
    (silence_omission (fun n => match n with
                                | 0 => Some 0
                                | 1 => None
                                | S n => Some n
                                end))
      (shift from 1 i).
  Proof.
    cbv [shift silence_omission].
    crush_deciders (idtac;
                    multimatch goal with
                    | |- context[match ?x with _ => _ end] =>
                      lazymatch x with
                      | context[match _ with _ => _ end] => fail
                      | _ => idtac
                      end;
                      let x' := fresh "x" in remember x as x'; destruct x'
                    end).
  Qed.

  Lemma shift_continuation_omitted e t total j :
    j < total ->
    expr_omits_range total e ->
    continuation_omits
      (fun n => match n with
                | 0 => Some 0
                | 1 => None
                | S n => Some n
                end) t
      (shift_expr_continuation e t total (S j))
      (shift_expr_continuation e t total j).
  Proof.
    cbv [shift_expr_continuation]; intros ? He.
    replace (S (total - j)) with (S (S (total - S j))) by lia.
    erewrite (renumber_expr_ext
                _ _ _ ltac:(eapply (shift_S (S (total - S j))))).
    rewrite renumber_renumber_expr with
        (h := (fun i =>
                 silence_omission
                   (fun n =>
                      match n with
                      | 0 => Some 0
                      | 1 => None
                      | S n => Some n
                      end) (shift (S (total - S j)) 1 i)))
        (g := silence_omission
                (fun n =>
                   match n with
                   | 0 => Some 0
                   | 1 => None
                   | S n => Some n
                   end))
        (f := (shift (S (total - S j)) 1))
      by reflexivity.
    eapply interp_omitted_expr.
    cbv [expr_omits expr_omits_range].
    intros i Hi.
    eapply expr_refs_renumber in Hi; destruct Hi as (x&?&?).
    subst.
    enough (shift (S (total - S j)) 1 x <> 1) by
        (destruct (shift (S (total - S j)) 1 x) as [|[|]]; congruence).
    destruct e; cbv [expr_omits_range] in *.
    specialize (He _ ltac:(eauto)).
    cbv [shift].
    destruct He; crush_deciders idtac.
  Qed.

  Lemma equiv_prefix l p o p' o' :
    equiv (p, o) (p', o') ->
    equiv (l ++ p, o) (l ++ p', o').
  Proof.
    cbv [equiv equiv_under interp_expr_cast interp_expr].
    intros H ???.
    crush_Mequiv.
    etransitivity; [|etransitivity]; [|eapply H|];
      crush_Mequiv.
  Qed.

  Lemma shift_trivial i : shift 1 1 i = i.
  Proof. cbv [shift]; crush_deciders idtac. Qed.

  Lemma offset_1_shift from to i :
    i = 0 \/ i > from ->
    offset_renumbering 1 (shift from to) i = shift (S from) (S to) i.
  Proof. cbv [shift offset_renumbering]; crush_deciders idtac. Qed.

  Lemma shift_shift a b c i :
    b <> 0 ->
    shift b c (shift a b i) = shift a c i.
  Proof.
    cbv [shift]; crush_deciders idtac.
  Qed.

  Lemma shift_expr_continuation_shift t ctxt ctx s so n n' :
    expr_omits_range n (s, so) ->
    Mequiv
      (shift_expr_continuation (s, so) t n 0 ctxt ctx)
      (shift_expr_continuation
         (renumber_expr (offset_renumbering 1 (shift n n')) (s, so))
         t n' 0 ctxt ctx).
  Proof.
    intros.
    erewrite (renumber_expr_ext_relevant
                _ _ _ ltac:(intros; rewrite offset_1_shift; eauto)).
    cbv [shift_expr_continuation].
    repeat (evar (x : nat); subst x; replace (?x - 0) with (?x) by lia).
    erewrite <-renumber_renumber_expr.
    - reflexivity.
    - intros.
      rewrite shift_shift; lia.
  Qed.

  Lemma omit_range_shift n n' e :
    expr_omits_range n e ->
    expr_omits_range n' (renumber_expr (offset_renumbering 1 (shift n n')) e).
  Proof.
    cbv [expr_omits_range].
    setoid_rewrite expr_refs_renumber.
    intros H ?(?&?&?); subst.
    specialize (H _ ltac:(eauto)).
    cbv [offset_renumbering shift]; crush_deciders idtac.
  Qed.

  Lemma equiv_suffix p o p' o' s so s' so' :
    op_type o = op_type o' ->
    expr_omits_range (length p) (s, so) ->
    (s', so') = renumber_expr
                  (offset_renumbering 1 (shift (length p) (length p')))
                  (s, so) ->
    equiv (p, o) (p', o') ->
    equiv (p ++ o :: s, so) (p' ++ o' :: s', so').
    intros ???.
    intros Hpp'.
    assert (expr_omits_range (length p') (s', so'))
      by (replace (s', so'); eauto using omit_range_shift).
    cbv [equiv equiv_under interp_expr_cast interp_expr].
    intros.
    crush_Mequiv.

    etransitivity; etransitivity; [..|etransitivity];
      [|
       solve [eapply assoc_many
                with (p := p)
                     (m := (fun ctxt ctx => interp_op_silent ctxt ctx o))
                     (ks := shift_expr_continuation (s, so) t
                                                    (length p));
              intros; eapply shift_continuation_omitted; eauto]
       | |
       solve [symmetry;
              eapply assoc_many
                with (p := p')
                     (m := (fun ctxt ctx => interp_op_silent ctxt ctx o'))
                     (ks := shift_expr_continuation (s', so') t
                                                    (length p'));
              intros; eapply shift_continuation_omitted; eauto]
       |]; cycle 1;
        [|cbv [shift_expr_continuation interp_expr_cast interp_expr];
          replace (length _ - length _) with 0 by lia;
          erewrite renumber_expr_ext by (eapply shift_trivial);
          rewrite renumber_id_expr;
          crush_Mequiv ..].

    etransitivity; [|etransitivity];
      [|eapply Mequiv_Mbind_cast
          with
            (c2 :=
               fun tx (x : interp_type tx) =>
                 (shift_expr_continuation (s, so) t (length p) 0
                                          (tx * ctxt) (x, ctx)))
            (c2' :=
               fun tx (x : interp_type tx) =>
                 (shift_expr_continuation (s', so') t (length p') 0
                                          (tx * ctxt) (x, ctx)));
        [eauto|eapply Hpp'|]|]; cycle 1;
        [|solve [cbv [interp_expr_cast interp_expr expr_type];
                 crush_Mequiv] ..].
    intros.
    replace (s', so').
    eapply shift_expr_continuation_shift; eauto.
  Qed.

  Section Rewriter.
    Inductive error :=
    | E_debug {t : Type} (_ : t)
    | E_trace {t u : Type} (_ : t) (_ : u + error)
    | E_todo (_ : string)
    | E_msg (_ : string).

    Local Notation ok := inl.
    Local Notation raise := inr.
    Definition err_bind {t1 t2} (a : t1 + error) (b : t1 -> t2 + error)
      : t2 + error :=
      match a with
      | ok x => b x
      | raise e => raise e
      end.
    Local Notation "x <-! a ; b" := (err_bind a (fun x => b))
                                      (right associativity,
                                       at level 100).
    Local Notation "' x <-! a ; b" := (err_bind a (fun 'x => b))
                                        (x strict pattern,
                                         right associativity,
                                         at level 100).

    Section WithMap.
      Context (map_ops : CrossCrypto.fmap.operations nat nat).
      Local Notation map := (map_ops.(fmap.M)).
      Local Notation empty := (map_ops.(fmap.empty)).
      Local Notation add := (map_ops.(fmap.add)).
      Local Notation find := (map_ops.(fmap.find)).
      Local Notation fold_ac := (map_ops.(fmap.fold_ac)).

      Definition op_matches (o1 o2 : op) :=
        match o1, o2 with
        | op_unit, op_unit => true
        | op_app c _, op_app c' _ =>
          if c ?= c' then true else false
        | op_retapp c _, op_retapp c' _ =>
          if c ?= c' then true else false
        | _, _ => false
        end.

      (* TODO
       * - matching rewrite
       *   + (normalize lemma by removing any unused bindings)
       *   X find a match (inverse maps which line up program and lemma)
       *   + (renumber the lemma's free variables)
       *   X check that the match isn't captured by the program's tail
       *   X generate a sequence of cycles
       *   X check the legality of the cycles
       *   X prove the cycle-checker correct
       *   X run the cycles individually
       *   X run the strict matcher
       *     (could prove that it always succeeds but that would be hard)
       *   X rewrite the lemma
       * - reification
       *   + reify to PHOAS first, then to flat structure
       * - support for ret
       *   + duplicating/deduplicating rets
       * - support for free variables
       *   + need to renumber them on both sides of the lemma to match the
       *     program
       * - support for unused bindings
       *)

      Definition update_maps_ind (lem2prog prog2lem : map) (li pi : nat)
        : map * map + error :=
        match find li lem2prog with
        | Some pi' => if pi =? pi'
                      then ok (lem2prog, prog2lem)
                      else raise (E_msg "map_match: lem2prog mismatch")
        | None =>
          let lem2prog := add li pi lem2prog in
          match find pi prog2lem with
          | Some li' => if li =? li'
                        then ok (lem2prog, prog2lem)
                        else raise (E_msg "map_match: prog2lem mismatch")
          | None =>
            let prog2lem := add pi li prog2lem in
            ok (lem2prog, prog2lem)
          end
        end.

      Fixpoint update_maps_ref (loff poff : nat) (lem2prog prog2lem : map)
               (lr pr : ref) {struct lr} :
        map * map + error :=
        match lr, pr with
        | ref_index ln, ref_index pn =>
          update_maps_ind lem2prog prog2lem (loff + ln) (poff + pn)
        | ref_pair lr1 lr2, ref_pair pr1 pr2 =>
          '(lem2prog, prog2lem) <-!
           update_maps_ref loff poff lem2prog prog2lem lr1 pr1;
            update_maps_ref loff poff lem2prog prog2lem lr2 pr2
        | _, _ => raise (E_msg "map_match: ref mismatch")
        end.

      Definition update_maps_op
                 (lop pop : op)
                 (loff poff : nat) (lem2prog prog2lem : map)
        : map * map + error :=
        match lop, pop with
        | op_unit, op_unit => ok (lem2prog, prog2lem)
        | op_app lc lr, op_app pc pr =>
          if lc ?= pc
          then update_maps_ref loff poff lem2prog prog2lem lr pr
          else raise (E_msg "map_match: op const mismatch")
        | op_retapp lc lr, op_retapp pc pr =>
          if lc ?= pc
          then update_maps_ref loff poff lem2prog prog2lem lr pr
          else raise (E_msg "map_match: op retconst mismatch")
        | _, _ => raise (E_msg "map_match: op mismatch")
        end.

      (* iterate over lbinds, using the map found so far to index into
       * pbinds.  lbinds gets shorter, pbinds stays the same.
       * The "empty lem2prog entry" error occurs if the lemma has unused
       * bindings; "bad lem2prog entry" occurs if the program refers to a
       * free variable but that variable is not free in the lemma. *)
      Fixpoint map_match'
               (lbinds pbinds : list op) (lhead phead : op)
               (loff poff : nat) (lem2prog prog2lem : map) {struct lbinds}
        : map * map + error :=
        '(lem2prog, prog2lem) <-!
         update_maps_op lhead phead loff poff lem2prog prog2lem;
          match lbinds with
          | nil => ok (lem2prog, prog2lem)
          | cons lhead lbinds =>
            match find loff lem2prog with
            | Some pi =>
              match List.nth_error pbinds pi with
              | Some phead => map_match' lbinds pbinds
                                         lhead phead
                                         (S loff) (S pi)
                                         lem2prog prog2lem
              | None => raise (E_msg "map_match: bad lem2prog entry")
              end
            | None => raise (E_msg "map_match: empty lem2prog entry")
            end
          end.

      (* binds and lbinds are in reversed order from their usual order in
       * expr.  returns lemma-to-program and program-to-lemma maps of de
       * Bruijn indices relative to the head
       *)
      Definition map_match (lbinds pbinds : list op)
                 (lhead phead : op) : map * map + error :=
        map_match' lbinds pbinds lhead phead 0 0 empty empty.

      Definition check_no_capturing_tail (ptail : list op)
                 (prog_end : op)
                 (prog2lem : map) : unit + error :=
        fold_ac _ (fun n _ acc =>
                     _ <-! acc;
                       if bindings_refb ptail (S n)
                          || op_refsb prog_end (S (length ptail) + n)
                       then raise (E_msg "check_no_capturing_tail: capture")
                       else ok tt)
                (ok tt) prog2lem.

      Definition renumber_lem2prog (lem2prog : map) (pi li : nat) :=
        fold_ac _ (fun lj pj lem2prog =>
                     if pj =? pi
                     then lem2prog
                     else add lj (cycle pi li pj) lem2prog)
                empty lem2prog.

      Fixpoint generate_cycles' lem2prog (cycles : list (nat * nat))
               (li : nat) (n : nat) :=
        match n with
        | 0 => ok cycles
        | S n =>
          match find li lem2prog with
          | Some pi =>
            if pi <? li
            then raise (E_msg "generate_cycles: pi < li")
            else generate_cycles' (renumber_lem2prog lem2prog pi li)
                                  ((pi, li) :: cycles)
                                  (S li) n
          | None => raise (E_msg "generate_cycles: bad li")
          end
        end.

      Definition generate_cycles lem2prog (len_lbinds : nat)
        : list (nat * nat) + error :=
        cycles <-! generate_cycles' lem2prog nil 0 len_lbinds;
          ok (rev cycles).

      Lemma generate_cycles'_correct lem2prog cycles li n :
        Forall (fun '(from, to) => to <= from) cycles ->
        match generate_cycles' lem2prog cycles li n with
        | ok cycles => Forall (fun '(from, to) => to <= from) cycles
        | raise _ => True
        end.
      Proof.
        revert lem2prog cycles li; induction n;
          intros lem2prog cycles li ?;
                 cbn [generate_cycles' err_bind]; eauto.
        destruct (find li lem2prog) as [pi|]; eauto.
        crush_deciders idtac.
        eapply IHn.
        eapply Forall_cons; eauto.
        lia.
      Qed.

      Lemma generate_cycles_correct lem2prog n :
        match generate_cycles lem2prog n with
        | ok cycles => Forall (fun '(from, to) => to <= from) cycles
        | raise _ => True
        end.
      Proof.
        cbv [generate_cycles].
        pose proof (generate_cycles'_correct lem2prog nil 0 n).
        destruct (generate_cycles' lem2prog nil 0 n); cbn [err_bind]; eauto.
        rewrite Forall_forall.
        setoid_rewrite <-in_rev.
        rewrite <-Forall_forall.
        eauto using Forall_nil.
      Qed.

      Definition cycle_pbinds (from to : nat) (pbinds : list op)
        : list op + error :=
        match Decompose.index pbinds to with
        | Some (coda, to_op, tmp) =>
          let distance := from - to in
          match Decompose.index (to_op :: tmp) distance with
          | Some (middle, from_op, prelude) =>
            if bindings_refb middle 0
            then raise (E_msg "middle references from")
            else
              ok (rev_append
                    (renumber_bindings (cycle_to_here_renumbering distance) coda)
                    ((renumber_op (plus distance) from_op)
                       :: (rev_append (renumber_bindings pred middle)
                                      prelude)))
          | None => raise (E_msg "to out of range")
          end
        | None => raise (E_msg "from out of range")
        end.

      Fixpoint cycles_pbinds (cycles : list (nat * nat))
               (pbinds : list op) : list op + error :=
        match cycles with
        | nil => ok pbinds
        | (from, to) :: cycles => pbinds <-! cycle_pbinds from to pbinds;
                                    cycles_pbinds cycles pbinds
        end.

      Fixpoint cycles_phead_ptail (cycles : list (nat * nat))
               (phead : op) (ptail : list op)
        : op * list op :=
        match cycles with
        | nil => (phead, ptail)
        | (from, to) :: cycles =>
          cycles_phead_ptail
            cycles
            (renumber_op (cycle from to) phead)
            (renumber_bindings
               (offset_renumbering 1 (cycle from to)) ptail)
        end.

      Fixpoint cycles_prog_end (len_ptail : nat) (cycles : list (nat * nat))
               (prog_end : op) : op :=
        match cycles with
        | nil => prog_end
        | (from, to) :: cycles =>
          cycles_prog_end len_ptail
                          cycles (renumber_op (offset_renumbering (S len_ptail)
                                                                  (cycle from to))
                                              prog_end)
        end.

      Definition assemble (pbinds : list op)
                 (phead : op) (ptail : list op)
                 (prog_end : op) :=
        (rev_append pbinds (phead :: ptail), prog_end).

      Definition commute_matches (lbinds : list op)
                 (lhead : op) (e : expr) :
        (* returns pbinds, phead, ptail, prog_end *)
        list (nat * ((list op * op *
                      list op * op) + error)) :=
        (* match base has the form:
         * (tail (normal order), head, binds (reversed order)) *)
        let '(prog, prog_end) := e in
        let match_bases :=
            Decompose.find_all (fun _ => op_matches lhead) (rev prog) in
        let len_lbinds := length lbinds in
        List.map
          (fun '(ptail, phead, pbinds) =>
             let len_ptail := length ptail in
             (len_ptail,
              '(lem2prog, prog2lem) <-! map_match lbinds pbinds lhead phead;
                _ <-! check_no_capturing_tail ptail prog_end prog2lem;
                cycles <-! generate_cycles lem2prog len_lbinds;
                new_pbinds <-! cycles_pbinds cycles pbinds;
                let '(new_phead, new_ptail) :=
                    cycles_phead_ptail cycles phead ptail in
                ok (new_pbinds, new_phead, new_ptail,
                    cycles_prog_end len_ptail cycles prog_end)))
          match_bases.

      Ltac step_err_bind :=
        lazymatch goal with
        | H : raise _ = ok _ |- _ => congruence
        | H : ?e = ok _ |- _ =>
          lazymatch e with
          | x <-! ?y; ?z =>
            let y' := fresh in
            remember y as y';
            destruct y' as [x|];
            cbn [err_bind] in H;
            [|congruence];
            match type of x with
            | unit => destruct x
            | _ => idtac
            end
          | ok _ => inversion H; clear H
          end
        | H : ok _ = ?e |- _ =>
          symmetry in H
        end.

      Lemma commute_matches_correct lbinds lhead e :
        Forall (fun '(_, err) =>
                  match err with
                  | ok (new_pbinds, new_phead, new_ptail, new_prog_end) =>
                    equiv e
                          (assemble new_pbinds new_phead new_ptail new_prog_end)
                  | raise _ => True
                  end)
               (commute_matches lbinds lhead e).
        destruct e as [prog prog_end].
        cbv [commute_matches].
        rewrite Forall_forall.
        setoid_rewrite in_map_iff.
        intros [n [[[[new_pbinds' new_phead'] new_ptail'] new_prog_end']|]]
               ([[ptail phead] pbinds]&H&?); eauto.
        inversion H; clear dependent n.

        destruct (map_match lbinds pbinds lhead phead) as [[lem2prog prog2lem]|];
          cbn [err_bind] in *; [|congruence].

        repeat step_err_bind.
        let c := constr:(cycles_phead_ptail cycles phead ptail) in
        replace c with (fst c, snd c) in * by (destruct c; eauto).
        repeat step_err_bind.
        subst new_pbinds' new_phead' new_ptail' new_prog_end'.
        cbv [assemble].

        match goal with
        | H : context[check_no_capturing_tail] |- _ => clear H
        end.

        pose proof (Decompose.find_all_correct (fun _ => op_matches lhead)
                                               (rev prog)) as F;
          rewrite Forall_forall in F;
          specialize (F _ ltac:(eauto)); cbn iota beta in F;
            match goal with
            | H : In (ptail, phead, pbinds) _ |- _ => clear H
            end;
            cbv [Decompose.found] in F;
            destruct F as [Hprog _];
            eapply (f_equal (@rev _)) in Hprog;
            listrew;
            subst prog.

        pose proof generate_cycles_correct lem2prog (length lbinds) as G;
          replace (generate_cycles lem2prog (length lbinds)) in G;
          match goal with
          | H : context[generate_cycles] |- _ => clear H
          end.

        cbv [equiv equiv_under interp_expr_cast interp_expr];
          intros ctxt ctx t;
          crush_Mequiv.

        revert dependent new_pbinds;
          revert pbinds phead ptail prog_end;
          induction cycles as [|[from to] cycles];
          intros pbinds phead ptail prog_end
                 new_pbinds Hnew_pbinds;
          cbn [cycles_phead_ptail fst snd cycles_prog_end cycles_pbinds] in *.
        { inversion_clear Hnew_pbinds; reflexivity. }

        match goal with
        | H : Forall _ (_ :: _) |- _ => inversion_clear H
        end.

        remember (cycle_pbinds from to pbinds) as e eqn:Hpbinds';
          destruct e as [pbinds'|]; cbn [err_bind] in *; [|congruence].
        cbv [cycle_pbinds] in Hpbinds'.
        pose proof (Decompose.index_correct pbinds to);
          destruct (Decompose.index pbinds to) as [[[coda to_op] tmp]|];
          [|congruence].
        pose proof (Decompose.index_correct (to_op :: tmp) (from - to));
          destruct (Decompose.index (to_op :: tmp) (from - to))
          as [[[middle from_op] prelude]|]; [|congruence].
        remember (bindings_refb middle 0) as e;
          destruct e; [congruence|].
        inversion Hpbinds'; clear Hpbinds'; subst pbinds'.
        repeat match goal with
               | H : _ /\ _ |- _ => destruct H
               end.
        match goal with
        | H : to_op :: tmp = _ |- _ => rewrite H in *; clear tmp H
        end.
        subst pbinds.
        specialize (IHcycles (ltac:(eauto))
                             (rev
                                ((rev prelude)
                                   ++ (renumber_bindings pred middle)
                                   ++ renumber_op (plus (length middle)) from_op
                                   :: (renumber_bindings
                                         (cycle (length middle) 0)
                                         coda)))
                             (renumber_op
                                (offset_renumbering
                                   (length coda)
                                   (cycle (length middle) 0))
                                phead)
                             (renumber_bindings
                                (offset_renumbering
                                   (S (length coda))
                                   (cycle (length middle) 0))
                                ptail)
                             (renumber_op
                                (offset_renumbering
                                   (S (length coda) + length ptail)
                                   (cycle (length middle) 0))
                                prog_end)
                             new_pbinds).
        listrew.

        replace (length middle) in *.
        specialize (IHcycles Hnew_pbinds).

        etransitivity; [|etransitivity];
          [clear IHcycles|eapply IHcycles|clear IHcycles].

        - etransitivity.
          + clear dependent cycles.
            clear new_pbinds.

            crush_Mequiv.
            eapply interp_bindings_Mequiv; intros ??.
            change (from_op :: middle ++ coda)
              with ((from_op :: middle) ++ coda).
            setoid_rewrite interp_bindings_app at 1.

            set (ks j ctxt ctx :=
                   interp_expr_cast ctxt ctx
                                    (renumber_expr
                                       (cycle (length middle) j)
                                       (coda ++ phead :: ptail, prog_end))
                                    t).

            etransitivity; [|eapply commute_many with
                                 (ks := cycle_expr_continuation
                                          (length middle)
                                          (coda ++ phead :: ptail, prog_end)
                                          t)].
            * cbv [cycle_expr_continuation].

              crush_Mequiv.
              erewrite renumber_expr_ext by (eapply cycle_trivial).
              rewrite renumber_id_expr.
              cbv [interp_expr_cast interp_expr].
              crush_Mequiv.
            * pose proof bindings_refb_ref middle 0;
                intuition congruence.
            * intros.
              eapply cycle_continuation_renumbered; eauto.
          + cbv [cycle_expr_continuation].
            replace (length middle).
            crush_Mequiv.
            cbv [interp_expr_cast interp_expr].

            rewrite renumber_expr_renumber_bindings.

            crush_Mequiv.
            rewrite renumber_bindings_app.
            crush_Mequiv.
            cbn [renumber_bindings interp_bindings].
            crush_Mequiv.

            erewrite renumber_bindings_ext
              by (intros; rewrite <-offset_renumbering_plus; eauto).
            cbn [plus].
            crush_Mequiv.
            listrew.
            crush_Mequiv.
        - crush_Mequiv.
          replace (length coda).
          cbn [renumber_bindings].
          erewrite renumber_op_ext by (eapply offset_cycle).
          repeat erewrite
                 (renumber_bindings_ext _ _ _
                                        ltac:(eapply offset_cycle)).
          cbn [plus].
          replace (from - to + to) with from by lia.
          replace (from - to + S to) with (S from) by lia.
          replace (from + 1) with (S from) by lia.
          replace (to + 1) with (S to) by lia.
          crush_Mequiv.
          rewrite length_renumber.
          repeat erewrite
                 (renumber_op_ext _ _ _
                                  ltac:(eapply offset_cycle)).
          cbn [plus].
          replace (from - to + S (to + length ptail))
            with (from + S (length ptail)) by lia.
          replace (to + S (length ptail))
            with (S (to + length ptail)) by lia.
          crush_Mequiv.
      Qed.

      Definition replace_lemma
                 (lbinds fwd_rbinds : list op)
                 (lhead rhead : op)
                 (pbinds : list op) (phead : op)
                 (ptail : list op) (prog_end : op)
        : list op * op * list op * op + error :=
        let len_lbinds := length lbinds in
        let len_rbinds := length fwd_rbinds in
        _ <-! if expr_omits_rangeb len_lbinds (ptail, prog_end)
              then ok tt
              else raise (E_msg "replace_lemma: lbinds not omitted in tail");
          match Decompose.prefix op_eqb (lhead :: lbinds) (phead :: pbinds) with
          | Some rest =>
            let f := shift len_lbinds len_rbinds in
            ok (rev_append fwd_rbinds rest,
                rhead,
                renumber_bindings (offset_renumbering 1 f) ptail,
                renumber_op (offset_renumbering (S (length ptail)) f)
                            prog_end)
          | None =>
            raise (E_msg "replace_lemma: match failed")
          end.

      Lemma replace_lemma_correct lbinds fwd_rbinds lhead rhead
            pbinds phead ptail prog_end :
        op_type lhead = op_type rhead ->
        equiv (rev lbinds, lhead) (fwd_rbinds, rhead) ->
        match replace_lemma lbinds fwd_rbinds lhead rhead
                            pbinds phead ptail prog_end with
        | ok (new_pbinds, new_phead, new_ptail, new_prog_end) =>
          equiv (assemble pbinds phead ptail prog_end)
                (assemble new_pbinds new_phead new_ptail new_prog_end)
        | raise _ => True
        end.
      Proof.
        intros L ?.
        remember (replace_lemma lbinds fwd_rbinds lhead rhead
                                pbinds phead ptail prog_end) as err;
          destruct err as
            [[[[new_pbinds' new_phead'] new_ptail'] new_prog_end']|];
          eauto.
        cbv [replace_lemma] in *.
        pose proof (Decompose.prefix_correct op_eqb op_eqb_eq
                                             (lhead :: lbinds)
                                             (phead :: pbinds));
          destruct (Decompose.prefix op_eqb
                                     (lhead :: lbinds)
                                     (phead :: pbinds)) as [rest|];
          repeat step_err_bind.
        listrew.
        match goal with
        | H : _ :: _ = _ :: _ |- _ => inversion H; clear H
        end.
        subst new_pbinds' new_phead' new_ptail' new_prog_end' pbinds phead.
        cbv [assemble]; listrew.

        eapply equiv_prefix.
        remember (rev lbinds) as fwd_lbinds.
        eapply (f_equal (@rev _)) in Heqfwd_lbinds; listrew.
        subst lbinds; listrew.
        eapply equiv_suffix; eauto.
        - pose proof (expr_omits_rangeb_correct (length fwd_lbinds)
                                                (ptail, prog_end));
            destruct (expr_omits_rangeb (length fwd_lbinds) (ptail, prog_end));
            eauto; congruence.
        - rewrite renumber_expr_renumber_bindings.
          f_equal.
          eapply renumber_op_ext.
          intros.
          rewrite <-offset_renumbering_plus.
          f_equal.
          lia.
      Qed.
    End WithMap.
  End Rewriter.

  Section WithUnused.
    Context {Mbind_unused :
               forall {t1 t2} (a : M t1) (b : M t2),
                 Mequiv (Mbind a (fun _ => b)) b}.
    Arguments Mbind_unused {t1 t2}.

    Lemma interp_expr_cast_different ctxt ctx e t :
      t <> expr_type e ->
      Mequiv (interp_expr_cast ctxt ctx e t)
             (Mret interp_type_inhabited).
    Proof.
      intros; cbv [interp_expr_cast].
      setoid_rewrite <-(Mbind_unused (interp_expr ctxt ctx e)
                                     (Mret interp_type_inhabited)).
      step_Mequiv.
      rewrite cast_different by eauto; reflexivity.
    Qed.

    Lemma equiv_under_same_type ctxt ctx e1 e2 :
      expr_type e1 = expr_type e2 ->
      Mequiv (interp_expr ctxt ctx e1)
             (interp_expr_cast ctxt ctx e2 _) ->
      equiv_under ctxt ctx e1 e2.
    Proof.
      setoid_rewrite <-interp_expr_cast_expr_type.
      cbv [equiv_under].
      intros.
      destruct (type_eq_or t (expr_type e1)).
      - subst; eauto.
      - setoid_rewrite interp_expr_cast_different; try congruence.
        reflexivity.
    Qed.
  End WithUnused.
End Language.

Require Import FCF.FCF.
Close Scope rat_scope.
Close Scope vector_scope.
Require Import CrossCrypto.RewriteUtil.
Require Import CrossCrypto.fmap.list_of_pairs.

Module LanguageImpl.
  Inductive basetype : Set :=
  | tnat : basetype
  | tbool : basetype.

  Definition basetype_eqb (t1 t2 : basetype) : bool :=
    match t1, t2 with
    | tnat, tnat => true
    | tbool, tbool => true
    | _, _ => false
    end.
  Lemma basetype_eqb_eq t1 t2 : basetype_eqb t1 t2 = true <-> t1 = t2.
  Proof. destruct t1, t2; cbn [basetype_eqb]; intuition congruence. Qed.
  Instance basetype_eqdec : EqDec basetype :=
    Build_EqDec basetype_eqb basetype_eqb_eq.

  Definition interp_basetype (b : basetype) : Set :=
    match b with
    | tnat => nat
    | tbool => bool
    end.
  Definition interp_basetype_eqb {b} (x y : interp_basetype b)
    : bool :=
    match b return interp_basetype b -> interp_basetype b -> bool with
    | tnat
    | tbool => fun x y => x ?= y
    end x y.
  Lemma interp_basetype_eqb_eq {b} (x y : interp_basetype b) :
    interp_basetype_eqb x y = true <-> x = y.
  Proof. destruct b; cbn [interp_basetype_eqb]; crush_deciders idtac. Qed.
  Instance interp_basetype_eqdec {b} : EqDec (interp_basetype b) :=
    Build_EqDec interp_basetype_eqb interp_basetype_eqb_eq.

  Definition interp_basetype_inhabited {b} : interp_basetype b :=
    match b with
    | tnat => 0
    | tbool => false
    end.

  Definition basetype_transport {P : basetype -> Type} {b1} b2 :
    P b1 -> option (P b2) :=
    match b1, b2 with
    | tnat, tnat
    | tbool, tbool => Some
    | _, _ => fun _ => None
    end.
  Lemma basetype_transport_same {P b} (p : P b) :
    basetype_transport b p = Some p.
  Proof. destruct b; cbn [basetype_transport]; congruence. Qed.
  Lemma basetype_transport_different {P b1 b2} (p : P b1) :
    b2 <> b1 -> (@basetype_transport _ b1 b2 p) = None.
  Proof. destruct b1, b2; cbn [basetype_transport]; congruence. Qed.

  Definition B : Basetype :=
    Build_Basetype (@basetype)
                   (@basetype_eqdec)
                   (@interp_basetype)
                   (@interp_basetype_eqdec)
                   (@interp_basetype_inhabited)
                   (@basetype_transport)
                   (@basetype_transport_same)
                   (@basetype_transport_different).

  Notation type := (@type B).
  Notation interp_type := (@interp_type B).
  Notation tbase := (@tbase B).



  Definition MM t := Comp (interp_type t).
  Definition Ret {t : type} : interp_type t -> MM t :=
    Ret (EqDec_dec interp_type_eqdec).
  Definition Bind {t1 t2 : type} :
    MM t1 -> (interp_type t1 -> MM t2) -> MM t2 :=
    @Bind _ _.
  Definition MMequiv {t} : MM t -> MM t -> Prop := Comp_eq.
  Instance MMequiv_equiv {t} : Equivalence (@MMequiv t).
  Proof. typeclasses eauto. Qed.
  Instance Proper_Mbind {t1 t2} :
    Proper
      (MMequiv ==> (pointwise_relation _ MMequiv) ==> MMequiv)
      (@Bind t1 t2).
  Proof. eapply Proper_Bind. Qed.
  Lemma Bind_assoc {t1 t2 t3} (f : MM t1)
        (g : interp_type t1 -> MM t2) (h : interp_type t2 -> MM t3) :
    MMequiv (Bind (Bind f g) h)
           (Bind f (fun x => Bind (g x) h)).
  Proof. symmetry; eapply Bind_assoc. Qed.
  Lemma Mbind_Mret_l {t1 t2} x (f : interp_type t1 -> MM t2) :
    MMequiv (Bind (Ret x) f) (f x).
  Proof. eapply Bind_Ret_l. Qed.
  Lemma Mbind_Mret_r {t} (x : MM t) : MMequiv (Bind x Ret) x.
  Proof. eapply Bind_Ret_r. Qed.
  Lemma Mbind_comm (t1 t2 t3 : type) (c1 : MM t1) (c2 : MM t2)
        (c3 : interp_type t1 -> interp_type t2 -> MM t3) :
    MMequiv (Bind c1 (fun a => Bind c2 (fun b => c3 a b)))
            (Bind c2 (fun b => Bind c1 (fun a => c3 a b))).
  Proof. eapply Bind_comm. Qed.

  Definition Mon : @Monad B :=
    @Build_Monad B
                 (@MM)
                 (@Ret)
                 (@Bind)
                 (@MMequiv)
                 (@MMequiv_equiv)
                 (@Proper_Mbind)
                 (@Bind_assoc)
                 (@Mbind_Mret_l)
                 (@Mbind_Mret_r)
                 (@Mbind_comm).

  Inductive const : Type :=
  | coin.
  Definition const_eqb (c1 c2 : const) : bool :=
    match c1, c2 with
    | coin, coin => true
    end.
  Lemma const_eqb_eq (c1 c2 : const) : const_eqb c1 c2 = true <-> c1 = c2.
  Proof. destruct c1, c2; intuition eauto. Qed.
  Instance const_eqdec : EqDec const := Build_EqDec const_eqb const_eqb_eq.

  Definition cdom c : type :=
    match c with
    | coin => tunit
    end.

  Definition ccod c : type :=
    match c with
    | coin => tbase tbool
    end.

  Definition interp_const c : interp_type (cdom c) -> MM (ccod c) :=
    match c with
    | coin => fun _ => x <-$ Rnd 1; ret (Vector.nth x Fin.F1)
    end.

  Inductive retconst : Type :=
  | xor'
  | zero
  | id (t : type).

  Definition retconst_eqb (c c' : retconst) : bool :=
    match c, c' with
    | xor', xor' => true
    | zero, zero => true
    | id t1, id t2 => type_eqb t1 t2
    | _, _ => false
    end.
  Lemma retconst_eqb_eq c1 c2 : retconst_eqb c1 c2 = true <-> c1 = c2.
  Proof.
    destruct c1, c2; cbv [retconst_eqb]; rewrite ?type_eqb_eq;
      intuition congruence.
  Qed.
  Instance retconst_eqdec : EqDec retconst :=
    Build_EqDec retconst_eqb retconst_eqb_eq.

  Definition rcdom c : type :=
    match c with
    | xor' => tprod (tbase tbool) (tbase tbool)
    | zero => tunit
    | id t => t
    end.

  Definition rccod c : type :=
    match c with
    | xor' => tbase tbool
    | zero => tbase tbool
    | id t => t
    end.

  Definition interp_retconst c :
    interp_type (rcdom c) -> interp_type (rccod c) :=
    match c with
    | xor' => fun '(x, y) => xorb x y
    | zero => fun _ => false
    | id _ => fun x => x
    end.

  Definition C : @Const B Mon :=
    @Build_Const B Mon
                 (@const)
                 (@const_eqdec)
                 (@cdom)
                 (@ccod)
                 (@interp_const)
                 (@retconst)
                 (@retconst_eqdec)
                 (@rcdom)
                 (@rccod)
                 (@interp_retconst).

  (** Reification *)
  Ltac reify_type t :=
    lazymatch t with
    | prod ?ta ?tb =>
      let ta := reify_type ta in
      let tb := reify_type tb in
      uconstr:(tprod ta tb)
    | bool => uconstr:(tbase tbool)
    | unit => uconstr:(tbase tunit)
    | interp_type ?t => t
    | _ => fail "UNKNOWN TYPE" t
    end.

  Ltac pindexof x ctx :=
    lazymatch ctx with
    | (x, _) => uconstr:(O)
    | (_, ?ctx) =>
      let i := pindexof x ctx in
      uconstr:(S i)
    | _ => fail "NOT FOUND" x
    end.

  Ltac reify_ref ctx r :=
    lazymatch r with
    | pair ?a ?b =>
      let a := reify_ref ctx a in
      let b := reify_ref ctx b in
      uconstr:(ref_pair a b)
    | ?x =>
      let r := pindexof r ctx in
      uconstr:(ref_index r)
    end.

  Ltac reify_op ctx o :=
    lazymatch o with
    | ret tt => uconstr:(op_unit)
    | interp_const coin ?a =>
      let a := pindexof a ctx in
      uconstr:(op_app coin (ref_index a))
    | ret xorb ?a ?b =>
      let a := pindexof a ctx in
      let b := pindexof b ctx in
      uconstr:(op_retapp xor' (ref_pair (ref_index a) (ref_index b)))
    | ret ?x =>
      let t := lazymatch type of x with ?T => reify_type T end in
      let x := reify_ref ctx x in
      uconstr:(op_retapp (id t) x)
    | ?O => fail "UNKNOWN OP" O
    end.

  Ltac reify_to_list ctx e :=
    lazymatch e with
    | (x <-$ ?o; ?f) =>
      let T := lazymatch type of o with
               | Comp ?T => T
               | MM ?T => constr:(interp_type T)
               | ?X => fail "XX" X
               end in
      let o := reify_op ctx o in
      let _y := fresh in let y := fresh in (* andres thinks this might work around a coq bug but does not remember which one :( *)
      lazymatch constr:(fun (y:T) => ltac:(
          let r := reify_to_list
            constr:(pair y ctx)
            constr:(match y return _ with x => f end) in
          exact r
       )) with
      | fun _ => ?r => uconstr:(@cons op o r)
      | _ => fail "FUNDEP"
      end
    | ?o =>
      let o := reify_op ctx o in
      uconstr:(@cons op o (@nil op))
    | ?O => fail "UNKNOWN EXPR" O
    end.

  Ltac reify e :=
    let e := reify_to_list tt e in
    let e := eval cbv in (List.removelast e, List.last e op_unit) in
        constr:(e).

  Section ExampleCoins.
    Local Notation map := (list_of_pairs Nat.eqb).

    Notation expr := (@expr B Mon C).
    Notation op_app := (@op_app B Mon C).
    Notation op_retapp := (@op_retapp B Mon C).

    Definition example_coin_lemma_lhs : expr :=
      (op_unit
         :: op_unit
         :: (op_app coin (ref_index 1))
         :: (op_app coin (ref_index 1))
         :: nil,
       op_retapp xor' (ref_pair (ref_index 0) (ref_index 1))).

    Definition example_coin_lemma_rhs : expr :=
      ((op_unit :: nil), op_app coin (ref_index 0)).

    Lemma Bind_unused {t1 t2} (a : MM t1) (b : MM t2) :
      MMequiv (Bind a (fun _ => b)) b.
    Proof. eapply Bind_unused. Qed.

    Notation equiv := (@equiv B Mon C).

    Notation equiv_under_same_type :=
      (@equiv_under_same_type B Mon C (@Bind_unused)).

    Lemma example_coin_lemma :
      equiv example_coin_lemma_lhs example_coin_lemma_rhs.
    Proof.
      intros ??.
      eapply equiv_under_same_type; eauto.
      cbv -[Comp_eq
              interp_const interp_retconst
              interp_type_eqdec
              basetype_eqdec
              interp_basetype
              interp_basetype_inhabited
              interp_basetype_eqdec
              basetype_transport];
        cbn [interp_const interp_retconst interp_type
                          interp_basetype basetype_transport].
      (* anomalies if the wrong things are unfolded (see coq/coq#8204) *)
      repeat (setoid_rewrite RewriteUtil.Bind_Ret_l ||
              setoid_rewrite <-RewriteUtil.Bind_assoc).
      cbv [Comp_eq image_relation pointwise_relation evalDist getSupport
                   getAllBvectors].
      cbn [List.map app sumList fold_left
                    Vector.nth xorb Vector.caseS
                    expnat Nat.mul Nat.add].
      intros a.
      repeat lazymatch goal with
             | |- context[(@EqDec_dec bool ?x)] =>
               let d := fresh in
               pose (EqDec_dec x) as d;
                 change (EqDec_dec x) with d;
                 destruct (d true a), (d false a)
             end;
        try congruence; reflexivity.
    Qed.

    Existing Instance equiv_equiv.

    Definition coins_example : expr :=
      (op_unit :: op_app coin (ref_index 0)
               :: op_unit :: op_app coin (ref_index 0)
               :: op_unit :: op_app coin (ref_index 0)
               :: op_retapp xor' (ref_pair (ref_index 4) (ref_index 0))
               :: nil,
       op_retapp
         (id (tprod (tprod (tbase tbool) (tbase tbool)) (tbase tbool)))
         (ref_pair (ref_pair (ref_index 0) (ref_index 3)) (ref_index 3))).
    Derive coins_endpoint
           SuchThat (equiv coins_example coins_endpoint)
           As coins_example_rewrite.
    Proof.
      set (lbinds := rev (fst example_coin_lemma_lhs)).
      set (lhead := snd example_coin_lemma_lhs).
      pose proof (commute_matches_correct
                    map lbinds lhead coins_example) as HC.
      set (C := commute_matches _ _ _ _) in HC.
      (* since introduction of records this computation is quite slow
         with every strategy except cbn. *)
      (* Time lazy in C. (* 32.827 secs *) *)
      (* Time cbv in C. (* 18.912 secs *) *)
      (* Time vm_compute in C. (* 2.201 secs *) *)
      (* Time native_compute in C. (* 2.428 secs *) *)
      (* Time cbn in C. (* 0.176 secs *) *)
      cbn in C.
      cbv [C assemble] in HC.
      eapply Forall_inv in HC.
      cbv [rev_append] in HC.
      setoid_rewrite HC; clear HC.

      set (fwd_rbinds := fst example_coin_lemma_rhs).
      set (rhead := snd example_coin_lemma_rhs).

      pose proof (replace_lemma_correct
                    lbinds fwd_rbinds lhead rhead
                    (op_app coin (ref_index 1)
                            :: op_app coin (ref_index 1)
                            :: op_unit :: op_unit
                            :: op_app coin (ref_index 0) :: op_unit :: nil)
                    (op_retapp xor' (ref_pair (ref_index 0) (ref_index 1)))
                    nil
                    (op_retapp (id (tprod (tprod (tbase tbool) (tbase tbool))
                                          (tbase tbool)))
                               (ref_pair (ref_pair (ref_index 0)
                                                   (ref_index 5))
                                         (ref_index 5)))
                    eq_refl
                    example_coin_lemma) as HR.
      (* Again reduction is slow if not using cbn *)
      set (R := replace_lemma _ _ _ _ _ _ _ _) in HR; cbn in R.
      cbv [R assemble rev_append] in HR.
      setoid_rewrite HR; clear HR.
      subst coins_endpoint; reflexivity.
    Qed.

    (* reification not yet ported because of modularity issues *)

    (* Definition coins_example' := *)
    (*   x <-$ ret tt; *)
    (*     x0 <-$ interp_const coin x; *)
    (*     x1 <-$ ret tt; *)
    (*     x2 <-$ interp_const coin x1; *)
    (*     x3 <-$ ret tt; *)
    (*     x4 <-$ interp_const coin x3; *)
    (*     x5 <-$ ret xorb x0 x4; *)
    (*     ret (x5, x2, x2). *)
    (* Derive reified_coins_example *)
    (*        SuchThat (reified_coins_example = coins_example') *)
    (*        As reified_coins_example'_correct. *)
    (* Proof. *)
    (*   cbv [coins_example']. *)

    (*   let x := reified_coins_example in *)
    (*   let x := eval unfold x in x in *)
    (*       let e := match goal with |- ?LHS = ?RHS => RHS end in *)
    (*       let e := reify e in *)
    (*       unify x (interp_expr tunit tt e). *)

    (*   reflexivity. *)
    (* Qed. *)
    (* Print reified_coins_example. *)
  End ExampleCoins.
End LanguageImpl.
