Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.derive.Derive.

Require Import FCF.FCF FCF.EqDec.
Close Scope rat_scope.
Close Scope vector_scope.

Require Import CrossCrypto.RewriteUtil.
Require Import CrossCrypto.ListUtil.


Inductive type : Set :=
| tunit : type
| tnat : type
| tbool : type
| tprod : type -> type -> type.

Lemma type_dec (t1 t2 : type) : {t1 = t2} + {t1 <> t2}.
Proof. decide equality. Defined.

Bind Scope etype_scope with type.
Delimit Scope etype_scope with etype.
Local Notation "A * B" := (tprod A%etype B%etype) : etype_scope.

Fixpoint interp_type (t : type) : Set :=
  match t with
  | tunit => unit
  | tnat => nat
  | tbool => bool
  | tprod t1 t2 => interp_type t1 * interp_type t2
  end.

Lemma interp_type_dec {t} (x1 x2 : interp_type t) : {x1 = x2} + {x1 <> x2}.
Proof. induction t; decide equality. Defined.

(* necessary for ret *)
Local Instance interp_type_eqdec {t} : EqDec (interp_type t).
Proof. induction t; typeclasses eauto. Defined.

Ltac type_head x :=
  match x with
  | tunit => idtac
  | tnat => idtac
  | tbool => idtac
  | tprod _ _ => idtac
  end.

Fixpoint type_inhabited {t : type} : interp_type t :=
  match t with
  | tunit => tt
  | tbool => false
  | tnat => 0%nat
  | tprod t1 t2 => (type_inhabited, type_inhabited)
  end.

Definition M t := Comp (interp_type t).
Definition Mret {t : type} : interp_type t -> M t :=
  Ret (EqDec_dec interp_type_eqdec).
Definition Mbind {t1 t2 : type} :
  M t1 ->
  (interp_type t1 -> M t2) -> M t2 :=
  @Bind _ _.
Definition Mequiv {t} : M t -> M t -> Prop := Comp_eq.

Inductive const : Type :=
| coin.

Lemma const_dec (c1 c2 : const) : {c1 = c2} + {c1 <> c2}.
Proof. decide equality. Defined.

Definition cdom c : type :=
  match c with
  | coin => tunit
  end.

Definition ccod c : type :=
  match c with
  | coin => tbool
  end.

Definition interp_const c : interp_type (cdom c) -> M (ccod c) :=
  match c with
  | coin => fun _ => x <-$ Rnd 1; ret (Vector.nth x Fin.F1)
  end.

Inductive ret_const : Type :=
| xor'
| zero.

Lemma retconst_dec (c1 c2 : ret_const) : {c1 = c2} + {c1 <> c2}.
Proof. decide equality. Defined.

Definition rcdom c : type :=
  match c with
  | xor' => tbool * tbool
  | zero => tunit
  end.

Definition rccod c : type :=
  match c with
  | xor' => tbool
  | zero => tbool
  end.

Definition interp_retconst c :
  interp_type (rcdom c) -> interp_type (rccod c) :=
  match c with
  | xor' => fun '(x, y) => xorb x y
  | zero => fun _ => false
  end.

(* De bruijn indices which can be paired together to get a tuple *)
Inductive ref : Type :=
| ref_index : nat -> ref
| ref_pair : ref -> ref -> ref.

Inductive operation : Type :=
| op_unit : operation
| op_app (c : const) : ref -> operation
| op_retapp (c : ret_const) : ref -> operation.

Lemma op_dec (o1 o2 : operation) : {o1 = o2} + {o1 <> o2}.
Proof. repeat decide equality. Defined.

Definition op_type o : type :=
  match o with
  | op_unit => tunit
  | op_app c _ => ccod c
  | op_retapp c _ => rccod c
  end.

Definition transport {P : type -> Type} {a : type} (b : type) (p : P a)
  : option (P b).
  destruct (type_dec a b).
  - subst; exact (Some p).
  - exact None.
Defined.

Fixpoint lookup (ctxt : type) (ctx : interp_type ctxt)
         (n : nat) (t : type) {struct n}
  : option (interp_type t).
  destruct ctxt; [exact None .. |].
  refine match n, ctx with
         | 0, (x, _) => transport t x
         | S n, (_, ctx) => lookup ctxt2 ctx n t
         end.
Defined.

Fixpoint lookup_ref (ctxt : type) (ctx : interp_type ctxt)
         (r : ref) (t : type) {struct r} : option (interp_type t) :=
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

Definition interp_op (ctxt : type) (ctx : interp_type ctxt)
           (o : operation) : option (M (op_type o)) :=
  match o with
  | op_unit => Some (@Mret tunit tt)
  | op_app c r => match lookup_ref ctxt ctx r (cdom c) with
                    | Some x => Some (interp_const c x)
                    | None => None
                    end
  | op_retapp c r => match lookup_ref ctxt ctx r (rcdom c) with
                       | Some x => Some (Mret (interp_retconst c x))
                       | None => None
                       end
  end.

Definition interp_op_silent (ctxt : type) (ctx : interp_type ctxt)
           (o : operation) : M (op_type o) :=
  match interp_op ctxt ctx o with
  | Some m => m
  | None => Mret type_inhabited
  end.

Definition expr : Type := (list operation) * operation.

Definition expr_type '((_, p2) : expr) : type := op_type p2.

(* Interpreter in continuation-passing style. This has several
   advantages over direct style:
   - No need to rewrite Bind_Ret_l (very slowly!) on binds of the
     contexts to get the correct form and to eliminate
     lookups/transports
   - Good commutation relation with List.app
   - Can refer to universally-quantified variables as free de Bruijn indices
*)
Fixpoint interp_bindings (ctxt : type) (ctx : interp_type ctxt)
         (p : list operation)
         (tk : type) (k : forall ctxt : type, interp_type ctxt -> M tk)
         {struct p} : (M tk) :=
  match p with
  | nil => k ctxt ctx
  | cons o p =>
    Mbind (interp_op_silent ctxt ctx o)
          (fun x => interp_bindings (op_type o * ctxt) (x, ctx) p tk k)
  end.

Definition interp_expr (ctxt : type) (ctx : interp_type ctxt)
           (e : expr) : M (expr_type e) :=
  let '(p, o) := e in
  interp_bindings ctxt ctx p (op_type o)
                  (fun ctxt ctx => interp_op_silent ctxt ctx o).

Example reflection_example :
  let x := ((op_unit
               :: op_unit
               :: (op_app coin (ref_index 1))
               :: (op_app coin (ref_index 1))
               :: nil),
            (op_retapp xor' (ref_pair (ref_index 0) (ref_index 1)))) in
  {z | forall ctxt ctx,
      let y := interp_expr ctxt ctx x in
      Comp_eq y z}.
Proof.
  intros x.
  eexists.
  intros.
  subst x y.
  cbv - [Vector.nth xorb Comp_eq].
  repeat setoid_rewrite Bind_unused.
  reflexivity.
Defined.

Lemma Mequiv_Mbind (t1 t2 : type)
      (c1 c1' : M t1) (c2 c2' : interp_type t1 -> M t2) :
  Mequiv c1 c1' ->
  (forall x, Mequiv (c2 x) (c2' x)) ->
  Mequiv (Mbind c1 c2) (Mbind c1' c2').
Proof. cbv [Mequiv Mbind]; intros; eapply Proper_Bind; eauto. Qed.

Lemma interp_bindings_app ctxt (ctx : interp_type ctxt)
      (p1 p2 : list operation) tk (k : forall ctxt, interp_type ctxt -> M tk) :
  Mequiv
    (interp_bindings ctxt ctx (p1 ++ p2) tk k)
    (interp_bindings ctxt ctx p1 tk
                     (fun ctxt ctx => interp_bindings ctxt ctx p2 tk k)).
Proof.
  revert ctxt ctx p2 tk k;
    induction p1 as [|o p1]; intros ctxt ctx p2 tk k;
      [reflexivity|].
  cbn [interp_bindings app].
  eapply Mequiv_Mbind; [reflexivity | eauto].
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

Definition renumber_op (f : nat -> nat) (o : operation) : operation :=
  match o with
  | op_unit => op_unit
  | op_app c r => op_app c (renumber_ref f r)
  | op_retapp c r => op_retapp c (renumber_ref f r)
  end.

Fixpoint optsub (n m : nat) {struct m} : option nat :=
  match m with
  | 0 => Some n
  | S m => match n with
           | 0 => None
           | S n => optsub n m
           end
  end.

Local Notation "a -? b" := (optsub a b) (left associativity, at level 50).

Lemma optsub_plus a b :
  match a -? b with
  | Some c => a = b + c
  | None => True
  end.
Proof.
  revert a; induction b; intros a; cbn [optsub plus]; eauto.
  destruct a; eauto.
  specialize (IHb a).
  destruct (a -? b); eauto.
Qed.

Definition offset_renumbering (offset : nat)
           (f : nat -> nat) (n : nat) : nat :=
  match n -? offset with
  | Some k => offset + (f k)
  | None => n
  end.

Fixpoint renumber_bindings (f : nat -> nat) (p : list operation)
  : list operation :=
  match p with
  | nil => nil
  | cons o p =>
    cons (renumber_op f o)
         (renumber_bindings (offset_renumbering 1 f) p)
  end.

Fixpoint refs (r : ref) (n : nat) :=
  match r with
  | ref_index k => n = k
  | ref_pair r1 r2 => refs r1 n \/ refs r2 n
  end.

Definition op_refs (o : operation) (n : nat) :=
  match o with
  | op_unit => False
  | op_app _ r | op_retapp _ r => refs r n
  end.

Fixpoint bindings_ref (p : list operation) (n : nat) :=
  match p with
  | nil => False
  | o :: p => op_refs o n \/ bindings_ref p (S n)
  end.

Lemma bindings_ref_app (p1 p2 : list operation) n :
  bindings_ref (p1 ++ p2) n <->
  bindings_ref p1 n \/ bindings_ref p2 (length p1 + n).
Proof.
  revert n; induction p1; intros n; cbn [bindings_ref length plus app].
  - intuition idtac.
  - replace (S (length p1 + n)) with (length p1 + S n) by omega.
    setoid_rewrite IHp1; intuition idtac.
Qed.

Lemma renumber_ref_ext f f' r :
  (forall i, refs r i -> f i = f' i) ->
  renumber_ref f r = renumber_ref f' r.
  Proof.
    intros Hf; induction r; cbn [renumber_ref refs] in *.
    - rewrite Hf; eauto.
    - rewrite IHr1, IHr2; eauto.
  Qed.

  Lemma renumber_op_ext f f' o :
    (forall i, op_refs o i -> f i = f' i) ->
    renumber_op f o = renumber_op f' o.
  Proof.
    intros Hf; induction o; cbn [renumber_op];
      try erewrite renumber_ref_ext; eauto.
  Qed.

Lemma renumber_bindings_ext_relevant f f' p :
  (forall i, bindings_ref p i -> f i = f' i) ->
  renumber_bindings f p = renumber_bindings f' p.
Proof.
  revert f f'; induction p as [|o p]; eauto.
  intros; cbn [renumber_bindings bindings_ref] in *.
  f_equal; try (erewrite renumber_op_ext; eauto).
  apply IHp.
  intros []; cbv [offset_renumbering optsub]; eauto.
Qed.

Lemma renumber_bindings_ext f f' p :
  (forall i, f i = f' i) ->
  renumber_bindings f p = renumber_bindings f' p.
Proof. intros; eapply renumber_bindings_ext_relevant; eauto. Qed.

Lemma offset_renumbering_plus a b n f :
  offset_renumbering (a + b) f n =
  offset_renumbering a (offset_renumbering b f) n.
Proof.
  revert b n; induction a; intros b n; eauto.
  cbv [offset_renumbering] in *.
  rewrite PeanoNat.Nat.add_succ_l.
  cbn [optsub].
  destruct n; eauto.
  specialize (IHa b n).
  destruct (n -? (a + b)), (n -? a); omega.
Qed.

Lemma renumber_bindings_app (f : nat -> nat) (p1 p2 : list operation) :
  renumber_bindings f (p1 ++ p2) =
  (renumber_bindings f p1)
    ++ renumber_bindings (offset_renumbering (length p1) f) p2.
Proof.
  revert f; induction p1; intros f; eauto.
  repeat (rewrite <- app_comm_cons ||
          cbn [renumber_bindings offset_renumbering optsub length]).
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
  intros; split; intros.
  - etransitivity; [symmetry; eauto|];
      etransitivity; [|eauto]; eauto.
  - etransitivity; [|symmetry; eauto];
      etransitivity; [eauto|]; eauto.
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

Lemma lookup_renumbered_ref ctxt ctx ctxt' ctx' f g r t :
  context_renumbered f ctxt ctx ctxt' ctx' ->
  (forall i, refs r i -> g i = f i) ->
  lookup_ref ctxt' ctx' (renumber_ref g r) t =
  lookup_ref ctxt ctx r t.
Proof.
  cbv [context_renumbered].
  intros ? Hg.
  revert t; induction r; intros t; cbn [lookup_ref renumber_ref refs] in *.
  - rewrite Hg; cbn [refs]; eauto.
  - destruct t; eauto.
    rewrite IHr1, IHr2 by eauto.
    reflexivity.
Qed.

Lemma interp_renumbered_op n f g o ctxt ctx ctxt' ctx' tk
      (k k' : forall ctxt, interp_type ctxt -> M tk) :
  context_renumbered (offset_renumbering n f) ctxt ctx ctxt' ctx' ->
  continuation_renumbered (offset_renumbering (n + 1) f) tk k k' ->
  (forall i, op_refs o (n + i) -> g i = f i) ->
  Mequiv
    (Mbind (interp_op_silent ctxt ctx o)
       (fun x => k (op_type o * ctxt)%etype (x, ctx)))
    (Mbind
       (interp_op_silent ctxt' ctx'
          (renumber_op (offset_renumbering n g) o))
       (fun x => k'
                   (op_type (renumber_op (offset_renumbering n g) o) *
                    ctxt')%etype (x, ctx'))).
Proof.
  intros Hctx Hk Hg.
  destruct o; cbn [renumber_op op_type op_refs] in *;
    (eapply Mequiv_Mbind;
     [|intros;
       eapply Hk;
       rewrite plus_comm;
       rewrite context_renumbered_ext by
           (eauto using offset_renumbering_plus);
       eapply context_renumbered_1; eauto]).
  - reflexivity.
  - cbv [interp_op_silent interp_op].
    erewrite lookup_renumbered_ref by
        (eauto; cbv [offset_renumbering];
         intros i ?; pose proof optsub_plus i n;
         destruct (i -? n); subst; eauto).
    reflexivity.
  - cbv [interp_op_silent interp_op].
    erewrite lookup_renumbered_ref by
        (eauto; cbv [offset_renumbering];
         intros i ?; pose proof optsub_plus i n;
         destruct (i -? n); subst; eauto).
    reflexivity.
Qed.

Lemma interp_renumbered_bindings_relevant (f g : nat -> nat)
      (p : list operation)
      tk (k k' : forall ctxt : type, interp_type ctxt -> M tk) :
  continuation_renumbered (offset_renumbering (length p) f) tk k k' ->
  (forall i, bindings_ref p i -> g i = f i) ->
  continuation_renumbered
    f tk
    (fun ctxt ctx => interp_bindings ctxt ctx p tk k)
    (fun ctxt ctx => interp_bindings ctxt ctx (renumber_bindings g p) tk k').
Proof.
  revert tk k k'.
  pattern p; revert p; eapply rev_ind;
    cbn [renumber_bindings interp_bindings length offset_renumbering
                           optsub plus]; eauto.
  intros o p IHp tk k k' Hkk' Hg.
  rewrite app_length in Hkk'; cbn [length] in Hkk'.
  setoid_rewrite bindings_ref_app in Hg; cbn [bindings_ref] in Hg.
  rewrite renumber_bindings_app.
  cbn [renumber_bindings].
  setoid_rewrite interp_bindings_app.
  eapply IHp; eauto.
  cbn [interp_bindings].
  intros ?????; eapply interp_renumbered_op; eauto.
Qed.

Lemma interp_renumbered_bindings (f : nat -> nat)
      (p : list operation)
      tk (k k' : forall ctxt : type, interp_type ctxt -> M tk) :
  continuation_renumbered (offset_renumbering (length p) f) tk k k' ->
  continuation_renumbered
    f tk
    (fun ctxt ctx => interp_bindings ctxt ctx p tk k)
    (fun ctxt ctx => interp_bindings ctxt ctx (renumber_bindings f p) tk k').
Proof. intros; eapply interp_renumbered_bindings_relevant; eauto. Qed.

Lemma Mbind_comm (t1 t2 t3 : type) (c1 : M t1) (c2 : M t2)
      (c3 : interp_type t1 -> interp_type t2 -> M t3) :
  Mequiv (Mbind c1 (fun a => Mbind c2 (fun b => c3 a b)))
         (Mbind c2 (fun b => Mbind c1 (fun a => c3 a b))).
Proof. eapply Bind_comm. Qed.

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
      (o1 o2 : operation)
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
  { eapply Mequiv_Mbind; [reflexivity|intros x].
    eapply Mequiv_Mbind; [reflexivity|intros y].
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
  { eapply Mequiv_Mbind; [reflexivity|intros x].
    destruct o2; cbn [op_type renumber_op];
      (eapply Mequiv_Mbind; [|reflexivity]);
      cbn [op_refs] in Ho2; cbv [interp_op_silent interp_op].
    - reflexivity.
    - rewrite lookup_unref_0 by eauto.
      reflexivity.
    - rewrite lookup_unref_0 by eauto.
      reflexivity. }

  transitivity
  (Mbind (interp_op_silent ctxt ctx (renumber_op pred o2))
         (fun y =>
            Mbind (interp_op_silent ctxt ctx o1)
                  (fun x =>
                     k' (op_type o1 *
                         (op_type (renumber_op pred o2) * ctxt))%etype
                        (x, (y, ctx))))).
  { eapply Mbind_comm. }

  { eapply Mequiv_Mbind; [reflexivity|intros y].
    destruct o1; cbn [op_type renumber_op];
      (eapply Mequiv_Mbind; [|reflexivity]);
      cbv [interp_op_silent interp_op].
    - reflexivity.
    - rewrite lookup_ref_S.
      reflexivity.
    - rewrite lookup_ref_S.
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

Lemma renumber_id_ref r :
  renumber_ref (fun x => x) r = r.
Proof. induction r; cbn [renumber_ref]; congruence. Qed.

Lemma renumber_id_op o :
  renumber_op (fun x => x) o = o.
Proof.
  destruct o; cbn [renumber_op]; try rewrite renumber_id_ref; congruence.
Qed.

Lemma commute_many ctxt (ctx : interp_type ctxt)
      (o : operation) (p : list operation)
      tk (ks : nat -> forall ctxt, interp_type ctxt -> M tk) :
  ~bindings_ref p 0 ->
  (forall j,
      j < length p ->
      continuation_renumbered
        (offset_renumbering j
           (fun n => match n with
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

    cbn [renumber_bindings length interp_bindings] in IHlenp |- *.
    eapply Mequiv_Mbind; [reflexivity|intros x].
    fold interp_bindings.
    fold (app (renumber_bindings (offset_renumbering 1 pred) p)).

    etransitivity.
    {
      eapply IHlenp; eauto.
      - rewrite length_renumber; eauto.
      - setoid_rewrite bindings_ref_renumber.
        intros ([|[]]&?&?); intuition congruence.
    }

    replace (renumber_op (plus (S (length p))) o) with
        (renumber_op (plus (length p)) (renumber_op S o)) by
        (erewrite <-renumber_renumber_op; eauto; intros; omega).
    erewrite <-renumber_renumber_bindings by (intros; reflexivity).
    rewrite renumber_bindings_ext_relevant with
        (f' := (offset_renumbering 1 pred)); try reflexivity.
    intros [|[]] ?; intuition idtac.
Qed.
