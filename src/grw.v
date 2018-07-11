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

Section RenumberExt.
  Context (f f' : nat -> nat)
          (H : forall n, f n = f' n).
  Lemma renumber_ref_ext r : renumber_ref f r = renumber_ref f' r.
  Proof. induction r; cbn [renumber_ref]; congruence. Qed.
  Lemma renumber_op_ext o : renumber_op f o = renumber_op f' o.
  Proof.
    induction o; cbn [renumber_op]; try rewrite renumber_ref_ext; congruence.
  Qed.
End RenumberExt.
Lemma renumber_bindings_ext f f' p :
  (forall n, f n = f' n) ->
  renumber_bindings f p = renumber_bindings f' p.
Proof.
  revert f f'; induction p as [|o p]; eauto.
  intros; cbn [renumber_bindings].
  f_equal; eauto using renumber_op_ext.
  apply IHp.
  intros n.
  cbv [offset_renumbering]; destruct (optsub n 1); congruence.
Qed.

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

Lemma lookup_renumber_ref ctxt ctx ctxt' ctx' f r t :
  context_renumbered f ctxt ctx ctxt' ctx' ->
  lookup_ref ctxt' ctx' (renumber_ref f r) t =
  lookup_ref ctxt ctx r t.
Proof.
  cbv [context_renumbered].
  intros.
  revert t; induction r; intros t; cbn [lookup_ref renumber_ref]; eauto.
  destruct t; eauto.
  rewrite IHr1, IHr2.
  reflexivity.
Qed.

Lemma interp_op_renumber n f o ctxt ctx ctxt' ctx' tk
      (k k' : forall ctxt, interp_type ctxt -> M tk) :
  context_renumbered (offset_renumbering n f) ctxt ctx ctxt' ctx' ->
  continuation_renumbered (offset_renumbering (n + 1) f) tk k k' ->
  Mequiv
    (Mbind (interp_op_silent ctxt ctx o)
       (fun x : interp_type (op_type o) =>
        k (op_type o * ctxt)%etype (x, ctx)))
    (Mbind
       (interp_op_silent ctxt' ctx'
          (renumber_op (offset_renumbering n f) o))
       (fun
          x : interp_type
                (op_type
                   (renumber_op (offset_renumbering n f) o)) =>
        k'
          (op_type (renumber_op (offset_renumbering n f) o) *
           ctxt')%etype (x, ctx'))).
Proof.
  intros Hctx Hk.
  destruct o; cbn [renumber_op op_type];
    (eapply Mequiv_Mbind;
     [|intros;
       eapply Hk;
       rewrite plus_comm;
       rewrite context_renumbered_ext by
           (eauto using offset_renumbering_plus);
       eapply context_renumbered_1; eauto]).
  - reflexivity.
  - cbv [interp_op_silent interp_op].
    erewrite lookup_renumber_ref by eauto.
    reflexivity.
  - cbv [interp_op_silent interp_op].
    erewrite lookup_renumber_ref by eauto.
    reflexivity.
Qed.

Lemma interp_renumbered_bindings (f : nat -> nat)
      (p : list operation)
      tk (k k' : forall ctxt : type, interp_type ctxt -> M tk) :
  continuation_renumbered (offset_renumbering (length p) f) tk k k' ->
  continuation_renumbered
    f tk
    (fun ctxt ctx => interp_bindings ctxt ctx p tk k)
    (fun ctxt ctx => interp_bindings ctxt ctx (renumber_bindings f p) tk k').
Proof.
  revert tk k k'.
  pattern p; eapply rev_ind;
    cbn [renumber_bindings interp_bindings length offset_renumbering
                           optsub plus]; eauto.
  clear p.
  intros o p IHp tk k k' Hkk'.
  rewrite app_length in Hkk'; cbn [length] in Hkk'.
  rewrite renumber_bindings_app.
  cbn [renumber_bindings].
  setoid_rewrite interp_bindings_app.
  eapply IHp.
  cbn [interp_bindings].
  intros ctxt ctx ctxt' ctx' Hctx'.
  eapply interp_op_renumber; eauto.
Qed.
