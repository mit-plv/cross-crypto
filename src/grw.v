Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.derive.Derive.
Require Import Coq.Strings.String.

Require Import FCF.FCF FCF.EqDec.
Close Scope rat_scope.
Close Scope vector_scope.

Require Import CrossCrypto.RewriteUtil.
Require Import CrossCrypto.ListUtil.
Require CrossCrypto.fmap.list_of_pairs.

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
  | None => a < b
  end.
Proof.
  revert a; induction b; intros a; cbn [optsub plus]; eauto.
  destruct a; try omega.
  specialize (IHb a).
  destruct (a -? b); omega.
Qed.

Local Ltac destruct_decider k comparison lemma a b :=
  pose proof (lemma a b); destruct (comparison a b);
  try k a;
  try k b.

Local Ltac crush_deciders_in x :=
  lazymatch x with
  | context[?a =? ?b] =>
    destruct_decider crush_deciders_in Nat.eqb Nat.eqb_eq a b
  | context[?a -? ?b] =>
    destruct_decider crush_deciders_in optsub optsub_plus a b
  | context[?a <=? ?b] =>
    destruct_decider crush_deciders_in Nat.leb Nat.leb_le a b
  | context[?a <? ?b] =>
    destruct_decider crush_deciders_in Nat.ltb Nat.ltb_lt a b
  end.

Local Ltac crush_deciders t :=
  repeat (multimatch goal with
          | |- ?x => crush_deciders_in x
          | H : ?x -> false = true |- _ =>
            assert (~ x) by (let H' := fresh in
                             intro H'; specialize (H H');
                             congruence);
            clear H
          | _ => intuition idtac
          | _ => omega
          end; t).

Inductive type : Set :=
| tunit : type
| tnat : type
| tbool : type
| tprod : type -> type -> type.

Lemma type_dec (t1 t2 : type) : {t1 = t2} + {t1 <> t2}.
Proof. decide equality. Defined.

Fixpoint type_eqb (t1 t2 : type) : bool :=
  match t1, t2 with
  | tunit, tunit => true
  | tnat, tnat => true
  | tbool, tbool => true
  | tprod t1a t1b, tprod t2a t2b => andb (type_eqb t1a t2a) (type_eqb t1b t2b)
  | _, _ => false
  end.
Lemma type_eqb_eq t1 t2 : type_eqb t1 t2 = true <-> t1 = t2.
Proof.
  split.
  - revert t2; induction t1; destruct t2; cbn [type_eqb];
      intuition (try congruence).
    rewrite andb_true_iff in *;
      erewrite IHt1_1, IHt1_2; intuition eauto.
  - intros; subst t2; induction t1; cbn [type_eqb]; try congruence.
    rewrite andb_true_iff; intuition congruence.
Qed.

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

Definition const_eqb (c1 c2 : const) : bool :=
  match c1, c2 with
  | coin, coin => true
  end.
Lemma const_eqb_eq (c1 c2 : const) : const_eqb c1 c2 = true <-> c1 = c2.
Proof. destruct c1, c2; intuition eauto. Qed.

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
| zero
| id (t : type).

Lemma retconst_dec (c1 c2 : ret_const) : {c1 = c2} + {c1 <> c2}.
Proof. repeat decide equality. Defined.

Definition retconst_eqb (c c' : ret_const) : bool :=
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

Definition rcdom c : type :=
  match c with
  | xor' => tbool * tbool
  | zero => tunit
  | id t => t
  end.

Definition rccod c : type :=
  match c with
  | xor' => tbool
  | zero => tbool
  | id t => t
  end.

Definition interp_retconst c :
  interp_type (rcdom c) -> interp_type (rccod c) :=
  match c with
  | xor' => fun '(x, y) => xorb x y
  | zero => fun _ => false
  | id _ => fun x => x
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
Proof. repeat decide equality; congruence. Defined.

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
         (n : nat) (t : type) {struct n} : option (interp_type t).
  destruct ctxt; [exact None .. |].
  refine match n, ctx with
         | 0, (x, _) => transport t x
         | S n, (_, ctx) => lookup ctxt2 ctx n t
         end.
Defined.

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

Definition cast {a : type} (b : type) (x : interp_type a) : interp_type b :=
  match transport b x with
  | Some x => x
  | None => type_inhabited
  end.

Definition interp_op_silent ctxt ctx o : M (op_type o) :=
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

Definition interp_expr ctxt ctx e : M (expr_type e) :=
  let '(p, o) := e in
  interp_bindings ctxt ctx p (op_type o)
                  (fun ctxt ctx => interp_op_silent ctxt ctx o).

Definition interp_expr_cast ctxt ctx e t : M t :=
  Mbind (interp_expr ctxt ctx e)
        (fun x => Mret (cast t x)).

Lemma Mequiv_Mbind {t1 t2 : type}
      (c1 c1' : M t1) (c2 c2' : interp_type t1 -> M t2) :
  Mequiv c1 c1' ->
  (forall x, Mequiv (c2 x) (c2' x)) ->
  Mequiv (Mbind c1 c2) (Mbind c1' c2').
Proof. cbv [Mequiv Mbind]; intros; eapply Proper_Bind; eauto. Qed.

Lemma Mbind_assoc {t1 t2 t3} (f : M t1)
      (g : interp_type t1 -> M t2) (h : interp_type t2 -> M t3) :
  Mequiv (Mbind (Mbind f g) h)
         (Mbind f (fun x => Mbind (g x) h)).
Proof. setoid_rewrite <-Bind_assoc; reflexivity. Qed.

Lemma Mbind_comm (t1 t2 t3 : type) (c1 : M t1) (c2 : M t2)
      (c3 : interp_type t1 -> interp_type t2 -> M t3) :
  Mequiv (Mbind c1 (fun a => Mbind c2 (fun b => c3 a b)))
         (Mbind c2 (fun b => Mbind c1 (fun a => c3 a b))).
Proof. eapply Bind_comm. Qed.

Lemma Mbind_Mret_l {t1 t2} x (f : interp_type t1 -> M t2) :
  Mequiv (Mbind (Mret x) f) (f x).
Proof. eapply Bind_Ret_l. Qed.

Lemma Mbind_Mret_r {t} (x : M t) : Mequiv (Mbind x Mret) x.
Proof. eapply Bind_Ret_r. Qed.

Lemma Mbind_unused {t1 t2} (a : M t1) (b : M t2) :
  Mequiv (Mbind a (fun _ => b)) b.
Proof. eapply Bind_unused. Qed.

Local Create HintDb mbind discriminated.
Hint Rewrite
     @Mbind_assoc
     @Mbind_Mret_l
     @Mbind_Mret_r
     @Mbind_unused
  : mbind.

Ltac step_Mequiv :=
  repeat multimatch goal with
         | |- Mequiv (Mbind _ _) (Mbind _ _) =>
           eapply Mequiv_Mbind; [try reflexivity | intros]
         | |- Mequiv ?x ?y => change x with y; reflexivity
         | |- _ => autorewrite with mbind
         end.

Lemma transport_same {P t} (x : P t) : transport t x = Some x.
Proof.
  cbv [transport eq_rect_r]; destruct (type_dec t t); try congruence.
  cbv [eq_rect_r]. rewrite <-eq_rect_eq_dec; eauto using type_dec.
Qed.

Lemma cast_same {t} (x : interp_type t) : cast t x = x.
Proof. cbv [cast]; rewrite transport_same; eauto. Qed.

Lemma interp_expr_cast_expr_type ctxt ctx e :
  Mequiv (interp_expr_cast ctxt ctx e (expr_type e))
         (interp_expr ctxt ctx e).
Proof.
  cbv [interp_expr_cast].
  setoid_rewrite <-(Mbind_Mret_r (interp_expr ctxt ctx e)) at 2.
  eapply Mequiv_Mbind; [reflexivity|intros].
  rewrite cast_same; reflexivity.
Qed.

Lemma transport_different {P t u} (x : P t) : u <> t -> transport u x = None.
Proof.
  intros; cbv [transport eq_rect_r]; destruct (type_dec t u); congruence.
Qed.

Lemma cast_different {t u} (x : interp_type t) :
  u <> t -> cast u x = type_inhabited.
Proof. intros; cbv [cast]; rewrite transport_different; eauto. Qed.

Lemma interp_expr_cast_different ctxt ctx e t :
  t <> expr_type e ->
  Mequiv (interp_expr_cast ctxt ctx e t)
         (Mret type_inhabited).
Proof.
  intros; cbv [interp_expr_cast].
  setoid_rewrite <-(Mbind_unused (interp_expr ctxt ctx e)
                                 (Mret type_inhabited)).
  eapply Mequiv_Mbind; [reflexivity|intros].
  rewrite cast_different by eauto; reflexivity.
Qed.

Definition equiv_under ctxt ctx e1 e2 :=
  forall t, Mequiv (interp_expr_cast ctxt ctx e1 t)
                   (interp_expr_cast ctxt ctx e2 t).

Definition equiv e1 e2 := forall ctxt ctx, equiv_under ctxt ctx e1 e2.
Lemma equiv_relevant_types ctxt ctx (e1 e2 : expr) :
  equiv_under ctxt ctx e1 e2 <->
  (Mequiv (interp_expr ctxt ctx e1)
          (interp_expr_cast ctxt ctx e2 _) /\
   Mequiv (interp_expr_cast ctxt ctx e1 _)
          (interp_expr ctxt ctx e2)).
Proof.
  setoid_rewrite <-interp_expr_cast_expr_type.
  split; [solve [eauto]|].
  intros H t.
  destruct (type_dec t (expr_type e1)); [solve [subst; intuition idtac]|].
  destruct (type_dec t (expr_type e2)); [solve [subst; intuition idtac]|].
  setoid_rewrite interp_expr_cast_different; eauto; reflexivity.
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
  destruct (type_dec t (expr_type e1)).
  - subst; eauto.
  - setoid_rewrite interp_expr_cast_different; try congruence.
    reflexivity.
Qed.

Local Instance equiv_equiv : Equivalence equiv.
Proof.
  split; cbv [equiv equiv_under Reflexive Symmetric Transitive];
    [reflexivity|symmetry; eauto|etransitivity; eauto].
Qed.

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

Definition renumber_op (f : nat -> nat) (o : operation) : operation :=
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

Fixpoint renumber_bindings (f : nat -> nat) (p : list operation)
  : list operation :=
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

Definition expr_refs '((p, o) : expr) (n : nat) :=
  bindings_ref p n \/ op_refs o (length p + n).

Lemma bindings_ref_app (p1 p2 : list operation) n :
  bindings_ref (p1 ++ p2) n <->
  bindings_ref p1 n \/ bindings_ref p2 (length p1 + n).
Proof.
  revert n; induction p1; intros n; cbn [bindings_ref length plus app].
  - intuition idtac.
  - replace (S (length p1 + n)) with (length p1 + S n) by omega.
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
Proof. intros; eapply renumber_ref_ext_relevant; eauto. Qed.

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
Proof. intros; eapply renumber_op_ext_relevant; eauto. Qed.

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
Proof. intros; eapply renumber_bindings_ext_relevant; eauto. Qed.

Lemma renumber_expr'_ext f f' acc p o' :
  (forall i, f i = f' i) ->
  renumber_expr' acc f p o' = renumber_expr' acc f' p o'.
Proof.
  revert acc f f'; induction p; intros acc f f' Hf;
    cbn [renumber_expr'].
  - erewrite renumber_op_ext; eauto.
  - erewrite renumber_op_ext; eauto.
    eapply IHp.
    intros []; cbv [offset_renumbering optsub]; eauto.
Qed.

Lemma renumber_expr_ext f f' e :
  (forall i, f i = f' i) ->
  renumber_expr f e = renumber_expr f' e.
Proof. destruct e; eapply renumber_expr'_ext. Qed.

Lemma offset_renumbering_plus a b n f :
  offset_renumbering (a + b) f n =
  offset_renumbering a (offset_renumbering b f) n.
Proof.
  cbv [offset_renumbering] in *.
  crush_deciders idtac.
  subst.
  match goal with
  | _ : (_ + _ + ?x) = (_ + (_ + ?y)) |- _ => assert (x = y) by omega
  end.
  subst; omega.
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
      f_equal; omega.
Qed.

Lemma renumber_expr_renumber_bindings f p o' :
  renumber_expr f (p, o') =
  (renumber_bindings f p,
   renumber_op (offset_renumbering (length p) f) o').
Proof. eapply renumber_expr'_renumber_bindings. Qed.

Lemma renumber_bindings_app (f : nat -> nat) (p1 p2 : list operation) :
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
    erewrite lookup_renumbered_ref by
        (eauto; cbv [offset_renumbering];
         crush_deciders idtac;
         subst;
         eauto);
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
    erewrite lookup_renumbered_ref by
        (eauto; cbv [offset_renumbering];
         crush_deciders idtac;
         subst;
         eauto);
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
  replace (S (length p)) with (1 + length p) in * by omega.
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
  { eapply Mbind_comm. }

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
    | H : ?a + ?b = ?a + ?c |- _ => assert (b = c) by omega
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

Lemma renumber_id_ref r :
  renumber_ref (fun x => x) r = r.
Proof. induction r; cbn [renumber_ref]; congruence. Qed.

Lemma renumber_id_op o :
  renumber_op (fun x => x) o = o.
Proof.
  destruct o; cbn [renumber_op]; try rewrite renumber_id_ref; congruence.
Qed.

Lemma renumber_id_expr' acc p o' :
  renumber_expr' acc (fun x => x) p o' = (rev_append acc p, o').
Proof.
  revert acc; induction p; intros; cbn [renumber_expr']; listrew.
  - rewrite renumber_id_op; eauto.
  - rewrite renumber_id_op.
    erewrite renumber_expr'_ext by (eapply offset_id).
    rewrite IHp; listrew; eauto.
Qed.

Lemma renumber_id_expr e :
  renumber_expr (fun x => x) e = e.
Proof. destruct e; eapply renumber_id_expr'. Qed.

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
        (erewrite <-renumber_renumber_op; eauto; intros; omega).
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

Module Rewriter.
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
    Context (map_operations : fmap.operations nat nat).
    Local Notation map := (map_operations.(fmap.M)).
    Local Notation empty := (map_operations.(fmap.empty)).
    Local Notation add := (map_operations.(fmap.add)).
    Local Notation find := (map_operations.(fmap.find)).
    Local Notation fold_ac := (map_operations.(fmap.fold_ac)).

    Definition op_matches (o1 o2 : operation) :=
      match o1, o2 with
      | op_unit, op_unit => true
      | op_app c _, op_app c' _ =>
        if const_eqb c c' then true else false
      | op_retapp c _, op_retapp c' _ =>
        if retconst_eqb c c' then true else false
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
     *   + run the strict matcher
     *     (could prove that it always succeeds but that would be hard)
     *   + rewrite the lemma
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
               (lop pop : operation)
               (loff poff : nat) (lem2prog prog2lem : map)
      : map * map + error :=
      match lop, pop with
      | op_unit, op_unit => ok (lem2prog, prog2lem)
      | op_app lc lr, op_app pc pr =>
        if const_eqb lc pc
        then update_maps_ref loff poff lem2prog prog2lem lr pr
        else raise (E_msg "map_match: op const mismatch")
      | op_retapp lc lr, op_retapp pc pr =>
        if retconst_eqb lc pc
        then update_maps_ref loff poff lem2prog prog2lem lr pr
        else raise (E_msg "map_match: op retconst mismatch")
      | _, _ => raise (E_msg "map_match: operation mismatch")
      end.

    (* iterate over lbinds, using the map found so far to index into
     * pbinds.  lbinds gets shorter, pbinds stays the same.
     * The "empty lem2prog entry" error occurs if the lemma has unused
     * bindings; "bad lem2prog entry" occurs if the program refers to a
     * free variable but that variable is not free in the lemma. *)
    Fixpoint map_match'
             (lbinds pbinds : list operation) (lhead phead : operation)
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
    Definition map_match (lbinds pbinds : list operation)
               (lhead phead : operation) : map * map + error :=
      map_match' lbinds pbinds lhead phead 0 0 empty empty.

    Fixpoint refsb (r : ref) (n : nat) :=
      match r with
      | ref_index k => n =? k
      | ref_pair r1 r2 => refsb r1 n || refsb r2 n
      end.

    Definition op_refsb (o : operation) (n : nat) :=
      match o with
      | op_unit => false
      | op_app _ r | op_retapp _ r => refsb r n
      end.

    Fixpoint bindings_refb (p : list operation) (n : nat) :=
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

    Definition check_no_capturing_tail (ptail : list operation)
               (prog_end : operation)
               (prog2lem : map) : unit + error :=
      fold_ac _ (fun n _ acc =>
                   _ <-! acc;
                     if bindings_refb ptail (S n)
                        || op_refsb prog_end (S (length ptail) + n)
                     then raise (E_msg "check_no_capturing_tail: capture")
                     else ok tt)
              (ok tt) prog2lem.

    Definition cycle_to_here_renumbering (from j : nat) : nat :=
      if j =? from
      then 0
      else if j <? from
           then S j
           else j.

    Definition cycle_renumbering (from to j : nat) : nat :=
      if j =? from
      then to
      else if (to <=? j) && (j <? from)
           then S j
           else j.

    Lemma cycle_renumbering_trivial n j :
      cycle_renumbering n n j = j.
    Proof.
      cbv [cycle_renumbering].
      crush_deciders idtac.
    Qed.

    Lemma offset_cycle_renumbering a b c j :
      offset_renumbering b (cycle_renumbering a c) j =
      cycle_renumbering (a + b) (c + b) j.
    Proof.
      cbv [offset_renumbering cycle_renumbering].
      let t := (cbn [andb]) in crush_deciders t.
    Qed.

    Definition cycle_expr_continuation ncommute e t j ctxt ctx :=
      interp_expr_cast ctxt ctx
                       (renumber_expr (cycle_renumbering ncommute j) e)
                       t.

    Lemma cycle_renumbering_S from to :
      to < from ->
      forall i,
        cycle_renumbering from to i =
        offset_renumbering to
                           (fun n => match n with
                                     | 0 => 1
                                     | 1 => 0
                                     | _ => n
                                     end)
                           (cycle_renumbering from (S to) i).
    Proof.
      cbv [cycle_renumbering offset_renumbering].
      let t := (cbn [andb] in * ) in
      crush_deciders t;
        repeat match goal with
               | |- context[match ?x with _ => _ end] => destruct x
               end;
        crush_deciders idtac.
    Qed.

    Lemma cycle_expr_continuation_renumbering ncommute e t j :
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
                  ltac:(eapply (cycle_renumbering_S ncommute j
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
                                  (cycle_renumbering ncommute (S j) i))
          (g := offset_renumbering j
                                   (fun n : nat => match n with
                                                   | 0 => 1
                                                   | 1 => 0
                                                   | S (S _) => n
                                                   end))
          (f := cycle_renumbering ncommute (S j))
          by reflexivity.
      eapply interp_renumbered_expr.
    Qed.

    Definition renumber_lem2prog (lem2prog : map) (pi li : nat) :=
      fold_ac _ (fun lj pj lem2prog =>
                   if pj =? pi
                   then lem2prog
                   else add lj (cycle_renumbering pi li pj) lem2prog)
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
      omega.
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

    Definition cycle_pbinds (from to : nat) (pbinds : list operation)
      : list operation + error :=
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
             (pbinds : list operation) : list operation + error :=
      match cycles with
      | nil => ok pbinds
      | (from, to) :: cycles => pbinds <-! cycle_pbinds from to pbinds;
                                 cycles_pbinds cycles pbinds
      end.

    Fixpoint cycles_phead_ptail (cycles : list (nat * nat))
             (phead_ptail : list operation) : list operation :=
      match cycles with
      | nil => phead_ptail
      | (from, to) :: cycles =>
        cycles_phead_ptail cycles
                          (renumber_bindings (cycle_renumbering from to)
                                             phead_ptail)
      end.

    Fixpoint cycles_prog_end (len_ptail : nat) (cycles : list (nat * nat))
             (prog_end : operation) : operation :=
      match cycles with
      | nil => prog_end
      | (from, to) :: cycles =>
        cycles_prog_end len_ptail
          cycles (renumber_op (offset_renumbering (S len_ptail)
                                                 (cycle_renumbering from to))
                             prog_end)
      end.

    Definition commute_matches (lbinds : list operation)
               (lhead : operation) (e : expr) :
      list (nat * ((list operation * operation) + error)) :=
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
              ok (rev_append new_pbinds
                             (cycles_phead_ptail cycles (phead :: ptail)),
                  cycles_prog_end len_ptail cycles prog_end)))
        match_bases.

    Ltac step_err_bind :=
      lazymatch goal with
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
        | ok _ => inversion_clear H
        end
      end.

    Lemma commute_matches_correct lbinds lhead e :
      Forall (fun '(_, err) => match err with
                             | ok new_p =>
                               equiv e new_p
                             | raise _ => True
                             end)
             (commute_matches lbinds lhead e).
      destruct e as [prog prog_end].
      cbv [commute_matches].
      rewrite Forall_forall.
      setoid_rewrite in_map_iff.
      intros [n [[new_prog new_prog_end]|]]
             ([[ptail phead] pbinds]&H&?); eauto.
      inversion H; clear dependent n.

      destruct (map_match lbinds pbinds lhead phead) as [[lem2prog prog2lem]|];
        cbn [err_bind] in *; [|congruence].

      repeat step_err_bind.

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

      revert dependent new_pbinds; revert pbinds phead ptail prog_end;
        induction cycles as [|[from to] cycles];
        intros pbinds phead ptail prog_end new_pbinds Hnew_pbinds;
        cbn [cycles_phead_ptail cycles_prog_end cycles_pbinds] in *.
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
                                       (cycle_renumbering (length middle) 0)
                                       coda)))
                           (renumber_op
                              (offset_renumbering
                                 (length coda)
                                 (cycle_renumbering (length middle) 0))
                              phead)
                           (renumber_bindings
                              (offset_renumbering
                                 (S (length coda))
                                 (cycle_renumbering (length middle) 0))
                              ptail)
                           (renumber_op
                              (offset_renumbering
                                 (S (length coda) + length ptail)
                                 (cycle_renumbering (length middle) 0))
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
                                     (cycle_renumbering (length middle) j)
                                     (coda ++ phead :: ptail, prog_end))
                                  t).

          etransitivity; [|eapply commute_many with
                               (ks := cycle_expr_continuation
                                        (length middle)
                                        (coda ++ phead :: ptail, prog_end)
                                        t)].
          * cbv [cycle_expr_continuation].

            crush_Mequiv.
            erewrite renumber_expr_ext by (eapply cycle_renumbering_trivial).
            rewrite renumber_id_expr.
            cbv [interp_expr_cast interp_expr].
            crush_Mequiv.
          * pose proof bindings_refb_ref middle 0;
              intuition congruence.
          * intros.
            eapply cycle_expr_continuation_renumbering; eauto.
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
        erewrite renumber_op_ext by (eapply offset_cycle_renumbering).
        repeat erewrite
               (renumber_bindings_ext _ _ _
                                      ltac:(eapply offset_cycle_renumbering)).
        cbn [plus].
        replace (from - to + to) with from by omega.
        replace (from - to + S to) with (S from) by omega.
        replace (from + 1) with (S from) by omega.
        replace (to + 1) with (S to) by omega.
        crush_Mequiv.
        rewrite length_renumber.
        repeat erewrite
               (renumber_op_ext _ _ _
                                ltac:(eapply offset_cycle_renumbering)).
        cbn [plus].
        replace (from - to + S (to + length ptail))
                with (from + S (length ptail)) by omega.
        replace (to + S (length ptail))
                with (S (to + length ptail)) by omega.
        crush_Mequiv.
    Qed.
  End WithMap.
End Rewriter.

(** Reification *)
Ltac reify_type t :=
  lazymatch t with
  | prod ?ta ?tb =>
    let ta := reify_type ta in
    let tb := reify_type tb in
    uconstr:(tprod ta tb)
  | bool => tbool
  | unit => tunit
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
    let T := lazymatch type of o with Comp ?T => T | M ?T => constr:(interp_type T) | ?X => fail "XX" X end in
    let o := reify_op ctx o in
    let _y := fresh in let y := fresh in (* andres thinks this might work around a coq bug but does not remember which one :( *)
    lazymatch constr:(fun (y:T) => ltac:(
        let r := reify_to_list
          constr:(pair y ctx)
          constr:(match y return _ with x => f end) in
        exact r
     )) with fun _ => ?r => uconstr:(@cons operation o r) | _ => fail "FUNDEP" end
  | ?o =>
    let o := reify_op ctx o in
    uconstr:(@cons operation o (@nil operation))
  | ?O => fail "UNKNOWN EXPR" O
  end.
Ltac reify e :=
  let e := reify_to_list tt e in
  let e := eval cbv in (List.removelast e, List.last e op_unit) in
  constr:(e).

Section ExampleCoins.
  Import CrossCrypto.fmap.list_of_pairs.
  Local Notation map := (list_of_pairs Nat.eqb).

  Definition example_coin_lemma_lhs :=
    (op_unit
       :: op_unit
       :: (op_app coin (ref_index 1))
       :: (op_app coin (ref_index 1))
       :: nil,
     op_retapp xor' (ref_pair (ref_index 0) (ref_index 1))).

  Definition example_coin_lemma_rhs :=
    ((op_unit :: nil), op_app coin (ref_index 0)).

  Lemma example_coin_lemma :
    equiv example_coin_lemma_lhs example_coin_lemma_rhs.
  Proof.
    intros ??.
    eapply equiv_under_same_type; eauto.
    cbv -[Comp_eq interp_const interp_retconst];
      cbn [interp_const interp_retconst].
    repeat (setoid_rewrite Bind_Ret_l || setoid_rewrite <-Bind_assoc).
    cbv [Comp_eq image_relation pointwise_relation evalDist getSupport
                 getAllBvectors].
    cbn [List.map app sumList fold_left
                  Vector.nth xorb Vector.caseS
                  expnat Nat.mul Nat.add].
    generalize (@EqDec_dec bool (@interp_type_eqdec tbool)); intros d0.
    generalize (EqDec_dec bool_EqDec); intros d1.
    intros a.
    destruct (d0 true a), (d0 false a); try congruence;
      destruct (d1 true a), (d1 false a); try congruence;
        reflexivity.
  Qed.

  Definition coins_example :=
    (op_unit :: op_app coin (ref_index 0)
  :: op_unit :: op_app coin (ref_index 0)
  :: op_unit :: op_app coin (ref_index 0)
  :: op_retapp xor' (ref_pair (ref_index 4) (ref_index 0))
       :: nil,
     op_retapp
       (id ((tbool * tbool) * tbool))
       (ref_pair (ref_pair (ref_index 0) (ref_index 3)) (ref_index 3))).

  Derive coins_endpoint
         SuchThat (equiv coins_example coins_endpoint)
         As coins_example_rewrite.
  Proof.
    set (lbinds := rev (fst example_coin_lemma_lhs)).
    set (lhead := snd example_coin_lemma_lhs).
    pose proof (Rewriter.commute_matches_correct
                  map lbinds lhead coins_example) as H.
    set (C := Rewriter.commute_matches map lbinds lhead coins_example) in H;
      cbv in C;
      subst C.
    eapply Forall_inv in H.
    etransitivity; [eapply H|].
  Abort.


  (*
  Eval cbv [M interp_expr coins_example interp_bindings Mbind Mret interp_op_silent interp_op lookup_ref lookup transport type_dec type_rec type_rect op_type cdom eq_rect_r eq_rect eq_sym rcdom ccod rccod interp_retconst] in
      interp_expr tunit tt coins_example.
   *)
  
  Definition coins_example' :=
    x <-$ ret tt;
    x0 <-$ interp_const coin x;
    x1 <-$ ret tt;
    x2 <-$ interp_const coin x1;
    x3 <-$ ret tt;
    x4 <-$ interp_const coin x3;
    x5 <-$ ret xorb x0 x4;
    ret (x5, x2, x2).
  Derive reified_coins_example
  SuchThat (reified_coins_example = coins_example')
  As reified_coins_example'_correct.
  Proof.
    cbv [coins_example'].

    let x := reified_coins_example in
    let x := eval unfold x in x in
    let e := match goal with |- ?LHS = ?RHS => RHS end in
    let e := reify e in
    unify x (interp_expr tunit tt e).

    reflexivity.
  Qed.
  Print reified_coins_example.
End ExampleCoins.
