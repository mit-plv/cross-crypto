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
         (p1 : list operation)
         (tk : type) (k : forall ctxt : type, interp_type ctxt -> M tk)
         {struct p1} : (M tk) :=
  match p1 with
  | nil => k ctxt ctx
  | cons o p1 =>
    Mbind (interp_op_silent ctxt ctx o)
          (fun x => interp_bindings (op_type o * ctxt) (x, ctx) p1 tk k)
  end.

Definition interp_expr (ctxt : type) (ctx : interp_type ctxt)
           (e : expr) : M (expr_type e) :=
  let '(p1, p2) := e in
  interp_bindings ctxt ctx p1 (op_type p2)
                  (fun ctxt ctx => interp_op_silent ctxt ctx p2).

Definition interp_closed_expr (e : expr) : M (expr_type e) :=
  interp_expr tunit tt e.

Example reflection_example :
  let x := ((op_unit
               :: op_unit
               :: (op_app coin (ref_index 1))
               :: (op_app coin (ref_index 1))
               :: nil),
            (op_retapp xor' (ref_pair (ref_index 0) (ref_index 1)))) in
  let y := interp_closed_expr x in
  {z & Comp_eq y z}.
Proof.
  intros x y; subst x y.
  eexists.
  cbv - [Vector.nth xorb Comp_eq].
  repeat setoid_rewrite Bind_unused.
  reflexivity.
Defined.
