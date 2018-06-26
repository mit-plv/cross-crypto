Require Import CrossCrypto.fmap.list_of_pairs.
Require CrossCrypto.fmap.
Require Import FCF.FCF FCF.EqDec.

Definition mapops V := list_of_pairs (V:=V) (Nat.eqb).
Notation map V := (mapops V).(fmap.M).
Notation mempty := (mapops _).(fmap.empty).
Notation madd := (mapops _).(fmap.add).
Notation mfind := (mapops _).(fmap.find).
Notation mfold := (mapops _).(fmap.fold_ac).

(* the positivity checker requires that "map type" is list (nat * type) *)
Inductive type : Type :=
| tunit : type
| tnat : type
| tbool : type
| tprod : type -> type -> type
| tmap : map type -> type.

Section TypeRec.
  Context (P : type -> Type)
          (Q : map type -> Type)
          (ctunit : P tunit)
          (ctnat : P tnat)
          (ctbool : P tbool)
          (ctprod : forall t1 t2, P t1 -> P t2 -> P (tprod t1 t2))
          (ctmap : forall m, Q m -> P (tmap m))
          (cnil : Q nil)
          (ccons : forall n t m, P t -> Q m -> Q (cons (n, t) m)).

  Fixpoint type_tmap_rect (t : type) : P t.
    refine match t with
           | tunit => ctunit
           | tnat => ctnat
           | tbool => ctbool
           | tprod _ _ => ctprod _ _ _ _
           | tmap m => ctmap _ _
           end; eauto.
    revert m; fix tmap_type_rect 1; intros m.
    refine match m with
           | nil => cnil
           | cons (_, _) _ => ccons _ _ _ _ _
           end; eauto.
  Defined.
End TypeRec.

Fixpoint interp_type (t : type) : Set :=
  match t with
  | tunit => unit
  | tnat => nat
  | tbool => bool
  | tprod t1 t2 => interp_type t1 * interp_type t2
  | tmap m => (fix interp_tmap (m : map type) : Set :=
                 match m with
                 | nil => unit
                 | cons (n, t) m => (interp_type t * interp_tmap m)%type
                 end) m
  end.

(* necessary for ret *)
Local Instance interp_type_eqdec {t} : EqDec (interp_type t).
Proof.
  induction t using type_tmap_rect
    with (Q := fun m => EqDec (interp_type (tmap m)));
    typeclasses eauto.
Defined.

Definition cfunc (t1 t2 : type) : Type :=
  interp_type t1 -> interp_type t2.

Definition func (t1 t2 : type) : Type :=
  interp_type t1 -> Comp (interp_type t2).

Definition liftc {t1 t2 : type} (cf : cfunc t1 t2) : func t1 t2 :=
  fun x => ret (cf x).

Definition fcompose {t1 t2 t3} (f : func t1 t2) (g : func t2 t3)
  : func t1 t3 :=
  fun x => Bind (f x) g.

Definition ftensor {t1 t2 t1' t2'} (f : func t1 t2) (f' : func t1' t2')
  : func (tprod t1 t1') (tprod t2 t2') :=
  fun '(x, x') => y <-$ f x; y' <-$ f' x'; ret (y, y').

Inductive expr : type -> type -> Type :=
| ecconst {t1 t2} : cfunc t1 t2 -> expr t1 t2
| econst {t1 t2} : func t1 t2 -> expr t1 t2
| ecompose {t1 t2 t3} : expr t1 t2 -> expr t2 t3 -> expr t1 t3
| etensor {t1 t1' t2 t2'} :
    expr t1 t2 -> expr t1' t2' -> expr (tprod t1 t1') (tprod t2 t2').

Fixpoint interp_expr {t1 t2} (e : expr t1 t2) : func t1 t2 :=
  match e with
  | ecconst cf => liftc cf
  | econst f => f
  | ecompose e1 e2 => fcompose (interp_expr e1) (interp_expr e2)
  | etensor e e' => ftensor (interp_expr e) (interp_expr e')
  end.

Definition empty : cfunc tunit (tmap mempty) := fun _ => tt.

Definition find (m : map type) (i : nat) (l : interp_type (tmap m))
  : match mfind i m with
    | Some t => interp_type t
    | None => unit
    end.
  cbv [fmap.find mapops list_of_pairs].
  induction m as [|[n t] m]; cbn [interp_type find] in l |- *.
  - exact tt.
  - destruct (n =? i); cbn [option_map snd].
    + exact (fst l).
    + apply IHm.
      exact (snd l).
Defined.

Definition add (m : map type) (i : nat) (t : type) (x : interp_type t)
  (l : interp_type (tmap m)) : interp_type (tmap (madd i t m)) := (x, l).

Definition fadd (m : map type) (i : nat) (t : type)
  : cfunc (tprod t (tmap m)) (tmap (madd i t m)) :=
  fun '(x, l) => add m i t x l.
