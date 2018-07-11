Require Import FCF.FCF FCF.EqDec.
Require Import Coq.Classes.Morphisms.
Require Import Coq.derive.Derive.
Require Import Coq.Logic.Eqdep_dec.
Require Import CrossCrypto.RewriteUtil.

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

Definition cfunc (t1 t2 : type) : Type :=
  interp_type t1 -> interp_type t2.

Definition func (t1 t2 : type) : Type :=
  interp_type t1 -> Comp (interp_type t2).

Definition ccompose {t1 t2 t3} (f : cfunc t1 t2) (g : cfunc t2 t3)
  : cfunc t1 t3 :=
  fun x => g (f x).

Definition ctensor {t1 t2 t1' t2'} (f : cfunc t1 t2) (f' : cfunc t1' t2')
  : cfunc (tprod t1 t1') (tprod t2 t2') :=
  fun '(x, x') => (f x, f' x').

Definition liftc {t1 t2 : type} (cf : cfunc t1 t2) : func t1 t2 :=
  fun x => ret (cf x).

Definition fcompose {t1 t2 t3} (f : func t1 t2) (g : func t2 t3)
  : func t1 t3 :=
  fun x => Bind (f x) g.

Definition ftensor {t1 t2 t1' t2'} (f : func t1 t2) (f' : func t1' t2')
  : func (tprod t1 t1') (tprod t2 t2') :=
  fun '(x, x') => y <-$ f x; y' <-$ f' x'; ret (y, y').

Inductive box_const : type -> type -> Type :=
| bxor : box_const (tbool * tbool) tbool
| bzero : box_const tunit tbool.

Definition box_const_sigT_dec {t1 t2 t1' t2'}
           (b : box_const t1 t2) (b' : box_const t1' t2') :
  let P := fun '(t1, t2) => box_const t1 t2 : Type in
  {existT P (t1, t2) b = existT P (t1', t2') b'} +
  {existT P (t1, t2) b <> existT P (t1', t2') b'}.
  intros; destruct b; destruct b';
    solve [left; eauto |
           right; intro; inversion_sigma; congruence].
Defined.

Definition box_const_dec {t1 t2} (b b' : box_const t1 t2)
  : {b = b'} + {b <> b'}.
  destruct (box_const_sigT_dec b b').
  - left.
    apply inj_pair2_eq_dec with (P := fun '(t1, t2) => box_const t1 t2 : Type)
                                (p := (t1, t2)); eauto.
    decide equality; eauto using type_dec.
  - right; congruence.
Defined.

Inductive box : type -> type -> Type :=
| bconst {t1 t2} : box_const t1 t2 -> box t1 t2
| id {t} : box t t
| assoc {t1 t2 t3} : box ((t1 * t2) * t3) (t1 * (t2 * t3))
| iassoc {t1 t2 t3} : box (t1 * (t2 * t3)) ((t1 * t2) * t3)
| unit_l {t} : box (tunit * t) t
| iunit_l {t} : box t (tunit * t)
| unit_r {t} : box (t * tunit) t
| iunit_r {t} : box t (t * tunit)
| copy {t} : box t (t * t)
| delete {t} : box t tunit
| swap {t1 t2} : box (t1 * t2) (t2 * t1)
| bcompose {t1 t2 t3} : box t1 t2 -> box t2 t3 -> box t1 t3
| btensor {t1 t1' t2 t2'} :
    box t1 t2 -> box t1' t2' -> box (t1 * t1') (t2 * t2').

Bind Scope box_scope with box.
Delimit Scope box_scope with box.

Local Notation "'#' x" := (bconst x)
                            (no associativity,
                             at level 9,
                             format "# x") : box_scope.
Local Notation "f1 * f2" := (btensor f1%box f2%box)
                              (left associativity,
                               at level 40) : box_scope.
Local Notation "f @ g" := (bcompose f%box g%box)
                            (right associativity,
                             at level 41) : box_scope.

Fixpoint size (t : type) : nat :=
  match t with
  | tprod t1 t2 => S (size t1 + size t2)
  | _ => 1
  end.

Lemma bconst_eq_inv {t1 t2 : type} (b b' : box_const t1 t2) :
  bconst b = bconst b' ->
  existT (fun '(t1, t2) => box_const t1 t2 : Type)
         (t1, t2) b =
  existT (fun '(t1, t2) => box_const t1 t2 : Type)
         (t1, t2) b'.
Proof.
  intros.
  set (f (e : box t1 t2) :=
         match e with
         | @bconst t1 t2 b => existT _ (t1, t2) b
         | _ => existT (fun '(t1, t2) => box_const t1 t2) (t1, t2) b
         end).
  change (f (bconst b) = f (bconst b')).
  f_equal; eauto.
Defined.

Lemma bcompose_eq_inv {t1 t2 t2' t3 : type}
      (b1 : box t1 t2) (b2 : box t2 t3)
      (b1' : box t1 t2') (b2' : box t2' t3)  :
  bcompose b1 b2 = bcompose b1' b2' ->
  existT (fun '(t1, t2) => box t1 t2 : Type)
         (t1, t2) b1 =
  existT (fun '(t1, t2) => box t1 t2 : Type)
         (t1, t2') b1' /\
  existT (fun '(t1, t2) => box t1 t2 : Type)
         (t2, t3) b2 =
  existT (fun '(t1, t2) => box t1 t2 : Type)
         (t2', t3) b2'.
Proof.
  intros.
  set (f (e : box t1 t3) :=
         match e with
         | @bcompose t1 t2 t3 b1 b2 => existT _ (t1, t2) b1
         | _ => existT (fun '(t1, t2) => box t1 t2) (t1, t2) b1
         end).
  set (g (e : box t1 t3) :=
         match e with
         | @bcompose t1 t2 t3 b1 b2 => existT _ (t2, t3) b2
         | _ => existT (fun '(t1, t2) => box t1 t2) (t2, t3) b2
         end).
  split.
  - change (f (bcompose b1 b2) = f (bcompose b1' b2')).
    f_equal; eauto.
  - change (g (bcompose b1 b2) = g (bcompose b1' b2')).
    f_equal; eauto.
Defined.

Lemma btensor_eq_inv {t1 t1' t2 t2' : type}
      (b1 b1' : box t1 t2) (b2 b2' : box t1' t2') :
  btensor b1 b2 = btensor b1' b2' ->
  existT (fun '(t1, t2) => box t1 t2 : Type)
         (t1, t2) b1 =
  existT (fun '(t1, t2) => box t1 t2 : Type)
         (t1, t2) b1' /\
  existT (fun '(t1, t2) => box t1 t2 : Type)
         (t1', t2') b2 =
  existT (fun '(t1, t2) => box t1 t2 : Type)
         (t1', t2') b2'.
Proof.
  intros.
  set (f (e : box (t1 * t1') (t2 * t2')) :=
         match e with
         | @btensor t1 t1' t2 t2' b1 b2 => existT _ (t1, t2) b1
         | _ => existT (fun '(t1, t2) => box t1 t2) (t1, t2) b1
         end).
  set (g (e : box (t1 * t1') (t2 * t2')) :=
         match e with
         | @btensor t1 t1' t2 t2' b1 b2 => existT _ (t1', t2') b2
         | _ => existT (fun '(t1, t2) => box t1 t2) (t1', t2') b2
         end).
  split.
  - change (f (btensor b1 b2) = f (btensor b1' b2')).
    f_equal; eauto.
  - change (g (btensor b1 b2) = g (btensor b1' b2')).
    f_equal; eauto.
Defined.

Ltac disprove_recursion :=
  multimatch goal with
  | H : ?a = _ |- _ =>
    apply (f_equal size) in H;
    cbn [size] in H;
    omega
  end.

(* TODO Maybe possible to improve this proof by injecting into a version
   with type-codes erased and showing a partial retraction? *)
Definition box_sigT_dec {t1 t2 t1' t2'} (b : box t1 t2)
           (b' : box t1' t2') :
  let P := fun '(t1, t2) => box t1 t2 : Type in
  {existT P (t1, t2) b = existT P (t1', t2') b'} +
  {existT P (t1, t2) b <> existT P (t1', t2') b'}.
  intros.

  revert t1' t2' b'.
  induction b; intros ? ? b'; destruct b';
    try solve [right;
               intro;
               inversion_sigma;
               match goal with
               | H : (_, _) = (_, _) |- _ => inversion H
               end;
               repeat match goal with
                      | H : ?x = ?y |- _ => type_head x;
                                            type_head y;
                                            inversion H;
                                            clear H
                      end;
               try disprove_recursion;
               subst;
               rewrite <- eq_rect_eq_dec in * by
                   (decide equality; eauto using type_dec);
               congruence];
    match goal with
    | |- {existT _ (?t1, ?t2) _ =
          existT _ (?t1', ?t2') _} + {_} =>
      destruct (type_dec t1 t1') as [e1|?];
        [|right; intro; inversion_sigma; congruence];
        inversion e1; subst;
          solve [eauto] ||
                (destruct (type_dec t2 t2') as [e2|?];
                 [|right; intro; inversion_sigma; congruence];
                 inversion e2; subst; eauto)
    end.
  - destruct (box_const_dec b b0). (* TODO name *)
    + subst; eauto.
    + right.
      intro.
      inversion_sigma.
      match goal with
      | H : (_, _) = (_, _) |- _ => inversion H
      end.
      subst.
      rewrite <- eq_rect_eq_dec in * by
          (decide equality; eauto using type_dec).
      match goal with
      | H : bconst _ = bconst _ |- _ => apply bconst_eq_inv in H
      end.
      inversion_sigma.
      rewrite <- eq_rect_eq_dec in * by
          (decide equality; eauto using type_dec).
      congruence.
  - destruct (IHb1 _ _ b'1). (* TODO name *)
    + destruct (IHb2 _ _ b'2). (* TODO name *)
      * inversion_sigma.
        match goal with
        | H : (_, _) = (_, _) |- _ => inversion H
        end.
        subst.
        repeat rewrite <- eq_rect_eq_dec in * by
            (decide equality; eauto using type_dec).
        eauto.
      * right.
        intro.
        inversion_sigma.
        match goal with
        | H : (_, _) = (_, _) |- _ => inversion H
        end.
        rewrite <- eq_rect_eq_dec in * by
            (decide equality; eauto using type_dec).
        match goal with
        | H : bcompose _ _ = bcompose _ _ |- _ => apply bcompose_eq_inv in H;
                                                    destruct H
        end.
        inversion_sigma.
        subst.
        rewrite <- eq_rect_eq_dec in * by
            (decide equality; eauto using type_dec).
        congruence.
    + right.
      intro.
      inversion_sigma.
      match goal with
      | H : (_, _) = (_, _) |- _ => inversion H
      end.
      rewrite <- eq_rect_eq_dec in * by
          (decide equality; eauto using type_dec).
      match goal with
      | H : bcompose _ _ = bcompose _ _ |- _ => apply bcompose_eq_inv in H;
                                                  destruct H
      end.
      inversion_sigma.
      inversion H4. (* TODO naming *)
      subst.
      rewrite <- eq_rect_eq_dec in * by
          (decide equality; eauto using type_dec).
      congruence.
  - destruct (IHb1 _ _ b'1). (* TODO name *)
    + destruct (IHb2 _ _ b'2). (* TODO name *)
      * inversion_sigma.
        match goal with
        | H : (_, _) = (_, _) |- _ => inversion H
        end.
        subst.
        repeat rewrite <- eq_rect_eq_dec in * by
            (decide equality; eauto using type_dec).
        eauto.
      * right.
        intro.
        inversion_sigma.
        match goal with
        | H : (_, _) = (_, _) |- _ => inversion H
        end.
        rewrite <- eq_rect_eq_dec in * by
            (decide equality; eauto using type_dec).
        match goal with
        | H : btensor _ _ = btensor _ _ |- _ => apply btensor_eq_inv in H;
                                                  destruct H
        end.
        inversion_sigma.
        subst.
        rewrite <- eq_rect_eq_dec in * by
            (decide equality; eauto using type_dec).
        congruence.
    + right.
      intro.
      inversion_sigma.
      match goal with
      | H : (_, _) = (_, _) |- _ => inversion H
      end.
      rewrite <- eq_rect_eq_dec in * by
          (decide equality; eauto using type_dec).
      match goal with
      | H : btensor _ _ = btensor _ _ |- _ => apply btensor_eq_inv in H;
                                                destruct H
      end.
      inversion_sigma.
      subst.
      rewrite <- eq_rect_eq_dec in * by
          (decide equality; eauto using type_dec).
      congruence.
Defined.

Lemma box_dec t1 t2 (b1 b2 : box t1 t2) : {b1 = b2} + {b1 <> b2}.
Proof.
  destruct (box_sigT_dec b1 b2).
  - inversion_sigma.
    subst.
    rewrite <- eq_rect_eq_dec in * by
        (decide equality; eauto using type_dec).
    eauto.
  - right; congruence.
Defined.

Inductive fconst : type -> type -> Type :=
| coin : fconst tunit tbool.

Inductive expr : type -> type -> Type :=
| ebox {t1 t2} : box t1 t2 -> expr t1 t2
| const {t1 t2} : fconst t1 t2 -> expr t1 t2
| compose {t1 t2 t3} : expr t1 t2 -> expr t2 t3 -> expr t1 t3
| tensor {t1 t1' t2 t2'} :
    expr t1 t2 -> expr t1' t2' -> expr (tprod t1 t1') (tprod t2 t2').

Bind Scope expr_scope with expr.
Delimit Scope expr_scope with expr.
Local Notation "[[ x ]]" := (ebox x%box) : expr_scope.
Local Notation "'#' x" := (const x)
                            (no associativity,
                             at level 9,
                             format "# x") : expr_scope.
Local Notation "f1 * f2" := (tensor f1%expr f2%expr)
                              (left associativity,
                               at level 40) : expr_scope.
Local Notation "f @ g" := (compose f%expr g%expr)
                            (right associativity,
                             at level 41) : expr_scope.

Definition interp_box_const {t1 t2} (c : box_const t1 t2) : cfunc t1 t2 :=
  match c with
  | bxor => fun '(x, y) => xorb x y
  | bzero => fun _ => false
  end.

Fixpoint interp_box {t1 t2} (b : box t1 t2) : cfunc t1 t2 :=
  match b with
  | bconst c => interp_box_const c
  | id => fun x => x
  | assoc => fun '((x, y), z) => (x, (y, z))
  | iassoc => fun '(x, (y, z)) => ((x, y), z)
  | unit_l => fun '(_, x) => x
  | iunit_l => fun x => (tt, x)
  | unit_r => fun '(x, _) => x
  | iunit_r => fun x => (x, tt)
  | copy => fun x => (x, x)
  | delete => fun _ => tt
  | swap => fun '(x, y) => (y, x)
  | bcompose b1 b2 => ccompose (interp_box b1) (interp_box b2)
  | btensor b1 b2 => ctensor (interp_box b1) (interp_box b2)
  end.

Definition interp_fconst {t1 t2} (f : fconst t1 t2) : func t1 t2 :=
  match f with
  | coin => fun _ => x <-$ Rnd 1; ret (Vector.nth x Fin.F1)
  end.

Fixpoint interp_expr {t1 t2} (e : expr t1 t2) : func t1 t2 :=
  match e with
  | [[b]] => liftc (interp_box b)
  | #f => (interp_fconst f)
  | e1 @ e2 => fcompose (interp_expr e1) (interp_expr e2)
  | e * e' => ftensor (interp_expr e) (interp_expr e')
  end%expr.

Fixpoint tlist (m : list type) : type :=
  match m with
  | nil => tunit
  | cons t m => t * (tlist m)
  end.

(* empty is just @id unit *)

Fixpoint tindex (m : list type) (i : nat) {struct i} : type :=
  match i with
  | 0 => match m with
         | nil => tunit
         | cons t _ => t
         end
  | S i => match m with
           | nil => tunit
           | cons _ m => tindex m i
           end
  end.

Definition ffst {t1 t2} : box (t1 * t2) t1 := (id * delete) @ unit_r.
Definition fsnd {t1 t2} : box (t1 * t2) t2 := (delete * id) @ unit_l.

Definition index (m : list type) (i : nat) :
  box (tlist m) (tindex m i).
  revert m.
  induction i as [|i]; intros m.
  - destruct m; cbn [tindex interp_type tlist] in *.
    + exact delete.
    + exact ffst.
  - destruct m; cbn [tindex interp_type tlist] in *.
    + exact delete.
    + eapply bcompose.
      * exact fsnd.
      * eapply IHi.
Defined.

(* add is id *)

Definition units (t : type) :
  box tunit
      ((fix units_type t :=
          match t with
          | t1 * t2 =>
            (units_type t1) * (units_type t2)
          | _ => tunit
          end%etype) t).
  induction t; try exact delete.
  eapply bcompose.
  - exact copy.
  - eapply btensor; eauto.
Defined.

Definition fequiv {t1 t2} : func t1 t2 -> func t1 t2 -> Prop :=
  pointwise_relation _ Comp_eq.

Local Instance Equivalence_fequiv {t1 t2} : Equivalence (@fequiv t1 t2).
Proof. typeclasses eauto. Qed.

Definition cfequiv {t1 t2} : cfunc t1 t2 -> cfunc t1 t2 -> Prop :=
  pointwise_relation _ eq.

Local Instance Equivalence_cfequiv {t1 t2} : Equivalence (@cfequiv t1 t2).
Proof. typeclasses eauto. Qed.

Local Existing Instance eq_subrelation | 5.

Local Instance Proper_liftc {t1 t2} :
  Proper (cfequiv ==> fequiv) (@liftc t1 t2).
Proof.
  intros ????.
  cbv [liftc].
  setoid_rewrite H.
  reflexivity.
Qed.

Definition equiv {t1 t2} (e e' : expr t1 t2) : Prop :=
  fequiv (interp_expr e) (interp_expr e').

Local Instance Equivalence_equiv {t1 t2} : Equivalence (@equiv t1 t2).
Proof. typeclasses eauto. Qed.

Local Instance Proper_interp_expr {t1 t2} :
  Proper (equiv ==> fequiv) (@interp_expr t1 t2).
Proof. intros ???; eauto. Qed.

Local Instance Proper_equiv_compose {t1 t2 t3} :
  Proper (equiv ==> equiv ==> equiv) (@compose t1 t2 t3).
Proof.
  cbv [equiv fequiv pointwise_relation].
  intros ???????.
  cbn [interp_expr].
  cbv [fcompose].
  f_equiv; eauto.
Qed.

Local Instance Proper_equiv_tensor {t1 t2 t3 t4} :
  Proper (equiv ==> equiv ==> equiv) (@tensor t1 t2 t3 t4).
Proof.
  cbv [equiv fequiv pointwise_relation].
  intros f f' Hf g g' Hg [].
  cbn [interp_expr].
  cbv [ftensor].
  setoid_rewrite Hf.
  setoid_rewrite Hg.
  reflexivity.
Qed.

Lemma compose_assoc {t1 t2 t3 t4}
      (f : expr t1 t2) (g : expr t2 t3) (h : expr t3 t4) :
  equiv ((f @ g) @ h) (f @ (g @ h)).
Proof.
  cbv [equiv fequiv].
  cbn [interp_expr].
  cbv [fcompose].
  setoid_rewrite <-Bind_assoc.
  reflexivity.
Qed.

Lemma interchange {s1 s2 s3 t1 t2 t3}
      (f1 : expr s1 s2) (f2 : expr s2 s3)
      (g1 : expr t1 t2) (g2 : expr t2 t3) :
  equiv ((f1 * g1) @ (f2 * g2)) ((f1 @ f2) * (g1 @ g2)).
Proof.
  cbv [equiv fequiv].
  cbn [interp_expr].
  cbv [fcompose ftensor].
  intros [].
  repeat setoid_rewrite <-Bind_assoc.
  setoid_rewrite Bind_Ret_l.
  f_equiv; intros ?.
  setoid_rewrite Bind_comm with
      (c1 := interp_expr f2 _) (c2 := interp_expr g1 _).
  reflexivity.
Qed.

Lemma id_l {t1 t2} (x : expr t1 t2) : equiv ([[id]] @ x) x.
Admitted.
Lemma delete_r {t1 t2} (x : expr t1 t2) : equiv (x @ [[delete]]) [[delete]].
Admitted.

Lemma index_0_add {t m} :
  equiv [[index (cons t m) 0]] [[ffst]].
Proof. reflexivity. Qed.

Lemma index_S_add {t m} n :
  equiv [[index (cons t m) (S n)]] ([[fsnd]] @ [[index m n]]).
Proof.
  intro.
  cbn [interp_expr].
  cbv [liftc fcompose].
  setoid_rewrite Bind_Ret_l.
  reflexivity.
Qed.

Fixpoint associate_type (t : type) : type :=
  match t with
  | tprod t1 t2 =>
    match associate_type t1 with
    | tunit => associate_type t2
    | t1' => match associate_type t2 with
             | tunit => t1'
             | tprod t2a t2b => tprod (tprod t1' t2a) t2b
             | t2' => tprod t1' t2'
             end
    end
  | _ => t
  end.

Fixpoint associate (t : type) : box t (associate_type t).
  induction t; cbn [associate_type]; try exact id.
  refine ((IHt1 * IHt2) @ _)%box.
  destruct (associate_type t1); try exact unit_l;
    destruct (associate_type t2);
    exact id || exact unit_r || exact iassoc.
Defined.

Definition unassociate (t : type) : box (associate_type t) t.
  induction t; cbn [associate_type interp_type]; try exact id.
  refine (_ @ (IHt1 * IHt2))%box.
  destruct (associate_type t1); try exact iunit_l;
    destruct (associate_type t2);
    exact id || exact iunit_r || exact assoc.
Defined.

Section ExampleCoins.
  Lemma coins_xor :
    equiv ([[units (tunit * tunit)]]
             @ (#coin * #coin)
             @ [[#bxor]])
          #coin.
  Proof.
    cbv [equiv fequiv interp_type interp_expr fcompose ftensor liftc units type_rect type_rec interp_fconst interp_box interp_box_const ccompose ctensor].
    intros _.
    repeat (setoid_rewrite Bind_Ret_l || setoid_rewrite <-Bind_assoc).
    cbv [Comp_eq image_relation pointwise_relation evalDist getSupport
        getAllBvectors].
    cbn [List.map app sumList fold_left
                  Vector.nth xorb Vector.caseS
                  expnat Nat.mul Nat.add].
    generalize (@EqDec_dec bool (@interp_type_eqdec tbool));
      intros d0.
    generalize (EqDec_dec bool_EqDec); intros d1.
    intros a.
    destruct (d0 true a), (d0 false a); try congruence;
      destruct (d1 true a), (d1 false a); try congruence;
        reflexivity.
  Qed.

  Example coins_example : expr tunit (tbool * (tbool * tbool)) :=
    ([[units (tunit * tlist nil)]]
      @ (#coin * [[id]])
       @ [[copy]]
       @ (([[delete]] @ #coin) * [[id]])
       @ [[copy]]
       @ (([[delete]] @ #coin) * [[id]])
       @ [[copy]]
       @ ((([[copy]] @ ([[copy]] * [[id]]))
             @ (let m := (cons tbool (cons tbool (cons tbool nil))) in
                [[delete]] * [[index m 2]] * [[index m 0]])
             @ [[associate (tunit * tbool * tbool)]]
             @ [[#bxor]])
          * [[id]])
       @ ([[copy]] @ ([[id]] * ([[copy]] @ ([[id]] * [[copy]]))))
       @ (let m := (cons tbool (cons tbool (cons tbool (cons tbool nil)))) in
          [[index m 0]] * ([[index m 2]] * ([[index m 2]] * [[delete]])))
       @ [[associate (tbool * (tbool * (tbool * tunit)))]]
       @ [[unassociate (tbool * (tbool * tbool))]])%expr.

  Derive coins_endpoint
         SuchThat (equiv coins_example coins_endpoint)
         As coins_example_rewrite.
  Proof.
    subst coins_endpoint.
    cbv [coins_example].

    setoid_rewrite <-compose_assoc with
        (h :=
           ([[associate (tbool * (tbool * (tbool * tunit)))]]
              @
              [[unassociate (tbool * (tbool * tbool))]])%expr).

    setoid_rewrite compose_assoc with
        (f := [[copy]]%expr).
    setoid_rewrite interchange.
    setoid_rewrite compose_assoc with
        (f := [[copy]]%expr)
        (g := ([[id]] * [[copy]])%expr).
    setoid_rewrite interchange.

    setoid_rewrite id_l.

    cbn [index nat_rec nat_rect units type_rec type_rect tlist
        associate associate_type unassociate].
    assert (forall t1 t2 t3 (f : box t1 t2) (g : box t2 t3),
               equiv [[f @ g]] ([[f]] @ [[g]]))%expr as box_compose
        by admit.
    assert (forall t1 t2 t1' t2' (f : box t1 t2) (f' : box t1' t2'),
               equiv [[f * f']] ([[f]] * [[f']]))%expr as box_tensor
        by admit.
    repeat (setoid_rewrite box_compose ||
            setoid_rewrite box_tensor).

    assert (forall t1 t2 (x : expr t1 t2),
               equiv ([[copy]] @ (x * [[delete]]))
                     (x @ [[iunit_r]])) as copy_delete_r
      by admit.
    setoid_rewrite copy_delete_r.

    assert (forall t1 t2, equiv ([[@id t1]] * [[@id t2]]) [[id]]) as id_tensor by admit.

    setoid_rewrite id_l.
    setoid_rewrite id_tensor.
    setoid_rewrite id_tensor.

    assert (forall t1 t2 (x : expr t1 t2), equiv (x @ [[id]]) x) as id_r by admit.
    setoid_rewrite id_r.
    setoid_rewrite id_l.
    (* TODO commute copy and tensor *)
  Abort.
End ExampleCoins.
