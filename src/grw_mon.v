Require Import CrossCrypto.fmap.list_of_pairs.
Require CrossCrypto.fmap.
Require Import FCF.FCF FCF.EqDec.
Require Import Coq.Classes.Morphisms.
Require Import CrossCrypto.RewriteUtil.

Definition mapops V := list_of_pairs (V:=V) (Nat.eqb).
Notation map V := (mapops V).(fmap.M).
Notation mempty := (mapops _).(fmap.empty).
Notation madd := (mapops _).(fmap.add).
Notation mfind := (mapops _).(fmap.find).
Notation mfold := (mapops _).(fmap.fold_ac).

Inductive type : Type :=
| tunit : type
| tnat : type
| tbool : type
| tprod : type -> type -> type.

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
| cconst {t1 t2} : cfunc t1 t2 -> expr t1 t2
| const {t1 t2} : func t1 t2 -> expr t1 t2
| compose {t1 t2 t3} : expr t1 t2 -> expr t2 t3 -> expr t1 t3
| tensor {t1 t1' t2 t2'} :
    expr t1 t2 -> expr t1' t2' -> expr (tprod t1 t1') (tprod t2 t2').

Bind Scope expr_scope with expr.
Delimit Scope expr_scope with expr.
Local Notation "'[[' x ']]'" := (cconst x)
                            (format "[[ x ]]") : expr_scope.
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

Fixpoint interp_expr {t1 t2} (e : expr t1 t2) : func t1 t2 :=
  match e with
  | [[cf]] => liftc cf
  | #f => f
  | e1 @ e2 => fcompose (interp_expr e1) (interp_expr e2)
  | e * e' => ftensor (interp_expr e) (interp_expr e')
  end%expr.

Fixpoint tmap (m : map type) : type :=
  match m with
  | nil => tunit
  | cons (_, t) m => tprod t (tmap m)
  end.

(* empty is just id_unit *)

Definition find (m : map type) (i : nat) (l : interp_type (tmap m))
  : match mfind i m with
    | Some t => interp_type t
    | None => unit
    end.
  cbv [fmap.find mapops list_of_pairs].
  induction m as [|[n t] m]; cbn [interp_type tmap find option_map] in l |- *.
  - exact tt.
  - destruct (n =? i); cbn [option_map snd].
    + exact (fst l).
    + apply IHm; exact (snd l).
Defined.

Definition add (m : map type) (i : nat) (t : type) (x : interp_type t)
  (l : interp_type (tmap m)) : interp_type (tmap (madd i t m)) := (x, l).

Definition fadd {m : map type} (i : nat) {t : type}
  : cfunc (tprod t (tmap m)) (tmap (madd i t m)) :=
  fun '(x, l) => add m i t x l.

Definition copy {t} : cfunc t (tprod t t) :=
  fun x => (x, x).
Definition delete {t} : cfunc t tunit :=
  fun _ => tt.
Definition swap {t1 t2} : cfunc (tprod t1 t2) (tprod t2 t1) :=
  fun '(t1, t2) => (t2, t1).

Definition units (t : type) :
  cfunc tunit
        ((fix units_type t :=
            match t with
            | t1 * t2 =>
              (units_type t1) * (units_type t2)
            | _ => tunit
            end%etype) t).
  induction t; try exact delete.
  intros ?; cbn [interp_type]; eauto.
Defined.

Definition fequiv {t1 t2} (f f' : func t1 t2) : Prop :=
  forall x, Comp_eq (f x) (f' x).

Local Instance Equivalence_fequiv {t1 t2} : Equivalence (@fequiv t1 t2).
Proof.
  split; cbv [fequiv Reflexive Symmetric Transitive]; intros;
    solve [(reflexivity + symmetry + etransitivity); eauto].
Qed.

Definition cfequiv {t1 t2} (f f' : cfunc t1 t2) : Prop :=
  forall x, f x = f' x.

Local Instance Equivalence_cfequiv {t1 t2} : Equivalence (@cfequiv t1 t2).
Proof.
  split; cbv [cfequiv Reflexive Symmetric Transitive]; intros;
    solve [(reflexivity + symmetry + etransitivity); eauto].
Qed.

Lemma cfequiv_fequiv {t1 t2} (f f' : cfunc t1 t2) :
  cfequiv f f' -> fequiv (liftc f) (liftc f').
Proof.
  cbv [cfequiv fequiv liftc].
  intros H ?; setoid_rewrite H; reflexivity.
Qed.

Definition equiv {t1 t2} (e e' : expr t1 t2) : Prop :=
  fequiv (interp_expr e) (interp_expr e').

Local Instance Equivalence_equiv {t1 t2} : Equivalence (@equiv t1 t2).
Proof.
  split; cbv [equiv Reflexive Symmetric Transitive]; intros;
    solve [(reflexivity + symmetry + etransitivity); eauto].
Qed.

Section ExampleCoins.
  Definition coin : func tunit tbool :=
    fun _ => x <-$ Rnd 1; ret (Vector.nth x Fin.F1).

  Definition xor' : cfunc (tprod tbool tbool) tbool :=
    fun '(x, y) => xorb x y.

  Lemma coins_xor :
    equiv ([[units (tunit * tunit)]]
             @ (#coin * #coin)
             @ [[xor']])
          #coin.
  Proof.
    cbv [equiv fequiv interp_type interp_expr fcompose ftensor liftc coin xor' units type_rect delete].
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

  Fixpoint associate (t : type) : cfunc t (associate_type t).
    cbv [cfunc].
    induction t; cbn [associate_type]; eauto.
    intros [x y].
    destruct (associate_type t1);
      [eauto |
       destruct (associate_type t2);
       [apply IHt1; eauto |
        split; [apply IHt1 | apply IHt2]; eauto |
        split; [apply IHt1 | apply IHt2]; eauto |
        split; [split|]; [apply IHt1; eauto|..];
        edestruct IHt2; eauto] ..].
  Defined.

  Definition unassociate (t : type) : cfunc (associate_type t) t.
    cbv [cfunc].
    induction t; cbn [associate_type interp_type]; eauto.
    intros x.
    destruct (associate_type t1); cbn [interp_type] in *;
      [eauto using pair, tt |
       destruct (associate_type t2); cbn [interp_type] in *;
       [split; [apply IHt1 | apply IHt2]; eauto using tt |
        destruct x as [x y]; split; [apply IHt1; exact x |
                                     apply IHt2; exact y] .. |
        destruct x as ((x&y)&z); split; [apply IHt1; exact x |
                                         apply IHt2; exact (y, z)] ] ..].
  Defined.

  Example coins_example : expr tunit (tbool * (tbool * tbool)) :=
    ([[units (tunit * tmap nil)]]
      @ (#coin * [[id]])
       @ [[fadd 0]]
       @ [[copy]]
       @ (([[delete]] @ #coin) * [[id]])
       @ [[fadd 1]]
       @ [[copy]]
       @ (([[delete]] @ #coin) * [[id]])
       @ [[fadd 2]]
       @ [[copy]]
       @ ((([[copy]] @ ([[copy]] * [[id]]))
             @ (let m := (madd 2 tbool (madd 1%nat tbool (madd 0%nat tbool mempty))) in
                [[delete]] * [[find m 0]] * [[find m 2]])
             @ [[associate (tunit * tbool * tbool)]]
             @ [[xor']])
          * [[id]])
       @ [[fadd 3]]
       @ ([[copy]] @ ([[id]] * ([[copy]] @ ([[id]] * [[copy]]))))
       @ (let m := (madd 3 tbool (madd 2 tbool (madd 1%nat tbool (madd 0%nat tbool mempty)))) in
          [[find m 3]] * ([[find m 1]] * ([[find m 1]] * [[delete]])))
       @ [[associate (tbool * (tbool * (tbool * tunit)))]]
       @ [[unassociate (tbool * (tbool * tbool))]])%expr.
End ExampleCoins.
