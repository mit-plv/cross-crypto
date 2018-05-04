Require CrossCrypto.fmap.list_of_pairs.
Require CrossCrypto.Loops.

(* TODO: moveme *)
Fixpoint Fixn {A B} (n:nat) (f : (A -> option B) -> A -> option B) {struct n}
  : A -> option B :=
  match n with
  | O => f (fun _ => None)
  | S n => f (Fixn n f)
  end.
Fixpoint Fixn_silent {A B} (inhabited_B:B) (n:nat) (f : (A -> B) -> A -> B) {struct n}
  : A -> B :=
  match n with
  | O => f (fun _ => inhabited_B)
  | S n => f (Fixn_silent inhabited_B n f)
  end.

Lemma Fixn_partial_correctness {A B} n (f : _ -> A -> option B)
      (P : A -> B -> Prop) :
      match (fun F => forall a b, F a = Some b -> P a b) with ok => forall
      (Hstep : forall F, ok F -> ok (f F))
  , ok (Fixn n f) end.
Proof. intros; induction n; cbn; refine (Hstep _ _); [congruence|assumption]. Qed.

Module monad.
  Record monad :=
    {
      m : Type -> Type;
      ret : forall {T}, T -> m T;
      bind : forall {A B}, m A -> (A -> m B) -> m B
    }.

  Section with_monad.
    Context (M : monad).
    Let m := monad.m M.
    Let ret {T} := @monad.ret M T.
    Let bind {A B} := @monad.bind M A B.
    
    Record ok :=
      {
        bind_ret_l : forall {A B} (a : A) (f : A -> m B) , bind (ret a) f = f a;
        bind_ret_r : forall {A} (a : m A), bind a ret = a;
        bind_assoc : forall {A B C} (a : m A) (f : A -> m B) (g : B -> m C),
            bind (bind a f) g = bind a (fun x => bind (f x) g)
      }.

    Definition commutative :=
      forall A B C (a : m A) (b : m B) (f : A -> B -> m C),
        bind a (fun a => bind b (fun b => f a b)) = bind b (fun b => bind a (fun a => f a b)).
                                       
  End with_monad.
End monad.
Notation monad := monad.monad.

Module let_in_monad.
  Definition let_in_monad : monad :=
    {|
      monad.m := fun A => A;
      monad.ret := fun _ x => x;
      monad.bind := fun A B (a : A) (f : A -> B) => let x := a in f x
    |}.

  Lemma ok : monad.ok let_in_monad.
  Proof. split; intros; cbv; reflexivity. Qed.

  Lemma commutative : monad.commutative let_in_monad.
  Proof. cbv; intros; reflexivity. Qed.
End let_in_monad.
Notation let_in_monad := let_in_monad.let_in_monad.

Module option_monad.
  Local Definition m A := option A.
  Local Definition ret {A} : A -> m A := Some.
  Definition bind {A B } : m A  -> (A -> m B) -> m B := fun a f =>  option_rect _ f None a.
  Definition option_monad : monad :=
    {|
      monad.m := m;
      monad.ret := @ret;
      monad.bind := @bind
    |}.

  Lemma ok : monad.ok option_monad.
  Proof.
    split; cbv; intros;
      repeat match goal with
             | |- context [match ?x with _ => _ end] => destruct x eqn:?
             end; congruence.
  Qed.

  Lemma commutative : monad.commutative option_monad.
  Proof.
    cbv; intros;
      repeat match goal with
             | |- context [match ?x with _ => _ end] => destruct x eqn:?
             end; congruence.
  Qed.
End option_monad.
Notation option_monad := option_monad.option_monad.

Ltac is_sort x :=
  lazymatch x with
  | Type => idtac
  | Set => idtac
  | Prop => idtac
  | _ => fail 0 "not a sort"
  end.

Ltac is_convertible_to_a_type e :=
  let __ := open_constr:(_ : e) in
  idtac.

Goal False.
  is_convertible_to_a_type Set.
  is_convertible_to_a_type Prop.
  is_convertible_to_a_type Type.
  is_convertible_to_a_type nat.
  is_convertible_to_a_type False.
  is_convertible_to_a_type (let x := True in False).
  is_convertible_to_a_type ((fun x => x) False).
  is_convertible_to_a_type (forall (x:unit), nat).
  is_convertible_to_a_type (forall (x:unit), x = x).
  Fail is_convertible_to_a_type O.
  Fail is_convertible_to_a_type (@nil nat).
  Fail is_convertible_to_a_type (Set, Set).
Abort.

Ltac appears_in x l :=
  lazymatch l with
  | nil => fail
  | cons x _ => idtac
  | cons _ ?tl => appears_in x tl
  end.

Ltac add_to_set x l :=
  match constr:(Set) with
  | _ => let __ := appears_in x l in l
  | _ =>
    let T := match type of x with ?T => T end in
    constr:(@List.cons T x l)
  end.

Ltac list_union l1 l2 :=
  lazymatch l1 with
  | nil => l2
  | @cons ?T ?x ?l1' =>
    let x := (* preserve types after matching, COQBUG(7425 *)
        match type of x with
        | T => x
        | _ => constr:((x : T))
        end in
    let l2 := add_to_set x l2 in
    list_union l1' l2
  end.

Goal False.
  let l1 := constr:(cons 1 (cons 2 nil)) in
  let l2 := constr:(cons 2 (cons 3 nil)) in
  let l3 := list_union l1 l2 in
  constr_eq l3 (cons 1 (cons 2 (cons 3 nil))).

  let l1 := constr:(cons nat (cons unit nil)) in
  let l2 := constr:(cons bool (cons unit nil)) in
  let l3 := list_union l1 l2 in
  constr_eq l3 (nat :: bool :: unit :: nil)%list.
  
  let l1 := constr:(cons (list nat) (cons unit nil)) in
  let l2 := constr:(cons bool (cons unit nil)) in
  let l3 := list_union l1 l2 in
  constr_eq l3 (list nat :: bool :: unit :: nil)%list.

  let l1 := constr:(@cons Type (nat:Type) (@nil Type)) in
  let l2 := constr:(@cons Type (unit:Type) (@nil Type)) in
  let l := list_union l1 l2 in
  constr_eq l (((nat : Type) :: (unit : Type) :: nil)%list).
Abort.

(** Reification *)
Section WithMonad.
  Context (M : monad).
  Let m := monad.m M.
  Let ret {T} := @monad.ret M T.
  Let bind {A B} := @monad.bind M A B.
  Reserved Notation "A <- X ; B" (at level 70, X at next level, right associativity, format "'[v' A  <-  X ; '/' B ']'").
  Local Notation    "A <- X ; B" := (bind X (fun A => B)).
  

  Ltac types_in e :=
    (* FIXME: exclude function types *)
    let T := match type of e with ?T => constr:((T : Type)) end in
    match e with
    | _ => let __ := is_convertible_to_a_type e in constr:(@nil Type)
    | _ => lazymatch e with
           | ?f ?x =>
             let tix := types_in x in
             let tif := types_in f in
             let tir := list_union tif tix in
             let ti := add_to_set T tir in ti
           | _ => constr:(@cons Type T (@nil Type))
           end
    end.
  Goal False.
    let e := nat in
    let tie := types_in e in
    constr_eq tie (@nil Type).

    let e := constr:(O) in
    let tie := types_in e in
    constr_eq tie ((nat:Type) :: nil)%list.

    let e := constr:(S O) in
    let tie := types_in e in
    idtac tie.

    let e := constr:(tt) in
    let tie := types_in e in
    constr_eq tie ((unit : Type) :: nil)%list.

    let e := constr:(@pair unit unit tt tt) in
    let tie := types_in e in
    idtac tie.

    let e := constr:(@pair unit nat tt O) in
    let tie := types_in e in
    idtac tie.

    let e := constr:(@pair unit unit tt tt) in
    let tie := types_in e in
    idtac tie.

    let t := constr:((nat : Type)) in
    let T := match type of t with ?T => T end in
        pose T.

    let e := constr:((tt, O)) in
    let tie := types_in e in
    idtac tie.

    let e := constr:((S O + S O, tt)) in
    let tie := types_in e in
    idtac tie.

    (*
    let e := constr:((1+2, tt, ((1,2)::(0,0)::nil))%list) in
    let tie := types_in e in
    pose tie.
     *)

    Abort.

  Context
    {TK} {K : TK}
    {TB} {B : TK -> m TB}
    {TA} {A : TK -> m TA}
    {TX} {X : TB -> TB -> m TX}
    {TC} {C : TK -> TA -> TB -> TB -> TX -> m TC}
    {TD} {D : TK -> TA -> TC -> m TD}.

  Context {TG}
          {F : TK -> TG}
          {G : TG -> TK}.
  Goal forall (a : TA) (c : TC), False.
    intros.
    let e := constr:(
               k <- ret (G (F K));
               D k a c) in
    idtac e.
  Abort.

  Goal False.
    let e := constr:(
               k <- ret K;
               b <- B k;
               b'<- B k;
               a <- A k;
               x <- X b b';
               c <- C k a b b' x;
               D k a c) in
    idtac e.
  Abort.
End WithMonad.



(*

Each lemma has

- 0 or more universally quantified variables, each of which can be referenced 1 or more times
- 0 or more bound operations in the LHS
- 1 or more distinguished output operations (initially we will support exactly 1) in the LHS
- a function that given the LHS returns "option RHS", containing 0 or more bound operations and the same number as outputs as in the LHS

Each operation is either

- return of a pure function applied to some arguments
- a monadic function applied to some arguments

An argument is simply a reference to an earlier binder.
Constants are treated as functions of 0 arguments and thus bound instead of inlined.

Each expression has
- 0 or more bound operations
- a final oputput operation


Matching a lemma should be equivalent to transforming a program to a form where the lemma is a subexpression:

   k <- ret K;
   b <- B k;
   b'<- B k;
   a <- A k;
   x <- x b b';
   c <- C k a b b' x;
   D k a c;

could be written as

   k <- ret K;
   a <- A k;
   c <- (k' <- ret K;
         b  <- B k';
         b' <- B k';
         x  <- X b b';
         C k' a b b' x);
   D k a c;

Note that it is important that

- B commutes with A and X
- [x <- ret K; P x x] is equivalent to [x <- ret K; y <- ret K; P x y] where P is the rest of the program (this is true for all P because [ret K] is a ret)
- [ret K] commutes with A, B, and X (because it is a ret)
- the k passed to C is the same as the k passed to B
- b and b' are different binders in the original expression (e.g., B may be coin toss in the probability monad)
- b and b' do not appear outside the subexpression; in particular, they are not arguments to D, and X only appears inside the subexpression

Now, a lemma that is unviversally quantified over D and over the operation that defines a (but not necessarily over K) can be used to rewrite the computation of c.

To check that the expression can be rewritten in this way, the matcher needs to maintain the following state:

- For each universal quantifier in the lemma, optionally the binder in the expression that it is instantiated with.
- For each binder in the lemma, optionally the binder in the expression matched to it
- For each binder in the expression, if it is non-duplicatable, optionally the binder in the lemma matched to it

For every operation in the expression, (* guess and check whether it is the output of the LHS of the lemma *)
  1. Recursively match each argument of the operation, updating the state described above.
  2. For each matched binder in the expression, compute the list of unmatched binders in the expression whose operations directly reference this first binder. If this is non-empty, the intermediate binder is still referenced in the outside program and thus cannot be rewritten using a lemma that does not allow leaking its value.
*)

Require Import Coq.Lists.List.
Import monad.
Module List.
  Module FromNil.
    Section WithElementType.
      Context {A : Type}.
      Definition nth_error_count l n : nat + A :=
                 fold_right (fun a s
                             => match s with
                                | inl n =>
                                  match n with
                                  | O => inr a
                                  | S n => inl n
                                  end
                                | inr a => inr a
                                end
                            ) (inl n) l.
      Definition nth_error (l : list A) (n : nat) : option A :=
        match nth_error_count l n with
        | inl _ => None
        | inr a => Some a
        end.
    End WithElementType.

    Module _test.
      Local Definition t0 : nth_error (2::1::0::nil) 0 = Some 0 := eq_refl.
      Local Definition t1 : nth_error (2::1::0::nil) 1 = Some 1 := eq_refl.
      Local Definition t2 : nth_error (2::1::0::nil) 2 = Some 2 := eq_refl.
      Local Definition tx : nth_error (2::1::0::nil) 3 = None := eq_refl.
    End _test.
  End FromNil.
End List.

Import List.
Import monad.

Module type. (* obviously insufficient for real use *)
  Inductive type :=
  | nat : type
  | m (_:type) : type
  .

  Fixpoint interp m (t : type) {struct t} : Type :=
    match t with
    | type.nat => Datatypes.nat
    | type.m t => m (interp m t)
    end.

  Lemma inhabited {m} {ret : forall T, T -> m T} : forall (t : type), interp m t.
  Proof.
    induction t; [ apply O | apply ret, IHt ].
  Qed.

  Fixpoint transport (P : type -> Type) (a b : type) {struct a}
    : P a -> option (P b) :=
    match a, b with
    | type.nat, type.nat => Some
    | type.m a, type.m b => transport (fun t => P (m t)) a b
    | _, _ => fun _ => None
    end.

  Definition eqb a b :=
    match transport (fun _ => unit) a b tt with
    | Some _ => true
    | None => false
    end.
End type.
Notation type := type.type.

Module simply_typed.
  Section WithMonad.
    Context {M : monad.monad}.
    Local Notation m := M.(monad.m).
    Local Notation type_interp := (type.interp m).
    Local Notation type_inhabited := (@type.inhabited m M.(@monad.ret)).
    
    Variant operation := const (t : type) (v : type_interp t) | id (n : nat).
    Definition expr : Type := list (type * operation) * operation.

    Definition lookup  {P} (ctx : list { t : type.type & P t}) (n : nat) (t : type.type) : option (P t) :=
      match FromNil.nth_error ctx n with
      | None => None
      | Some (existT _ u v) =>
        @type.transport _ _ _ v
      end.

    Definition interp_operation (ctx : list { t : type.type & type_interp t}) (o : operation) t
      : option (m (type_interp t)) :=
      match o with
      | @const tv v =>
        match type.transport _ tv t v with
        | Some v => Some (M.(monad.ret) v)
        | None => None
        end
      | @id n =>
        match lookup ctx n t with
        | None => None
        | Some v => Some (M.(monad.ret) v)
        end
      end.

    (* apparently we can't write a non-total tail-recursive interpreter because of binders *)
    (*
    Fixpoint interp_ (ctx : list { t : type.type & type_interp t}) (p1 : list operation) (p2 : operation) {struct p1} : option { t : type.type & m (type_interp t)} :=
      match p1 with
      | o::p1 =>
        match interp_operation (FromNil.nth_error ctx) o with
        | None => None
        | Some (existT _ u x)
          =>
          (* M.(monad.bind) x (fun bound => interp_ ((existT _ u bound) :: ctx) p1 p2) (* doesn't typeckeck because would return [m (option ...)]*) *)
          match interp_ ((existT _ u (*???*)_(*free variable?*)) :: ctx) p1 p2 with
          | None => None
          | Some body =>
            M.(monad.bind) x body (* doesn't typecheck because body lacks binder *)
          end
        end
      | nil => interp_operation (FromNil.nth_error ctx) p2
      end.
     *)

    Definition interp_operation_silent ctx o t :=
      match interp_operation ctx o t with
      | None => M.(monad.ret) (type_inhabited t)
      | Some v => v
      end.

    Fixpoint interp_silent (t : type) (p2 : operation)
             (p1 : list (type*operation))
             (ctx : list { t : type.type & type_interp t})
             {struct p1} : m (type_interp t) :=
      match p1 with
      | (u, o)::p1 =>
        M.(monad.bind) (interp_operation_silent ctx o u) (fun v => interp_silent t p2 p1 ((existT _ u v) :: ctx))
      | nil => interp_operation_silent ctx p2 t
      end.

    Definition interp_silent_toplevel (t : type) (p : expr) :=
      let (p1, p2) := p in interp_silent t p2 p1 nil.
  End WithMonad.

  Module _test_interp.
    Local Definition _t1 :
      interp_silent_toplevel (M:=let_in_monad)
                             type.nat
                             ((type.nat, const _ (3:type.interp _ type.nat)) ::
                                     (type.nat, const _ (7:type.interp _ type.nat)) ::
                                     (type.nat, const _ (11:type.interp _ type.nat)) ::
                                     nil,
                              @id _ 1) = 7 := eq_refl.
  End _test_interp.

  Module unification.
    Section unification.
      Context (map_operations : fmap.operations nat nat).
      Local Notation map := (map_operations.(fmap.M)).
      Local Notation empty := (map_operations.(fmap.empty)).
      Local Notation add := (map_operations.(fmap.add)).
      Local Notation find := (map_operations.(fmap.find)).

      Context {monad_operations : monad.monad}.
      Local Notation m := monad_operations.(monad.m).
      Local Notation type_interp := (type.interp m).
      Local Notation type_inhabited := (@type.inhabited m monad_operations.(@monad.ret)).
      Local Notation expr := (expr (M:=monad_operations)).
      Local Notation operation := (operation (M:=monad_operations)).

      (* TODO: universally quantified variables *)

      Definition unify_bound (il ip : nat) (lem2prog : map) (prog2lem : map) : option (map*map) :=
        match find il lem2prog with
        | Some ip' =>
          if Nat.eqb ip' ip
          then Some (lem2prog, prog2lem) (* nop (reverse map is fine by invariant) *)
          else None (* confict -- lemma-side variable already used for something else (TODO: handle ret) *)
        | None => (* unify... *)
          let lem2prog := add il ip lem2prog in
          match find ip prog2lem with
          | Some il' =>
            if Nat.eqb il il'
            then Some (lem2prog, prog2lem) (* nop *)
            else None (* confict -- program-side variable already used for something else (TODO: handle ret) *)
          | None => (* unify... *)
            let prog2lem := add ip il prog2lem in
            Some (lem2prog, prog2lem)
          end
        end.

      Context (eqb_const : forall t, type_interp t -> type_interp t -> bool).

      Context
        (lemma : list (type*operation))
        (program : list (type*operation)).

      Definition unify_operation : (type * operation) * (type * operation) * map * map -> option (map*map) :=
        Fixn (length lemma) (fun recurse '(ol, op, lem2prog, prog2lem) =>
          let '(tl, ol) := ol in
          let '(tp, op) := op in
          match type.transport (fun _ => unit) tp tl tt with
          | None => None
          | Some _ =>
            match ol, op with
            | const tvl vl, const tvp vp =>
              match type.transport _ tvp tvl vp with
              | None => None
              | Some vp =>
                match eqb_const _ vl vp with
                | false => None
                | true => Some (lem2prog, prog2lem)
                end
              end
            | id il, id ip =>
              match unify_bound il ip lem2prog prog2lem with
              | None => None
              | Some (lem2prog, prog_lem) =>
                match nth_error lemma il, nth_error program ip with
                | Some ol', Some op' => recurse (ol', op', lem2prog, prog2lem)
                | _, _ => None
                end
              end
            | _, _ => None
            end
          end).

      Context (lemma_last : type * operation).
      Context (prog_last : type * operation).

      Definition translate_operation (m : map) (o : operation) : option operation :=
        match o with
        | id il => option_map id (find il m)
        | const _ _ => Some o
        end.

      Definition option_all {T} : list (option T) -> option (list T) :=
        List.fold_right (fun ox ol =>
                           match ox, ol with
                           | Some x, Some l => Some (cons x l)
                           | _, _ => None
                           end)
                           (Some nil).

      Definition translate (m : map) (e : expr) : option expr :=
        let '(l, o) := e in
        match option_all (List.map (fun '(t, o) =>
                                      match translate_operation m o with
                                      | Some o' => Some (t, o)
                                      | None => None
                                      end)
                                   l)
        with None => None
        | Some l' =>
          match translate_operation m o
          with None => None
          | Some o' =>
            Some (l', o')
          end
        end.
        

      Check
        fun lemma_rhs : expr =>
          Loops.core.loop
            (fun '(op, iNext) =>
               match unify_operation (lemma_last, op, empty, empty) with
               | None => inl (nth_default op program iNext, iNext-1)
               | Some x => inr x
               end)
            (length program) (prog_last, length program - 1).
      Check Loops.for3 (length lemma) (fun i => Nat.ltb 0 i) (fun i => 1+i)
            (fun _ => _).

      Lemma unify_operation_correct args ret:
        unify_operation args = Some ret -> True.
      Proof.
        cbv [unify_operation].
        refine (Fixn_partial_correctness _ _ _ _ _ _); clear args ret;
          intros recurse IH [[[[tl ol] [tp op]] lem2prog] prog2lem] [lem2prog' prog2lem'].
        destruct ol, op;
          repeat match goal with
                 | _ => discriminate
                 | |- context [match ?E with None => _ | _ => _ end] => destruct E eqn:?
                 | |- context[eqb_const ?t ?a ?b] => destruct (eqb_const t a b) eqn:?
                 end.
             
      Abort.
    End unification.

    Import CrossCrypto.fmap.list_of_pairs.

    Module _test.
      Local Definition sillytest :
        unify_operation
          (list_of_pairs Nat.eqb)
          (monad_operations := option_monad)
          (fix eqb_const (t:type.type) {struct t} : _ -> _ -> bool :=
             match t with
             | type.nat => Nat.eqb
             | type.m t =>
               fun a b =>
                 match a, b with
                 | None, None => true
                 | Some a, Some b => eqb_const t a b
                 | _, _ => false
                 end
             end)
          ((type.nat, const type.nat 1)::(type.nat, const type.nat 1)::nil)
          ((type.nat, const type.nat 2)::(type.nat, const type.nat 1)::(type.nat, const type.nat 0)::nil)
          ((type.nat, id 0), (type.nat, id 1), (list_of_pairs _).(fmap.empty), (list_of_pairs _).(fmap.empty))
          = Some ((0, 1) :: nil, nil) := eq_refl.
    End _test.
  End unification.
End simply_typed.

(*
monad rewriting unification notes:

normalization: sort by (topological order, arbitrary strict order)

single-output lemmas:
match root of lemma LHS expression tree first, then its dependencies, then their dependencies
the matching needs to be isolated in various ways:
the internal binds of the lemma cannot be matched to the same bind in code: conunterexample coin xor coin
the internal binds must be removed during the rewrite, so they cannot be used anywhere else: (coin xor coin) xor (coin xor coin)
for the proof of this, we want to say that the code is equivalent to [ctx1; x <-(lemma...); ctx2]
this will require queries to a commutability oracle to move parts of the lemma to be adjacent (we probably want to move everything next to the root)
the only guess that will need to be backtracked is the location of the root

multi-output lemmas like DDH are inherently harder, essentially we are doing single-output rewrite on the tuple of all outputs PLUS higher-order unification to find out how ctx2 is a function of that tuple. will involve lots of guessing.
*)