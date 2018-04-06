Require CrossCrypto.fmap.

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
      monad.ret := id;
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
End type.
Notation type := type.type.

Module simply_typed.
  Section WithMonad.
    Context {M : monad.monad}.
    Local Notation m := M.(monad.m).
    Local Notation type_interp := (type.interp m).
    Local Notation type_inhabited := (@type.inhabited m M.(@monad.ret)).
    
    Variant operation : type.type -> Type :=
    | const {t} (_ : type_interp t) : operation t
    | id {t} (n : nat) : operation t.

    Definition expr t : Type := (list { u : type.type & operation u} ) * operation t.

    Definition lookup  {P} (ctx : list { t : type.type & P t}) (n : nat) (t : type.type) : option (P t) :=
      match FromNil.nth_error ctx n with
      | None => None
      | Some (existT _ u v) =>
        @type.transport _ _ _ v
      end.

    Definition interp_operation (ctx : list { t : type.type & type_interp t}) {t} (o : operation t)
      : option (m (type_interp t)) :=
      match o in operation t return option (m (type_interp t)) with
      | @const t v => Some (M.(monad.ret) v)
      | @id t n =>
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

    Definition interp_operation_silent ctx {t} o :=
      match interp_operation ctx o with
      | None => M.(monad.ret) (type_inhabited t)
      | Some v => v
      end.

    Fixpoint interp_silent
             (ctx : list { t : type.type & type_interp t})
             {t : type.type} (p1 : list { t : type.type & operation t }) (p2 : operation t)
             {struct p1} : m (type_interp t) :=
      match p1 with
      | (existT _ u o)::p1 =>
        M.(monad.bind) (interp_operation_silent ctx o) (fun v => interp_silent ((existT _ u v) :: ctx) p1 p2)
      | nil => interp_operation_silent ctx p2
      end.

    Definition interp_silent_toplevel {t} (p : expr t) :=
      let (p1, p2) := p in interp_silent nil p1 p2.
  End WithMonad.

  Module _test_interp.
    Local Definition _t1 :
      interp_silent_toplevel (M:=let_in_monad)
                             (existT _ _ (const (3:type.interp _ type.nat)) ::
                                     existT _ _ (const (7:type.interp _ type.nat)) ::
                                     existT _ _ (const (11:type.interp _ type.nat)) ::
                                     nil,
                              @id _ type.nat 1) = 7 := eq_refl.
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

      (* Context {tC} (eC : expr tC). *)

      Context (eqb_const : forall t, type_interp t -> type_interp t -> bool).

      Definition unify_operation (unify_operation : forall {tl} (ol : operation tl) (lem2prog : map)
                 {tp} (op : operation tp) (prog2lem : map)
        , option (map*map))
                 {tl} (ol : operation tl) (lem2prog : map)
                 {tp} (op : operation tp) (prog2lem : map)
        : option (map*map).
        refine
        match type.transport _ tp tl op with
        | None => None
        | Some op =>
          match ol in simply_typed.operation tl return operation tl -> _ with
          | @const _ t cl =>
            fun (op : operation t) =>
            match op in simply_typed.operation t return type_interp t -> _ with
            | const cp =>
              fun cl =>
                if eqb_const _ cl cp
                then Some (lem2prog, prog2lem)
                else None
            | _ => _
            end cl
          | id il => _
          end op
        end.
      Abort.
    End unification.
  End unification.
End simply_typed.




(* TODO: switch to nil-based indexing below *)
  


Section i.
  Context (i : nat).
  Definition retnegb x : option bool := Some (negb x).
  Fixpoint interp_option_bool (p : list (nat + bool)) (c : list bool) : option bool :=
    match p with
    | nil => nth_error c i
    | i::p' =>
      match i with
      | inr b => option_monad.bind (Some b) (fun x => interp_option_bool p' (x::c))
      | inl n =>
        match nth_error c n with
        | None => None (* TODO: ??? *)
        | Some x => option_monad.bind (retnegb x) (fun x => interp_option_bool p' (x::c))
        end
      end
    end.
End i.

Module phoasprog.
  Section with_typecodes.
    Context {type : Type} {interp_type : type -> Type}.
    Section with_var.
      Context {var : type -> Type}.
      Inductive pure : type -> Type := (* obviously insufficient for real use *)
      | const {t} (_ : interp_type t) : pure t
      | ref {t} (_ : var t) : pure t.
      Inductive monadic : type  -> Type :=
      | ret {t} (_ : pure t) : monadic t
      | bind {A B} (a : monadic A) (f : var A -> monadic B) : monadic B.
    End with_var.
    Global Arguments pure : clear implicits.
    Global Arguments monadic : clear implicits.

    Section with_monad.
      Context (M : monad).
      Let m := monad.m M.
      Let ret {T} := @monad.ret M T.
      Let bind {A B} := @monad.bind M A B.

      Definition interp_pure {t} (e : pure interp_type t) : interp_type t :=
        match e with
        | const c => c
        | ref v => v
        end.
      Fixpoint interp_monadic {t} (e : monadic interp_type t) : m (interp_type t) :=
        match e with
        | with_typecodes.ret a => ret (interp_pure a)
        | with_typecodes.bind a f => bind (interp_monadic a) (fun a => interp_monadic (f a))
        end.
    End with_monad.
  End with_typecodes.
  Global Arguments pure : clear implicits.
  Global Arguments monadic : clear implicits.

  Section Example.
    Local Notation ret := Some.
    Local Notation "x <- a ; f" :=
      (option_monad.bind a (fun x => f))
        (at level 70, a at next level, right associativity, format "'[v' x  <-  a ; '/' f ']'").
    Import ListNotations.
    Goal False.
      let x := eval cbv -[retnegb option_monad.bind option_monad.ret] in (interp_option_bool 0 [inr true; inl 0; inl 0; inl 2; inl 1] []) in
      pose x.
    Abort.
  End Example.
End phoasprog.

Module Import MOVEME.
  Fixpoint fin n :=
    match n with
    | O => Empty_set
    | S n => option (fin n)
    end.

  Module fin.
    Fixpoint of_nat n m : option (fin n) :=
      match n with
      | O => None
      | S n =>
        match m with
        | O => Some None
        | S m => Some (of_nat n m)
        end
      end.
  End fin.
  
  Module List.
    Fixpoint nth_fin {A} (l : list A) {struct l} : forall (n : fin (length l)), A :=
      match l with
      | nil => fun member_of_empty_set => match member_of_empty_set with end
      | a :: l =>
        fun i =>
          match i with
          | None => a
          | Some i => nth_fin l i
          end
      end.
  End List.

  Module hlist.
    Fixpoint hlist {tc} interp_tc (ts : list tc) : Type :=
      match ts with
      | nil => unit
      | t::ts => (interp_tc t * hlist interp_tc ts)
      end.

    Definition hhd {tc} {interp_tc : tc -> Type} {t ts} (xs : hlist interp_tc (t :: ts)) : interp_tc t :=
      let (x, _) := xs in x.
    Definition htl {tc} {interp_tc : tc -> Type} {t ts} (xs : hlist interp_tc (t :: ts)) : hlist interp_tc ts :=
      let (_, xs) := xs in xs.

    Fixpoint nth_fin {tc interp_tc} {ts : list tc} {struct ts} : forall (n : fin (length ts)) (xs : hlist interp_tc ts), interp_tc (List.nth_fin ts n) :=
      match ts with
      | nil => fun member_of_empty_set => match member_of_empty_set with end
      | t::ts =>
        fun n =>
          match n with
          | Some n =>
            fun xs =>
              nth_fin n (htl xs)
          | None => hhd
          end
      end.
  End hlist.
End MOVEME.

Module prog.
  Section WithMonad.
    Context (M : monad.monad).
    Let m := M.(monad.m).
    Let type_interp := type.interp m.

    Inductive expr : forall (tctx : list type) (t : type), Type :=
    | const {tctx t} (_ : type_interp t) : expr tctx t
    | ret {tctx t} (_ : expr tctx t) : expr tctx (type.m t)
    | ref {tctx} (n : fin (length tctx)) : expr tctx (List.nth_fin tctx n)
    | sub {tctx t} (_ : prog tctx t) : expr tctx (type.m t)
    with
    prog : forall (tctx : list type) (t : type), Type :=
    | bind {u tctx} (_ : expr tctx (type.m u)) {t} (_ : prog (u::tctx) t) : prog tctx t
    | final {tctx t} (_ : expr tctx (type.m t)) : prog tctx t
    .
    
    Import hlist.
    Fixpoint interp_expr {tctx t} (e : expr tctx t) {struct e} : forall (ctx : hlist type_interp tctx), type_interp t :=
      match e with
      | const v => fun _ => v
      | ret e => fun ctx => M.(monad.ret) (interp_expr e ctx)
      | ref n => nth_fin n
      | sub p => interp_prog p
      end
    with
    interp_prog {tctx t} (p : prog tctx t) {struct p} : forall (ctx : hlist type_interp tctx), type_interp (type.m t) :=
      match p with
      | bind e p => fun ctx => M.(monad.bind) (interp_expr e ctx) (fun x => interp_prog p (x, ctx))
      | final e => interp_expr e
      end.
  End WithMonad.
End prog.


Module flatprog.
  Section WithMonad.
    Context (M : monad.monad).
    Let m := M.(monad.m).
    Let type_interp := type.interp m.

    Variant operation : forall (tctx : list type) (t : type), Type :=
    | const {tctx t} (_ : type_interp t) : operation tctx t
    | id {tctx} (n : fin (length tctx)) : operation tctx (List.nth_fin tctx n)
    .

    Inductive prog : forall (tctx : list type) (t : type), Type :=
    | bind {u tctx} (_ : operation tctx u) {t} (_ : prog (u::tctx) t) : prog tctx t
    | final {tctx t} (_ : operation tctx t) : prog tctx t
    .
    
    Import hlist.
    Definition interp_operation {tctx t} (e : operation tctx t) : forall (ctx : hlist type_interp tctx), type_interp (type.m t) :=
      match e with
      | const v => fun _ => M.(monad.ret) v
      | id n => fun ctx => M.(monad.ret) (nth_fin n ctx)
      end.

    Fixpoint interp {tctx t} (p : prog tctx t) {struct p} : forall (ctx : hlist type_interp tctx), type_interp (type.m t) :=
      match p with
      | bind o p => fun ctx => M.(monad.bind) (interp_operation o ctx) (fun x => interp p (x, ctx))
      | final o => interp_operation o
      end.

    Fixpoint of_prog {tctx t} (p : prog.prog M tctx t) : prog tctx t. Admitted.
  End WithMonad.
End flatprog.

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