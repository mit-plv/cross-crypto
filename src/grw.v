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

Require Import Coq.Lists.List.

Import monad.

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

  Fixpoint nth_fin {T} (xs : list T) : forall (n : fin (length xs)), T :=
    match xs with
    | nil => fun member_of_empty_set => match member_of_empty_set with end
    | x :: xs =>
      fun i =>
        match i with
        | None => x
        | Some i => nth_fin xs i
        end
    end.

  Fixpoint hlist {tc} interp_tc (ts : list tc) : Type :=
    match ts with
    | nil => unit
    | t::ts => (interp_tc t * hlist interp_tc ts)
    end.

  Definition admit {T} : T. Admitted.

  Definition hhd {tc} {interp_tc : tc -> Type} {t ts} (xs : hlist interp_tc (t :: ts)) : interp_tc t :=
    let (x, _) := xs in x.
  Definition htl {tc} {interp_tc : tc -> Type} {t ts} (xs : hlist interp_tc (t :: ts)) : hlist interp_tc ts :=
    let (_, xs) := xs in xs.

  Fixpoint hnth_fin {tc interp_tc} {ts : list tc} {struct ts} : forall (n : fin (length ts)) (xs : hlist interp_tc ts), interp_tc (nth_fin ts n) :=
    match ts with
    | nil => fun member_of_empty_set => match member_of_empty_set with end
    | t::ts =>
      fun n =>
        match n with
        | Some n =>
          fun xs =>
            hnth_fin n (htl xs)
        | None => hhd
        end
    end.
End MOVEME.

Module type. (* obviously insufficient for real use *)
  Inductive type :=
  | nat : type
  | m (_:type) : type
  .

  Fixpoint interp m (t : type) : Type :=
    match t with
    | type.nat => Datatypes.nat
    | type.m t => m (interp m t)
    end.
End type.
Notation type := type.type.

Module prog.
  Section WithMonad.
    Context (M : monad.monad).
    Let m := M.(monad.m).
    Let type_interp := type.interp m.

    Inductive expr : forall (tctx : list type) (t : type), Type :=
    | const {tctx t} (_ : type_interp t) : expr tctx t
    | ret {tctx t} (_ : expr tctx t) : expr tctx (type.m t)
    | ref {tctx} (n : fin (length tctx)) : expr tctx (nth_fin tctx n)
    | sub {tctx t} (_ : prog tctx t) : expr tctx (type.m t)
    with
    prog : forall (tctx : list type) (t : type), Type :=
    | bind {u tctx} (_ : expr tctx (type.m u)) {t} (_ : prog (u::tctx) t) : prog tctx t
    | final {tctx t} (_ : expr tctx (type.m t)) : prog tctx t
    .
    
    Fixpoint interp_expr {tctx t} (e : expr tctx t) {struct e} : forall (ctx : hlist type_interp tctx), type_interp t :=
      match e with
      | const v => fun _ => v
      | ret e => fun ctx => M.(monad.ret) (interp_expr e ctx)
      | ref n => hnth_fin n
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
    | id {tctx} (n : fin (length tctx)) : operation tctx (nth_fin tctx n)
    .

    Inductive prog : forall (tctx : list type) (t : type), Type :=
    | bind {u tctx} (_ : operation tctx u) {t} (_ : prog (u::tctx) t) : prog tctx t
    | final {tctx t} (_ : operation tctx t) : prog tctx t
    .
    
    Definition interp_operation {tctx t} (e : operation tctx t) : forall (ctx : hlist type_interp tctx), type_interp (type.m t) :=
      match e with
      | const v => fun _ => M.(monad.ret) v
      | id n => fun ctx => M.(monad.ret) (hnth_fin n ctx)
      end.

    Fixpoint interp {tctx t} (p : prog tctx t) {struct p} : forall (ctx : hlist type_interp tctx), type_interp (type.m t) :=
      match p with
      | bind o p => fun ctx => M.(monad.bind) (interp_operation o ctx) (fun x => interp p (x, ctx))
      | final o => interp_operation o
      end.

    Fixpoint of_prog {tctx t} (p : prog.prog M tctx t) : prog tctx t. Admitted.
  End WithMonad.

  Module simply_typed.
    Section WithMonad.
      Context (M : monad.monad).
      Let m := M.(monad.m).
      Let type_interp := type.interp m.
      
      Variant operation :=
      | const {t} (_ : type_interp t)
      | id (n : nat).

      Definition prog : Type := (list operation) * operation.

      Definition interp_operation (ctx : nat -> option { t : type.type & type_interp t}) (o : operation) : option { t : type.type & type_interp t } :=
        match o with
        | const v => Some (existT _ _ v)
        | id n => ctx n
        end.

      Fixpoint interp_ (ctx : list { t : type.type & type_interp t}) (p1 : list operation) (p2 : operation) {struct p1} : option { t : type.type & type_interp t} :=
        match p1 with
        | o::p1 =>
          match interp_operation (nth_error ctx) o with
          | None => None
          | Some bound => interp_ (bound :: ctx) p1 p2
          end
        | nil => interp_operation (nth_error ctx) p2
        end.

      Definition interp (ctx : list { t : type.type & type_interp t}) (p : prog) : option { t : type.type & type_interp t} := 
        let (p1, p2) := p in interp_ ctx p1 p2.

    End WithMonad.
  End simply_typed.
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