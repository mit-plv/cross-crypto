Set Universe Polymorphism.
Set Primitive Projections.
Unset Printing Primitive Projection Parameters.

Definition sum1 A B (X : Type) : Type := A X + B X.

Delimit Scope eff_scope with eff.
Local Notation "E1 + E2" := (sum1 E1 E2) : eff_scope.

Module interaction.
  Inductive interaction {E : Type -> Type} {T : Type} :=
  | interact {R : Type} (e : E R) (k : R -> interaction)
  | ret (_ : T).
  Arguments interaction : clear implicits.
  Arguments interaction _%eff _%type.

  Section bind.
    Context {E : Type -> Type} {T U : Type} (k : T -> interaction E U).
    Fixpoint bind' (c : interaction E T) : interaction E U :=
      match c with
      | ret r => k r
      | interact e k' => interact e (fun x => bind' (k' x))
      end.
  End bind.
  Definition bind {E T U} c k := @bind' E T U k c.
End interaction. Notation interaction := interaction.interaction.

Module rand. Variant rand : Type -> Type :=
  | coin : rand bool.
End rand. Notation rand := rand.rand.

Module state.
  Variant state {S : Type} : Type -> Type :=
  | get : state S
  | put (_ : S) : state unit.
  Arguments state : clear implicits.

  Section run.
    Import interaction.
    Context {E : Type -> Type} {T S : Type}.
    Fixpoint run (prog : interaction (E + state S) T) (s : S) {struct prog} : interaction E (T*S) :=
      match prog with
      | interact o k =>
        match o with
        | inl e => fun k => interact e (fun i => run (k i) s)
        | inr a =>
          match a with
          | get => fun k => run (k s) s
          | put s => fun k => run (k tt) s
          end
        end k
      | ret r => ret (pair r s)
      end.
    Definition run_and_havoc p s := bind (run p s) (fun x => ret (fst x)).
  End run.
End state. Notation state := state.state.

Module raw_adversary.
Section WithAdversary.
  Import interaction.
  Context {E T S}
          (A : forall R, E R -> interaction (rand + state S)%eff R)
          (D : T -> interaction (rand + state S) bool).
  Fixpoint run' (proto : interaction E T) : interaction (rand + state S)%eff T :=
    match proto with
    | interact o k => bind (A _ o) (fun i => run' (k i))
    | ret r => ret r
    end.
  Definition run proto := bind (run' proto) D.
End WithAdversary.
End raw_adversary.

Module raw_adversary_with_early_exit. (* TODO: use this one instead? *)
Section WithAdversary.
  Import interaction.
  Context {E T S}
          (A : forall R, E R -> interaction (rand + state S)%eff (R + bool))
          (D : T -> interaction (rand + state S) bool).
  Fixpoint run' (proto : interaction E T) : interaction (rand + state S)%eff (T + bool) :=
    match proto with
    | interact o k => bind (A _ o)
                           (fun x =>
                              match x with
                              | inl i => run' (k i)
                              | inr b => ret (inr b)
                              end)
    | ret r => ret (inl r)
    end.
  Definition run proto := bind (run' proto)
                               (fun x =>
                                  match x with
                                  | inl i => D i
                                  | inr b => ret b
                                  end).
End WithAdversary.
End raw_adversary_with_early_exit.

Require Coq.Logic.Eqdep_dec.
Require Coq.Lists.List.

Module List.
  Import Coq.Lists.List.
  Lemma flat_map_singleton {A B} f l :
    @flat_map A B (fun a : A => cons (f a) nil) l = map (fun a : A => f a) l.
  Proof. induction l. reflexivity. cbn. f_equal. Qed.

  Module count.
    Inductive count : list Prop -> nat -> Prop :=
    | nil : count nil 0
    | True  (P : Prop) (_:    P) n' l' (_:count l' n') : count (cons P l') (S n')
    | False (P : Prop) (_:not P) n' l' (_:count l' n') : count (cons P l')    n'.

    Lemma le_length l n (H : count l n) : n <= length l.
    Proof. induction H; cbn; auto using le_n_S. Qed.
    Lemma count_all l (H : List.Forall (fun P => P) l) : count l (length l).
    Proof. induction H; cbn; constructor; auto. Qed.
    Lemma count_none l (H : List.Forall not l) : count l O.
    Proof. induction H; cbn; constructor; auto. Qed.
  End count. Notation count := count.count.
End List.

Module nonempty.
  Section WithT.
    Context {T : Type}.
    Definition ok (l : list T) := match l with nil => False | _ => True end.

    Lemma hprop_ok l (p q : ok l) : p = q.
    Proof. destruct l, p, q; reflexivity. Qed.

    Lemma ok_iff_length l : ok l <-> length l <> O.
    Proof. destruct l; cbn [ok length] in *; intuition congruence. Qed.

    Record list := of_list' { to_list : Datatypes.list T ; _ : ok to_list }.

    Lemma eq_iff (a b : list) : a = b <-> to_list a = to_list b.
    Proof.
      split. congruence.
      destruct a as [[][]], b as [[][]].
      inversion 1; congruence.
    Qed.

    Definition of_list l p := of_list' l (proj2 (ok_iff_length l) p).

    Lemma to_list_of_list' l p : to_list (of_list' l p) = l. reflexivity. Qed.
    Lemma to_list_of_list l p : to_list (of_list l p) = l. reflexivity. Qed.

    Definition cons_list (x : T) (l : List.list T) : list := (of_list' (cons x l) I).
    Definition singleton (x : T) : list := (of_list' (cons x nil) I).
  End WithT. Arguments list : clear implicits.

  Definition map {A B} (f : A -> B) (l : list A) : list B.
    refine (of_list' (List.map (fun a => f a) (to_list l)) _).
    abstract (destruct l as [[|a l][]]; exact I).
  Defined.

  Definition flat_map {A B} (f : A -> list B) (l : list A) : list B.
    refine (of_list' (List.flat_map (fun a => to_list (f a)) (to_list l)) _).
    abstract (destruct l as [[|a l][]];
              cbn [List.flat_map to_list];
              destruct (f a) as [[][]] eqn:?;
              exact I).
  Defined.

  Lemma flat_map_singleton {A B} l f : @flat_map A B (fun a => singleton (f a)) l = map f l.
  Proof. apply eq_iff, List.flat_map_singleton. Qed.
End nonempty.

Definition ddist T := nonempty.list T.
Module ddist.
  Definition ret {A} (x : A) := nonempty.singleton x.
  Definition bind {A B} (a : ddist A) (f : A -> ddist B) :=
    nonempty.flat_map f a.
  Definition map {A B} (f : A -> B) (a : ddist A) := 
    nonempty.map f a.

  (* TODO: define canonical fractions, only return canonical fractions *)
  Definition Pr (d : ddist Prop) '(num, den) :=
    List.count (nonempty.to_list d) num /\ length (nonempty.to_list d) = den.
  Definition prob {A} (P : A -> Prop) (d : ddist A) pr := Pr (map P d) pr.
  Definition Prb := prob is_true.
  Definition Prc (d : ddist bool) :=
    (List.length (List.filter id (nonempty.to_list d)), length (nonempty.to_list d)).

  Lemma Prc_correct d f : Prb d f <-> Prc d = f.
  Proof.
    destruct d as [l o], f as [num den]; split; cbv [Pr prob Prb Prc]; cbn.
    { intros [H ?]; subst. rewrite List.map_length. f_equal. clear o.
      remember (List.map (fun a : bool => is_true a) l) as Pl eqn:HPl.
      revert dependent l; induction H; intros.
      { destruct l; inversion HPl. reflexivity. }
      { destruct l; inversion HPl; subst; clear HPl.
        inversion H; subst; cbn. f_equal. eauto. }
      { destruct l; inversion HPl; subst; clear HPl.
        cbv [is_true] in *; destruct b; [contradiction|]; cbn in *; eauto. } }
    { intros H. inversion H; subst; clear H. split; auto using List.map_length.
      clear o.
      induction l as [|a l]; [solve[constructor]|].
      destruct a; cbn in *.
      { constructor. constructor. assumption. }
      { constructor. firstorder. assumption. } }
  Qed.

  Lemma bind_ret_r {A B} a f : @bind A B a (fun a => ret (f a)) = map f a.
  Proof. cbv [ret map bind]. apply nonempty.flat_map_singleton. Qed.
  
  Definition coin : ddist bool := nonempty.of_list' (true::false::nil)%list I.

  Fixpoint interp {T} (p : interaction rand T) : ddist T :=
    match p with
    | @interaction.interact _ _ R e k =>
      match e in rand R return (R -> _) -> _ with
      | rand.coin => fun k => bind coin (fun b => interp (k b))
      end k
    | interaction.ret x => ret x
    end.
End ddist.

Module adversary.
  Import ddist.
  Section adversary.
    Context {E : Type -> Type} {T : Type}.
    Record adversary := {
      S : Type;
      A : forall R : Type, E R -> interaction (rand + state S) R;
      D : T -> interaction (rand + state S) bool;
      s : S;
    }.
    Definition run a p : ddist bool
      := ddist.interp (state.run_and_havoc (raw_adversary.run a.(A) a.(D) p) a.(s)).

    Definition advantage a l r DST : nat * nat := DST (Prc (run a l)) (Prc (run a r)).
  End adversary. Arguments adversary : clear implicits.
End adversary. Notation adversary := adversary.adversary.



(*
    def condition(self, testFunc):
        s = sum(self.prob(a)*testFunc(a) for a in self.support())
        return DDist({a:self.prob(a)/s for a in self.support() if testFunc(a)})

    def bayesianUpdate(self, PBgA, b):
        return makeJointDistribution(self, PBgA).condition(lambda x: x[1]==b).project(lambda x: x[0])

def makeJointDistribution(PA, PBgA):
    return DDist({ (a,b):PA.prob(a)*PBgA(a).prob(b) for a in PA.support() for b in PBgA(a).support()})

def totalProbability(PA, PBgA):
    return makeJointDistribution(PA,PBgA).project(lambda x: x[1])
*)

(*
Module dist.
  (* which probabiliy monad? *)
  (* nonempty_list T -- finite, trivial ok, custom eq*)
  (* T -> { R | 0 <= R <= 1} -- infinite, trivial ok, trivial eq assuming prop degeneracy *)
  (* { R | 0 <= R <= 1} -> T -- infinite, trivial ok, custom eq *)
  (* list T -- finite, custom ok, custom eq*)
  (* T -> Q  --- finite, custom ok, custom eq *)
  (* T -> R  --- infinite, custom ok, custom eq *)
  (* stream bool -> T -- infinite, trivial ok, custom eq *)
  (* (T -> nat) * nat -- finite, custom ok, custom eq*)
  
  Definition dist T : Type := list T.
  
  Definition ret {T} (x : T) : dist T := cons x nil.
  Definition bind {A B} (x : dist A) (f : A -> dist B) : dist B :=
    List.flat_map f x.
  Definition coin : dist bool := cons true (cons false nil).
End dist. Notation dist := dist.dist.

Inductive sample : Type -> Type :=
| rnd {A} (_ : dist A) : sample A.
*)

(* exmt adversary := itree (sample + adversary) *)
(* indist A : exmt A -> exmt A -> Prop *)

(*
Module expr. Section expr.
  Context {var : (* bool*) Type}.
  Inductive expr :=
  | ref (_ : var)
  | true
  | false
  | coin (_ : var -> expr)
  | neg (_ : expr) (_ : var -> expr)
  | eq (_ _ : expr) (_ : var -> expr).
End expr. End expr. Arguments expr.expr : clear implicits. Notation expr := expr.expr.

Fixpoint interp (e : expr bool) : dist bool :=
  match e with
  | expr.ref b => dist.ret b
  | expr.true => dist.ret true
  | expr.false => dist.ret false
  | expr.coin C => dist.bind dist.coin (fun b => interp (C b))
  | expr.neg e C => dist.bind (interp e) (fun b => dist.ret (negb b))
  | expr.eq e1 e2 C => dist.bind (interp e1) (fun b1 => dist.bind (interp e2) (fun b2 => dist.ret (Bool.eqb b1 b2)))
  end.

Eval cbv [interp] in interp (expr.coin (fun x => expr.eq (expr.ref x) (expr.ref x) (fun y => expr.ref y))).
*)
                   

(* CRHF:
H <- $;
x1, x2 <- interact H;
ret (if H(x1) == H(x2) then x1 == x2 else x1 != x2)

    ~

H <- $;
_, _ <- interact H;
ret true
 *)

(* (disproven) conjecture of random oracle instantiability using function families:

H <- $
x <- interact H;
y <- ret (H x);
interact y

    ~

H <- $
x <- interact H;
y <- $
interact y

counterexample: x = H, y == H(H)
first experiment computes H(H)
secnd experiment computes $

 *)

(* the same without higher-order functions: 

s <- $
x <- interact s;
y <- ret (H s x);
interact y

    ~

s <- $
x <- interact s;
y <- $
interact y

counterexample: x = s, y == H s s
first experiment computes H s s
secnd experiment computes $
*)