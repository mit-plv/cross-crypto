Set Universe Polymorphism.
Set Primitive Projections.
Unset Printing Primitive Projection Parameters.

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Omega.

Require Import FCF.EqDec.

Require Import CrossCrypto.NatUtil.
Require CrossCrypto.fmap.

Notation "x ?= y" := (eqb x y) (at level 70,
                                right associativity,
                                y at next level).

Ltac destruct_decider k comparison lemma a b :=
  let H := fresh in
  pose proof (lemma a b) as H; destruct (comparison a b);
  try k a;
  try k b;
  let Ht := type of H in
  try k Ht.

Ltac crush_deciders_in x :=
  lazymatch x with
  | context[(@eqb ?T ?E ?a ?b)] =>
    destruct_decider crush_deciders_in (@eqb T E) (@eqb_leibniz T E) a b
  | context[?a -? ?b] =>
    destruct_decider crush_deciders_in optsub optsub_plus a b
  | context[?a =? ?b] =>
    destruct_decider crush_deciders_in Nat.eqb Nat.eqb_eq a b
  | context[?a <=? ?b] =>
    destruct_decider crush_deciders_in Nat.leb Nat.leb_le a b
  | context[?a <? ?b] =>
    destruct_decider crush_deciders_in Nat.ltb Nat.ltb_lt a b
  end.

Ltac use_boolean_equalities :=
  repeat match goal with
         | H : true = true -> ?x |- _ => specialize (H eq_refl)
         | H : _ -> true = true |- _ => clear H
         | H : false = true -> _ |- _ => clear H
         | H : ?x -> false = true |- _ =>
           assert (~ x) by (let H' := fresh in
                            intro H'; specialize (H H');
                            congruence);
           clear H
         | H : _ = true <-> _ |- _ => destruct H
         end.

Ltac crush_deciders' t :=
  repeat (multimatch goal with
          | |- ?x => crush_deciders_in x
          | _ => use_boolean_equalities
          | _ => cbn [andb orb negb] in *
          | _ => intuition idtac
          | _ => congruence
          | _ => omega
          | _ => t
          end).

Tactic Notation "crush_deciders" tactic3(t) :=
  crush_deciders' t.


Section Language.
  Context {type : Set} {type_eqdec : EqDec type}
          {const : Set} {const_eqdec : EqDec const}

          {tunit tbool trand : type} {tprod : type -> type -> type}.
  Context {func : Set} {func_eqdec : EqDec func}.

  Bind Scope etype_scope with type.
  Delimit Scope etype_scope with etype.
  Local Notation "A * B" := (tprod A%etype B%etype) : etype_scope.
  Local Notation "A -> B" := (func A%etype B%etype) : etype_scope.

  (* De bruijn indices which can be paired together to get a tuple *)
  Inductive ref : Type :=
  | ref_index : nat -> ref
  | ref_pair : ref -> ref -> ref.

  Inductive op : Type :=
  | op_const : const -> op
  | op_rand : op
  | op_app : func -> ref -> op
  | op_input : type -> op
  | op_output : type -> ref -> op.

  Definition pgraph : Set := list op.

  Section Rewriter.
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

    Context (map_ops : CrossCrypto.fmap.operations nat nat).
    Local Notation map := (map_ops.(fmap.M)).
    Local Notation empty := (map_ops.(fmap.empty)).
    Local Notation add := (map_ops.(fmap.add)).
    Local Notation find := (map_ops.(fmap.find)).
    Local Notation fold_ac := (map_ops.(fmap.fold_ac)).

    Fixpoint renumber_ref (f : nat -> nat) (r : ref) : ref :=
      match r with
      | ref_index n => ref_index (f n)
      | ref_pair r1 r2 => ref_pair (renumber_ref f r1) (renumber_ref f r2)
      end.

    Definition renumber_op (f : nat -> nat) (o : op) : op :=
      match o with
      | op_app c r => op_app c (renumber_ref f r)
      | op_output t r => op_output t (renumber_ref f r)
      | _ => o
      end.

    Definition offset_renumbering (offset : nat)
               (f : nat -> nat) (n : nat) : nat :=
      match n -? offset with
      | Some k => offset + (f k)
      | None => n
      end.

    Definition update_maps (lem2prog prog2lem : map) (li pi : nat)
      : map * map + error :=
      match find li lem2prog with
      | Some pi' => if pi =? pi'
                    then ok (lem2prog, prog2lem)
                    else raise (E_msg "update_maps: lem2prog mismatch")
      | None =>
        let lem2prog := add li pi lem2prog in
        match find pi prog2lem with
        | Some li' =>
          if li =? li'
          then ok (lem2prog, prog2lem)
          else raise (E_msg "update_maps: prog2lem mismatch")
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
        update_maps lem2prog prog2lem (loff + ln) (poff + pn)
      | ref_pair lr1 lr2, ref_pair pr1 pr2 =>
        '(lem2prog, prog2lem) <-!
         update_maps_ref loff poff lem2prog prog2lem lr1 pr1;
          update_maps_ref loff poff lem2prog prog2lem lr2 pr2
      | _, _ => raise (E_msg "update_maps: ref mismatch")
      end.

    Definition update_maps_op
               (lop pop : op)
               (loff poff : nat) (lem2prog prog2lem : map)
      : map * map + error :=
      match lop, pop with
      | op_const lc, op_const pc =>
        if lc ?= pc
        then ok (lem2prog, prog2lem)
        else raise (E_msg "update_maps: op const mismatch")
      | op_rand, op_rand => ok (lem2prog, prog2lem)
      | op_app lc lr, op_app pc pr =>
        if lc ?= pc
        then update_maps_ref loff poff lem2prog prog2lem lr pr
        else raise (E_msg "map_match: op app mismatch")
      | op_input t, _ =>
        (* todo check type *)
        ok (lem2prog, prog2lem)
      | op_output _ _, _ => raise (E_msg "map_match: op_output")
      | _, _ => raise (E_msg "map_match: op mismatch")
      end.

    Fixpoint walk_tree
             (lemma program : pgraph)
             (loff poff : nat)
             (lem2prog : map)
             (prog2lem : map)
             {struct lemma} : map * map + error :=
      match lemma with
      | nil => ok (lem2prog, prog2lem)
      | l_op :: lemma =>
        match find loff lem2prog with
        | Some absolute_p_i =>
          match absolute_p_i -? poff with
          | Some relative_p_i =>
            match List.nth_error program relative_p_i with
            | Some p_op =>
              '(lem2prog, prog2lem) <-! update_maps_op l_op p_op (S loff) (S absolute_p_i) lem2prog prog2lem;
                walk_tree lemma program (S loff) poff lem2prog prog2lem
            | None => raise (E_msg "walk_tree: bad lem2prog entry")
            end
          | None => raise (E_msg "walk_tree: bad lem2prog entry")
          end
        | None => walk_tree lemma program (S loff) poff lem2prog prog2lem
        end
      end.

    Fixpoint match_output' (loff poff : nat)
             (output_ref : ref) (lemma program : pgraph)
             (acc : list (map * map))
      : list (map * map) :=
      match program with
      | nil => acc
      | _ :: program' =>
        let acc :=
            match
              (* TODO check output type *)
              '(lem2prog, prog2lem) <-!
               update_maps_ref loff 0 empty empty output_ref (ref_index poff);
               walk_tree lemma program loff poff lem2prog prog2lem with
            | ok new_maps => new_maps :: acc
            | raise _ => acc
            end in
        match_output' loff (S poff) output_ref lemma program' acc
      end.

    Definition match_output (loff : nat) (output_ref : ref)
               (lemma program : pgraph) : list (map * map) :=
      match_output' loff 0 output_ref lemma program nil.

    (* TODO check types when matching? *)
    Fixpoint find_outputs' (lemma : pgraph) (loff : nat)
             (acc : list (nat * ref * pgraph)) : list (nat * ref * pgraph) :=
      match lemma with
      | nil => acc
      | l_op :: lemma' =>
        find_outputs' lemma' (S loff)
                      match l_op with
                      | op_output _ r => (S loff, r, lemma') :: acc
                      | _ => acc
                      end
      end.

    Definition find_outputs (lemma : pgraph) : list (nat * ref * pgraph) :=
      find_outputs' lemma 0 nil.

    Definition walk_tree_all
               (lemma : pgraph)
               (program : pgraph) : list (list (map * map)) :=
      List.map (fun '(loff, output_ref, lemma) =>
                  match_output loff output_ref lemma program)
               (find_outputs lemma).

  End Rewriter.

End Language.

Require Import CrossCrypto.fmap.list_of_pairs.

Section Test.
  Inductive type :=
  | tnat : type
  | tbool : type
  | tunit : type
  | tprod : type -> type -> type.

  Fixpoint type_eqb (t1 t2 : type) : bool :=
    match t1, t2 with
    | tnat, tnat => true
    | tbool, tbool => true
    | tunit, tunit => true
    | tprod t1a t1b, tprod t2a t2b => (type_eqb t1a t2a) && (type_eqb t1b t2b)
    | _, _ => false
    end.
  Lemma type_eqb_eq t1 t2 : type_eqb t1 t2 = true <-> t1 = t2.
  Proof.
    revert t2; induction t1; intros []; cbn [type_eqb];
      crush_deciders rewrite ?andb_true_iff, ?IHt1_1, ?IHt1_2 in *.
  Qed.
  Local Instance type_eqdec : EqDec type := Build_EqDec type_eqb type_eqb_eq.

  Inductive const :=
  | cunit : const
  | cnat : nat -> const
  | cbool : bool -> const
  | cprod : const -> const -> const.

  Fixpoint const_eqb (c1 c2 : const) : bool :=
    match c1, c2 with
    | cunit, cunit => true
    | cnat n1, cnat n2 => n1 ?= n2
    | cbool b1, cbool b2 => b1 ?= b2
    | cprod c1a c1b, cprod c2a c2b => (const_eqb c1a c2a) && (const_eqb c1b c2b)
    | _, _ => false
    end.
  Lemma const_eqb_eq (c1 c2 : const) : const_eqb c1 c2 = true <-> c1 = c2.
  Proof.
    revert c2; induction c1; intros []; cbn [const_eqb];
      crush_deciders rewrite ?andb_true_iff, ?IHc1_1, ?IHc1_2 in *.
  Qed.
  Local Instance const_eqdec : EqDec const := Build_EqDec const_eqb const_eqb_eq.

  Inductive func :=
  | f_add
  | f_times
  | f_not
  | f_iszero.

  Definition func_eqb (f1 f2 : func) : bool :=
    match f1, f2 with
    | f_add, f_add => true
    | f_times, f_times => true
    | f_not, f_not => true
    | f_iszero, f_iszero => true
    | _, _ => false
    end.
  Lemma func_eqb_eq (f1 f2 : func) : func_eqb f1 f2 = true <-> f1 = f2.
  Proof. destruct f1, f2; cbn [func_eqb]; crush_deciders idtac. Qed.
  Local Instance func_eqdec : EqDec func := Build_EqDec func_eqb func_eqb_eq.

  Notation pgraph := (@pgraph type const func).

  Example ex_0_arith : pgraph :=
    ((op_output tnat (ref_index 1))
       :: (op_output tnat (ref_index 1))
       :: (op_app f_times (ref_pair (ref_index 2) (ref_index 1)))
       :: (op_app f_add (ref_pair (ref_index 1) (ref_index 0)))
       :: (op_input tnat)
       :: (op_input tnat) :: nil).

  Example ex_2_arithprog : pgraph :=
    ((op_output tnat (ref_index 0))
       :: (op_app f_add (ref_pair (ref_index 0) (ref_index 1)))
       :: (op_app f_add (ref_pair (ref_index 2) (ref_index 1)))
       :: (op_app f_times (ref_pair (ref_index 1) (ref_index 0)))
       :: (op_const (cnat 4))
       :: (op_const (cnat 3)) :: nil).

  Local Notation map := (list_of_pairs Nat.eqb).

  Eval cbv in find_outputs ex_0_arith.

  Eval cbv in walk_tree_all map ex_0_arith ex_2_arithprog.
  (* TODO:
   * Semantics
   * - interpretation under adversary
   * - definition of join
   * - proof of moving the input/output boundary
   *   (possibly "trivially" by permitting
        arbitrary adversary graph structure)
   *
   * Algorithm evaluation
   * - subgraph rewriter
   *)

  (* Rewriter strategy
   * similar to grw.  However we no longer have a single
   * base node, so this will take some additional work.
   * (Assume all nodes are reachable from the base?
   *  Seems unworkable even if we just want multiple returns.)
   * We can assume all nodes are reachable from some output.
   *
   * Strategy: guess the last output; match that; then guess the
   * next-to-last output, etc.
   *
   * Another question - what's the reordering strategy?  And how to verify it?
   * Thinking about verification requires having a definition of join,
   * as well as some sort of notion of isomorphism
   * - at least the theorem that isomorphism is preserved by the semantics
   *
   * Might be worth experimenting in a different language but we'll give
   * it a try.
   *)
