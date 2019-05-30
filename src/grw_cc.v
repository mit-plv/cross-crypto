Set Universe Polymorphism.
Set Primitive Projections.
Unset Printing Primitive Projection Parameters.

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Omega.

Require Import FCF.EqDec.

Import EqNotations.

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

  Section Semantics.
    Context {const_type : const -> type}
            {dom cod : func -> type}.
    Context {interp_type : type -> Set}
            {interp_type_inhabited : forall t, interp_type t}
            {interp_const : forall c, interp_type (const_type c)}
            {interp_func : forall f,
                interp_type (dom f) -> interp_type (cod f)}
            {mkprod : forall t1 t2,
                interp_type t1 -> interp_type t2 -> interp_type (tprod t1 t2)}.

    Arguments interp_type_inhabited {t}.
    Arguments mkprod {t1 t2}.

    Definition op_type o : type :=
      match o with
      | op_const c => const_type c
      | op_rand => trand
      | op_app f _ => cod f
      | op_input t => t
      | op_output t _ => tunit
      end.

    Definition prog_types : pgraph -> list type :=
      List.map op_type.

    Fixpoint ref_type (ctxt : list type) (r : ref) : option type :=
      match r with
      | ref_index n => List.nth_error ctxt n
      | ref_pair r1 r2 =>
        match ref_type ctxt r1 with
        | None => None
        | Some t1 =>
          match ref_type ctxt r2 with
          | None => None
          | Some t2 => Some (t1 * t2)%etype
          end
        end
      end.

    Definition check_op (ctxt : list type) (o : op) : bool :=
      match o with
      | op_app f r =>
        match ref_type ctxt r with
        | None => false
        | Some t => t ?= dom f
        end
      | op_output t' r =>
        match ref_type ctxt r with
        | None => false
        | Some t => t ?= t'
        end
      | _ => true
      end.

    Definition check_prog (p : pgraph) : bool :=
      match List.fold_right
              (fun o ctxt' =>
                 match ctxt' with
                 | None => None
                 | Some ctxt =>
                   if check_op ctxt o
                   then Some (op_type o :: ctxt)
                   else None
                 end) (Some nil) p with
      | None => false
      | Some _ => true
      end.

    Definition ctxt_type : list type -> Set :=
      List.fold_right (fun t (T : Set) => interp_type t * T)%type unit.

    Definition transport {t : type} (x : interp_type t) (u : type) :
      option (interp_type u) :=
      match EqDec_dec _ t u with
      | left e => Some (rew e in x)
      | right _ => None
      end.

    Definition recover {t : type} (o : option (interp_type t)) : interp_type t :=
      match o with
      | Some y => y
      | None => interp_type_inhabited
      end.

    Definition cast {t : type} (x : interp_type t) (u : type) : interp_type u := recover (transport x u).

    Fixpoint ctxt_nth {ctxt : list type} (ctx : ctxt_type ctxt) (n : nat) : option {t : type & interp_type t} :=
      match ctxt as ctxt' return (ctxt_type ctxt' -> _) with
      | nil => fun _ => None
      | cons _ ctxt =>
        fun '(x, ctx) =>
          match n with
          | 0 => Some (existT _ _ x)
          | S n => ctxt_nth ctx n
          end
      end ctx.

    Fixpoint ctxt_nth_trans {ctxt : list type} (ctx : ctxt_type ctxt) (n : nat) (t : type) {struct ctxt} : option (interp_type t) :=
      match ctxt as ctxt' return (ctxt_type ctxt' -> _) with
      | nil => fun _ => None
      | cons _ ctxt =>
        fun '(x, ctx) =>
          match n with
          | 0 => transport x t
          | S n => ctxt_nth_trans ctx n t
          end
      end ctx.

    Fixpoint interp_ref {ctxt : list type} (ctx : ctxt_type ctxt) (r : ref) : option {t & interp_type t} :=
      match r with
      | ref_index n => ctxt_nth ctx n
      | ref_pair r1 r2 =>
        match interp_ref ctx r1 with
        | None => None
        | Some (existT _ _ x1) =>
          match interp_ref ctx r2 with
          | None => None
          | Some (existT _ _ x2) => Some (existT _ _ (mkprod x1 x2))
          end
        end
      end.

    Definition interp_ref_cast {ctxt : list type} (ctx : ctxt_type ctxt) (r : ref) (t : type) : interp_type t :=
      recover match interp_ref ctx r with
              | Some (existT _ _ x) => transport x t
              | None => None
              end.

    Definition interp_op (rands : list (interp_type trand))
               (o : op) {ctxt : list type} (ctx : ctxt_type ctxt)
      : (interp_type (op_type o) * list (interp_type trand)) :=
      match o with
      | op_const c => (interp_const c, rands)
      | op_rand =>
        match rands with
        | nil => (interp_type_inhabited, nil)
        | cons r rands => (r, rands)
        end
      | op_app f r => (interp_func f (interp_ref_cast ctx r (dom f)), rands)
      | _ => (interp_type_inhabited, rands)
      end.

    (* Semantics of a well-formed graph
       (no inputs or outputs, all refs and types match up).
       You must pass in enough randomness (at least 1 for every op_rand).
     *)
    Fixpoint interpret (rands : list (interp_type trand))
             (p : pgraph) {struct p} : ctxt_type (prog_types p) * list (interp_type trand) :=
      match p with
      | nil => (tt, rands)
      | cons o p =>
        let '(ctx, rands) := interpret rands p in
        let '(x, rands) := interp_op rands o ctx in
        ((x, ctx), rands)
      end.
  End Semantics.

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

    Context (map_bool_ops : CrossCrypto.fmap.operations nat bool).
    Local Notation map_b := (map_bool_ops.(fmap.M)).
    Local Notation empty_b := (map_bool_ops.(fmap.empty)).
    Local Notation add_b := (map_bool_ops.(fmap.add)).
    Local Notation find_b := (map_bool_ops.(fmap.find)).
    Local Notation fold_ac_b := (map_bool_ops.(fmap.fold_ac)).

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

    Definition map_add_safe (k v : nat) (m : map) : map + error :=
      match find k m with
      | Some v' => if v =? v'
                   then ok m
                   else raise (E_msg "map_add_safe: mismatch")
      | None => ok (add k v m)
      end.

    Definition update_maps (lem2prog prog2lem : map) (li pi : nat)
      : map * map + error :=
      lem2prog' <-! map_add_safe li pi lem2prog;
        prog2lem' <-! map_add_safe pi li prog2lem;
        ok (lem2prog', prog2lem').

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

    Fixpoint filter_errors {t} (l : list (t + error)) : list t :=
      match l with
      | nil => nil
      | cons (ok x) l' => cons x (filter_errors l')
      | cons (raise _) l' => filter_errors l'
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

    Definition unify_map (m1 m2 : map) : map + error :=
      fold_ac _ (fun k v me =>
                   m <-! me;
                     map_add_safe k v m) (inl m1) m2.

    Definition unify_both (lp : (map * map) * (map * map)) : map * map + error :=
      let '((lem2prog1, prog2lem1), (lem2prog2, prog2lem2)) := lp in
      lem2prog <-! unify_map lem2prog1 lem2prog2;
        prog2lem <-! unify_map prog2lem1 prog2lem2;
        ok (lem2prog, prog2lem).

    Definition compatible_maps (l : list (list (map * map))) : list (map * map) :=
      List.fold_left
        (fun l1 l2 =>
           filter_errors (List.map unify_both (List.list_prod l1 l2)))
        l (cons (empty, empty) nil).

    Definition find_err x (m : map) :=
      match find x m with
      | None => raise (E_msg "find_err: not present")
      | Some y => ok y
      end.
    Definition find_b_err x (m : map_b) :=
      match find_b x m with
      | None => raise (E_msg "find_err: not present")
      | Some y => ok y
      end.

    Fixpoint check_ordering' (lem2prog : map) (lemma : pgraph) (i highestI highestO : nat) : unit + error :=
      match lemma with
      | nil => ok tt
      | o :: lemma =>
        '(highestI, highestO) <-!
         match o with
         | op_input _ => j <-! find_err i lem2prog;
                           if j <? highestO
                           then raise (E_msg "check_ordering: disorder")
                           else ok (max j highestI, highestO)
         | op_output _ _ => j <-! find_err i lem2prog;
                              if j <? highestI
                              then raise (E_msg "check_ordering: disorder")
                              else ok (highestI, max j highestO)
         | _ => ok (highestI, highestO)
         end;
          check_ordering' lem2prog lemma (S i) highestI highestO
      end.

    Definition check_ordering (lem2prog : map) (lemma : pgraph) : unit + error :=
      check_ordering' lem2prog lemma 0 0 0.

    Fixpoint find_pure_ops' (rlemma : list op)
             (loff : nat) (l2pure : map_b) {struct rlemma} : map_b + error :=
      match rlemma with
      | nil => ok l2pure
      | l_op :: rlemma =>
        pure <-!
             match l_op with
             | op_const _
             | op_input _ => ok true
             | op_rand => ok false
             | op_app _ r
             | op_output _ r =>
               (fix ref_pure r :=
                  match r with
                  | ref_index n => find_b_err (n + loff) l2pure
                  | ref_pair r1 r2 =>
                    s1 <-! ref_pure r1;
                      s2 <-! ref_pure r2;
                      ok (s1 && s2)
                  end) r
             end;
          let loff := Nat.pred loff in
          find_pure_ops' rlemma loff (add_b loff pure l2pure)
      end.

    Definition find_pure_ops (lemma : pgraph) : map_b + error :=
      find_pure_ops' (List.rev lemma) (List.length lemma) empty_b.

    Fixpoint check_leaks_are_pure' (prog : pgraph) (poff : nat)
             (prog2lem : map) (l2pure : map_b) : unit + error :=
      match prog with
      | nil => ok tt
      | p_op :: prog =>
        _ <-! match find poff prog2lem with
              | Some _ => ok tt
              | _ =>
                match p_op with
                | op_app _ r
                | op_output _ r =>
                  (fix check_ref r :=
                     match r with
                     | ref_index n =>
                       match find (n + S poff) prog2lem with
                       | Some loff =>
                         pure <-! find_b_err loff l2pure;
                           if pure
                           then ok tt
                           else raise (E_msg "unpure leak")
                       | None => ok tt
                       end
                     | ref_pair r1 r2 =>
                       _ <-! check_ref r1; check_ref r2
                     end) r
                | _ => ok tt
                end
              end;
          check_leaks_are_pure' prog (S poff) prog2lem l2pure
      end.

    Definition check_leaks_are_pure (prog : pgraph)
               (prog2lem : map) (l2pure : map_b) : unit + error :=
      check_leaks_are_pure' prog 0 prog2lem l2pure.

  End Rewriter.

End Language.

Require Import CrossCrypto.fmap.list_of_pairs.

Section Test.
  Inductive type :=
  | tnat : type
  | tbool : type
  | tunit : type
  | tsig : type
  | tpkey : type
  | tkey : type
  | tmsg : type
  | tmac : type
  | t_A : type
  | tprod : type -> type -> type.

  Fixpoint type_eqb (t1 t2 : type) : bool :=
    match t1, t2 with
    | tnat, tnat => true
    | tbool, tbool => true
    | tunit, tunit => true
    | tsig, tsig => true
    | tpkey, tpkey => true
    | tkey, tkey => true
    | tmsg, tmsg => true
    | tmac, tmac => true
    | t_A, t_A => true
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
  | czero_msg : const
  | czero_sig : const
  | czero_pkey : const
  | cprod : const -> const -> const.

  Fixpoint const_eqb (c1 c2 : const) : bool :=
    match c1, c2 with
    | cunit, cunit => true
    | cnat n1, cnat n2 => n1 ?= n2
    | cbool b1, cbool b2 => b1 ?= b2
    | czero_msg, czero_msg => true
    | czero_sig, czero_sig => true
    | czero_pkey, czero_pkey => true
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
  | f_iszero
  | f_eq
  | f_impl
  | f_ite
  | f_id
  | ekeygen
  | mkeygen
  | skeygen
  | pkeygen
  | encode_tskey
  | decode_tskey
  | encrypt
  | decrypt
  | mac
  | mverify
  | sign
  | sverify.

  Definition func_eqb (f1 f2 : func) : bool :=
    match f1, f2 with
    | f_add, f_add => true
    | f_times, f_times => true
    | f_not, f_not => true
    | f_iszero, f_iszero => true
    | f_eq, f_eq => true
    | f_impl, f_impl => true
    | f_ite, f_ite => true
    | f_id, f_id => true
    | ekeygen, ekeygen => true
    | mkeygen, mkeygen => true
    | skeygen, skeygen => true
    | pkeygen, pkeygen => true
    | encode_tskey, encode_tskey => true
    | decode_tskey, decode_tskey => true
    | encrypt, encrypt => true
    | decrypt, decrypt => true
    | mac, mac => true
    | mverify, mverify => true
    | sign, sign => true
    | sverify, sverify => true
    | _, _ => false
    end.
  Lemma func_eqb_eq (f1 f2 : func) : func_eqb f1 f2 = true <-> f1 = f2.
  Proof. destruct f1, f2; cbn [func_eqb]; crush_deciders idtac. Qed.
  Local Instance func_eqdec : EqDec func := Build_EqDec func_eqb func_eqb_eq.

  Notation pgraph := (@pgraph type const func).

  Example ex_0_arith_lhs : pgraph :=
    ((op_output tnat (ref_index 1))
       :: (op_output tnat (ref_index 1))
       :: (op_app f_times (ref_pair (ref_index 2) (ref_index 1)))
       :: (op_app f_add (ref_pair (ref_index 1) (ref_index 0)))
       :: (op_input tnat)
       :: (op_input tnat) :: nil).

  Example ex_0_arith_prog : pgraph :=
    ((op_output tnat (ref_index 0))
       :: (op_app f_add (ref_pair (ref_index 0) (ref_index 1)))
       :: (op_app f_add (ref_pair (ref_index 2) (ref_index 1)))
       :: (op_app f_times (ref_pair (ref_index 1) (ref_index 0)))
       :: (op_const (cnat 4))
       :: (op_const (cnat 3)) :: nil).

  Local Notation map := (list_of_pairs Nat.eqb).

  Eval cbv in find_outputs ex_0_arith_lhs.

  Eval cbv in walk_tree_all map ex_0_arith_lhs ex_0_arith_prog.

  Time Eval cbv in (compatible_maps map (walk_tree_all map ex_0_arith_lhs ex_0_arith_prog)).

  Example ex_1_authconf_prog N : pgraph :=
    ((op_output tbool (ref_index 0))
       :: (op_app f_impl (ref_pair (ref_index 1) (ref_index 0)))
       :: (op_app f_eq (ref_pair (ref_index 2) (ref_index 18)))
       :: (op_app sverify (ref_pair (ref_index 26) (ref_pair (ref_index 1) (ref_index 0))))
       :: (op_input tsig)
       :: (op_input tmsg)
       :: (op_output tmsg (ref_index 0))
       :: (op_app f_ite (ref_pair (ref_index 11) (ref_pair (ref_index 13) (ref_index 0))))
       :: (op_const czero_msg)
       :: (op_output tsig (ref_index 0))
       :: (op_app f_ite (ref_pair (ref_index 8) (ref_pair (ref_index 5) (ref_index 0))))
       :: (op_const czero_sig)
       :: (op_output tpkey (ref_index 0))
       :: (op_app f_ite (ref_pair (ref_index 5) (ref_pair (ref_index 1) (ref_index 0))))
       :: (op_const czero_pkey)
       :: (op_app pkeygen (ref_index 1))
       :: (op_app sign (ref_pair (ref_index 0) (ref_index 4)))
       :: (op_app decode_tskey (ref_index 0))
       :: (op_app decrypt (ref_pair (ref_index 15) (ref_index 4)))
       :: (op_app mverify (ref_pair (ref_index 0) (ref_pair (ref_index 3) (ref_index 2))))
       :: (op_app f_id (ref_index 12))
       :: (op_input tmsg)
       :: (op_input tmac)
       :: (op_input tmsg)
       :: (op_output tmac (ref_index 2))
       :: (op_output tmsg (ref_index 2))
       :: (op_output tkey (ref_index 3))
       :: (op_app mac (ref_pair (ref_index 5) (ref_index 0)))
       :: (op_app encrypt (ref_pair (ref_index 5) (ref_pair (ref_index 0) (ref_index 2))))
       :: (op_const (cnat N))
       :: (op_app pkeygen (ref_index 1))
       :: (op_app encode_tskey (ref_index 0))
       :: (op_app skeygen (ref_index 2))
       :: (op_app mkeygen (ref_index 2))
       :: (op_app ekeygen (ref_index 2))
       :: op_rand
       :: op_rand
       :: op_rand :: nil).

  Example ex_1_authconf_lhs : pgraph :=
    ((op_output t_A (ref_index 0))
       :: (op_app f_ite (ref_pair (ref_index 2) (ref_pair (ref_index 1) (ref_index 0))))
       :: (op_input t_A)
       :: (op_input t_A)
       :: (op_app mverify (ref_pair (ref_index 5) (ref_pair (ref_index 1) (ref_index 0))))
       :: (op_input tmac)
       :: (op_input tmsg)
       :: (op_output tmac (ref_index 0))
       :: (op_app mac (ref_pair (ref_index 2) (ref_index 0)))
       :: (op_input tmsg)
       :: (op_app f_id (ref_index 0))
       :: (op_app mkeygen (ref_index 0))
       :: op_rand :: nil).

  Eval cbv in walk_tree_all map ex_1_authconf_lhs (ex_1_authconf_prog 5).

  Eval cbv in compatible_maps map (walk_tree_all map ex_1_authconf_lhs (ex_1_authconf_prog 5)).

End Test.

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
