Require Import Minimalistic.
Require Import Coq.Numbers.BinNums.
Import BinPos.

Section Safety.
  Context {type : Set} {interp_type : type -> nat -> Set}
          {trand tmessage tskey tpkey tbool : type} {tlist : type -> type}
          {tprod : type -> type -> type}
          {func : type -> type -> Set}.
  Context {skeygen : func trand tskey} (* secret key generation (from randomness) *)
          {pkeygen : func tskey tpkey}  (* public key generation (from secret key) *)
          {sign : func (tprod tmessage tskey) tmessage}.
  Let expr :=
    @expr type interp_type trand tmessage tlist tprod func.

  Inductive signature_safe (sk : positive) :
    forall {t}, expr t -> list (expr tmessage) -> Prop :=
  | sconst : forall t eta,
      @signature_safe sk t (expr_const eta) nil
  | srand_neq :
      forall i, i <> sk ->
                signature_safe sk (expr_random i) nil
  | sadv : forall e s, signature_safe sk e s ->
                       signature_safe sk (expr_adversarial e) s
  | spkeygen :
        signature_safe sk
                       (expr_func pkeygen (expr_func skeygen (expr_random sk)))
                       nil
  | ssign :
      forall m s,
        signature_safe sk m s -> 
        signature_safe sk
                       (expr_func sign
                                  (expr_pair m (expr_func skeygen (expr_random sk))))
                       (m :: s)
  | sfunc : forall {t1 t2} (f : func t1 t2) e s,
      signature_safe sk e s ->
      signature_safe sk (expr_func f e) s
  | spair : forall {t1 t2} (e1: expr t1) (e2: expr t2) s1 s2,
      signature_safe sk e1 s1 ->
      signature_safe sk e2 s2 ->
      signature_safe sk (expr_pair e1 e2) (s1 ++ s2)
  .

  Context {eq_dec : EqDec.EqDec type}
          {eq_dec_interp_type : forall (t : type) (eta : nat),
              EqDec.EqDec (interp_type t eta)}.
  Context {cast_rand : forall eta : nat,
              Bvector.Bvector eta ->
              interp_type trand eta}
          {interp_func : forall t1 t2 : type,
              func t1 t2 ->
              forall eta : nat,
                interp_type t1 eta ->
                interp_type t2 eta}
          {interp_pair : forall (t1 t2 : type) (eta : nat),
              interp_type t1 eta ->
              interp_type t2 eta ->
              interp_type (tprod t1 t2) eta}
          {interp_expr : forall t eta, expr t -> interp_type t eta}.
  Let indist :=
    @indist type eq_dec interp_type eq_dec_interp_type
            tbool trand tmessage tlist tprod func
            cast_rand interp_func interp_pair.

  Context {tcons : forall t, func (tprod (tlist t) t) (tlist t) }.
  Context {tnil : forall t, expr (tlist t) }.
  Fixpoint adv_knowledge msgs : expr (tlist tmessage) :=
    match msgs with
    | nil => tnil _
    | cons m msgs' =>
      expr_func (tcons _)
                (expr_pair (adv_knowledge msgs') m)
    end.

  Context {tand : func (tprod tbool tbool) tbool}.
  Context {tin : forall t, func (tprod (tlist t) t) tbool}.
  Lemma signature_safe_conclusion (sk : positive) {t} (e : expr t) S
    (verify : func tmessage tbool) :
    signature_safe sk e S ->
    forall (adv : expr (tlist tmessage) -> expr tmessage),
      let x := adv (adv_knowledge S) in
      indist tbool
             (expr_func verify x)
             (expr_func tand
                        (expr_pair
                           (expr_func verify x)
                           (expr_func (tin _) (expr_pair (adv_knowledge S) x)))).
  Proof.
  Admitted.

End Safety.