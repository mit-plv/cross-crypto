Require Import Minimalistic.
Require Import Coq.Numbers.BinNums.
Import BinPos.

Section Safety.
  Context {type : Set} {interp_type : type -> nat -> Set}
          {trand tmessage tsignature tskey tpkey tbool : type}
          {tprod : type -> type -> type}
          {func : type -> type -> Set}.
  Context {skeygen : func trand tskey} (* secret key generation (from randomness) *)
          {pkeygen : func tskey tpkey}  (* public key generation (from secret key) *)
          {sign : func (tprod tmessage tskey) tsignature}.
  Let expr :=
    @expr type interp_type trand tmessage tprod func.

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
            tbool trand tmessage tprod func
            cast_rand interp_func interp_pair.


  (* todo move all this into Minimalistic *)

  (* todo make this a fold-right *)
  Definition expr_in {t : type} (x : expr t) (S : list (expr t)) : expr tbool.
  Admitted.

  Context {tand : func (tprod tbool tbool) tbool}.
  Definition signature_safe_conclusion (sk : positive) {t} (m : expr tmessage) (s : expr tsignature) S
    (verify : func (tprod tpkey (tprod tmessage tsignature)) tbool) :=
    signature_safe sk s S ->
    (* It's okay if the key was leaked at the time we got the message,
       just not the signature; hence no "signature_safe" for m. *)
    let ve := (expr_func verify (expr_pair (expr_func pkeygen (expr_func skeygen (expr_random sk)))
                                           (expr_pair m s))) in
    eqwhp ve
          (expr_func tand (expr_pair ve
                                     (expr_in m S))).

End Safety.