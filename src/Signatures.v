Require Import Minimalistic.
Require Import Coq.Numbers.BinNums.
Import BinPos.

Section Safety.
  Context {type : Set} {interp_type : type -> nat -> Set}
          {trand tmessage tkey : type} {tlist : type -> type}
          {tprod : type -> type -> type}
          {func : type -> type -> Set}
          {keygen : func trand tkey}
          {sign : func (tprod tmessage tkey) tmessage}. 
  Let expr :=
    @expr type interp_type trand tmessage tlist tprod func.

  Context {tmessage_eq : forall m1 m2 : expr tmessage, Prop}.

  Inductive signature_safe (sk : positive) :
    forall {t}, expr t -> (expr tmessage -> Prop) -> Prop :=
  | sconst : forall t eta,
      @signature_safe sk t (expr_const eta) (fun m => False)
  | srand_eq : signature_safe sk (expr_random sk) (fun m => True)
  | srand_neq :
      forall i, i <> sk ->
                signature_safe sk (expr_random i) (fun m => False)
  | sadv : forall e s, signature_safe sk e s ->
                       signature_safe sk (expr_adversarial e) s
  | ssign :
      forall m,
        signature_safe sk (expr_func sign (expr_pair m (expr_func keygen (expr_random sk)))) (fun m' => tmessage_eq m m')
  | sfunc : forall {t1 t2} (f : func t1 t2) e s,
      signature_safe sk e s ->
      signature_safe sk (expr_func f e) s
  | spair : forall {t1 t2} (e1: expr t1) (e2: expr t2) s1 s2,
      signature_safe sk e1 s1 ->
      signature_safe sk e2 s2 ->
      signature_safe sk (expr_pair e1 e2) (fun m => s1 m \/ s2 m)
  .

End Safety.