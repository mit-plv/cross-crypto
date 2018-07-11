Require Import Coq.Lists.List.

Module FromNil.
  Section WithElementType.
    Context {A : Type}.
    Definition nth_error_count l n : nat + A :=
      fold_right (fun a s => match s with
                             | inl n =>
                               match n with
                               | O => inr a
                               | S n => inl n
                               end
                             | inr a => inr a
                             end)
                 (inl n) l.
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
