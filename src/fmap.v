Section Maps.
  Local Set Universe Polymorphism.
  Context {K V : Type}.

  Record operations :=
    {
      M : Type;
      
      empty : M;
      add : K -> V -> M -> M;
      find : K -> M -> option V;
      (* remove : K -> M V -> M V; *)

      fold_ac : forall S (f : K -> V -> S -> S), S -> M -> S;
    }.

  Section Spec.
    Context (Kper : K -> K -> Prop).
    Context (Vper : V -> V -> Prop).
    Context (M_operations : operations).
    Local Notation M := M_operations.(M).
    Local Notation empty := M_operations.(empty).
    Local Notation add := M_operations.(add).
    Local Notation find := M_operations.(find).
    Local Notation fold_ac := M_operations.(fold_ac).

    Record ok :=
      {
        per : M -> M -> Type;
        ok_empty : per empty empty;
        ok_add :
          forall (k1 k2:K) (_ : Kper k1 k2),
          forall (v1 v2:V) (_ : Vper v1 v2),
          forall (m1 m2 : M) (_ : per m1 m2),
            per (add k1 v1 m1) (add k2 v2 m2);
        ok_find :
            forall (k1 k2 : K) (_ : Kper k1 k2),
            forall (m1 m2 : M) (_ : per m1 m2),
              (* option_per *)
              match find k1 m1, find k2 m2 with
              | Some v1, Some v2 => Vper v1 v2
              | None, None => True
              | _, _ => False
              end;
        ok_fold_ac :
                forall S1 S2 (Sper : S1 -> S2 -> Type),
                forall f1 f2 (_ : forall k1 k2, Kper k1 k2 ->
                                        forall v1 v2, Vper v1 v2 ->
                                                  forall s1 s2, Sper s1 s2 ->
                                                                Sper (f1 k1 v1 s1) (f2 k2 v2 s2)),
                forall s1 s2 (_ : Sper s1 s2),
                forall m1 m2 (_ : per m1 m2),
                  Sper (fold_ac S1 f1 s1 m1) (fold_ac S2 f2 s2 m2);

        find_empty :
          forall k (_ : Kper k k),
            match find k empty with
            | Some _ => False
            | None => True
            end;
        find_add :
          forall kf (_ : Kper kf kf),
          forall ka (_ : Kper ka kf),
          forall va (_ : Vper va va),
          forall m (_ : per m m),
            (Kper kf ka -> match find kf (add ka va m) with
                           | Some vf => Vper vf va
                           | None => False
                           end) /\
            (~ Kper kf ka ->
             match find kf (add ka va m), find kf m with
             | Some vf1, Some vf2 => Vper vf1 vf2
             | None, None => True
             | _, _ => False
             end);

        (* TODO: specify fold_ac *)
      }.
  End Spec.
End Maps.

Global Arguments operations : clear implicits.