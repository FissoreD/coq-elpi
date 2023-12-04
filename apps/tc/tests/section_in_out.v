From elpi.apps Require Import tc.
From elpi.apps.tc Extra Dependency "base.elpi" as base.

Set TC NameShortPath.

(*
  Test to verify that at each section exit, global instances are kept and
  evenutally recompiled (if any local variable is used) and local instances are
  dropped.
*)

(* Command to test that the elpi database has the same instances of coq one *)
Elpi Command len_test.
Elpi Accumulate Db tc.db.
Elpi Accumulate File base.
Elpi Accumulate lp:{{
  pred has-one-implementation i:tc-instance.
  has-one-implementation (tc-instance InstGR _) :-
    std.findall (instance _ InstGR _) L,
    std.assert! (std.length L 1) "Instance has duplications or is absent".

  % contains the number of instances that are not
  % imported from other files
  main [] :-
    coq.TC.db CoqInsts,
    std.findall (instance _ _ _) ElpiInsts,
    std.forall CoqInsts has-one-implementation,
    std.length CoqInsts Len,
    std.assert! (std.length ElpiInsts Len)
      "The number of coq instance is not equal to the number of elpi instances".
}}.
Elpi Typecheck.

Class Eqb A:= eqb: A -> A -> bool.

Global Instance eqA : Eqb unit := { eqb x y := true }.

Elpi len_test.

Section A.
  Context (A : Type).
  Global Instance eqB : Eqb bool := { eqb x y := if x then y else negb y }.
  Elpi len_test.

  Global Instance eqC : Eqb A := {eqb _ _ := true}.
  Elpi len_test.

  Section B.
    Context (B : Type).
    Global Instance eqD : Eqb B := {eqb _ _ := true}.
    Elpi len_test.
  End B.

  Elpi len_test.

End A.

Elpi len_test.

Section ClassPersistence.
  Section S1.
    Context (X : Type) (A : X).
    Class class (A : X).
    Global Instance x : class A. Qed.
    Elpi TC.AddInstances x.
    Goal exists x, class x. eexists. apply _. Qed.
    Elpi len_test.
  End S1.
  Elpi len_test.
  Elpi TC.Get_class_info class.
  Elpi Accumulate TC.Solver lp:{{
    tc-class A B {{x lp:A lp:B}}.
  }}.
  (* Here the accumulate should not give typecheck issue, since
    predicates for classes are global *)
  Elpi Typecheck TC.Solver.
End ClassPersistence.