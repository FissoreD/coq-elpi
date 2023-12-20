From elpi.apps Require Import tc.
Elpi Override TC TC.Solver All.
Set TC NameShortPath.

(*
  We deactivate TC.Compiler to add the instances after precompilation
*)
Elpi TC Deactivate Observer TC.Compiler.

Elpi Accumulate TC.Solver lp:{{
  :after "0" msolve _ _ :- coq.say "Solving in elpi", fail.
}}.

(* Elpi Accumulate TC.precompile lp:{{
  :after "to-debug-instance-creation"
  to-debug-instance-creation.
}}. *)

(* Section compile1.
  Class A (i: nat).
  Instance i : A 0 -> A 1. Qed.

  Elpi TC.AddAllClasses.
  Elpi TC.AddRawInstances A.
  Elpi TC.precompile 5 A show.
End compile1. *)

Section A.

  Class B (i:nat).
  Class C (i: nat).
  Class D (i: nat).

  Instance i1 (x : nat) : B x -> C x. Qed.
  Instance i2 : B 0. Qed.
  Instance i3 : B 1. Qed.
  Instance i4 : D 0. Qed.

  Elpi TC.AddAllClasses.
  Elpi TC.AddRawInstances B C.

  Elpi Query TC.precompile lp:{{
    precompile-class 5 {{:gref C}} R,
    % TODO: the right number should be 3 : we have to remove tc-C c0 c1 :- tc-C c0 c1
    std.assert! (std.length R 4) "Invalid number of generated clauses".
  }}.
  Elpi TC.precompile 5 C show.
End A.

XX.
(* Section numbers.
  Class number (i:nat).
  Elpi Accumulate tc.db lp:{{
    :index (50)
    pred tc-number o:term, o:term.
  }}.

  (* Instance zero : number O. Qed. *)
  Instance succ (N : nat): number N -> number (S N). Qed.

  (* Elpi TC.AddRawInstances zero. *)
  Elpi TC.AddRawInstances succ.

  Elpi TC.precompile 2 number show.
  Elpi TC.precompile 5 number.

  Goal number 3. apply _. Qed.
End numbers.

Section failFast.
  Class is0 (N : nat).
  Instance is0I : is0 0. Qed.

  Class get (N : nat).
  Instance get_0 : get 0 | 10. Qed.
  Instance get_1 : get 1. Qed.
  Instance get_2 : get 2. Qed.
  Instance get_3 : get 3. Qed.
  Instance get_4 : get 4. Qed.
  Instance get_5 : get 5. Qed.
  Instance get_6 : get 6. Qed.
  Instance get_7 : get 7. Qed.
  Instance get_8 : get 8. Qed.
  Instance get_9 : get 9. Qed.

  Class same (n0 n1 : nat).
  Instance sameI (A : nat): same A A. Qed.

  Class sameList10 (n0 n1 n2 n3 : nat).
  Instance sameList10I (n0 n1 n2 n3 : nat) :
    get n0 -> get n1 -> get n2 -> get n3 ->
    same n0 n1 -> same n0 n2 -> same n0 n3 -> is0 n0 -> sameList10 n0 n1 n2 n3. Qed.

  Elpi Accumulate tc.db lp:{{
    pred tc-is0 o:term, o:term.
    pred tc-get o:term, o:term.
    pred tc-same o:term, o:term, o:term.
    pred tc-sameList10 o:term, o:term, o:term, o:term, o:term, o:term.
  }}.

  Elpi TC.AddRawInstances get is0 sameList10 same.

  Time TC.precompile 1 sameList10.

  Goal exists (n0 n1 n2 n3  : nat),
      sameList10 n0 n1 n2 n3 .
  Proof.
    do 4 eexists.
    Succeed Time apply _.
    Elpi Override TC TC.Solver None.
    Time apply _.
  Qed.
End failFast.

Section arrowInPremise.
  (* Reset numbers. *)
  Class class1 (i: nat).
  Class class2 (i: nat).
  Class class3 (i: nat).

  Elpi TC.AddClasses class1 class2 class3.
  
  Instance a : class1 0 -> (forall A, class1 A -> class2 A) -> class3 0. Qed.
  Instance b : forall A, class1 A -> class2 A. Qed.

  Elpi TC.AddRawInstances class1 class2 class3.
  Elpi TC.precompile 2 class3 show. 

  Goal class3 0.
    apply _.
  Qed.
End arrowInPremise. *)