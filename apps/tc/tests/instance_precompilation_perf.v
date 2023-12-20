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

Section failFast.

  Class get (N : nat).
  (* Instance get_0 : get 0 | 10. Qed. *)
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
  Instance sameI (A B C D E F G H I J K L M N O P Q R S T U V Z : nat)
  : get 0 -> same A A. Qed.


  Elpi TC.AddAllClasses.

  Elpi TC.AddRawInstances get same.

  Time TC.precompile 2 same show.

  xxx.

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
End arrowInPremise.