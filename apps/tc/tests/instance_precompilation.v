From elpi.apps Require Import tc.
Elpi Override TC TC.Solver All.
Set TC NameShortPath.

(*
  We deactivate TC.Compiler to
*)
Elpi TC Deactivate Observer TC.Compiler.

Elpi Accumulate TC.Solver lp:{{
  :after "0" msolve _ _ :- coq.say "Solving in elpi", fail.
}}.

Section numbers.
  Class number (i:nat).
  Elpi Accumulate tc.db lp:{{
    :index (50)
    pred tc-number o:term, o:term.
  }}.

  Instance zero : number O. Qed.
  Instance succ (N : nat): number N -> number (S N). Qed.

  (*
    We add the "raw" version of the two instances in the precompilation.instances predicate
  *)
  Elpi Accumulate tc.db lp:{{
    shorten precompilation.{instances, instance-clause, instance-lambda}.
    instances (instance-clause {{number O zero}} []).
    instances (instance-lambda (N\
                instance-lambda (Sol\
                  instance-clause {{number (S lp:N) (succ lp:N lp:Sol)}} [{{number lp:N lp:Sol}}]))).
  }}.
  Elpi Typecheck TC.precompile.

  (* The following command only shows the list of precompiled instances *)
  TC.precompile 2 number show.

  (* Here we accumulate the instances *)
  TC.precompile 4 number.

  Elpi Typecheck TC.Solver.
  Elpi Trace Browser.
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

  Class sameList10 (n0 n1 n2 n3 n4 : nat).
  Instance sameList10I (n0 n1 n2 n3 n4 : nat) :
    get n0 -> get n1 -> get n2 -> get n3 -> get n4 ->
    same n0 n1 -> same n0 n2 -> same n0 n3 -> same n0 n4 -> sameList10 n0 n1 n2 n3 n4. Qed.

  Elpi Accumulate tc.db lp:{{
    pred tc-is0 o:term, o:term.
    pred tc-get o:term, o:term.
    pred tc-same o:term, o:term, o:term.
    pred tc-sameList10 o:term, o:term, o:term, o:term, o:term, o:term.
  }}.
  (* Elpi TC.AddAllInstances. *)

  Elpi Accumulate tc.db lp:{{
    shorten precompilation.{instances, instance-clause, instance-lambda}.
    instances (instance-clause {{is0 0 is0I}} []).
    instances (instance-clause {{get 0 get_0}} []).
    instances (instance-clause {{get 1 get_1}} []).
    instances (instance-clause {{get 2 get_2}} []).
    instances (instance-clause {{get 3 get_3}} []).
    instances (instance-clause {{get 4 get_4}} []).
    instances (instance-clause {{get 5 get_5}} []).
    instances (instance-clause {{get 6 get_6}} []).
    instances (instance-clause {{get 7 get_7}} []).
    instances (instance-clause {{get 8 get_8}} []).
    instances (instance-clause {{get 9 get_9}} []).
    instances (instance-lambda (x\ instance-lambda y\
      instance-clause ({{same lp:x lp:x (sameI lp:x)}}) []
    )).
    instances (
      instance-lambda (x0\ instance-lambda (get0\
      instance-lambda (x1\ instance-lambda (get1\ (instance-lambda same1\
      instance-lambda (x2\ instance-lambda (get2\ (instance-lambda same2\
      instance-lambda (x3\ instance-lambda (get3\ (instance-lambda same3\
      instance-lambda (x4\ instance-lambda (get4\ (instance-lambda same4\
        instance-clause {{sameList10 lp:x0 lp:x1 lp:x2 lp:x3 lp:x4
          (sameList10I lp:x0 lp:x1 lp:x2 lp:x3 lp:x4
          lp:get0 lp:get1 lp:get2 lp:get3 lp:get4
          lp:same1 lp:same2 lp:same3 lp:same4)
        }}
        [
          {{get lp:x0 lp:get0}},
          {{get lp:x1 lp:get1}},
          {{get lp:x2 lp:get2}},
          {{get lp:x3 lp:get3}},
          {{get lp:x4 lp:get4}},
          {{same lp:x0 lp:x1 lp:same1}},
          {{same lp:x0 lp:x2 lp:same2}},
          {{same lp:x0 lp:x3 lp:same3}},
          {{same lp:x0 lp:x4 lp:same4}}
        ]
    ))))))))))))))).
  }}.
  Elpi Typecheck TC.precompile.

  Time TC.precompile 1 sameList10.

    Elpi Print TC.Solver.

  Goal exists (n0 n1 n2 n3 n4  : nat),
      sameList10 n0 n1 n2 n3 n4 .
  Proof.
    do 5 eexists.
    Succeed Time apply _.
    Elpi Override TC TC.Solver None.
    Time apply _.

  Qed.
