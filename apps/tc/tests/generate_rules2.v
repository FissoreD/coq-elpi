From elpi Require Import tc.

Set TC NameShortPath.
Elpi Override TC TC.Solver All.

Class cl (T : Type).

Elpi TC Deactivate Observer TC.Compiler.
Instance inst1 : cl nat. Qed.
Instance inst2 (A : Type) : cl A -> cl (list A). Qed.

Elpi Accumulate TC.Solver lp:{{

  kind clause type.
  type clause term -> list term -> clause.
  type all (term -> clause) -> clause.

  pred run i:int, i:list clause, i:list term, o:list term.
  run _ _ [] [].
  run 0 P_ GL GL.
  run N P [G|GS] GL :- N > 0, M is N - 1, run.aux M P P G GL1, run M P GS GL2, std.append GL1 GL2 GL.
  run.aux N [C|_] P G GL :- print "try=" C, backchain N C P G GL.
  run.aux N [_|CL] P G GL :- run.aux N CL P G GL.

  pred backchain i:int, i:clause,i:list clause, o:term, o:list term.
  backchain N (all C) P G GL :- backchain N (C FRESH_) P G GL.
  backchain N (clause HD HYPS) P G GL :-
    G = HD,
    print "success, subgoals=" HYPS,
    run N P HYPS GL.

  pred main1 o:term.
  main1 Clause :-
    run 3 [
      clause ({{cl O}}) [],
      all (x\ clause {{cl (S lp:x)}} [{{cl lp:x}}])
    ] [{{cl lp:X}}] Goals,
    Clause = (app[{{cl lp:X}} | Goals ]).
}}.
Elpi Typecheck TC.Solver.

Elpi Accumulate TC.Solver lp:{{

  % we add a new constructor to terms to represent terms to be abstracted
  type abs int -> term.

  % bind back abstracted subterms
  pred bind i:int, i:int, i:term, o:clause.
  bind I M T T1 :- M > I, !,
    T1 = all B,
    N is I + 1,
    pi x\                           % we allocate the fresh symbol for (abs M)
      (copy (abs N) x :- !) =>      % we schedule the replacement (abs M) -> x
      bind N M T (B x).
  bind M M T T1 :- copy T T1', T1 = clause T1' [].         % we perform all the replacements

  % for a term with M holes, returns a term with M variables to fill these holes
  % the clause see is only generated for a term if it hasn't been seen before
  % the term might need to be typechecked first or main generates extra holes for the
  % type of the parameters
  pred abs-evars i:term, o:clause, o:int.
  abs-evars T1 T3 M :- std.do! [
    % we put (abs N) in place of each occurrence of the same hole
    (pi T Ty N N' M \ fold-map T N (abs M) M :- var T, not (seen? T _), !, M is N + 1, seen! T M) =>
    (pi T N M \ fold-map T N (abs M) N :- var T, seen? T M, !) =>
      fold-map T1 0 T2 M,
    % we abstract M holes (M abs nodes)
    bind 0 M T2 T3,
    % cleanup constraint store
    purge-seen!,
  ].

  % all constraints are also on _ so that they share
  % a variable with the constraint to purge the store

  % we query if the hole was seen before, and if so
  % we fetch its number
  pred seen? i:term, o:int.
  seen? X Y :- declare_constraint (seen? X Y) [X,_].

  % we declare it is now seen and label it with a number
  pred seen! i:term, i:int.
  seen! X Y :- declare_constraint (seen! X Y) [X,_].

  % to empty the store
  pred purge-seen!.
  purge-seen! :- declare_constraint purge-seen! [_].

  constraint seen? seen! purge-seen!  {
    % a succesful query, give the label back via M
    rule (seen! X N) \ (seen? X M) <=> (M = N).
    % an unsuccesful query
    rule             \ (seen? X _) <=> false.

    rule purge-seen! \ (seen! _ _).
    rule \ purge-seen!.
  }

}}.
Elpi Typecheck TC.Solver.

Elpi Query TC.Solver lp:{{
  sigma C L L1\
   std.findall (main1 C) L, print L,
   std.map L (x\r\ main1 r = x) L1,
   std.map L1 (x\r\ abs-evars x r _) L2.
   coq.say L1.
}}.