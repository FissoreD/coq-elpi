From elpi Require Import tc.

Set TC NameShortPath.
Elpi Override TC TC.Solver All.

Class cl (T : Type).

Elpi TC Deactivate Observer TC.Compiler.
Instance inst1 : cl nat. Qed.
Instance inst2 (A : Type) : cl A -> cl (list A). Qed.

Elpi Accumulate TC.Solver lp:{{
  precompilation.instances (tc-cl {{nat}} {{inst1}} :- []).
  precompilation.instances (pi a s\ tc-cl {{list lp:a}} {{inst2 lp:a lp:s}} :- [tc-cl a s]).
  % precompilation.instances (tc-cl {{bool}} {{inst1}} :- []).

  pred findall-one-arg i:(B -> A), o:list A.
  findall-one-arg P L :-
    std.findall (P _) R,
    std.map R (x\r\ x = P r) L.
}}.
Elpi Typecheck TC.Solver.

Elpi Query TC.Solver lp:{{
  pi A B\
  precompilation.instances (pi a b\ D A B :- C A B).
}}.

Elpi Accumulate TC.Solver lp:{{
  pred normalize i:prop, o:prop.
  normalize (pi x\ X x) R :- !, normalize (X Fresh_) R.
  normalize ((_ :- _) as X) X :- !.
  normalize X (X :- []).

  pred get-head i:prop, o:prop.
  get-head A B :- normalize A (B :- _).

  pred same-head i:prop, i:prop.
  same-head A B :- get-head A A2, get-head B B2, A2 = B2.

  pred map-filter i:list A, i:(A -> B -> prop), o:list B.
  map-filter [] _ [] :- !.
  map-filter [X|XS] F [Y|YS] :- F X Y, map-filter XS F YS.
  map-filter [_|XS] F YS :- map-filter XS F YS.

  pred run i:int, i:prop, i:list prop, o:list prop.
  run Depth Goal Program ProgramFilter1 :-
    std.filter Program (same-head Goal) ProgramFilter,
    std.map ProgramFilter normalize Normalized, !,
    % coq.say "The initial goal is" Goal,
    map-filter Normalized (x\r\
      % coq.say "--------------------------------------------",
      sigma Head Hyps Hyps'\
      (Head :- Hyps) = x,
      compile-rule Depth Program Hyps Hyps',
      r = (Head :- Hyps')
      % coq.say "Found the result",
      % coq.say r
      ) ProgramFilter1.

  pred compile-rule i:int, i:list prop, i:list prop, o:list prop.
  compile-rule 0 _ R R :- !.
  compile-rule _ _ [] [] :- !.

  compile-rule Depth Program [Hyp|Hyps] Res :-
    Depth > 0, Depth1 is Depth - 1,
    compile-rule Depth Program Hyps R1,
    compile-rule.aux Depth1 Program Program Hyp R2,
    std.append R1 R2 Res.

  pred compile-rule.aux i:int, i:list prop, i:list prop, i:prop, o:list prop.
  compile-rule.aux Depth [C|_] Program Hyp GL :-
    normalize C C1, same-head Hyp C1, C1 = (_ :- Hyps'),
    compile-rule Depth Program Hyps' GL.
  compile-rule.aux Depth [_|TL] Program Hyp GL :-
    compile-rule.aux Depth TL Program Hyp GL.

  pred mainn o:list prop.
  mainn R :- !,
    A = (pi X Y\ tc-cl X Y),
    findall-one-arg precompilation.instances L, !,
    run 1 A L R.
}}.
Elpi Typecheck TC.Solver.

Elpi Query TC.Solver lp:{{
  sigma L L1 L2 L3 R'\
    std.findall (mainn _) L,
    std.map L (x\r\ x = mainn r) L1,
    std.flatten L1 L2,
    % std.map L2 (x\y\ abs-evars x y _) R',
    coq.say "\n\nResult:\n" L2
  .
}}.

Elpi Typecheck TC.Solver.

(* Elpi Trace Browser. *)
Elpi Query TC.Solver lp:{{
  sigma L G G1\
    std.findall (mainn _) L,
    std.map L (x\y\ mainn y = x) G,
    std.flatten G G1,
    coq.say G1.
}}.
