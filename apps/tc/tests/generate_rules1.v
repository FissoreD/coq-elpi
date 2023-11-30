From elpi Require Import tc.

Set TC NameShortPath.
Elpi Override TC TC.Solver All.
Elpi Command compiler.

Section T.
  Class cl (T : Type).

  Elpi TC Deactivate Observer TC.Compiler.
  Instance inst1 : cl nat. Qed.
  Instance inst2 (A : Type) : cl A -> cl (A * A). Qed.

  Elpi Accumulate TC.Solver lp:{{
    precompilation.instances (pi a s\ tc-cl {{prod lp:a lp:a}} {{inst2 lp:a lp:s}} :- [tc-cl a s]).
    precompilation.instances (tc-cl {{nat}} {{inst1}} :- []).
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
    get-head (A :- _) A.

    pred get-hyps i:prop, o:list prop.
    get-hyps (_ :- Hyps) Hyps.

    % [same-head P HD] P is a clause and HD is a HD without pi
    pred same-head i:prop, i:prop.
    same-head A B :- normalize A A1, normalize B B1, get-head A1 A2, get-head B1 B2, A2 = B2.

    pred run i:int, i:prop, i:list prop, o:list prop.
    run Depth Goal Program ProgramFilter1 :-
      std.filter Program (same-head Goal) ProgramFilter,
      std.map ProgramFilter normalize Normalized,
      std.map-filter Normalized (x\r\
        sigma Head Hyps\
        (Head :- Hyps) = x,
        compile-rule Depth Program Hyps Hyps',
        r = (Head :- Hyps')) ProgramFilter1.

    pred compile-rule i:int, i:list prop, i:list prop, o:list prop.
    compile-rule 0 _ R R.
    compile-rule _ _ [] [].

    compile-rule Depth Program [Hyp|Hyps] Res :-
      Depth > 0, Depth1 is Depth - 1,
      compile-rule Depth Program Hyps R1,
      compile-rule.aux Depth1 Program Program Hyp R2,
      std.append R1 R2 Res.

    pred compile-rule.aux i:int, i:list prop, i:list prop, i:prop, o:list prop.
    compile-rule.aux Depth [C|_] Program Hyp GL :-
      normalize C C1, same-head Hyp C1, C1 = (_ :- Hyps'),
      compile-rule Depth Program Hyps' GL.

    % pred compile-hyps i:int, i:list prop, i:list prop, i:list prop, o:list prop.
    % compile-hyps 0 Hyps _ _ Hyps.
    % compile-hyps Depth Hyps Program [Hd|_] Res :-

    %   std.map Hyps (compile-rule Depth1 Program) Hyps'.

    pred mainn o:list prop.
    mainn R :- !,
        findall-one-arg precompilation.instances L,
        run 0 (pi X Y\ tc-cl X Y) L R.
  }}.
  Elpi Typecheck TC.Solver.

  Elpi Query TC.Solver lp:{{
    sigma L L1 L2\
      std.findall (mainn L) L1,
      coq.say L1
      % std.forall L (x\ coq.say x "\n\n")
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


  Elpi Accumulate TC.Solver lp:{{
    tc-cl {{nat}} {{inst1}} :- coq.say "A".
    tc-cl {{prod nat nat}} {{inst2 nat inst1}} :- coq.say "B".
    tc-cl {{prod (prod nat nat) (prod nat nat)}} {{inst2 (prod nat nat) (inst2 nat inst1)}} :- coq.say "C".
    tc-cl {{prod lp:A lp:A}} {{inst2 lp:A lp:S}} :- tc-cl A S, coq.say "D".

  }}.
  Elpi Typecheck TC.Solver.

  Goal cl (nat * nat). apply _. Qed.

End T.

Section T.
  Class A (T : Type) := {FA : T -> T}.
  Class B (T : Type) := {FB : T -> T}.
  Class C (T : Type) := {FC : T -> T}.

  Instance a : A unit := {FA x := x}.
  Instance b : (A unit) -> B bool := {FB x := x}.
  Instance c : (B bool) -> C nat := {FC x := x}.

  Elpi TC.Get_class_info C.

  Elpi Accumulate TC.Solver lp:{{
    :after "0"
    tc-C {{nat}} {{c lp:S}} :- !,
      tc-B {{bool}} S.

    % :after "0"
    % tc-C {{nat}} {{c (b lp:S)}} :- !,
    %   coq.say "BB",
    %   tc-A {{unit}} S.

    % :after "0"
    % tc-C {{nat}} {{c (b a)}} :- !,
    %   coq.say "CC".
  }}.
  Elpi Typecheck TC.Solver.

  Elpi Print TC.Solver.

  Goal C nat. apply _. Qed.
