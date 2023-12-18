(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

From elpi Require Import elpi.

From elpi.apps.tc Extra Dependency "base.elpi".
From elpi.apps.tc Extra Dependency "tc_aux.elpi".

(*
  tc_option.db contains the set of options used by the solver of tc.
  all the options are set to false by default
*)
Elpi Db tc_options.db lp:{{
  pred oTC-ignore-eta-reduction o:list string.
  oTC-ignore-eta-reduction ["TC", "IgnoreEtaReduction"].

  % Time taken by only instance search (we time tc-recursive-search)
  pred oTC-time-instance-search o:list string.
  oTC-time-instance-search ["TC", "Time", "Instance", "Search"].

  % Time taken by the whole search in tc
  pred oTC-time o:list string.
  oTC-time ["TC", "Time"].

  % Time taken to refine the solution
  pred oTC-time-refine o:list string.
  oTC-time-refine ["TC", "Time", "Refine"].

  pred oTC-clauseNameShortName o:list string.
  oTC-clauseNameShortName ["TC", "NameShortPath"].

  pred oTC-debug o:list string.
  oTC-debug ["TC", "Debug"].

  pred oTC-use-pattern-fragment-compiler o:list string.
  oTC-use-pattern-fragment-compiler ["TC", "CompilerWithPatternFragment"].

  pred all-options o:list ((list string) -> prop).
  all-options [
    oTC-ignore-eta-reduction, oTC-time-refine, oTC-time,
    oTC-clauseNameShortName, oTC-time-instance-search, oTC-debug,
    oTC-use-pattern-fragment-compiler
  ].

  pred is-option-active i:(list string -> prop).
  is-option-active Opt :-
    Opt X, coq.option.get X (coq.option.bool tt).
}}.

Elpi Db tc.db lp:{{
  % the type of search for a typeclass
  % deterministic :- no backtrack after having found a solution/fail
  % classic       :- the classic search, if a path is failing, we backtrack
  kind search-mode type.
  type deterministic  search-mode.
  type classic        search-mode.

  % [instance Path InstGR ClassGR], ClassGR is the class implemented by InstGR
  pred instance o:list string, o:gref, o:gref.

  % [class ClassGR PredName SearchMode], for each class GR, it contains
  % the name of its predicate and its SearchMode
  pred class o:gref, o:string, o:search-mode.

  % pred on which we graft instances in the database
  pred hook o:string.
  :name "firstHook" hook "firstHook".
  :name "lastHook" hook "lastHook".

  % the set of instances that we are not yet able to compile,
  % in majority they use universe polimorphism
  pred banned o:gref.

  % [tc-signature TC Modes], returns for each Typeclass TC
  % its Modes
  pred tc-mode i:gref, o:list (pair argument_mode string).

  namespace precompilation {
    /*
      Given:
        ```coq
          Class cl (T : Type).
          Instance inst1 : cl nat.
          Instance inst2 (A : Type) : cl A -> cl (A * A).
        ```
      The instances of `cl` are compiled into
        ```elpi
          tc-cl {{nat}} {{inst1}}.
          tc-cl {{lp:A * lp:A}} {{inst2 lp:A lp:S}} :- tc-cl A S.
        ```
      Out goal is to pre-compile the class `cl` with a certain height.
      For example, if this height is 3, then we wish to replace this database
      with:
        ```elpi
          tc-cl {{nat}} {{inst1}}.
          tc-cl {{nat * nat}} {{inst2 nat inst1}}.
          tc-cl {{(nat * nat) * (nat * nat)}} {{inst2 (nat * nat) (inst2 nat inst1)}}.
          tc-cl {{lp:A * lp:A}} {{inst2 lp:A lp:S}} :- tc-cl A S.
        ```
      Here, an efficient algorithm of clause retrival would immediately solve the
      goal `cl ((nat * nat) * (nat * nat))` since its solution is precompiled.
      The `instances` predicate below contains the raw representation of an elpi
      rule. In the example below, the instances `inst1` and `inst2`
      would produce the two rules:
        ```elpi
          instances (instance-clause {{cl}} [{{nat}}, {{inst1}}] []).
          instances (instance-lambda A (instance-lambda S\ instance-clause {{cl}} [{{lp:A * lp:A}}, {{inst2 lp:A lp:S}}] [tc-cl A S]).
        ```
    */
    kind raw-clause type.
    /*
      [clause cl args body]
      - cl   : is the class corresponding to the current rule
      - args : represents the list of the argument of the current class + its solution
      - body : is the list of the premises of the current rule
    */
    type instance-clause term -> list raw-clause -> raw-clause.
    type instance-lambda (term -> raw-clause) -> raw-clause.
    % TODO: an instance-clause may contain props in the list of premises

    :index (30)
    pred instances o:raw-clause.
  }
}}.
