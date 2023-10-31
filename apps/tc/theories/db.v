(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

From elpi Require Import elpi.

(* 
  tc_option.db contains the set of options used by the solver of tc. 
  all the options are set to false by default
*)
Elpi Db tc_options.db lp:{{
  pred oTC-ignore-eta-reduction o:list string. 
  oTC-ignore-eta-reduction ["TC", "IgnoreEtaReduction"].

  pred oTC-resolution-time o:list string. 
  oTC-resolution-time ["TC", "ResolutionTime"].

  pred oTC-clauseNameShortName o:list string. 
  oTC-clauseNameShortName ["TC", "NameShortPath"].

  pred oTC-time-refine o:list string. 
  oTC-time-refine ["TC", "TimeRefine"].

  pred oTC-debug o:list string.
  oTC-debug ["TC", "Debug"].
  
  pred oTC-addModes o:list string.
  oTC-addModes ["TC", "AddModes"].

  pred oTC-use-pattern-fragment-compiler o:list string. 
  oTC-use-pattern-fragment-compiler ["TC", "CompilerWithPatternFragment"].

  pred is-option-active i:list string.
  is-option-active Opt :- 
    coq.option.get Opt (coq.option.bool tt).
}}.

Elpi Db tc.db lp:{{
  % the type of search for a typeclass
  % deterministic :- no backtrack after having found a solution/fail
  % classic       :- the classic search, if a path is failing, we backtrack
  kind search-mode type.
  type deterministic  search-mode.
  type classic        search-mode.

  % contains the instances added to the DB 
  % associated to the list of sections they belong to
  pred instance o:list string, o:gref, o:gref.

  % contains the typeclasses added to the DB
  pred classes o:gref, o:search-mode.

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
}}.