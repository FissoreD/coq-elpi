From elpi.apps Require Import tc.
Elpi Override TC TC.Solver All.

Set TC NameShortPath.
Elpi TC Deactivate Observer TC.Compiler.

Class number (i:nat).
Instance n0 : number 0. Qed.

Definition pred n := match n with 
  | O => number O
  | S n => number n
  end.

Existing Class pred.

Class take_number (i: nat).
Instance i (x : nat) : pred x -> take_number x. Qed.

Hint Extern 2 (pred _) => unfold pred; simpl : typeclass_instances.
Elpi TC.AddAllClasses.
Elpi TC.Get_class_info take_number.

Elpi Accumulate TC.Solver lp:{{
  pred const->redflags i:gref, o:coq.redflag.
  const->redflags (const C) (coq.redflags.const C).

  pred cbn i:list string, i:term, o:term.
  cbn ToUnfold T T' :-
    std.do![std.map {std.map ToUnfold coq.locate} const->redflags LRedflag,
    Reds = [coq.redflags.beta, coq.redflags.fix, coq.redflags.match | LRedflag],
    coq.redflags.add coq.redflags.nored Reds L,
    @redflags! L => coq.reduction.cbv.norm T T'].

  tc-pred T T'' :-
    cbn ["pred"] {coq.mk-app {{pred}} [T]} T',
    not (T = T'),
    tc-recursive-search T' T''.
  :after "0" msolve _ _ :- coq.say "In elpi", fail.
}}.
Elpi Typecheck TC.Solver.
Elpi TC.AddAllInstances.

Goal take_number 1.
  apply _. (* (i 1 (n0 : pred 1)). *)
Qed.
