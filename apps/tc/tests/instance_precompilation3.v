From elpi.apps Require Import tc.
Elpi Override TC TC.Solver All.
Require Import Arith.

Set TC NameShortPath.
Elpi TC Deactivate Observer TC.Compiler.

Class number (i:nat).
Instance n0 : number 0. Qed.
Instance ns n : number n -> number (S n). Qed. 

Definition pred n := match n with 
  | O => number O
  | S n => number n
  end.

Existing Class pred.

Class give_nat (i:nat).

Class take_number (i: nat).
Instance i (x : nat) : pred x -> take_number x. Qed.

Hint Extern 2 (pred _) => unfold pred; simpl : typeclass_instances.
Elpi TC.AddAllClasses.
(* Elpi TC.Get_class_info take_number. *)

Elpi Accumulate tc.db lp:{{
  shorten precompilation.{instance-clause, instance-lambda, instances, raw-clause, body-raw, body-prop, body-arg, body-search}.

  pred const->redflags i:gref, o:coq.redflag.
  const->redflags (const C) (coq.redflags.const C).

  pred cbn i:list string, i:term, o:term.
  cbn ToUnfold T T' :-
    std.do![std.map {std.map ToUnfold coq.locate} const->redflags LRedflag,
    Reds = [coq.redflags.beta, coq.redflags.fix, coq.redflags.match | LRedflag],
    coq.redflags.add coq.redflags.nored Reds L,
    @redflags! L => coq.reduction.cbv.norm T T']
    % coq.say "In cbn give the result" T' "from" T
    .

  instances (instance-lambda T\ instance-lambda T'\ instance-lambda T''\ 
    instance-lambda TApp\
    instance-clause ({{pred lp:T lp:T''}})
    [
      body-prop (ground_term T),
      body-prop (coq.mk-app {{pred}} [T] TApp),
      body-prop (cbn ["pred"] TApp T'),
      % body-prop (coq.say "In instance precompiler" T T'),
      body-search [T', T'']
      /*body-prop (tc-recursive-search T' T'')*/]
  ).
  % tc-pred T T'' :-
  %   cbn ["pred"] {coq.mk-app {{pred}} [T]} T',
  %   not (T = T'),
  %   tc-recursive-search T' T''.

  instances (instance-clause ({{give_nat 0}}) []).
  instances (
    % instance-lambda Str\
      instance-lambda N\ 
        instance-clause {{give_nat (S lp:N)}} [body-raw (instance-clause {{give_nat lp:N}} [])]).
  instances (instance-lambda x\ instance-lambda Sol\ 
    instance-clause {{take_number lp:x (i lp:x lp:Sol)}} [
      body-raw (instance-clause {{give_nat lp:x}} []),
      body-prop (ground_term x),
      % body-prop (coq.term->string x Str),
      % body-prop (coq.say "The current int is" Str),
      body-raw (instance-clause {{pred lp:x lp:Sol}} [])
    ]
  ).
}}.
Elpi Typecheck TC.precompile.

(* Elpi Accumulate TC.precompile lp:{{
  :after "to-debug-instance-creation"
  to-debug-instance-creation.
}}. *)

Elpi TC.AddRawInstances number.

(* Elpi Print TC.AddRawInstances. *)
  (* Elpi Trace Browser. *)
  (* Elpi Trace Browser. *)
  Elpi TC.precompile 10 take_number show.

Goal take_number 2.
  refine (i 2 (ns 0 n0)).
  simpl.
  Show Proof.
  Show Proof.
  apply ns.
  apply ns.
  apply n0.
  Show Proof.
  apply _.
  Show Proof.

(* Elpi Accumulate TC.Solver lp:{{
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
Elpi Typecheck TC.Solver. *)

(* Elpi TC.AddAllInstances. *)
xx.
Goal take_number 2.
  apply _. (* (i 1 (n0 : pred 1)). *)
Qed.
