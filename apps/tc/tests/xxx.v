From elpi Require Import tc.
Elpi Command A.
Elpi Accumulate  lp:{{
  main [indt-decl S] :-
    coq.env.add-indt S I,
    coq.say I.
}}.
Elpi Typecheck.

Record Eqb (T: Type) := {
    eqb : T -> T -> bool; 
    eqb_leibniz A B: eqb A B = true <-> A = B
}.

Existing Class Eqb.

#[refine] Instance eqBool : Eqb bool := {
  eqb x y := if x then y else negb y
}.
Proof. intros [] []; intuition. Qed.
