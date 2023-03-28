From elpi.apps Require Import tc.stdpp.inj_hardcoded.
From elpi Require Import elpi.
(* Elpi Bound Steps 1000. *)

Elpi Debug "debug".

Set Printing All.
Check (_ : Inj _ _ g).
Check (_ : Inj _ _ inr). 

Check (_ : Inj _ _ (@compose nat nat nat g f)).
Check (_ : Inj _ _ (compose g f)).
Check (_ : Inj _ _ (prod_map (compose f g) (compose f f))).
(* Check (_ : Inj _ _ _). *)

Check (_ : Inj eq eq (prod_map f f)).

Check (_ : Inj _ _ (prod_map g (compose f f))).

Check (_ : Inj _ _ g).

Goal forall (A: Type) (x y: A -> A), Inj eq eq x -> Inj eq eq (compose x x).
Proof.
  intros.
  Check (_ : Inj _ _ (compose x x)).
  Check (_ : Inj _ _ x).
Admitted.

Goal forall (A: Type) (x: A -> A), let y := Inj eq eq x in let z := y in z -> Inj eq eq (compose x x).
Proof.
  intros T x y z H.
  Check (_ : Inj eq eq (compose x x)).
Admitted.