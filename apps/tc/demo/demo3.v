Require Export Bool.
From elpi.apps Require Export compiler.

Class Eqb A : Type := eqb : A -> A -> bool.

Notation " x == y " := (eqb x y) (no associativity, at level 70).

Local Instance eqU : Eqb unit | 2 := { eqb x y := true }.
Local Instance eqB : Eqb bool | 2 := { eqb x y := if x then y else negb y }.
Local Instance eqP {A B} `{Eqb A} `{Eqb B} : Eqb (A * B) | 1 := { 
  eqb x y := (fst x == fst y) && (snd x == snd y) }.

Elpi Override TC TC_check Only Eqb.
Elpi add_instances Eqb.

(* Show how generated clauses are *)
Elpi Print TC_check.

Check (eqb (tt, (tt, true)) (tt, (tt, true))).

Fail Check (fun x y : _ => eqb x y).

Elpi Override TC - Eqb.

Check (fun x y : _ => eqb x y).
