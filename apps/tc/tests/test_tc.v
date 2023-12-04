From elpi.apps Require Import tc.

(* Small test to solve a goal in elpi *)

Elpi Override TC TC.Solver All.

Class a (N: nat).
Instance b : a 3. Qed.
Instance c : a 4. Qed.

Goal a 4. apply _. Qed.
