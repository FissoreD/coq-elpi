From elpi.apps Require Import tc.

Elpi TC Solver Override TC.Solver All.

Class a (N: nat).
Instance b : a 3. Qed.
Instance c : a 4. Qed.

Elpi AddAllClasses.
Elpi AddAllInstances.

Goal a 4. apply _. Qed.
