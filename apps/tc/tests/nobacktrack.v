From elpi Require Import compiler.

Elpi Debug "simple-compiler".
Elpi Debug "get-full-path".

Module A.

  Class C (n : nat) := {}.
  Local Instance c_1 : C 1 | 10 := {}.
  Local Instance c_2 : C 2 | 1 := {}.

  Class D (n : nat) := {}.
  Local Instance d_1 : D 1 := {}.

  Class E (n : nat) := {}.
  Local Instance foo {n} : C n -> D n -> E n := {}.

  Elpi AddAllInstances.

  Elpi Override TC TC_solver All.

  Elpi Accumulate TC_solver lp:{{
    tc {{:gref E}} {{E lp:N}} Sol :-
      tc {{:gref C}} {{C lp:N}} P1, !,
      tc {{:gref D}} {{D lp:N}} P2,
      Sol = {{foo lp:P1 lp:P2}}.
  }}.
  Elpi Print TC_solver.

  Check (_ : E _).
End A.

Module B.
  Class Persistent (A: Prop).
  Class Separable (A: Prop).
  Local Instance persistent_separable P: Persistent P -> Separable P | 10. Admitted.
  Local Instance and_persistent P Q : Persistent P -> Persistent Q -> Persistent (P /\ Q) | 0. Admitted.
  Local Instance and_separable P1 P2 : Separable P1 -> Separable P2 -> Separable (P1 /\ P2) | 0. Admitted.

  Elpi Override TC TC_solver None.

  Goal forall P Q, Persistent P -> Separable (P /\ Q).
    Time Fail apply _.
  Abort.

  Goal forall P, Persistent P -> Separable (P /\ P).
    Time apply _.
  Abort.

  Elpi Override TC TC_solver All.
  Elpi AddAllInstances.
  Goal forall P Q, Persistent P -> Separable (P /\ Q).
    Time Fail solve [unshelve (apply _)].
  Abort.

  Elpi Print TC_solver.

  Elpi Accumulate TC_solver lp:{{
    :replace "elpi.apps.tc.tests.nobacktrack.B.and_separable"
    tc {{:gref Separable}} {{Separable (lp:A /\ lp:B)}} Sol :- !,
      tc {{:gref Separable}} {{Separable lp:A}} P1,
      tc {{:gref Separable}} {{Separable lp:B}} P2,
      Sol = {{and_separable _ _ lp:P1 lp:P2}}.
  }}.


  Goal forall (P Q: Prop), Persistent P -> Separable (P /\ Q).
    Time Fail solve [unshelve (apply _)].
  Abort.

  Goal forall (P Q: Prop), Persistent (Q /\ P) -> Separable (P /\ Q).
    intros.
    Fail apply _.
  Abort.

  Lemma forwRewrite {P Q}: Persistent (P /\ Q) -> Persistent P /\ Persistent Q. Admitted.

  Elpi AddForwardRewriting forwRewrite.

  Goal forall (P Q: Prop), (Persistent ((P /\ Q /\ Q) /\ Q) -> Separable ((P /\ P) /\ (Q /\ Q))).
    apply _.
  Qed.

  Goal forall (P Q: Prop), (Persistent (P /\ Q) -> Separable (P /\ Q)).
    apply _.
  Qed.

  Goal forall (P Q: Prop), Persistent (Q /\ P) -> Separable (P /\ Q).
    apply _.
  Qed.
End B.