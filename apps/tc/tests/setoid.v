
From Coq Require Import Setoid.
From Coq Require Import Morphisms.
(* From elpi Require Import tc.

Elpi TC.AddAllClasses.
Elpi TC.AddAllInstances.
Elpi Override TC TC.Solver All.
Elpi Override TC - Morphisms.ProperProxy Proper. *)

Section section.
  Variables (A : Type).
  Implicit Types f : A -> A -> A.

  Class BagUnion T := { union : T -> T -> T }.
  Global Instance IBagUnion : BagUnion A := {union a b := a}.

  Definition assoc f := forall x y z,
    f x (f y z) = f (f x y) z.
    
  Class Rewrite `{BagUnion A} := { rewrite_me : assoc union }.
  Global Instance RewriteInst : Rewrite. Admitted.
End section.

Arguments rewrite_me {A} {H} {Rewrite}.
Arguments assoc {A}.
Arguments Rewrite {A} {H}.

Notation "m1 '\u' m2" := (union m1 m2)
  (at level 37, right associativity).

Lemma ex1 (T : Type) (a b c d e f: T): a \u b \u c \u d \u e \u f = (a \u b \u c \u d \u e) \u f.
  intros.
  (* Set Typeclasses Debug.
  From elpi Require Import tc.
  Elpi TC.AddAllClasses.
  Elpi TC.AddAllInstances. 
  Elpi Override TC TC.Solver None.  *)
  From elpi Require Import tc.
  Elpi TC.AddAllClasses.
  Elpi TC.AddAllInstances.
  Elpi Accumulate TC.Solver lp:{{
    % :after "0" solve-aux (goal Ctx _ Ty _ _) _ :-
    %   coq.say "Ctx" Ctx "Ty" Ty, fail.
    :before "print-solution" print-solution :- !.
    :before "print-goal" print-goal :- !.
    % :after "0" msolve L _ :- coq.say "The goal list is:" L, fail.
  }}.
  Elpi Override TC - Proper.
  rewrite rewrite_me.
Abort.
