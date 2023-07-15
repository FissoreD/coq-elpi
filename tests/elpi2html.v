From elpi Require Import elpi.
(* From elpi Extra Dependency "elpi2html2.elpi" as elpi2html. *)
(* 
Elpi Command C. 
Elpi Accumulate File elpi2html "test.json".
Elpi Typecheck. *)


Elpi Command Test.
Elpi Accumulate lp:{{
  pred mytest i:int, o:int. 
  mytest A B :- 
    B is (3 + 4) * A.

  mytest A B :- 
    mytest {calc (3 * A)} B.

  mytest A B :- 
    B is A * {mytest A}.

  mytest A B :- 
    (B = A; B = 3), true.

  mytest A_ B :- 
    (pi x\ mytest 3 x => true), 
    B = 4.

  mytest A_ B :- (mytest 3 2 => true), 
    mytest 3 B => true.

  mytest A_ B :- mytest 3 2 => (true, 
    mytest 3 B => true).

  mytest A B :- mytest 3 2 => B is (4 + 5) * A, true.

  mytest 3 4.

  main _ :- coq.say "CIAO".
}}. 
Elpi Typecheck.

Elpi Print Test "test.json".