From elpi Require Import elpi.
(* From elpi Extra Dependency "elpi2html2.elpi" as elpi2html. *)
(* 
Elpi Command C. 
Elpi Accumulate File elpi2html.
Elpi Typecheck. *)


Elpi Command Test.
Elpi Accumulate lp:{{
  main _ :- coq.say "CIAO".
}}. 

Elpi Print Test.