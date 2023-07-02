From elpi Require Import elpi.
Elpi Command Test.
Elpi Accumulate lp:{{
  main _ :- coq.say "CIAO".
}}. 

Elpi Print Test.