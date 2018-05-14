(* Generates congruence lemmas using reflect

   license: GNU Lesser General Public License Version 2.1 or later           
   ------------------------------------------------------------------------- *)

From Coq Require Export Bool.
From elpi Require Import elpi derive.projK.

Elpi Db derive.bcongr.db "type bcongr-db term -> term -> prop.".

Elpi Command derive.bcongr.
Elpi Accumulate Db derive.bcongr.db.
Elpi Accumulate Db derive.projK.db.
Elpi Accumulate File "ltac/injection.elpi".
Elpi Accumulate File "derive/bcongr.elpi".
Elpi Accumulate "
  main [str I, str O] :- !, coq.locate I T, derive.bcongr.main T O _.
  main [str I] :- !, coq.locate I T, derive.bcongr.main T ""_congr"" _.
  main _ :- usage.

  usage :- coq.error ""Usage: derive.bcongr <inductive type name> [<output name suffix>]"".
".
Elpi Typecheck. 

Elpi derive.projK list.

Elpi derive.bcongr list.