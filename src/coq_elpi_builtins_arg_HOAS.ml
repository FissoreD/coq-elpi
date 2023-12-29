(* Automatically generated from elpi/coq-arg-HOAS.elpi, don't edit *)
(* Regenerate via 'make src/coq_elpi_builtins_arg_HOAS.ml' *)
let code = {|
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%% coq-arg-HOAS %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% This section contains the low level data types linking Coq and elpi.
% In particular the entry points for commands


% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Entry points
%
% Command and tactic invocation
% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Entry point for commands. Eg. "#[att=true] Elpi mycommand foo 3 (f x)." becomes
%   main [str "foo", int 3, trm (app[f,x])]
% in a context where
%   attributes [attribute "att" (leaf "true")]
% holds. The encoding of terms is described below.
% See also the coq.parse-attributes utility.
pred main i:list argument.
pred main-interp i:list argument, i:any.
pred main-synterp i:list argument, o:any.
pred usage.
pred attributes o:list attribute.

% see coq-lib.elpi for coq.parse-attributes generating the options below
type get-option string -> A -> prop.

% The data type of arguments (for commands or tactics)
kind argument type.
type int       int    -> argument. % Eg. 1 -2.
type str       string -> argument. % Eg. x "y" z.w. or any Coq keyword/symbol
type trm       term   -> argument. % Eg. (t).

% Extra arguments for commands. [Definition], [Axiom], [Record] and [Context]
% take precedence over the [str] argument above (when not "quoted").
%
% Eg. Record or Inductive
type indt-decl indt-decl -> argument.
% Eg. #[universes(polymorphic,...)] Record or Inductive
type upoly-indt-decl indt-decl -> upoly-decl -> argument.
type upoly-indt-decl indt-decl -> upoly-decl-cumul -> argument.
% Eg. Definition or Axiom (when the body is none)
type const-decl id -> option term -> arity -> argument.
% Eg. #[universes(polymorphic,...)] Definition or Axiom
type upoly-const-decl id -> option term -> arity -> upoly-decl -> argument.
% Eg. Context A (b : A).
type ctx-decl context-decl -> argument.

% Declaration of inductive types %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

kind indt-decl type.
kind indc-decl type.
kind record-decl type.

% An arity is written, in Coq syntax, as:
%    (x : T1) .. (xn : Tn) : S1 -> ... -> Sn -> U
% This syntax is used, for example, in the type of an inductive type or
% in the type of constructors. We call the abstractions on the left of ":"
% "parameters" while we call the type following the ":" (proper) arity.

% Note: in some contexts, like the type of an inductive type constructor,
% Coq makes no distinction between these two writings
%    (xn : Tn) : forall y1 : S1, ...    and      (xn : Tn) (y1 : S1) : ...
% while Elpi is a bit more restrictive, since it understands user directives
% such as the implicit status of an arguments (eg, using {} instead of () around
% the binder), only on parameters.
% Moreover parameters carry the name given by the user as an "id", while binders
% in terms only carry it as a "name", an irrelevant pretty pringintg hint (see
% also the HOAS of terms). A user command can hence only use the names of
% parameters, and not the names of "forall" quantified variables in the arity.
%
% See also the arity->term predicate in coq-lib.elpi

type parameter id -> implicit_kind -> term -> (term -> arity) -> arity.
type arity term -> arity.

type parameter   id -> implicit_kind -> term -> (term -> indt-decl) -> indt-decl.
type inductive   id -> bool -> arity -> (term -> list indc-decl) -> indt-decl. % tt means inductive, ff coinductive
type record      id -> term -> id -> record-decl -> indt-decl.

type constructor id -> arity -> indc-decl.

type field       field-attributes -> id -> term -> (term -> record-decl) -> record-decl.
type end-record  record-decl.

% Example.
% Remark that A is a regular parameter; y is a non-uniform parameter and t
% also features an index of type bool.
%
%  Inductive t (A : Type) | (y : nat) : bool -> Type :=
%  | K1 (x : A) {n : nat} : S n = y -> t A n true -> t A y true
%  | K2 : t A y false
%
% is written
%
%  (parameter "A" explicit {{ Type }} a\
%     inductive "t" tt (parameter "y" explicit {{ nat }} _\
%                     arity {{ bool -> Type }})
%      t\
%       [ constructor "K1"
%          (parameter "y" explicit {{ nat }} y\
%           (parameter "x" explicit a x\
%            (parameter "n" maximal {{ nat }} n\
%              arity {{ S lp:n = lp:y -> lp:t lp:n true -> lp:t lp:y true }})))
%       , constructor "K2"
%          (parameter "y" explicit {{ nat }} y\
%            arity {{ lp:t lp:y false }}) ])
%
% Remark that the uniform parameters are not passed to occurrences of t, since
% they never change, while non-uniform parameters are both abstracted
% in each constructor type and passed as arguments to t.
%
% The coq.typecheck-indt-decl API can be used to fill in implicit arguments
% an infer universe constraints in the declaration above (e.g. the hidden
% argument of "=" in the arity of K1).
%
% Note: when and inductive type declaration is passed as an argument to an
% Elpi command non uniform parameters must be separated from the uniform ones
% with a | (a syntax introduced in Coq 8.12 and accepted by coq-elpi since
% version 1.4, in Coq this separator is optional, but not in Elpi).

% Context declaration (used as an argument to Elpi commands)
kind context-decl type.
% Eg. (x : T) or (x := B), body is optional, type may be a variable
type context-item  id -> implicit_kind -> term -> option term -> (term -> context-decl) -> context-decl.
type context-end   context-decl.

typeabbrev field-attributes (list field-attribute).

macro @global!   :- get-option "coq:locality" "global".
macro @local!    :- get-option "coq:locality" "local".
|}
