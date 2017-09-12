[![Build Status](https://travis-ci.org/LPCIC/coq-elpi.svg?branch=master)](https://travis-ci.org/LPCIC/coq-elpi)

# coq-elpi
Coq plugin embedding ELPI. 

[Homepage](https://lpcic.github.io/coq-elpi-www/) with tutorials (thanks to [jscoq](https://github.com/ejgallego/jscoq)).

## What is ELPI
[ELPI](https://github.com/LPCIC/elpi) provides an easy-to-embed 
implementation of λProlog, a programming language well suited to
express transformations of abstract syntax trees with binders.  

## What is coq-elpi
Coq-elpi provides a Coq plugin that embeds ELPI.
It also provides a way to embed Coq's terms into λProlog using
the Higher-Order Abstract Syntax) approach
([HOAS](https://en.wikipedia.org/wiki/Higher-order_abstract_syntax))
and a way to read terms back.  In addition to that it exports to ELPI a
set of Coq's primitives, e.g. printing a message, accessing the
environment of theorems and data types, defining a new constant and so on.
Finally is provides a quotation and anti-quotation for Coq's syntax in
λProlog.  E.g. `{{nat}}` is expanded to the type name of natural numbers,
or `{{A -> B}}` to the representation of a product by unfolding the `->`
notation.

## What is the purpose of all that
Provide a scripting language to Coq well suited to express manipulation
of terms.  One can use such language to implement new features, like
code generation "à la derive".
Finally ELPI extends λProlog with a (still under study) language to declare and
manipulate higher order constraints. The aim to provide good language support
to express algorithms like higher order unification and type inference for
Coq's terms.  In particular one can extend the HOAS idea also to unification
variables, i.e. reuse λProlog's meta variables to implement Coq's ones.

## How to install coq-elpi

The simplest way is to use [OPAM](http://opam.ocaml.org/) and type
```
opam pin add coq-elpi https://github.com/LPCIC/coq-elpi.git
```
This gives you `From elpi Require Import elpi`.

You can also clone this repository and type `make` (in this case the
plugin is compiled against the Coq version in the `coq/` submodule directory).

### Syntax highlight in CoqIDE

The installation process puts [coq-elpi.lang](https://github.com/LPCIC/coq-elpi/blob/master/etc/coq-elpi.lang)
in a place where CoqIDE can find it.  Then you can select `coq-elpi`
from the menu `Edit -> Preferences -> Colors`.

### Syntax highlight in vim

We recommend to add the following lines to `~/.vimrc` (in addition to the ones
for [elpi](https://github.com/LPCIC/elpi#syntax-highlight-in-vim)).

```vim
"coq-elpi
autocmd FileType lprolog syn keyword coqElpiSpecial lam prod sort let match fix hole axiom indc indt const prop app
autocmd FileType lprolog syn cluster elpiAntiQuotation contains=elpiAntiQuotationVar,elpiAntiQuotationBound,elpiAntiQuotationTerm
autocmd FileType lprolog syn region elpiAntiQuotationTerm start=+lp:"+ end=+"+ contains=elpiQuotation,lprologVariable,coqElpiSpecial,elpiMacro,lprologSpecial
autocmd FileType lprolog syn match elpiAntiQuotationVar "lp:[A-Z_-]\+"ms=s+3
autocmd FileType lprolog syn match elpiAntiQuotationBound "lp:[a-z_-]\+"
autocmd FileType lprolog hi def link elpiAntiQuotationVar Keyword
autocmd FileType lprolog hi def link elpiAntiQuotationBound Normal
autocmd FileType lprolog hi def link coqElpiSpecial Special
```
