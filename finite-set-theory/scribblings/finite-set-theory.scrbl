#lang scribble/manual

@(require scribble/example
          scribble/eval
          racket/sandbox
          (for-label
            racket/base
            racket/list
            racket/set
            racket/function
            ;; your library modules (as installed by the package)
            finite-set-theory
            finite-set-theory/function
            finite-set-theory/relation))

@title{Finite Set Theory (API + Laws)}
@author{Keith Elliott Peterson}

@; Tell Scribble that this manual documents these modules, so identifiers
@; defined there get cross-linked automatically.
@declare-exporting[finite-set-theory]

@defmodule[finite-set-theory]

@; ---------- Evaluator for runnable examples ----------
@(define the-eval (make-base-eval))
@(the-eval '(require racket/base
                     racket/list
                     racket/set
                     racket/function
                     finite-set-theory
                     finite-set-theory/function
                     finite-set-theory/relation))

This module provides combinators and predicates for working with
finite sets, (total) functions between them, and relations.
It aims for clear error reporting and totality checks.

@section{Conventions}

@itemlist[
 @item{@bold{Sets}: use @racketmodname[racket/set] sets throughout.}
 @item{@bold{Functions}: construct function values with
       @racket[function] from @racketmodname[finite-set-theory/function].
       Use @racket[function-src], @racket[function-tgt], and
       @racket[function-proc].}
 @item{@bold{Relations}: from @racketmodname[finite-set-theory/relation].}
 @item{@bold{Errors}: every public procedure validates inputs and raises
       @racket[raise-argument-error] (wrong type) or
       @racket[raise-arguments-error] (mismatched arity/shape).
       Names in error messages match the procedure that failed.}
]

@subsection{Fixtures used in examples}

@examples[#:eval the-eval #:label "Fixtures"
  (define A (set 1 2))
  (define B (set 'x 'y 'z))
  (define C (set 'p 'q))

  ;; Some handy functions/relations we’ll re-use in the doc
  (define idA (function (λ (x) x) A A))
  (define idB (function (λ (x) x) B B))

  ;; f : A -> B (injective, not surjective)
  (define f  (function (λ (x) (if (= x 1) 'x 'y)) A B))

  ;; g : A -> B (constant)
  (define g  (function (λ (x) 'x) A B))

  ;; h : A -> C (bijection)
  (define h  (function (λ (x) (if (= x 1) 'p 'q)) A C))

  ;; k : B -> C (not inverse of anything; used for composition examples)
  (define k  (function (λ (x) (case x [(x) 'p] [else 'q])) B C))

  ;; a small relation R ⊆ A×B that holds exactly on (1,x) and (2,y)
  (define R (relation (λ (x y) (equal? y (if (= x 1) 'x 'y))) A B))
]

@section{Quick Start}

@examples[#:eval the-eval
  (set-count (function-set A B))
  (injective? f)
  (∀ f (set 1))
  (∃ f (set 1))
  (preimage f (set 'x))
]

@subsection{Error examples}

@examples[#:eval the-eval #:label "Bad types raise clean errors"
  (eval:error (map-set add1 '(1 2)))     ; not sets
  (eval:error (function-set A B #:as-functions? 'maybe))]

@section{Basic Constructions}

@subsection{map-set}
@defproc[(map-set [f (-> any/c any/c)] [s set?] ...) set?]{
Maps @racket[f] element-wise over one or more sets, returning a set.
Arity is checked against the number of input sets.
}
@examples[#:eval the-eval
  (map-set add1 A)
  (map-set cons A B) ; pairs as lists
]

@subsection{set-cartesian-product}
@defproc[(set-cartesian-product [s set?] ...) set?]{Cartesian product of sets.}
@examples[#:eval the-eval
  (set->list (set-cartesian-product A B))
  (set-count (set-cartesian-product A A A))
]

@subsection{set-disjoint-union}
@defproc[(set-disjoint-union [s set?] ...) set?]{Disjoint sum of sets.}
@examples[#:eval the-eval
  (set-count (set-disjoint-union A B))
]

@subsection{set-equalizer}
@defproc[(set-equalizer [A set?] [f procedure?] [g procedure?]) set?]{
Equalizer of two predicates @racket[f] and @racket[g] on @racket[A].}
@examples[#:eval the-eval
  (define f1 (λ (x) (if (= x 1) 'p 'q)))
  (define f2 (λ (x) (if (= x 1) 'p 'p)))
  (set->list (set-equalizer A f1 f2))
]

@subsection{set-coequalizer}
@defproc[(set-coequalizer [R relation?] [q (-> any/c any/c)]) set?]{
Co-equalizer for relations; see @racketmodname[finite-set-theory/relation].}

@subsection{set-pullback}
@defproc[(set-pullback [f procedure?] [g procedure?] [A set?] [B set?] [C set?]) set?]{
Pullback set of @racket[f] and @racket[g].}

@subsection{pullback-along}
@defproc[(pullback-along [h function?] [k function?] #:as-functions? [as? any/c #f]) (setof any/c)]{
Pullback of functions (as function-graphs unless @racket[#:as-functions? #t]).
}

@section{Function Sets}

@subsection{function-set}
@defproc[(function-set [A set?] [B set?] [#:as-functions? as? any/c #f]) set?]{
All total functions from @racket[A] to @racket[B].
If @racket[#:as-functions? #t], elements are function values (from
@racketmodname[finite-set-theory/function]); otherwise elements are fgraphs.}
@examples[#:eval the-eval
  (set-count (function-set A B))
  (define FB (function-set A B #:as-functions? #t))
  (set-first FB)
  (function-src (set-first FB))
  (function-tgt (set-first FB))
]

@subsection{injective-function-set}
@defproc[(injective-function-set [A set?] [B set?] [#:as-functions? as? any/c #f]) set?]{
All injections @racket[A] ↪ @racket[B].}
@examples[#:eval the-eval
  (set-count (injective-function-set A B))
  (set-count (injective-function-set (set) B))
  (define F∅B (injective-function-set (set) B #:as-functions? #t))
  (set-first F∅B)
  (function-src (set-first F∅B))
  (function-tgt (set-first F∅B))
]

@subsection{surjective-function-set}
@defproc[(surjective-function-set [A set?] [B set?] [#:as-functions? as? any/c #f]) set?]{All surjections.}

@subsection{curry-function-set}
@defproc[(curry-function-set [F set?]) set?]{Curries a set of multi-argument functions.}
@examples[#:eval the-eval
  (define F2 (function-set (set-cartesian-product A A) B #:as-functions? #t))
  (define cur (curry-function-set F2))
  (function? (set-first cur))
]

@subsection{uncurry-function-set}
@defproc[(uncurry-function-set [F set?]) set?]{Uncurries back.}
@examples[#:eval the-eval
  (define F2 (function-set (set-cartesian-product A A) B #:as-functions? #t))
  (define cur (curry-function-set F2))
  (define uncur (uncurry-function-set (function-tgt (function-proc cur))))
  (set-count (set-first F2))
]

@section{Boolean-Valued Maps and Powersets}

@subsection{boolean-ranged-function-set->powerset}
@defproc[(boolean-ranged-function-set->powerset [F set?]) set?]{
Collects the @racket[#t] fibres.}
@examples[#:eval the-eval
  (define P (powerset A))
  (define BF (powerset->boolean-ranged-function-set P))
  (boolean-ranged-function-set->powerset BF)
  (set (set 1 2) (set 2) (set 1) (set))
]

@subsection{powerset->boolean-ranged-function-set}
@defproc[(powerset->boolean-ranged-function-set [P set?]) set?]{
Inverse of @racket[boolean-ranged-function-set->powerset].}

@; ------------- Cross-references to other manuals in this package -------------
@section{Other APIs in this package}

See also:
@itemlist[
  @item{@seclink["function-api"]{Function API} in @racketmodname[finite-set-theory/function]}
  @item{@seclink["relation-api"]{Relation API} in @racketmodname[finite-set-theory/relation]}
]

