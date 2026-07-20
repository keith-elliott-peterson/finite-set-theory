#lang scribble/manual

@(require scribble/eval
          racket/sandbox
          (for-label
            racket/base
            racket/list
            racket/set
            ;; document ONLY the function module:
            finite-set-theory/function))

@title{Function API}

;; This page documents the installed module `finite-set-theory/function`
@defmodule[finite-set-theory/function]
@declare-exporting[finite-set-theory/function]

;; One evaluator for all examples on this page.
;; Only pull what we need: sets from `racket/set` and the function API.
@(define the-eval (make-base-eval))
@(the-eval '(require racket/base
                     racket/list
                     racket/set
                     finite-set-theory/function))

@section{Fixtures used in examples}
@examples[#:eval the-eval #:label "Fixtures"
  (define A (set 1 2))
  (define B (set 'x 'y 'z))
  (define C (set 'p 'q))

  ;; Basic functions we'll reuse in examples
  (define idA (function (λ (x) x) A A))
  (define f   (function (λ (x) (if (= x 1) 'x 'y)) A B))
  (define g   (function (λ (x) 'x) A B))           ; constant
]

@section{Constructors and Observers}

@defproc[(function [proc procedure?] [src set?] [tgt set?]) function?]{
Wrap a total procedure @racket[proc] into a function value from @racket[src] to @racket[tgt].
Signals an error if @racket[src] or @racket[tgt] is not a set, or if @racket[proc]
doesn’t map every element of @racket[src] into @racket[tgt].}

@defproc[(function-src [F function?]) set?]{The source set of @racket[F].}
@defproc[(function-tgt [F function?]) set?]{The target set of @racket[F].}
@defproc[(function-proc [F function?]) (-> any/c any/c)]{The underlying total procedure of @racket[F].}

@examples[#:eval the-eval
  (function-src f)
  (function-tgt f)
  ((function-proc f) 2)
]

@section{Sets of Functions}

@defproc[(function-set [A set?] [B set?] [#:as-functions? as? boolean? #f]) set?]{
The set of all total functions @italic{A → B}.
When @racket[#:as-functions? #t], elements are function values;
otherwise, elements are function-graphs.}

@defproc[(injective-function-set [A set?] [B set?] [#:as-functions? as? boolean? #f]) set?]{
All injections @italic{A ↪ B}. When @racket[A] is empty and @racket[#:as-functions? #t],
the set is inhabited by the unique empty function.}

@defproc[(surjective-function-set [A set?] [B set?] [#:as-functions? as? boolean? #f]) set?]{
All surjections @italic{A ↠ B}.}

@examples[#:eval the-eval
  (set-count (function-set A B))
  (set-count (injective-function-set A B))
  (set-count (surjective-function-set A A))
  (define F∅B (injective-function-set (set) B #:as-functions? #t))
  (set? F∅B)
]

@section{Properties}

@defproc[(injective?  [F function?]) boolean?]{True iff @racket[F] is one-to-one.}
@defproc[(surjective? [F function?]) boolean?]{True iff @racket[F] hits every element of its target.}
@defproc[(bijective?  [F function?]) boolean?]{True iff @racket[F] is both injective and surjective.}

@examples[#:eval the-eval
  (values (injective? idA) (surjective? idA) (bijective? idA))
  (values (injective? f)   (surjective? f)   (bijective? f))
  (values (injective? g)   (surjective? g)   (bijective? g))
]

@section{Composition and (Un)Currying}

@defproc[(compose [G function?] [F function?]) function?]{
Composition when @racket[(function-src G)] equals @racket[(function-tgt F)].}

@defproc[(curry-function-set   [F set?]) set?]{
Given a set of uncurried functions, produce the corresponding set of curried functions.}

@defproc[(uncurry-function-set [F set?]) set?]{
Inverse of @racket[curry-function-set] on appropriate domains.}

@examples[#:eval the-eval
  (define k (function (λ (x) (case x [(x) 'p] [else 'q])) B C))
  (define cf (function-proc (compose k f)))
  (for/list ([x (in-set A)]) (cf x))
]

@section{Boolean-Valued Maps and Powersets}

@defproc[(boolean-ranged-function-set->powerset [F set?]) set?]{
Collect the fibres @racket[(λ x. (proc x) = #t)] as a powerset element.}

@defproc[(powerset->boolean-ranged-function-set [P set?]) set?]{
Inverse of @racket[boolean-ranged-function-set->powerset] on powersets.}

@examples[#:eval the-eval
  (define P  (powerset A))
  (define BF (powerset->boolean-ranged-function-set P))
  (boolean-ranged-function-set->powerset BF)
]

@section{Cartesian-Product Utilities}
@defproc[(swap-cartesian-product [A set?] [B set?]) function?]{
A function @italic{A×B → B×A} that swaps the order of components.}

@defproc[(reverse-cartesian-product [X set?] ...) function?]{
A function from @racket[(× X ...)] to the reversed product @racket[(× (reverse X) ...)].}
