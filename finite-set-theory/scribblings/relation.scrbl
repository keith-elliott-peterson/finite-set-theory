#lang scribble/manual

@(require scribble/eval
          racket/sandbox
          (for-label racket/base
                     racket/set
                     finite-set-theory/relation))

@title{Relation API}

@defmodule[finite-set-theory/relation]
@declare-exporting[finite-set-theory/relation]

@(define the-eval (make-base-eval))
@(the-eval '(require racket/base
                     racket/set
                     finite-set-theory/relation))

@section{Constructors and Predicates}

@defproc[(relation [pred procedure?] [src set?] [tgt set?]) relation?]{
Construct a relation from @racket[src] to @racket[tgt] given a predicate
@racket[pred] on pairs.}

@defproc[(relation? [v any/c]) boolean?]{Recognizes relation values.}

@defproc[(relation-src [R relation?]) set?]{The source set of @racket[R].}
@defproc[(relation-tgt [R relation?]) set?]{The target set of @racket[R].}

@examples[#:eval the-eval
  (define A (set 'a 'b))
  (define B (set 'x 'y))
  (define R (relation (λ (x y) (equal? x 'a)) A B))
  (relation? R)
  (relation-src R)
  (relation-tgt R)
]