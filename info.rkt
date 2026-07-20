#lang info

;; multi-collection: code + docs live in sibling directories
(define collection "multi")

;; runtime deps for your code
(define deps '("base"))

;; build deps for docs
(define build-deps '("scribble-lib" "racket-doc" "scribble-doc"))

;; register the main manual; minimal, correct shape
(define scribblings
  '(("scribblings/finite-set-theory.scrbl")))
