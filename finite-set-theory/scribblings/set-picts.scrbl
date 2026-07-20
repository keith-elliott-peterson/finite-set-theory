#lang scribble/manual
@(require scribble/eval
          (for-label racket
                     pict pict-abbrevs
                     racket/set
                     (file "../finite-set-theory.rkt")
                     (file "../function.rkt")
                     (file "../set-picts.rkt")))

@title{Set Picts: Finite-set diagrams and function drawings}
@author{Keith Elliott Peterson}

@defmodule[(file "../set-picts.rkt")]

@(define ev (make-base-eval))
@(ev '(require racket/set
               (file "../finite-set-theory.rkt")
               (file "../function.rkt")
               (file "../set-picts.rkt")))

@section{Overview}

Utilities to draw finite sets, functions, chains of composable functions, and the
Cartesian product grid with projections — all using @racketmodname[pict].
Angles are in radians. Elements are ordinary Racket symbols; pairs/tuples are lists.

@examples[#:eval ev
(define A (list->set '(a b c)))
(define B (list->set '(x y)))
(values (set-count A) (set-count B))
]


@section{Basic set drawings}

@defproc[(dot-list [xs (listof any/c)]) (listof pict?)]{
Turn a (sorted) list of elements into a list of element-dot picts you can pin to.}

@defproc[(set-drawer [dots (listof pict?)]) pict?]{
Lay out a list of element dots as a tidy vertical stack.}

@examples[#:eval ev
(define dotsA (dot-list '(a b c)))
(set-drawer dotsA)
]


@section{Drawing a single function}

@defproc[(function-drawer
          [f function?]
          [#:distance-between d exact-nonnegative-integer? 160]
          [#:scale-in scli any/c 1]
          [#:scale-out sclo any/c 1]
          [#:use-as-input-dot-list  in-dots (or/c #f (listof pict?)) #f]
          [#:use-as-output-dot-list out-dots (or/c #f (listof pict?)) #f]
          [#:use-as-input-pict  in-p  (or/c #f pict?) #f]
          [#:use-as-output-pict out-p (or/c #f pict?) #f]
          [#:src-finder src (-> pict? real? real?)]
          [#:tgt-finder tgt (-> pict? real? real?)]
          [#:start-angle θ (or/c #f real?) #f]
          [#:end-angle   φ (or/c #f real?) #f]
          [#:appender app (-> pict? pict? pict?) hc-append])
         pict?]{
Draw a function @racket[f : A → B] as two stacks (source and target) with curved
arrow fibres. Supply your own dot lists or picts to stabilise layouts across draws.
By default, finder functions place arrows at right/left centres.}

@examples[#:eval ev
(define f (function (λ (u) (if (member u '(a b)) 'x 'y)) A B))
(function-drawer f)                               ; default bends
(function-drawer f #:start-angle 0.3 #:end-angle 0) ; mild bend
]


@defproc[(function-drawer/highlight
          [f function?] [y any/c]
          [#:distance-between d exact-nonnegative-integer? 160]
          [#:thick w real? 2]
          [#:start-angle θ (or/c #f real?) #f]
          [#:use-as-input-dot-list  in-dots (or/c #f (listof pict?)) #f]
          [#:use-as-output-dot-list out-dots (or/c #f (listof pict?)) #f])
         pict?]{
Draw @racket[f] and overdraw only the fibre landing at @racket[y] thicker.}

@examples[#:eval ev
(function-drawer/highlight f 'y #:start-angle -0.35)
]


@section{Chains of composable functions}

@defproc[(composable-function-drawer
          [f function?] [fs function?] ...
          [#:distance-between d exact-nonnegative-integer? 160]
          [#:scale-in scli any/c 1]
          [#:scale-out sclo any/c 1]
          [#:use-as-input-dot-list  in-dots (or/c #f (listof pict?)) #f]
          [#:use-as-output-dot-list out-dots (or/c #f (listof pict?)) #f]
          [#:use-as-input-pict  in-p  (or/c #f pict?) #f]
          [#:use-as-output-pict out-p (or/c #f pict?) #f]
          [#:src-finder src (-> pict? real? real?)]
          [#:tgt-finder tgt (-> pict? real? real?)]
          [#:start-angle θ (or/c #f real?) #f]
          [#:end-angle   φ (or/c #f real?) #f]
          [#:appender app (-> pict? pict? pict?) hc-append])
         pict?]{
Draw a left-to-right chain @racket[f, g, h, …] (checking composability) with
stable dot ordering so layouts don’t jitter.}

@examples[#:eval ev
(define Γ (list->set '(α β)))
(define g (function (λ (v) (case v [((x)) 'α] [else 'β])) B Γ))
(define Δ (list->set '(0 1)))
(define h (function (λ (w) (if (equal? w 'α) 1 0)) Γ Δ))
(composable-function-drawer f g h #:start-angle -0.3)
]


@defproc[(draw-chain+composite
          [f function?] [fs function?] ...
          [#:distance-between d exact-nonnegative-integer? 160]
          [#:start-angle θ (or/c #f real?) #f])
         (values pict? pict?)]{
Return two picts: the full chain, and its single-step composite (laid out with
the same dot ordering).}

@examples[#:eval ev
(define-values (chain composite)
  (draw-chain+composite f g #:start-angle -0.25))
chain
composite
]


@section{Cartesian product grid with projections}

@defproc[(cartesian-product-drawer
          [A set?] [B set?]
          [#:cell-gap   gap exact-nonnegative-integer? 18]
          [#:cell-pad-x px  exact-nonnegative-integer? 8]
          [#:cell-pad-y py  exact-nonnegative-integer? 6]
          [#:render     render (or/c 'text 'dot) 'text]
          [#:dot-diameter dot-d exact-positive-integer? 6]
          [#:pair->string pair->str (-> any/c any/c string?)
                         (λ (a b) (format "(~a, ~a)" a b))]
          [#:angle      ang real? (- (/ pi 4))]       ; rotate 45° clockwise
          [#:bg?        bg? boolean? #t]
          [#:bg-border? bgb? boolean? #t]
          [#:bg-x-margin bx exact-nonnegative-integer? 10]
          [#:bg-y-margin by exact-nonnegative-integer? 10]
          [#:h-gap      hgap exact-nonnegative-integer? 90]
          [#:v-gap      vgap exact-nonnegative-integer? 28]
          [#:show-projections? show? boolean? #t]
          [#:swap-projections? swap-proj? boolean? #f] ; if #t: A on top, B below
          [#:swap-rows-cols?  swap-rc? boolean? #f]   ; visual grid swap
          [#:start-angle-B θB real? (/ pi 4)]         ; to B (top by default)
          [#:end-angle-B   φB real? 0]
          [#:start-angle-A θA real? (- (/ pi 4))]     ; to A (bottom by default)
          [#:end-angle-A   φA real? 0]
          [#:fan-B   fanB real? 0.08]                 ; per A-index into B
          [#:fan-A   fanA real? 0.08]                 ; per B-index into A
          [#:line-w  lw   real? 2]
          [#:highlight?   hi? (or/c #f (-> any/c any/c any/c)) #f]
          [#:highlight-B? hiB? (or/c #f (-> any/c any/c any/c)) #f]
          [#:highlight-A? hiA? (or/c #f (-> any/c any/c any/c)) #f]
          [#:hi-line-w hiw real? 3]
          [#:show-proj-labels? labels? boolean? #t])
         pict?]{
Draw the @racket[A × B] grid (rotated) on the left, two projection stacks on
the right (B on top, A below by default), and arrow bundles from each pair to
its projections. Two-pass rendering prevents accidental “bold” overlaps. The
per-projection highlight predicates only affect their own bundles.}

@subsection{Quick uses}

@examples[#:eval ev
;; default: 45° bends, B on top
(cartesian-product-drawer A B)

;; straighter arrows + small fan to separate bundles
(cartesian-product-drawer A B
  #:start-angle-B 0.30 #:start-angle-A -0.30
  #:fan-A 0.06 #:fan-B 0.06)

;; highlight only the fibre over 'y (to B)
(cartesian-product-drawer A B
  #:highlight-B? (λ (_a b) (eq? b 'y)))

;; hide projections (just the grid)
(cartesian-product-drawer A B #:show-projections? #f)

;; swap rows/cols in the grid (visual)
(cartesian-product-drawer A B #:swap-rows-cols? #t)

;; render grid cells as dots instead of text
(cartesian-product-drawer A B #:render 'dot #:dot-diameter 7)
]

@subsection{Tuning notes}

- @racket[#:fan-A] and @racket[#:fan-B] add a small index-based offset to
  starting angles so arrowheads don’t stack on top of each other.
- @racket[#:start-angle-*] are source-side bends; @racket[#:end-angle-*] are
  target-side; zero gives straight lines.
- Keep @racket[A]/@racket[B] sorted (e.g., symbols) if you want stable layouts
  between runs — the drawer already sorts elements for you.


@section{Troubleshooting}

- If text looks cramped, increase @racket[#:cell-pad-x] / @racket[#:cell-pad-y]
  or the background margins.
- If bundles hit the grid border, bump @racket[#:h-gap] or margins.
- To force a particular ordering across multiple drawings, pass your own
  @racket[#:use-as-input-dot-list] / @racket[#:use-as-output-dot-list] to
  @racket[function-drawer] (and reuse them).
