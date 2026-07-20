#lang racket

(require rackunit
         rackunit/text-ui
         "finite-set-theory.rkt"
         "function.rkt")

;; ---------- helpers ----------

(define (same-function? f g)
  (and (equal? (function-src f) (function-src g))
       (equal? (function-tgt f) (function-tgt g))
       (for/and ([a (in-set (function-src f))])
         (equal? ((function-proc f) a)
                 ((function-proc g) a)))))

;; compare function graphs as *sets* of pairs (order-insensitive)
(define (graph=? f expected-pairs)
  (set=? (list->set (function->fgraph f))
         (list->set expected-pairs)))

;; sample small carriers
(define A2 (set 'a1 'a2))
(define B2 (set 'b1 'b2))
(define C2 (set 'c1 'c2))
(define D2 (set 'd1 'd2))

;; bijection A2↔B2, monotone C2→D2
(define f-bij (function (λ (a) (if (equal? a 'a1) 'b1 'b2)) A2 B2))
(define g-mono (function (λ (c) (if (equal? c 'c1) 'd1 'd2)) C2 D2))

;; a many-to-one example: both a1,a2 ↦ b1
(define f-many (function (λ (a) 'b1) A2 B2))

;; two-state X,Y
(define X2 (set 'x1 'x2))
(define Y2 (set 'y1 'y2))
(define hXY (function (λ (x) (if (equal? x 'x1) 'y1 'y2)) X2 Y2))

;; ---------- suite: basic algebra (id/compose/cartesian) ----------
(define suite-algebra
  (test-suite
   "algebraic properties"
   (test-case "identity and compose"
     (define idA (identity-function A2))
     (define idB (identity-function B2))
     (define f (function (λ (a) (if (equal? a 'a1) 'b1 'b2)) A2 B2))
     ;; compose-functions returns (second ∘ first)
     (check-true (same-function? (compose-functions idA f) f)) ; f ∘ idA
     (check-true (same-function? (compose-functions f idB) f))) ; idB ∘ f
   (test-case "cartesian product shape/value"
     (define top (function-cartesian-product hXY f-bij)) ; X×A -> Y×B
     (define XA (function-src top))
     (define YB (function-tgt top))
     (check-equal? (set-count XA) (* (set-count X2) (set-count A2)))
     (check-equal? (set-count YB) (* (set-count Y2) (set-count B2)))
     (check-equal? ((function-proc top) (list 'x1 'a2)) (list 'y1 'b2))
     (check-equal? ((function-proc top) (list 'x2 'a1)) (list 'y2 'b1)))))

;; ---------- suite: exponential domain enumeration ----------
(define suite-exponential
  (test-suite
   "exponential g^f domain enumeration"
   (test-case "bijective f : all alphas allowed; constants included"
     (define g^f (commuting-square-function f-bij g-mono #:as-squares? #t))
     (define dom (function-src g^f))
     (check-true (not (set-empty? dom)))
     ;; constant alpha to c1 must exist
     (check-true
      (for/or ([e (in-set dom)])
        (and (commuting-square? e)
             (graph=? (commuting-square-left e)
                      '((a1 c1) (a2 c1))))))
     ;; constant alpha to c2 must exist
     (check-true
      (for/or ([e (in-set dom)])
        (and (commuting-square? e)
             (graph=? (commuting-square-left e)
                      '((a1 c2) (a2 c2)))))))
   (test-case "many-to-one f : alpha must be fiber-constant"
     (define g^f (commuting-square-function f-many g-mono #:as-squares? #t))
     (define dom (function-src g^f))
     ;; any alpha where g∘alpha differs on a1,a2 should be absent
     (define bad-alpha
       (function (λ (a) (if (equal? a 'a1) 'c1 'c2)) A2 C2))
     (check-false
      (for/or ([e (in-set dom)])
        (and (commuting-square? e)
             (set=? (list->set (function->fgraph (commuting-square-left e)))
                    (list->set (function->fgraph bad-alpha))))))
     ;; constant alpha is allowed
     (check-true
      (for/or ([e (in-set dom)])
        (and (commuting-square? e)
             (graph=? (commuting-square-left e)
                      '((a1 c1) (a2 c1)))))))))

;; ---------- suite: curry / uncurry roundtrip ----------
(define suite-curry-uncurry
  (test-suite
   "curry/uncurry roundtrip"
   (test-case "build a square (h×f)⇒g and roundtrip"
     ;; Build S: (h×f) ⇒ g
     (define top (function-cartesian-product hXY f-bij))
     ;; α× uses A component; β× uses B component
     (define left
       (function (λ (xa) (if (equal? (second xa) 'a1) 'c1 'c2))
                 (function-src top) C2))
     (define right
       (function (λ (yb) (if (equal? (second yb) 'b1) 'd1 'd2))
                 (function-tgt top) D2))
     (define S (commuting-square top left right g-mono))
     ;; Exponential built with square domain
     (define g^f (commuting-square-function f-bij g-mono #:as-squares? #t))
     (define curry (curry-commuting-square-function g^f))
     (define T (curry S))
     (check-true (commuting-square? T))
     ;; Natural square: g^f ∘ χ0 = χ1 ∘ h  (pointwise over X)
     (define χ0 (commuting-square-left  T))
     (define χ1 (commuting-square-right T))
     (define h  (commuting-square-top   T))
     (for ([x (in-set X2)])
       (check-true
        (let ([lhs ((function-proc g^f) ((function-proc χ0) x))]
              [rhs ((function-proc χ1) ((function-proc h) x))])
          (equal? lhs rhs))))
     ;; Uncurry back
     (define uncurry (uncurry-commuting-square-function g^f))
     (define S* (uncurry T))
     (check-true (commuting-square? S*))
     ;; Check the top shape and a couple values
     (define top* (commuting-square-top S*))
     (check-equal? ((function-proc top*) (list 'x1 'a2)) (list 'y1 'b2))
     (check-equal? ((function-proc top*) (list 'x2 'a1)) (list 'y2 'b1)))))

;; ---------- suite: edge carriers ----------
(define suite-edges
  (test-suite
   "edge carriers"
   (test-case "empty A"
     (define A0 (set))
     (define B1 (set 'b))
     (define C1 (set 'c))
     (define D1 (set 'd))
     (define f0 (function (λ (a) 'b) A0 B1))
     (define g1 (function (λ (c) 'd) C1 D1))
     (define g^f (commuting-square-function f0 g1 #:as-squares? #t))
     (check-true (function? g^f))
     ;; Dom should have at least one (vacuously commuting) element
     (check-true (not (set-empty? (function-src g^f)))))
   (test-case "singleton carriers"
     (define A1 (set 'a))
     (define B1 (set 'b))
     (define C1 (set 'c))
     (define D1 (set 'd))
     (define f (function (λ (a) 'b) A1 B1))
     (define g (function (λ (c) 'd) C1 D1))
     (define g^f (commuting-square-function f g #:as-squares? #t))
     (define dom (function-src g^f))
     (check-equal? (set-count dom) 1)
     (define S (set-first dom))
     (check-true (commuting-square? S)))))

;; ---------- suite: error surfaces (sanity) ----------
(define suite-errors
  (test-suite
   "error surfaces"
   (test-case "curry expects a commuting-square"
     (define g^f (commuting-square-function f-bij g-mono #:as-squares? #t))
     (check-exn
      (λ (e) (and (exn:fail? e)
                  (regexp-match? #rx"commuting-square" (exn-message e))))
      (λ () ((curry-commuting-square-function g^f) 42))))
   (test-case "uncurry expects g^f with square domain"
     (define g^f-pairs (commuting-square-function f-bij g-mono #:as-squares? #f))
     (check-exn
      (λ (e) (and (exn:fail? e)
                  (regexp-match? #rx"#:as-squares\\?\\s*#t" (exn-message e))))
      (λ () (uncurry-commuting-square-function g^f-pairs))))))

;; ---------- aggregate runner ----------
(define all-tests
  (test-suite
   "function.rkt — extended"
   suite-algebra
   suite-exponential
   suite-curry-uncurry
   suite-edges
   suite-errors))

(module+ main
  (run-tests all-tests))
