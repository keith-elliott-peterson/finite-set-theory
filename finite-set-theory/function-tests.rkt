#lang racket
(require rackunit
         racket/set
         "finite-set-theory.rkt"
         "function.rkt")

;; Helpers
(define (apply-f f x) ((function-proc f) x))

;; ---------- Constructor & basic predicates ----------
(module+ test
  (let ()
    (define A (set 1 2 3))
    (define B (set 'a 'b 'c))
    (define f (function (λ (x) (vector-ref #(a b c) (sub1 x))) A B))

    (test-true "function? recognizes function" (function? f))
    (test-equal? "function-src" (function-src f) A)
    (test-equal? "function-tgt" (function-tgt f) B)
    (test-equal? "function application" (apply-f f 1) 'a)

    (check-exn
     (λ (e) (and (exn:fail:contract? e)
                 (regexp-match #rx"expected the src to be a set" (exn-message e))))
     (λ () (function (λ (x) x) 42 B)))

    (check-exn
     (λ (e) (and (exn:fail:contract? e)
                 (regexp-match #rx"expected the tgt to be a set" (exn-message e))))
     (λ () (function (λ (x) x) A 42)))

    (check-exn
     (λ (e) (and (exn:fail:contract? e)
                 (regexp-match #rx"does not map every element" (exn-message e))))
     (λ () (function (λ (x) 999) A B)))))

;; ---------- identity-function ----------
(module+ test
  (let ()
    (define X (set "x" "y"))
    (define idX (identity-function X))
    (test-true "id is function" (function? idX))
    (test-equal? "id src" (function-src idX) X)
    (test-equal? "id tgt" (function-tgt idX) X)
    (for ([x X]) (test-equal? "id acts as identity" ((function-proc idX) x) x))

    (check-exn
     (λ (e) (and (exn:fail:contract? e)
                 (regexp-match #rx"expected a set" (exn-message e))))
     (λ () (identity-function #f)))))

;; ---------- compose-functions ----------
(module+ test
  (let ()
    (define A (set 1 2 3))
    (define C (set 10 20 30))
    (define g (function (λ (x) (* 10 x)) A C))            ; 1→10, 2→20, 3→30
    (define comp1 (compose-functions (identity-function A) g)) ; should equal g
    (for ([x A])
      (test-equal? "compose with idA" ((function-proc comp1) x) ((function-proc g) x)))

    (check-exn
     (λ (e) (and (exn:fail:contract? e)))
     (λ () (compose-functions 1 2 3)))))

;; ---------- function-disjoint-union ----------
(module+ test
  (let ()
    (define A1 (set 'p 'q))
    (define B1 (set 0 1))
    (define f1 (function (λ (x) (if (eq? x 'p) 0 1)) A1 B1))

    (define A2 (set #t #f))
    (define B2 (set 'T 'F))
    (define f2 (function (λ (x) (if x 'T 'F)) A2 B2))

    (define f+g (function-disjoint-union f1 f2))

    ;; Inputs to the disjoint union function are tagged pairs like (list i x) or vectors.
    (test-equal? "⊔ on left component"
                 ((function-proc f+g) (list 0 'p))
                 (list 0 0))
    (test-equal? "⊔ on right component"
                 ((function-proc f+g) (list 1 #t))
                 (list 1 'T))

    (check-exn
     (λ (e) (and (exn:fail:contract? e)
                 (regexp-match #rx"expected at least one function" (exn-message e))))
     (λ () (function-disjoint-union)))

    (check-exn
     (λ (e) (and (exn:fail:contract? e)))
     (λ () (function-disjoint-union 42)))))

;; ---------- equalizer / pushout (smoke tests) ----------
(module+ test
  (let ()
    ;; Use id_A ⇒ id_A so squares are just endofunctions on A
    (define A (set 0 1 2))
    (define idA (identity-function A))

    ;; Two different endofunctions on A to define two parallel squares
    (define fL (function (λ (x) (if (zero? x) 0 1)) A A))
    (define gL (function (λ (x) (if (= x 2) 0 1)) A A))

    (define S1 (commuting-square idA fL fL idA))
    (define S2 (commuting-square idA gL gL idA))

    ;; function-equalizer returns a single function EqA → EqB
    (define eq-inc (function-equalizer idA idA S1 S2))
    (define eq-set (function-src eq-inc))

    (test-true "equalizer returns a function and a set"
               (and (function? eq-inc) (set? eq-set)))

    ;; All x in eq-set satisfy fL x = gL x
    (for ([x eq-set])
      (test-equal? "equalized points agree (left legs)"
                   ((function-proc fL) x)
                   ((function-proc gL) x)))

    ;; Pushout smoke test (build real commuting squares; use k=2 to avoid 1-leg chain edge-case)
    (let ()
      (define A (set 0 1 2))
      (define B (set 'z 'o))
      (define C (set 'L 'R))
      (define D (set 'L 'R))

      (define fpo (function (λ (x) (if (zero? x) 'z 'o)) A B)) ; A→B

      ;; Square 1: maps 'z ↦ 'L, 'o ↦ 'R so h1∘f = k1∘g1
      (define g1  (function (λ (x) (if (zero? x) 'L 'R)) A C)) ; A→C
      (define k1  (function (λ (c) c) C D))                    ; C→D (id)
      (define h1  (function (λ (b) (if (eq? b 'z) 'L 'R)) B D)) ; B→D
      (define S1  (commuting-square fpo g1 h1 k1))

      ;; Square 2: constant 'R everywhere so h2∘f = k2∘g2
      (define g2  (function (λ (x) 'R) A C))                   ; A→C
      (define k2  (function (λ (c) c) C D))                    ; C→D (id)
      (define h2  (function (λ (b) 'R) B D))                   ; B→D
      (define S2  (commuting-square fpo g2 h2 k2))

      (define po (function-pushout fpo S1 S2))
      (test-true "pushout returns a function" (function? po))
      (test-true "pushout src/tgt are sets"
                 (and (set? (function-src po)) (set? (function-tgt po)))))

    )

;; Pushout test (duplicate the square so k=2)
(let ()
  (define A (set 0 1 2))
  (define B (set 'z 'o))
  (define C (set 'L 'R))
  (define D (set 'L 'R))

  (define f (function (λ (x) (if (zero? x) 'z 'o)) A B)) ; A→B
  (define g (function (λ (x) (if (zero? x) 'L 'R)) A C)) ; A→C
  (define h (function (λ (b) (if (eq? b 'z) 'L 'R)) B D)) ; B→D
  (define k (function (λ (c) c) C D))                    ; C→D (id)

  (define S1 (commuting-square f g h k))
  (define S2 (commuting-square f g h k))                 ; duplicate → k=2

  (define po (function-pushout f S1 S2))
  (test-true "pushout returns a function" (function? po))
  (test-true "pushout src/tgt are sets"
             (and (set? (function-src po)) (set? (function-tgt po)))))

  ;; (Optional) Verify the error branch when you misuse the API
  (let ()
    (define AA (set 0 1))
    (define BB (set 'z 'o))
    (define CC (set 'L 'R))
    (define f (function (λ (x) (if (zero? x) 'z 'o)) AA BB))
    (define g (function (λ (x) (if (zero? x) 'L 'R)) AA CC))
    (check-exn
     (λ (e) (regexp-match #rx"expected exactly one top function" (exn-message e)))
     (λ () (function-pushout f g))))
  )


;; ---------- curry/uncurry commuting square (roundtrip smoke) ----------
(module+ test
  (let ()
    ;; Objects for g^f
    (define A (set 'a1 'a2))
    (define B (set 'b1 'b2))
    (define C (set 'c1 'c2))
    (define D (set 'd1 'd2))

    ;; f : A→B, g : C→D
    (define f (function (λ (a) (if (equal? a 'a1) 'b1 'b2)) A B))
    (define g (function (λ (c) (if (equal? c 'c1) 'd1 'd2)) C D))

    ;; Exponential g^f; domain wants commuting-square structs
    (define sqfunc (commuting-square-function f g #:as-squares? #t))

    ;; Build S : (h×f) ⇒ g
    (define X (set 'x1 'x2))
    (define Y (set 'y1 'y2))
    (define h (function (λ (x) 'y1) X Y))                         ; X→Y

    (define top   (function-cartesian-product h f))               ; X×A → Y×B
    (define left  (function (λ (xa) 'c1) (function-src top) C))   ; X×A → C
    (define right (function (λ (yb) 'd1) (function-tgt top) D))   ; Y×B → D

    (define S (commuting-square top left right g))

    ;; Curry: (h×f) ⇒ g  ↦  h ⇒ g^f
    (define χ  (curry-commuting-square-function sqfunc))
    (define T  (χ S))
    (test-true "curry produced a commuting-square" (commuting-square? T))

    ;; Uncurry: h ⇒ g^f  ↦  (h×f) ⇒ g
    (define ϒ  (uncurry-commuting-square-function sqfunc))
    (define S* (ϒ T))
    (test-true "uncurry produced a commuting-square" (commuting-square? S*))))

;; Run
(module+ main
  (require rackunit/text-ui)
  (run-tests))
