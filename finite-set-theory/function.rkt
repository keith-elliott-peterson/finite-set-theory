#lang racket
(require racket/lazy-require racket/format)
(lazy-require ["finite-set-theory.rkt"
               (map-set
                set-cartesian-product
                set-equalizer
                set-pullback
                set-disjoint-union
                set-coequalizer
                set-pushout
                function-set
                curry-function-set
                uncurry-function-set
                function->fgraph
                ensure-set
                ensure-nonempty-set
                ensure-boolean
                ensure-procedure
                ensure-function*
                ensure-relation*)]
              
              ["relation.rkt" (relation-proc
                               relation-src
                               relation-tgt)])

;; --------------------
;; Debug printers / preview helpers
;; --------------------
(define (preview-set s [n 4])
  (for/list ([e s] [i (in-naturals)] #:break (>= i n)) e))

(define (describe-function f [k 3])
  (cond
    [(not (function? f)) (list 'not-a-function f)]
    [else
     (list 'function
           (list 'src-count (set-count (function-src f)))
           (list 'tgt-count (set-count (function-tgt f)))
           (list 'graph-sample
                 (for/list ([p (function->fgraph f)] [i (in-naturals)] #:break (>= i k)) p)))]))

(define (describe-square S [k 2])
  (cond
    [(not (commuting-square? S)) (list 'not-a-square S)]
    [else
     (list 'commuting-square
           (list 'top    (describe-function (commuting-square-top S)    k))
           (list 'left   (describe-function (commuting-square-left S)   k))
           (list 'right  (describe-function (commuting-square-right S)  k))
           (list 'bottom (describe-function (commuting-square-bottom S) k)))]))

;; Small raiser with context
(define (raise-domain-mismatch who dom sample-count α β)
  (raise-arguments-error
   who
   "pair (alpha, beta) is not an element of the domain of g^f"
   "alpha" (describe-function α)
   "beta"  (describe-function β)
   "domain-sample"
   (for/list ([e (in-set dom)] [i (in-naturals)] #:break (>= i sample-count))
     (if (commuting-square? e)
         (list 'alpha (describe-function (commuting-square-left  e))
               'beta  (describe-function (commuting-square-right e)))
         (list 'alpha (describe-function (car e))
               'beta  (describe-function (cdr e)))))
   "hint"
   "Build domain elements from the same function-set enumerations (extensional equality isn’t structural). Use canonicalization or #:as-squares? #t."))


(struct function (proc src tgt)
  #:transparent
  #:guard
  (λ (proc src tgt this)
    (cond [(not (set? src))
           (raise-arguments-error 'function (format "expected the src to be a set. Given: ~a" src))]
          [(not (set? tgt))
           (raise-arguments-error 'function (format "expected the tgt to be a set. Given: ~a" tgt))]
          [(not (for/and ([x src])
                  (for/or ([y tgt])
                    (equal? (proc x) y))))
           (raise-arguments-error 'function (format "Procedure ~a does not map every element of ~a to an element of ~a" proc src tgt))]
          [else
           (values proc src tgt)]))
  #:methods gen:equal+hash
  [(define equal-proc
     (λ (func1 func2 rec-equal?)
       (and (set=? (function-src func1)
                   (function-src func2))
            (set=? (function-tgt func1)
                   (function-tgt func2))
            (for/and ([i (in-set (function-src func1))])
              (equal? ((function-proc func1) i)
                      ((function-proc func2) i))))))
   (define hash-proc
     (λ (func recur-equal-hash)
       (+ (set-count (function-src func))
          (set-count (function-tgt func)))))
   (define hash2-proc
     (λ (func recur-equal-hash)
       (+ (set-count (function-src func))
          (set-count (function-tgt func)))))]
  #:property prop:procedure
  (λ (f x)
    (cond [(set-member? (function-src f) x)
           ((function-proc f) x)]
          [(subset? x (function-src f))
           (for/set ([i x])
             ((function-proc f) i))]
          [else
           (raise-arguments-error 'function "internal error")])))

(define (function-from? func st)
  (set=? (function-src func) st))

(define (function-to? func st)
  (set=? (function-tgt func) st))

(define (function-from-to? func st1 st2)
  (and (function-from? func st1)
       (function-to? func st2)))

(define (compose-functions . funcs)
  (if (ormap (compose not function?) funcs)
      (apply raise-arguments-error
             'compose-functions
             "The following arguments are not functions,"
             (flatten (map cons
                           (map (compose (λ(x)(string-append "Position " x)) ~a add1)
                                (indexes-where funcs (compose not function?)))
                           (filter-not function? funcs))))
      (foldl
       (λ (x y)
         (cond [(not (set=? (function-tgt y)
                            (function-src x)))
                (raise-arguments-error 'compose-functions (format "expected the target of ~a, to match the source of ~a, given ~a as target and ~a as source instead."
                       y x (function-tgt y))(function-src x))]
               [(equal? y (function identity (function-src x)(function-src x)))
                x]
               [(equal? x (function identity (function-tgt y)(function-tgt y)))
                y]
               [else (function (compose1 (function-proc x)(function-proc y))
                               (function-src y)
                               (function-tgt x))]))
       (first funcs)(rest funcs))))

(define (identity-function st)
  (unless (set? st)
    (raise-arguments-error 'identity-function (format "expected a set, given: ~a" st)))
  (function identity st st))

(define (relation->function rel)
  (function (relation-proc rel)
            (set-cartesian-product
             (relation-src rel)
             (relation-tgt rel))
            (set #t #f)))

;; -----------------------------------------------------------------------------
;; function-disjoint-union : (Listof function?) -> function?
;; Given f_i : A_i -> B_i, produce ⨿_i f_i : (⨿_i A_i) -> (⨿_i B_i).
;; Calling styles accepted for the underlying procedure:
;;   - one tuple as a list:    (list i x)
;;   - one tuple as a vector:  (vector i x)
;;   - two separate args:      i x
;; Returns a list '(i y).
;; -----------------------------------------------------------------------------

(define (function-disjoint-union . funcs)
  (when (null? funcs)
    (raise-arguments-error 'function-disjoint-union "expected at least one function"))

  ;; Validate inputs are functions
  (for ([f (in-list funcs)] [i (in-naturals 1)])
    (unless (function? f)
      (raise-argument-error 'function-disjoint-union "function?" i f)))

  (define n (length funcs))
  (define srcs (map function-src funcs))
  (define tgts (map function-tgt funcs))

  ;; Build disjoint-union source/target sets with your finite-set helpers
  (define dis-src (apply set-disjoint-union srcs))
  (define dis-tgt (apply set-disjoint-union tgts))

  ;; Normalize inputs: accept (i x), '(i x), or #(i x)
  (define (->ix args)
    (cond
      [(= (length args) 2)
       (values (first args) (second args))]
      [(= (length args) 1)
       (define t (car args))
       (cond
         [(list? t)
          (unless (= (length t) 2)
            (raise-arguments-error 'function-disjoint-union
                                   "tuple arity mismatch" "expected" 2 "got" (length t)))
          (values (first t) (second t))]
         [(vector? t)
          (unless (= (vector-length t) 2)
            (raise-arguments-error 'function-disjoint-union
                                   "tuple arity mismatch" "expected" 2 "got" (vector-length t)))
          (values (vector-ref t 0) (vector-ref t 1))]
         [else
          (raise-arguments-error 'function-disjoint-union
                                 "expected either two args (i x) or one tuple (list/vector)"
                                 "got" t)])]
      [else
       (raise-arguments-error 'function-disjoint-union
                              "expected either two args (i x) or one tuple (list/vector)"
                              "arg-count" (length args))]))

  ;; The actual coproduct map
  (define proc*
    (λ args
      (define-values (i x) (->ix args))

      ;; tag checks
      (unless (and (integer? i) (<= 0 i) (< i n))
        (raise-arguments-error 'function-disjoint-union
                               "invalid summand index"
                               "index" i "valid-range" (format "[0..~a]" (sub1 n))))

      ;; domain membership check (per-summand)
      (define Ai (list-ref srcs i))
      (unless (set-member? Ai x)
        (raise-arguments-error 'function-disjoint-union
                               "element not in the i-th source summand"
                               "index" i "element" x))

      ;; apply the i-th function
      (define fi (list-ref funcs i))
      (define y ((function-proc fi) x))
      (define out (list i y))

      ;; codomain membership check (per-summand)
      (define Bi (list-ref tgts i))
      (unless (set-member? Bi y)
        (raise-arguments-error 'function-disjoint-union
                               "image not in the i-th target summand"
                               "index" i "image" y))

      ;; optional global membership sanity (cheap for finite sets)
      (unless (set-member? dis-src (list i x))
        (raise-arguments-error 'function-disjoint-union (format "internal: ~(~a~) not in disjoint source set" (list i x))))
      (unless (set-member? dis-tgt out)
        (raise-arguments-error 'function-disjoint-union (format "internal: ~(~a~) not in disjoint target set" out)))

      out))

  (function proc* dis-src dis-tgt))

;; -----------------------------------------------------------------------------
;; function-coequalizer : function? function? (listof commuting-square?) -> function?
;; Given func1 : A -> B, func2 : C -> D, and parallel morphisms (squares) from func1 to func2,
;; build the pointwise coequalizer in Set^{->}:
;;   e0 : C -> C/~  (coeq of the left legs A -> C)
;;   e1 : D -> D/≈  (coeq of the right legs B -> D)
;;   ḡ : C/~ -> D/≈ induced by func2, with e1 ∘ func2 = ḡ ∘ e0
;; Returns the arrow ḡ as a `function` struct with src C/~ and tgt D/≈.
;; Your set-coequalizer represents classes as flattened lists with '∼ between witnesses,
;; and keeps untouched elements of the codomain as themselves; we respect that encoding.
;; -----------------------------------------------------------------------------

(define (function-coequalizer func1 func2 . sqrs)
  ;; basic checks
  (unless (function? func1)
    (raise-argument-error 'function-coequalizer "function?" 0 func1))
  (unless (function? func2)
    (raise-argument-error 'function-coequalizer "function?" 1 func2))
  (when (null? sqrs)
    (raise-arguments-error 'function-coequalizer "expected at least one commuting-square"))

  (define A (function-src func1))
  (define B (function-tgt func1))
  (define C (function-src func2))
  (define D (function-tgt func2))

  ;; validate the squares and extract legs
  (define left-legs
    (for/list ([s (in-list sqrs)] [i (in-naturals 2)])
      (unless (commuting-square? s)
        (raise-argument-error 'function-coequalizer "commuting-square?" i s))
      (define f-top (commuting-square-top s))
      (define k-bot (commuting-square-bottom s))
      (unless (equal? f-top func1)
        (raise-arguments-error 'function-coequalizer
                               "square does not target the given top arrow (func1)"
                               "expected-top" func1 "got" f-top))
      (unless (equal? k-bot func2)
        (raise-arguments-error 'function-coequalizer
                               "square does not target the given bottom arrow (func2)"
                               "expected-bottom" func2 "got" k-bot))
      (define g-left (commuting-square-left s)) ; A -> C
      ;; sanity: sources/targets match
      (unless (and (set=? (function-src g-left) A)
                   (set=? (function-tgt g-left) C))
        (raise-arguments-error 'function-coequalizer
                               "left leg has wrong type"
                               "src(g-left)" (function-src g-left) "tgt(g-left)" (function-tgt g-left)
                               "expected-src" A "expected-tgt" C))
      g-left))

  (define right-legs
    (for/list ([s (in-list sqrs)])
      (define h-right (commuting-square-right s)) ; B -> D
      (unless (and (set=? (function-src h-right) B)
                   (set=? (function-tgt h-right) D))
        (raise-arguments-error 'function-coequalizer
                               "right leg has wrong type"
                               "src(h-right)" (function-src h-right) "tgt(h-right)" (function-tgt h-right)
                               "expected-src" B "expected-tgt" D))
      h-right))

  ;; coequalizers in Set at each component
  (define CoeqC
    (apply set-coequalizer
           A C
           (for/list ([g (in-list left-legs)])
             (λ (a) ((function-proc g) a)))))

  (define CoeqD
    (apply set-coequalizer
           B D
           (for/list ([h (in-list right-legs)])
             (λ (b) ((function-proc h) b)))))

  ;; induced map ḡ : CoeqC -> CoeqD, defined on representatives.
  ;; Respect your set-coequalizer encoding:
  ;;   - if x is a list like '(c1 ∼ c2 ∼ ...), map non-'∼ parts with func2 and re-insert '∼;
  ;;   - if x is an untouched element c in C, map to (g c).
  (define g (function-proc func2))
  (define (induced-map x)
    (cond
      [(list? x)
       (for/list ([t (in-list x)])
         (if (eq? t '∼) '∼ (g t)))]
      [(vector? x) ; be generous if someone passes a vector representative
       (for/list ([t (in-vector x)])
         (if (eq? t '∼) '∼ (g t)))]
      [else
       (g x)]))

  ;; (Optional) membership sanity; cheap for finite sets.
  (define proc*
    (λ (x)
      (unless (set-member? CoeqC x)
        (raise-arguments-error 'function-coequalizer
                               "input not in source coequalizer set" "value" x))
      (define y (induced-map x))
      (unless (set-member? CoeqD y)
        (raise-arguments-error 'function-coequalizer
                               "image not in target coequalizer set" "image" y))
      y))

  (function proc* CoeqC CoeqD))

;; -----------------------------------------------------------------------------
;; function-pushout : (list f S1 S2 ... Sk) -> function?
;; Arguments (order-insensitive, but must contain exactly one function and ≥1 squares):
;;   f    : A -> B
;;   Si   : (commuting-square f g_i h_i k_i)
;;
;; Result:
;;   F̂ :  PO(A --g_i--> C_i)  ->  PO(B --h_i--> D_i)
;;
;; Representation notes (matches set-pushout):
;;   - Elements coming from A or B appear as “chains” like '(c0 ∼ c1 ∼ ...).
;;   - Leftovers from C_i or D_i appear as tagged pairs '(i x).
;; -----------------------------------------------------------------------------
(define (function-pushout . sqrs-and-funcs)
  (define tops (filter function? sqrs-and-funcs))
  (define squares (filter commuting-square? sqrs-and-funcs))
  (when (not (= (length tops) 1))
    (raise-arguments-error 'function-pushout
                           "expected exactly one top function and ≥1 commuting-squares"))
  (when (null? squares)
    (raise-arguments-error 'function-pushout "expected at least one commuting-square"))

  (define f (car tops))
  (define A (function-src f))
  (define B (function-tgt f))

  ;; Extract legs, check tops match
  (define lefts  '()) ;; g_i : A -> C_i
  (define rights '()) ;; h_i : B -> D_i
  (define bottoms '()) ;; k_i : C_i -> D_i
  (for ([s (in-list squares)] [i (in-naturals 0)])
    (unless (equal? (commuting-square-top s) f)
      (raise-arguments-error 'function-pushout
                             "square’s top must equal the provided function"
                             "index" i "got-top" (commuting-square-top s)))
    (set! lefts   (append lefts   (list (commuting-square-left s))))
    (set! rights  (append rights  (list (commuting-square-right s))))
    (set! bottoms (append bottoms (list (commuting-square-bottom s)))))

  ;; Build pushout sets objectwise
  (define PO-left
    (apply set-pushout
           (append (list A)
                   (map (λ (g) (function-proc g)) lefts)
                   (map (λ (g) (function-tgt g)) lefts))))
  (define PO-right
    (apply set-pushout
           (append (list B)
                   (map (λ (h) (function-proc h)) rights)
                   (map (λ (h) (function-tgt h)) rights))))

  ;; Precompute (for deciding whether a D_i value is represented by a chain)
  (define right-procs (map function-proc rights))
  (define bottom-procs (map function-proc bottoms))
  (define images-of-h
    (for/list ([h rights])
      (for/set ([b (in-set B)]) ((function-proc h) b))))
  ;; For each i, map y ∈ D_i to a canonical chain produced by some b with h_i(b)=y
  (define (chain-for-b b)
    (add-between (for/list ([h rights]) ((function-proc h) b)) '∼))
  (define y->chain-by-i
    (for/list ([i (in-naturals 0)] [h rights])
      (define ht (make-hash))
      (for ([b (in-set B)])
        (hash-set! ht ((function-proc h) b) (chain-for-b b)))
      ht))

  ;; Map a left “chain” by applying the corresponding bottom k_i at each coordinate
  (define (map-left-chain lst)
    (let loop ([xs lst] [i 0] [acc '()])
      (cond
        [(null? xs) (reverse acc)]
        [else
         (define t (car xs))
         (if (eq? t '∼)
             (loop (cdr xs) i (cons '∼ acc))
             (let ([y ((list-ref bottom-procs i) t)])
               (loop (cdr xs) (add1 i) (cons y acc))))])))

  ;; Map a tagged leftover '(i x) via k_i; if image lands in Im(h_i),
  ;; return the corresponding chain; otherwise keep it tagged.
  (define (map-leftover i x)
    (define y ((list-ref bottom-procs i) x))
    (if (set-member? (list-ref images-of-h i) y)
        (hash-ref (list-ref y->chain-by-i i) y)
        (list i y)))

  ;; The induced arrow PO-left -> PO-right
  (define proc*
    (λ (z)
      (unless (set-member? PO-left z)
        (raise-arguments-error 'function-pushout
                               "input not in source pushout set" "value" z))
      (define image
        (cond
          [(list? z)
           (cond
             [(member '∼ z) (map-left-chain z)]                     ; chain
             [(and (= (length z) 2) (integer? (first z)))           ; tagged
              (map-leftover (first z) (second z))]
             [else (raise-arguments-error 'function-pushout (format "unexpected list form: ~v" z))])]
          [(vector? z)
           (define L (vector->list z))
           (if (member '∼ L)
               (map-left-chain L)
               (map-leftover (vector-ref z 0) (vector-ref z 1)))]
          [else
           (raise-arguments-error 'function-pushout (format "unexpected element form: ~v" z))]))
      (unless (set-member? PO-right image)
        (raise-arguments-error 'function-pushout
                               "image not in target pushout set" "image" image))
      image))

  (function proc* PO-left PO-right))




;; -----------------------------------------------------------------------------
;; function-cartesian-product : (Listof function?) -> function?
;; Given f_i : A_i -> B_i, produce Π_i f_i : (Π_i A_i) -> (Π_i B_i).
;; The resulting function's procedure accepts either:
;;   - a single tuple (list or vector) of arity N, or
;;   - N separate arguments (arg1 ... argN).
;; It returns a list of images (y1 ... yN).
;; -----------------------------------------------------------------------------

(define (function-cartesian-product . funcs)
  (cond
    [(null? funcs)
     (raise-argument-error 'function-cartesian-product
                           "at least one function"
                           0 funcs)]
    [else
     (for ([f funcs] [i (in-naturals)])
       (unless (function? f)
         (raise-argument-error 'function-cartesian-product
                               "function?"
                               i f)))

     (define srcs (map function-src funcs))
     (define tgts (map function-tgt funcs))

     ;; Build domain/codomain as cartesian products using your finite-set module
     (define prod-src (apply set-cartesian-product srcs))
     (define prod-tgt (apply set-cartesian-product tgts))

     ;; Helper: normalize incoming args to a list of length N
     (define (->tuple args n)
       (cond
         [(= (length args) n) args]                     ; passed N args
         [(= (length args) 1)
          (define x (car args))
          (cond
            [(list? x)
             (unless (= (length x) n)
               (raise-arguments-error 'function-cartesian-product (format "tuple arity mismatch: expected ~a, got ~a (list)"
                      n (length x))))
             x]
            [(vector? x)
             (unless (= (vector-length x) n)
               (raise-arguments-error 'function-cartesian-product (format "tuple arity mismatch: expected ~a, got ~a (vector)"
                      n (vector-length x))))
             (vector->list x)]
            [else
             (raise-arguments-error 'function-cartesian-product (format "expected a list/vector tuple or ~a separate arguments; got ~v"
                    n x))])]
         [else
          (raise-arguments-error 'function-cartesian-product (format "expected either ~a separate arguments or one list/vector; got ~a args"
                 n (length args)))]))

     ;; The actual mapping on product elements
     (define n (length funcs))
     (define proc*
       (λ args
         (define xs (->tuple args n))
         ;; Optional: domain membership check (cheap for finite sets; comment out if you prefer trusting callers)
         (unless (set-member? prod-src xs)
           (raise-arguments-error 'function-cartesian-product (format "input ~v not in product source set" xs)))
         (define ys
           (for/list ([f funcs] [x xs])
             ((function-proc f) x)))
         ;; Optional: codomain membership check
         (unless (set-member? prod-tgt ys)
           (raise-arguments-error 'function-cartesian-product (format "image ~v not in product target set" ys)))
         ys))

     (function proc* prod-src prod-tgt)]))

;; -----------------------------------------------------------------------------
;; function-equalizer : function? function? (listof commuting-square?) -> function?
;; Given func1 : A -> B, func2 : C -> D, and parallel morphisms (squares) S_i : func1 ⇒ func2,
;; build the equalizer in Set^{->} objectwise:
;;   EqA = Eq(g_i : A -> C)      ; equalizer of all left legs
;;   EqB = Eq(h_i : B -> D)      ; equalizer of all right legs
;;   ē  : EqA -> EqB             ; restriction of func1
;; Returns ē as a `function` struct with src EqA and tgt EqB.
;; -----------------------------------------------------------------------------
(define (function-equalizer func1 func2 . sqrs)
  (unless (function? func1)
    (raise-argument-error 'function-equalizer "function?" 0 func1))
  (unless (function? func2)
    (raise-argument-error 'function-equalizer "function?" 1 func2))
  (when (null? sqrs)
    (raise-arguments-error 'function-equalizer "expected at least one commuting-square"))

  (define A (function-src func1))
  (define B (function-tgt func1))
  (define C (function-src func2))
  (define D (function-tgt func2))

  ;; Validate squares and collect legs (order for commuting-square is: f, left, right, bottom)
  (define left-legs '())
  (define right-legs '())
  (for ([s (in-list sqrs)] [i (in-naturals 2)])
    (unless (commuting-square? s)
      (raise-argument-error 'function-equalizer "commuting-square?" i s))
    (define f-top (commuting-square-top s))
    (define g-left (commuting-square-left s))  ; A -> C
    (define h-right (commuting-square-right s)) ; B -> D
    (define k-bot (commuting-square-bottom s))   ; C -> D
    (unless (equal? f-top func1)
      (raise-arguments-error 'function-equalizer
                             "square’s top is not func1" "expected" func1 "got" f-top))
    (unless (equal? k-bot func2)
      (raise-arguments-error 'function-equalizer
                             "square’s bottom is not func2" "expected" func2 "got" k-bot))
    ;; light sanity (the commuting-square guard already checks shapes)
    (unless (and (set=? (function-src g-left) A)
                 (set=? (function-tgt g-left) C))
      (raise-arguments-error 'function-equalizer
                             "left leg type mismatch"
                             "src" (function-src g-left) "tgt" (function-tgt g-left)))
    (unless (and (set=? (function-src h-right) B)
                 (set=? (function-tgt h-right) D))
      (raise-arguments-error 'function-equalizer
                             "right leg type mismatch"
                             "src" (function-src h-right) "tgt" (function-tgt h-right)))
    (set! left-legs (cons g-left left-legs))
    (set! right-legs (cons h-right right-legs)))
  (set! left-legs (reverse left-legs))
  (set! right-legs (reverse right-legs))

  ;; Equalizers in Set, using your set-equalizer (returns subsets of A and B)
  (define EqA
    (apply set-equalizer
           A C
           (for/list ([gL (in-list left-legs)])
             (λ (a) ((function-proc gL) a)))))

  (define EqB
    (apply set-equalizer
           B D
           (for/list ([hR (in-list right-legs)])
             (λ (b) ((function-proc hR) b)))))

  ;; Restrict func1 to EqA -> EqB
  (define f1 (function-proc func1))
  (define proc*
    (λ (x)
      (unless (set-member? EqA x)
        (raise-arguments-error 'function-equalizer
                               "input not in source equalizer set" "value" x))
      (define y (f1 x))
      ;; should hold by construction; keep check for friendly errors while developing
      (unless (set-member? EqB y)
        (raise-arguments-error 'function-equalizer
                               "image not in target equalizer set" "image" y))
      y))

  (function proc* EqA EqB))

;; -----------------------------------------------------------------------------
;; function-pullback : (list k S1 S2 ... Sk) -> function?
;; Arguments:
;;   k    : C -> D  (the common bottom arrow)
;;   Si   : commuting-square with fields (f_i : A_i->B_i, g_i : A_i->C,
;;                                        h_i : B_i->D, k    : C->D)
;;
;; Result:
;;   F̂ :  PB(A_i --g_i--> C)  ->  PB(B_i --h_i--> D)
;;        given pointwise by the tops f_i.
;; -----------------------------------------------------------------------------
(define (function-pullback . sqrs-and-funcs)
  (define bottoms (filter function? sqrs-and-funcs))
  (define squares (filter commuting-square? sqrs-and-funcs))
  (when (not (= (length bottoms) 1))
    (raise-arguments-error 'function-pullback
                           "expected exactly one bottom function and ≥1 commuting-squares"))
  (when (null? squares)
    (raise-arguments-error 'function-pullback "expected at least one commuting-square"))

  (define k (car bottoms))
  (define C (function-src k))
  (define D (function-tgt k))

  ;; Collect legs; verify each square’s bottom matches k
  (define tops   '()) ; f_i : A_i -> B_i
  (define lefts  '()) ; g_i : A_i -> C
  (define rights '()) ; h_i : B_i -> D
  (for ([s (in-list squares)] [i (in-naturals 0)])
    (unless (equal? (commuting-square-bottom s) k)
      (raise-arguments-error 'function-pullback
                             "square’s bottom must equal the provided function"
                             "index" i "got-bottom" (commuting-square-bottom s)))
    (set! tops   (append tops   (list (commuting-square-top s))))
    (set! lefts  (append lefts  (list (commuting-square-left s))))
    (set! rights (append rights (list (commuting-square-right s)))))

  ;; Build pullbacks of domains/codomains in Set
  (define PB-left
    (apply set-pullback
           (append (map function-src tops)                 ; A_i
                   (map (λ (g) (function-proc g)) lefts)   ; g_i : A_i -> C
                   (list C))))                             ; common codomain

  (define PB-right
    (apply set-pullback
           (append (map function-src rights)               ; B_i
                   (map (λ (h) (function-proc h)) rights)  ; h_i : B_i -> D
                   (list D))))                             ; common codomain

  ;; Induced map PB-left -> PB-right by applying tops componentwise
  (define top-procs (map function-proc tops))
  (define proc*
    (λ (x)
      (define xs
        (cond
          [(list? x) x]
          [(vector? x) (vector->list x)]
          [else (raise-arguments-error 'function-pullback
                                       "expected tuple (list or vector)" "got" x)]))
      (unless (set-member? PB-left xs)
        (raise-arguments-error 'function-pullback
                               "input not in source pullback set" "value" xs))
      (define ys (for/list ([f top-procs] [xi xs]) (f xi)))
      (unless (set-member? PB-right ys)
        (raise-arguments-error 'function-pullback
                               "image not in target pullback set" "image" ys))
      ys))

  (function proc* PB-left PB-right))


(define (swap-cartesian-product a b)
  (function (λ(x)(list (second x)
                       (first x)))
            (set-cartesian-product a b)
            (set-cartesian-product b a)))

(define (reverse-cartesian-product . x)
  (function reverse
            (apply set-cartesian-product x)
            (apply set-cartesian-product (reverse x))))

(define (subobject-classifier-function)
  (define Ω0 (set 0 1/2 1))
  (define Ω1 (set 0 1))
  (define (s x)
    (cond [(equal? x 0) 0]
          [(or (equal? x 1/2) (equal? x 1)) 1]
          [else
           (raise-arguments-error
            'subobject-classifier-function
            "element of {0, 1/2, 1}"
            "given" x)]))
  (function s Ω0 Ω1))

;; classified-subfunction : commuting-square -> function
;; Input: a commuting square (f  χ0  χ1  Ω), where Ω = (subobject-classifier-function)
;; Output: the subfunction f' : A' -> B' classified by (χ0, χ1)

(define (classified-subfunction sq)
  (define f  (commuting-square-top sq))   ; top: A -> B
  (define χ0 (commuting-square-left sq))   ; left: A -> {0,1/2,1}
  (define χ1 (commuting-square-right sq))   ; right: B -> {0,1}
  (define Ω  (commuting-square-bottom sq))   ; bottom: {0,1/2,1} -> {0,1}

  ;; sanity check: bottom really is Ω
  (unless (equal? Ω (subobject-classifier-function))
    (raise-arguments-error
     'classified-subfunction
     "bottom of square must be (subobject-classifier-function)"
     "given" Ω))

  (define a-set (function-src f))
  (define b-set (function-tgt f))

  ;; fibres over '1' (top)
  (define a-sub
    (for/set ([a (in-set a-set)]
              #:when (equal? ((function-proc χ0) a) 1))
      a))
  (define b-sub
    (for/set ([b (in-set b-set)]
              #:when (equal? ((function-proc χ1) b) 1))
      b))

  ;; restricted arrow f' : A' -> B'
  (function
   (λ (a)
     (unless (set-member? a-sub a)
       (raise-arguments-error 'classified-subfunction "element of A'" "given" a))
     (define fb ((function-proc f) a))
     ;; s ∘ χ0 = χ1 ∘ f with s(1)=1 guarantees fb ∈ B' when a ∈ A'
     (unless (set-member? b-sub fb)
       (raise-arguments-error 'classified-subfunction "characteristic square does not classify a subfunction; image not in B'"))
     fb)
   a-sub b-sub))

;; classified-subfunction->square : function function -> commuting-square
;; Given g : A'->B' and f : A->B with g a subfunction of f, return:
;;   A -χ0-> Ω0
;;   |        |
;;   f        Ω
;;   v        v
;;   B -χ1-> Ω1
(define (classified-subfunction->square g f)
  (unless (and (function? g) (function? f))
    (raise-arguments-error 'classified-subfunction->square
                           "two function structs" "given" g f))
  (unless (subfunctor? g f)
    (raise-arguments-error 'classified-subfunction->square
                           "first argument must be a subfunction of the second"
                           "g" g "f" f))

  (define omega (subobject-classifier-function))
  (define omega0 (function-src omega))  ; {0, 1/2, 1}
  (define omega1 (function-tgt omega))  ; {0, 1}

  (define A  (function-src f))
  (define B  (function-tgt f))
  (define Asub (function-src g))
  (define Bsub (function-tgt g))

  ;; χ1 : B → {0,1}  (indicator of Bsub)
  (define chi1
    (function (λ (b) (if (set-member? Bsub b) 1 0))
              B omega1))

  ;; χ0 : A → {0,1/2,1}
  ;; 1    if a ∈ Asub
  ;; 1/2  if a ∉ Asub but f(a) ∈ Bsub
  ;; 0    otherwise
  (define chi0
    (function (λ (a)
                (cond [(set-member? Asub a) 1]
                      [(set-member? Bsub ((function-proc f) a)) 1/2]
                      [else 0]))
              A omega0))

  
  ;; Debug guard: find witness if something’s off
  (define (first-commutativity-witness f chi0 chi1 omega)
    (define A (function-src f))
    (define s   (function-proc omega))
    (define f·  (function-proc f))
    (define χ0· (function-proc chi0))
    (define χ1· (function-proc chi1))
    (for/first ([a (in-set A)]
                #:unless (equal? (s (χ0· a)) (χ1· (f· a))))
      (list 'a a
            's∘χ0 (s (χ0· a))
            'χ1∘f (χ1· (f· a))
            'χ0 (χ0· a)
            'f  (f· a))))
  
  (define w (first-commutativity-witness f chi0 chi1 omega))
  (when w
    (error 'classified-subfunction->square
           (format "constructed maps do not commute; witness: ~a" w)))

  (commuting-square f chi0 chi1 omega))




;; subfunctor? : function function -> boolean?
;; Is g : A' -> B' a subfunction of f : A -> B ?
;; Meaning: A' ⊆ A, B' ⊆ B, and for all a ∈ A', g(a) = f(a) ∈ B'.
(define (subfunctor? g f)
  (unless (and (function? g) (function? f))
    (raise-arguments-error 'subfunctor? "two function structs" "given" g f))
  (define A  (function-src f))
  (define B  (function-tgt f))
  (define Asub (function-src g))
  (define Bsub (function-tgt g))
  (and (subset? Asub A)
       (subset? Bsub B)
       (for/and ([a (in-set Asub)])
         (define fa ((function-proc f) a))
         (and (set-member? Bsub fa)
              (equal? ((function-proc g) a) fa)))))

;; proper-subfunctor? : function function -> boolean?
;; True when g ⊂ f in the sense above and at least one inclusion is proper.
(define (proper-subfunctor? g f)
  (and (subfunctor? g f)
       (or (not (equal? (function-src g) (function-src f)))
           (not (equal? (function-tgt g) (function-tgt f))))))

;; commuting-square-function : function function [#:as-squares? boolean] -> function
;; commuting-square-function : A→B -> C→D -> function (g^f)
;; Optional #:as-squares? chooses whether Dom holds pairs or square-structs
(define (commuting-square-function f g #:as-squares? [as-squares? #f])
  (ensure-function* 'commuting-square-function 0 f)
  (ensure-function* 'commuting-square-function 1 g)
  (define A (function-src f))
  (define B (function-tgt f))
  (define C (function-src g))
  (define D (function-tgt g))
  (ensure-set 'commuting-square-function 0 A)
  (ensure-set 'commuting-square-function 1 B)
  (ensure-set 'commuting-square-function 2 C)
  (ensure-set 'commuting-square-function 3 D)

  ;; Helper: fiber of b under f
  (define (fiber b)
    (for/list ([a (in-set A)]
               #:when (equal? ((function-proc f) a) b))
      a))

  ;; Check: g∘α is constant on each fiber of f
  (define (good-alpha? α)
    (define g∘α
      (function (λ (a) ((function-proc g) ((function-proc α) a))) A D))
    (for/and ([b (in-set B)])
      (define as (fiber b))
      (or (null? as)
          (let* ([v0 ((function-proc g∘α) (car as))])
            (for/and ([a (in-list (cdr as))])
              (equal? v0 ((function-proc g∘α) a)))))))

  ;; Derive the (unique) β forced by α on each fiber; if a fiber is empty,
  ;; pick a canonical value so we produce a well-formed β (doesn't affect commuting)
  (define (beta-for α)
    (function
     (λ (b)
       (define as (fiber b))
       (if (null? as)
           (set-first D)
           ((function-proc g) ((function-proc α) (car as)))))
     B D))

  (define A→C (function-set A C #:as-functions? #t))

  (define dom
    (list->set
     (for/list ([α (in-set A→C)] #:when (good-alpha? α))
       (define β (beta-for α))
       (if as-squares?
           (commuting-square f α β g)
           (cons α β)))))

  (define cod (function-set B D #:as-functions? #t))

  ;; The exponential g^f: picks β (right leg) out of the domain element
  (function
   (λ (e)
     (cond [as-squares? (commuting-square-right e)]
           [else        (cdr e)]))
   dom cod))

;; curry-commuting-square-function : (g^f) -> ((h×f ⇒ g) -> (h ⇒ g^f))
;; Given sqfunc = g^f, map a square (h×f) ⇒ g to a square h ⇒ g^f.
(define (curry-commuting-square-function sqfunc)
  (ensure-function* 'curry-commuting-square-function 0 sqfunc)
  (define dom-g^f (function-src sqfunc))
  (ensure-set 'curry-commuting-square-function 0 dom-g^f)

  ;; Domain representation + witness (if any) to infer f,g shapes
  (define domain-expects-squares?
    (and (not (set-empty? dom-g^f))
         (commuting-square? (set-first dom-g^f))))
  (define f-wit (and domain-expects-squares? (commuting-square-top    (set-first dom-g^f))))
  (define g-wit (and domain-expects-squares? (commuting-square-bottom (set-first dom-g^f))))

  ;; Order-insensitive graph equality for functions
  (define (graph=? f g)
    (set=? (list->set (function->fgraph f))
           (list->set (function->fgraph g))))

  ;; Return the stored domain element whose *alpha* matches a (β is forced by α).
  (define (lookup-dom-by-alpha a)
    (for/first ([e (in-set dom-g^f)])
      (cond
        [(commuting-square? e) (and (graph=? (commuting-square-left e) a) e)]
        [(pair? e)              (and (graph=? (car e) a)                e)]
        [else #f])))

  (define (raise-domain-mismatch a)
    (raise-arguments-error
     'curry-commuting-square-function
     "χ0(x) not in domain of g^f (no matching element found)"
     "alpha-graph" (function->fgraph a)))

  (λ (sq)
    (unless (commuting-square? sq)
      (raise-argument-error 'curry-commuting-square-function "commuting-square?" sq))

    ;; S : (h×f) ⇒ g
    (define top× (commuting-square-top sq))   ; X×A -> Y×B
    (define α×   (commuting-square-left sq))  ; X×A -> C
    (define β×   (commuting-square-right sq)) ; Y×B -> D
    (define g    (commuting-square-bottom sq))

    ;; Carriers and projections
    (define XA (function-src top×))
    (define YB (function-tgt top×))
    (define X (map-set first  XA))
    (define A (map-set second XA))
    (define Y (map-set first  YB))
    (define B (map-set second YB))
    (define C (function-tgt α×))
    (define D (function-tgt β×))
    (define πY (function (λ (yb) (first yb))  YB Y))
    (define πB (function (λ (yb) (second yb)) YB B))

    ;; Cheap witnesses (only used when factors are non-empty)
    (define a0 (and (not (set-empty? A)) (set-first A)))
    (define x0 (and (not (set-empty? X)) (set-first X)))

    ;; Build h : X -> Y directly from top× and a witness a0
    (define h
      (function
       (λ (x)
         (if a0
             (let ([yb ((function-proc top×) (list x a0))])
               (first yb))
             (set-first Y)))
       X Y))

    ;; Build f : A -> B directly from top× and a witness x0 (or reuse witness)
    (define f
      (or f-wit
          (function
           (λ (a)
             (if x0
                 (let ([yb ((function-proc top×) (list x0 a))])
                   (second yb))
                 (set-first B)))
           A B)))

    ;; χ1 : Y -> (B -> D) via currying on sets (codomain matches (B→D) set)
    (define β-cur
      ((function-proc
         (curry-function-set
          (function-set (function-src β×) (function-tgt β×) #:as-functions? #t)))
       β×))
    (define χ1 β-cur)

    ;; χ0 : X -> dom(g^f).  For each x, build αx(a) = α×(x,a), then look up
    ;; the *stored* domain element by α only.
    (define χ0
      (function
       (λ (x)
         (define αx
           (function (λ (a) ((function-proc α×) (list x a))) A C))
         (or (lookup-dom-by-alpha αx)
             (raise-domain-mismatch αx)))
       X dom-g^f))

    (commuting-square h χ0 χ1 sqfunc)))


;; uncurry-commuting-square-function : (g^f) -> ( (h ⇒ g^f) -> ((h×f) ⇒ g) )
(define (uncurry-commuting-square-function sqfunc)
  ;; We require #:as-squares? so dom(g^f) holds square structs (lets us read f,g).
  (define dom-g^f (function-src sqfunc))
  (unless (and (not (set-empty? dom-g^f))
               (commuting-square? (set-first dom-g^f)))
    (raise-arguments-error
     'uncurry-commuting-square-function
     "sqfunc must be an exponential built with #:as-squares? #t so its domain elements are commuting-square structs"))

  ;; Witness f and g from any domain square of g^f
  (define witness (set-first dom-g^f))
  (define f-wit (commuting-square-top    witness))  ; f : A -> B
  (define g-wit (commuting-square-bottom witness))  ; g : C -> D

  (λ (sq)
    ;; Input: T : h ⇒ g^f
    (define h   (commuting-square-top sq))    ; h : X -> Y
    (define χ0  (commuting-square-left sq))   ; χ0 : X -> Dom(g^f) (squares)
    (define χ1  (commuting-square-right sq))  ; χ1 : Y -> (B -> D)
    (define _g^f (commuting-square-bottom sq)) ; the exponential itself (unused here)

    ;; Carriers from h and the witnesses
    (define X (function-src h))
    (define Y (function-tgt h))
    (define A (function-src f-wit))
    (define B (function-tgt f-wit))
    (define C (function-src g-wit))
    (define D (function-tgt g-wit))

    ;; --- Right leg β× : Y×B -> D
    ;; IMPORTANT: uncurry the *function-set*, then apply it to χ1.
    (define β×
      ((function-proc
         (uncurry-function-set
           (function-set
            Y
            (function-set B D #:as-functions? #t)  ; codomain is the set (B -> D)
            #:as-functions? #t)))
       χ1))

    ;; --- Left leg α× : X×A -> C (build pointwise from χ0)
    (define α×
      (function
       (λ (xa)
         (define x (first xa))
         (define a (second xa))
         (define sqx ((function-proc χ0) x))
         (unless (commuting-square? sqx)
           (raise-arguments-error 'uncurry-commuting-square-function
                                  "χ0(x) must be a commuting-square"))
         (define αx (commuting-square-left sqx))  ; A -> C
         ((function-proc αx) a))
       (set-cartesian-product X A)                ; X×A carrier
       C))

    ;; --- Top: h×f (use your helper; reuse the witnessed f)
    (define h×f (function-cartesian-product h f-wit))

    ;; Bottom: g (witnessed). Guarded by commuting-square constructor.
    (commuting-square h×f α× β× g-wit)))



(struct commuting-square (top left right bottom)
  #:transparent
  #:guard
  (λ (f g h k this)
    (unless (and (function? f) (function? g) (function? h) (function? k))
      (raise-arguments-error 'commuting-square (format "expected four function structs, got: ~a ~a ~a ~a" f g h k)))
    (define A (function-src f))
    (define B (function-tgt f))
    (define A* (function-src g))
    (define C (function-tgt g))
    (define B* (function-src h))
    (define D (function-tgt h))
    (define C* (function-src k))
    (define D* (function-tgt k))

    (unless (set=? A A*)
      (raise-arguments-error 'commuting-square (format "domain mismatch: src(f)=~a but src(g)=~a" A A*)))
    (unless (set=? B B*)
      (raise-arguments-error 'commuting-square (format "codomain mismatch: tgt(f)=~a but src(h)=~a" B B*)))
    (unless (set=? C C*)
      (raise-arguments-error 'commuting-square (format "codomain mismatch: tgt(g)=~a but src(k)=~a" C C*)))
    (unless (set=? D D*)
      (raise-arguments-error 'commuting-square (format "codomain mismatch: tgt(h)=~a but tgt(k)=~a" D D*)))

    (define hf (compose-functions f h)) ; do f, then h
    (define kg (compose-functions g k)) ; do g, then k
    (unless (equal? hf kg)
      (raise-arguments-error 'commuting-square "square does not commute"))
    (values f g h k))
  #:property prop:custom-write
  (lambda (cs out mode)
    (define f* (commuting-square-top cs))
    (define g* (commuting-square-left cs))
    (define h* (commuting-square-right cs))
    (define k* (commuting-square-bottom cs))
    (fprintf out "#<commuting-square~n  [ ~a  ~a ]~n  [ ~a  ~a ]>"
             f* h* g* k*)))



          
(provide (all-defined-out))