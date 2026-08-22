#lang racket
(require racket/set
         racket/list
         racket/function
         "function.rkt"
         "relation.rkt")

;; --------------------
;; Error helpers
;; --------------------
(define (ensure-set who pos x)
  (unless (set? x)
    (raise-argument-error who "set?" x)))

(define (ensure-nonempty-set who pos x)
  (ensure-set who pos x)
  (when (set-empty? x)
    (raise-arguments-error who "expected a non-empty set" "set" x)))

(define (ensure-boolean who pos x)
  (unless (boolean? x)
    (raise-argument-error who "boolean?" x)))

(define (ensure-procedure who pos x [arity #f])
  (unless (procedure? x)
    (raise-argument-error who "procedure?" x))
  (when (and arity (not (procedure-arity-includes? x arity)))
    (raise-arguments-error who
                           (format "procedure does not accept ~a argument~a"
                                   arity (if (= arity 1) "" "s"))
                           "procedure" x
                           "expected-arity" arity
                           "actual-arity" (procedure-arity x))))

(define (ensure-function* who pos f)
  (unless (function? f)
    (raise-argument-error who "function?" f)))

(define (ensure-relation* who pos r)
  (unless (relation? r)
    (raise-argument-error who "relation?" r)))

;; --------------------
;; Small utilities
;; --------------------
(define (map-set f . st)
  (when (null? st)
    (raise-arguments-error 'map-set "expected at least one set argument"))
  (ensure-procedure 'map-set 0 f)
  (for ([s (in-list st)] [i (in-naturals 1)])
    (ensure-set 'map-set i s))
  (define n (length st))
  (ensure-procedure 'map-set 0 f n)
  (list->set (apply map f (map set->list st))))

;; --------------------
;; Graph conversions
;; --------------------
(define (function->fgraph func)
  (ensure-function* 'function->fgraph 0 func)
  (for/set ([x (function-src func)])
    (list x ((function-proc func) x))))

(define (relation->rgraph rel)
  (ensure-relation* 'relation->rgraph 0 rel)
  (for*/set ([x (relation-src rel)]
             [y (relation-tgt rel)]
             #:when ((relation-proc rel) x y))
    (list x y)))

(define (fgraph->procedure funcset)
  (ensure-set 'fgraph->procedure 0 funcset)
  (λ xs
    (define key (if (and (list? xs) (= (length xs) 1)) (first xs) xs))
    (for/first ([i funcset]
                #:when (or (equal? key (first i))
                           (and (list? key) (list? (first i))
                                (= (length key) (length (first i)))
                                (andmap equal? key (first i)))))
      (second i))))

;; --------------------
;; Basic set combinators
;; --------------------
(define (set-disjoint-union . sets)
  (when (null? sets)
    (raise-arguments-error 'set-disjoint-union "expected at least one set"))
  (for ([s (in-list sets)] [i (in-naturals 1)])
    (ensure-set 'set-disjoint-union i s))
  (apply set-union
         (for/list ([s (in-list sets)]
                    [n (in-naturals)])
           (for/set ([e (in-set s)])
             (list n e)))))

(define (merge-step classes)
  (cond
    [(null? classes) '()]
    [else
     (let* ([first-class (car classes)]
            [rest-classes (cdr classes)]
            ;; Find all sets in rest-classes that overlap with first-class
            [overlapping (filter (λ (c) (not (set-empty? (set-intersect first-class c)))) rest-classes)]
            [disjoint (filter (λ (c) (set-empty? (set-intersect first-class c))) rest-classes)])
       (if (null? overlapping)
           ;; No overlaps for first-class: keep it and recurse on the rest
           (cons first-class (merge-step rest-classes))
           ;; Overlaps found: merge them all into first-class and restart the step
           (merge-step (cons (apply set-union first-class overlapping) disjoint))))]))

(define (set-coequalizer set1 set2 . funcs)
  (ensure-set 'set-coequalizer 0 set1)
  (ensure-set 'set-coequalizer 1 set2)
  (when (null? funcs)
    (raise-arguments-error 'set-coequalizer "expected at least one function"))
  (for ([f (in-list funcs)] [i (in-naturals 2)])
    (ensure-procedure 'set-coequalizer i f))
 
  ;; 1. Generate set relations for each element in set1 based on the functions
  (define relations
    (for/list ([e (in-set set1)])
      (list->set (for/list ([f (in-list funcs)])
                   (f e)))))
  ;; 2. Include all elements from set2 as individual singletons so unmapped elements aren't lost
  (define singletons
    (for/list ([e (in-set set2)])
      (set e)))
  ;; 3. Merge overlapping equivalence classes into a single set of classes
  (list->set (merge-step (append relations singletons))))

;; Pushout: (set A) then k functions and k sets.
(define (set-pushout . funcsandsets)
  (when (< (length funcsandsets) 3)
    (raise-arguments-error 'set-pushout
      "expected (set A) followed by k>=1 functions and k sets"))
  (define setA (first funcsandsets))
  (ensure-set 'set-pushout 0 setA)
  (define rst (rest funcsandsets))
  (when (odd? (length rst))
    (raise-arguments-error 'set-pushout
      "expected an even number of trailing arguments: k functions and k sets"))
  (define k (/ (length rst) 2))
  (define funcs (take rst k))
  (define sets  (drop rst k))
  (for ([f funcs] [i (in-naturals 1)])
    (ensure-procedure 'set-pushout (+ i 1) f 1))
  (for ([s sets] [i (in-naturals 1)])
    (ensure-set 'set-pushout (+ i 1 k) s))
  ;; 1. For each element in setA, identify its images across all legs as a single relation class
  (define leg-relations
    (for/list ([e (in-set setA)])
      (list->set
       (for/list ([f (in-list funcs)] [idx (in-naturals)])
         (list idx (f e))))))
  ;; 2. Include all disjoint target set elements as tagged singletons
  (define tagged-singletons
    (apply append
           (for/list ([s (in-list sets)] [idx (in-naturals)])
             (for/list ([x (in-set s)])
               (set (list idx x))))))
  ;; 3. Partition via equivalence classes
  (list->set (merge-step (append leg-relations tagged-singletons))))

(define (set-cartesian-product . sets)
  (when (null? sets)
    (raise-arguments-error 'set-cartesian-product "expected at least one set"))
  (for ([s (in-list sets)] [i (in-naturals 0)])
    (ensure-set 'set-cartesian-product i s))
  (list->set (apply cartesian-product (map set->list sets))))

(define (set-equalizer set1 set2 . funcs)
  (ensure-set 'set-equalizer 0 set1)
  (ensure-set 'set-equalizer 1 set2)
  (when (null? funcs)
    (raise-arguments-error 'set-equalizer "expected at least one function"))
  (for ([f (in-list funcs)] [i (in-naturals 2)])
    (ensure-procedure 'set-equalizer i f 1))
  (for/set ([e1 set1]
            #:when (let ([v (map (λ (x) (x e1)) funcs)])
                     (andmap equal?
                             (take v (sub1 (length v)))
                             (rest v))))
    e1))

;; Pullback: k sets and k functions, then the common codomain set
(define (set-pullback . funcsandsets)
  (when (< (length funcsandsets) 3)
    (raise-arguments-error 'set-pullback
                           "expected at least 3 arguments: k>=1 sets and functions, then a common codomain set"))
  (define begin (take funcsandsets (sub1 (length funcsandsets))))
  (define setlast (last funcsandsets))
  (ensure-set 'set-pullback (sub1 (length funcsandsets)) setlast)
  (when (odd? (length begin))
    (raise-arguments-error 'set-pullback
                           "expected an even number of leading arguments: k sets then k functions"))
  (define half (/ (length begin) 2))
  (define sets (take begin half))
  (define funcs (drop begin half))
  (for ([s sets] [i (in-naturals 0)])
    (ensure-set 'set-pullback i s))
  (for ([f funcs] [i (in-naturals 0)])
    (ensure-procedure 'set-pullback (+ i half) f 1))
  (for/set ([e (apply set-cartesian-product sets)]
            #:when (let ([v (map (λ (f s) (f s)) funcs e)])
                     (andmap equal? (take v (sub1 (length v))) (rest v))))
    e))

(define (pullback-along func1 func2)
  (ensure-function* 'pullback-along 0 func1)
  (ensure-function* 'pullback-along 1 func2)
  (unless (equal? (function-tgt func1) (function-tgt func2))
    (raise-arguments-error 'pullback-along
                           "expected both functions to have the same target"
                           "function-1-target" (function-tgt func1)
                           "function-2-target" (function-tgt func2)))
  (function first
            (set-pullback (function-src func1) (function-src func2)
                          (function-proc func1) (function-proc func2)
                          (function-tgt func2))
            (function-src func1)))

;; --------------------
;; Function-set builders
;; --------------------
(define (function-set src tgt #:as-functions? [as-funcs #f])
  (ensure-set 'function-set 0 src)
  (ensure-set 'function-set 1 tgt)
  (ensure-boolean 'function-set 2 as-funcs)
  (list->set
   (map
    (if as-funcs
        (compose (λ (x) (function x src tgt)) fgraph->procedure list->set)
        list->set)
    (apply cartesian-product
           (for/list ([i src])
             (for/list ([j tgt]) (list i j)))))))

(define (injective-function-set set1 set2 #:as-functions? [as-funcs #f])
  (ensure-set 'injective-function-set 0 set1)
  (ensure-set 'injective-function-set 1 set2)
  (ensure-boolean 'injective-function-set 2 as-funcs)
  (define (inj s1 s2)
    (cond [(set-empty? s1) (list (set))]
          [(= (set-count s1) 1)
           (map (λ (x) (list (list (set-first s1) x))) s2)]
          [else (for*/list ([i s2]
                            [j (inj (set-rest s1) (set-remove s2 i))])
                  (cons (list (set-first s1) i) j))]))
  (list->set
   (map (if as-funcs
            (compose (λ (x) (function x set1 set2)) fgraph->procedure list->set)
            list->set)
        (inj (set->list set1) (set->list set2)))))

(define (surjective-function-set set1 set2 #:as-functions? [as-funcs #f])
  (ensure-set 'surjective-function-set 0 set1)
  (ensure-set 'surjective-function-set 1 set2)
  (ensure-boolean 'surjective-function-set 2 as-funcs)
  (define l
    (map (λ (x) (map - (cons (set-count set1) (reverse x))
                      (reverse (cons 0 x))))
         (combinations (range 1 (set-count set1)) (sub1 (set-count set2)))))
  (define (h st lst)
    (if (empty? (rest lst))
        (map list (combinations st (first lst)))
        (let ([cmbs (combinations (set->list st) (first lst))])
          (for*/list ([i cmbs]
                      [j (h (remove* i (set->list st)) (rest lst))])
            (cons i j)))))
  (list->set
   (map (λ (x)
          ((if as-funcs
               (compose (λ (x) (function x set1 set2))
                        fgraph->procedure list->set)
               list->set)
           (foldl append null
                  (map (λ (y z) (map (λ (a) (list a z)) y))
                       x (set->list set2)))))
        (foldr append null
               (map (λ (x) (apply cartesian-product (map list x)))
                    (foldl append null (map (curry h set1) l)))))))

;; --------------------
;; Currying helpers
;; --------------------
(define (curry-function-set funcst)
  (ensure-set 'curry-function-set 0 funcst)
  (ensure-nonempty-set 'curry-function-set 0 funcst)
  (unless (function? (set-first funcst))
    (raise-arguments-error 'curry-function-set "expected elements to be functions"
                           "first-element" (set-first funcst)))
  (let* ([src (map-set first (function-src (set-first funcst)))]
         [tgtfuncsrc (map-set (λ (x) (if (= 1 (length (rest x)))
                                         (second x)
                                         (rest x)))
                              (function-src (set-first funcst)))]
         [tgtfunctgt (function-tgt (set-first funcst))]
         [settgtfuncs (function-set tgtfuncsrc tgtfunctgt #:as-functions? #t)])
    (function (λ (func)
                (function
                 (λ (x)
                   (function
                    (λ (y) ((function-proc func)
                            (if (list? y) (cons x y) (list x y))))
                    tgtfuncsrc
                    tgtfunctgt))
                 src
                 settgtfuncs))
              funcst
              (function-set src settgtfuncs #:as-functions? #t))))

(define (uncurry-function-set funcst)
  (ensure-set 'uncurry-function-set 0 funcst)
  (ensure-nonempty-set 'uncurry-function-set 0 funcst)
  (unless (function? (set-first funcst))
    (raise-arguments-error 'uncurry-function-set "expected elements to be functions"
                           "first-element" (set-first funcst)))
  (let ([funcsrs (set-cartesian-product
                  (function-src (set-first funcst))
                  (function-src (set-first (function-tgt (set-first funcst)))))]
        [functgt (function-tgt (set-first (function-tgt (set-first funcst))))])
    (function
     (λ (f)
       (function
        (λ (x) (((function-proc f) (first x))
                (if (= 1 (length (rest x))) (second x) (rest x))))
        funcsrs
        functgt))
     funcst
     (function-set funcsrs functgt #:as-functions? #t))))

;; --------------------
;; Search & boolean-valued function-set conversions
;; --------------------
(define (search-function-set pred set1 set2)
  (ensure-procedure 'search-function-set 0 pred 3)
  (ensure-set 'search-function-set 1 set1)
  (ensure-set 'search-function-set 2 set2)
  (for/set ([i (function-set set1 set2 #:as-functions? #t)]
            #:when (pred set1 set2 i))
    i))

(define (boolean-ranged-function-set->powerset funcst)
  (ensure-set 'boolean-ranged-function-set->powerset 0 funcst)
  (for/set ([f funcst])
    (for/set ([i f] #:when (second i))
      (first i))))

(define (powerset->boolean-ranged-function-set pwrst)
  (ensure-set 'powerset->boolean-ranged-function-set 0 pwrst)
  (ensure-nonempty-set 'powerset->boolean-ranged-function-set 0 pwrst)
  (let ([biggest-set (argmax set-count (set->list pwrst))])
    (for/set ([s pwrst])
      (for/set ([i biggest-set])
        (list i (set-member? s i))))))

(define (powerset S)
  (ensure-set 'powerset 0 S)
  (define xs (set->list S))
  (for*/set ([k (in-range 0 (add1 (length xs)))]
             [c (in-list (combinations xs k))])
    (list->set c)))

;; --------------------
;; Quantifiers and preimage
;; --------------------
(define (∃ func sbst)
  (ensure-function* '∃ 0 func)
  (ensure-set '∃ 1 sbst)
  (let ([X (function-src func)]
        [Y (function-tgt func)])
    (if (subset? sbst X)
        (for/set ([y Y]
                  #:when (for/or ([x sbst]) (equal? ((function-proc func) x) y)))
          y)
        (error '∃ "~a is not a subset of src: ~a" sbst X))))

(define (preimage func sbst)
  (ensure-function* 'preimage 0 func)
  (ensure-set 'preimage 1 sbst)
  (let ([X (function-src func)]
        [Y (function-tgt func)])
    (if (subset? sbst Y)
        (for/set ([x X] #:when (set-member? sbst ((function-proc func) x)))
          x)
        (error 'preimage "~a is not a subset of tgt: ~a" sbst Y))))

(define (∀ func sbst)
  (ensure-function* '∀ 0 func)
  (ensure-set '∀ 1 sbst)
  (let ([X (function-src func)]
        [Y (function-tgt func)])
    (if (subset? sbst X)
        (for/set ([y Y] #:when (subset? (preimage func (set y)) sbst))
          y)
        (error '∀ "~a is not a subset of src: ~a" sbst X))))

;; --------------------

(define (∃f func)
  (ensure-function* '∃f 0 func)
  (function (λ (sbst) (∃ func sbst))
            (powerset (function-src func))
            (powerset (function-tgt func))))

(define (preimagef func)
  (ensure-function* 'preimagef 0 func)
  (function (λ (sbst) (preimage func sbst))
            (powerset (function-tgt func))
            (powerset (function-src func))))

(define (∀f func)
  (ensure-function* '∀f 0 func)
  (function (λ (sbst) (∀ func sbst))
            (powerset (function-src func))
            (powerset (function-tgt func))))

;; --------------------
;; Properties of functions
;; --------------------
(define (injective? f)
  (ensure-function* 'injective? 0 f)
  (let ([X (function-src f)]
        [p (function-proc f)])
    (for*/and ([e1 (in-set X)] [e2 (in-set X)])
      (implies (equal? (p e1) (p e2)) (equal? e1 e2)))))

(define (surjective? f)
  (ensure-function* 'surjective? 0 f)
  (let ([X (function-src f)]
        [Y (function-tgt f)]
        [p (function-proc f)])
    (for/and ([y (in-set Y)])
      (for/or ([x (in-set X)])
        (equal? (p x) y)))))

(define (bijective? f)
  (ensure-function* 'bijective? 0 f)
  (and (injective? f) (surjective? f)))

(define (left-inverse-of? f g)
  (ensure-function* 'left-inverse-of? 0 f)
  (ensure-function* 'left-inverse-of? 1 g)
  (and (injective? f)
       (for/and ([x (in-set (function-src f))])
         (equal? x (g (f x))))))

(define (right-inverse-of? f g)
  (ensure-function* 'right-inverse-of? 0 f)
  (ensure-function* 'right-inverse-of? 1 g)
  (and (surjective? f)
       (for/and ([y (in-set (function-tgt f))])
         (equal? y (f (g y))))))

(define (inverse-of? f g)
  (ensure-function* 'inverse-of? 0 f)
  (ensure-function* 'inverse-of? 1 g)
  (and (left-inverse-of? f g) (right-inverse-of? f g)))

(define-values (retraction? section? isomorphism?)
  (values left-inverse-of? right-inverse-of? inverse-of?))

(define (split-monomorphism? g f)
  (ensure-function* 'split-monomorphism? 0 g)
  (ensure-function* 'split-monomorphism? 1 f)
  (retraction? f g))

(define (split-epimorphism? g f)
  (ensure-function* 'split-epimorphism? 0 g)
  (ensure-function* 'split-epimorphism? 1 f)
  (section? f g))

(define (idempotent? f)
  (ensure-function* 'idempotent? 0 f)
  (for/and ([x (in-set (function-src f))])
    (equal? (f x) (f (f x)))))

(define (make-split-idempotent s r)
  (ensure-function* 'make-split-idempotent 0 s)
  (ensure-function* 'make-split-idempotent 1 r)
  (if (and (retraction? s r) (section? r s))
      (compose s r)
      (raise-arguments-error 'make-split-idempotent
                             "requires r be right-invertible and s be left-invertible."
                             "retraction?" (retraction? s r)
                             "section?"   (section? r s))))

(provide (all-defined-out))
