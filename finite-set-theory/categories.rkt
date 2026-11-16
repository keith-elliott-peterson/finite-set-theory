#lang racket

(struct category
  (objects morphisms identities composition source target)
  #:transparent
  #:guard
  (λ (objects morphisms identities composition source target this)
    (unless (set? objects)
      (error this "expected a set for objects. Given: ~e" objects))
    (unless (set? morphisms)
      (error this "expected a set for morphisms. Given: ~e" morphisms))
    
    ;; 1. Check object identity mappings
    (for ([o (in-set objects)])
      (define id-o (identities o))
      (unless (set-member? morphisms id-o)
        (error this "expected identity morphism of ~e (~e) to be member of morphisms." o id-o))
      (unless (equal? o (source id-o))
        (error this "expected ~e to equal source of identity ~e." o id-o))
      (unless (equal? o (target id-o))
        (error this "expected ~e to equal target of identity ~e." o id-o)))

    ;; 2. Check morphism sources, targets, and identity composition
    (for ([m (in-set morphisms)])
      (define src-m (source m))
      (define tgt-m (target m))
      (unless (set-member? objects src-m)
        (error this "expected source of ~e (~e) to be member of objects." m src-m))
      (unless (set-member? objects tgt-m)
        (error this "expected target of ~e (~e) to be member of objects." m tgt-m))
      
      ;; Right identity: m ∘ id_(src m) = m
      (unless (equal? m (composition m (identities src-m)))
        (error this "expected composition of ~e and ~e to equal ~e" m (identities src-m) m))
      ;; Left identity: id_(tgt m) ∘ m = m
      (unless (equal? m (composition (identities tgt-m) m))
        (error this "expected composition of ~e and ~e to equal ~e" (identities tgt-m) m)))

    ;; 3. Check closure and type agreement under composition
    (for* ([m (in-set morphisms)]
           [n (in-set morphisms)]
           #:when (equal? (target m) (source n)))
      (define nm (composition n m))
      (unless (set-member? morphisms nm)
        (error this "expected composition ~e of ~e and ~e to be a member of morphisms" nm m n))
      (unless (equal? (source m) (source nm))
        (error this "expected source of ~e to equal source of ~e." m nm))
      (unless (equal? (target n) (target nm))
        (error this "expected target of ~e to equal target of ~e." n nm)))

    ;; 4. Check associativity
    (for* ([m (in-set morphisms)]
           [n (in-set morphisms)]
           #:when (equal? (target m) (source n))
           [o (in-set morphisms)]
           #:when (equal? (target n) (source o)))
      (define o-nm (composition o (composition n m)))
      (define on-m (composition (composition o n) m))
      (unless (equal? o-nm on-m)
        (error this "associativity law failed: ~e ≠ ~e" o-nm on-m)))

    (values objects morphisms identities composition source target)))

(define (=category? cat1 cat2)
  (and
   ;; 1. Check underlying carrier sets first (quick bailout if mismatched)
   (equal? (category-objects cat1) (category-objects cat2))
   (equal? (category-morphisms cat1) (category-morphisms cat2))

   ;; 2. Check that identities match for every object
   (for/and ([o (in-set (category-objects cat1))])
     (equal? ((category-identities cat1) o)
             ((category-identities cat2) o)))

   ;; 3. Check that source mappings match for every morphism
   (for/and ([m (in-set (category-morphisms cat1))])
     (equal? ((category-source cat1) m)
             ((category-source cat2) m)))

   ;; 4. Check that target mappings match for every morphism
   (for/and ([m (in-set (category-morphisms cat1))])
     (equal? ((category-target cat1) m)
             ((category-target cat2) m)))

   ;; 5. Check composition point-wise for every composable pair
   (for*/and ([m (in-set (category-morphisms cat1))]
              [n (in-set (category-morphisms cat1))]
              #:when (equal? ((category-target cat1) m) ((category-source cat1) n)))
     (equal? ((category-composition cat1) n m)
             ((category-composition cat2) n m)))))

(define (opposite cat)
  (category (category-objects cat)
            (category-morphisms cat)
            (category-identities cat)
            (λ (g f) ((category-composition cat) f g))
            (category-target cat)
            (category-source cat)))

(define walking-span
  (let* ([objs (set 'L 'Apex 'R)]
         [id-L 'id-L]
         [id-Apex 'id-Apex]
         [id-R 'id-R]
         [f 'f] ; Apex -> L
         [g 'g] ; Apex -> R
         [morphs (set id-L id-Apex id-R f g)]
         [idents (hash 'L id-L 'Apex id-Apex 'R id-R)]
         [sources (hash id-L 'L id-Apex 'Apex id-R 'R f 'Apex g 'Apex)]
         [targets (hash id-L 'L id-Apex 'Apex id-R 'R f 'L g 'R)])
    (category
     objs
     morphs
     (λ (o) (hash-ref idents o))
     (λ (n m)
       ;; Since only identities compose non-trivially, fallback to unit laws
       (cond
         [(equal? m id-L) n] [(equal? m id-Apex) n] [(equal? m id-R) n]
         [(equal? n id-L) m] [(equal? n id-Apex) m] [(equal? n id-R) m]))
     (λ (m) (hash-ref sources m))
     (λ (m) (hash-ref targets m)))))

(define walking-cospan
  (let* ([objs (set 'L 'Apex 'R)]
         [id-L 'id-L]
         [id-Apex 'id-Apex]
         [id-R 'id-R]
         [f 'f] ; L -> Apex
         [g 'g] ; R -> Apex
         [morphs (set id-L id-Apex id-R f g)]
         [idents (hash 'L id-L 'Apex id-Apex 'R id-R)]
         [sources (hash id-L 'L id-Apex 'Apex id-R 'R f 'L g 'R)]
         [targets (hash id-L 'L id-Apex 'Apex id-R 'R f 'Apex g 'Apex)])
    (category
     objs
     morphs
     (λ (o) (hash-ref idents o))
     (λ (n m)
       (cond
         [(equal? m id-L) n] [(equal? m id-Apex) n] [(equal? m id-R) n]
         [(equal? n id-L) m] [(equal? n id-Apex) m] [(equal? n id-R) m]))
     (λ (m) (hash-ref sources m))
     (λ (m) (hash-ref targets m)))))

(define walking-idempotent
  (let* ([objs (set 'X)]
         [id-X 'id-X]
         [e 'e]
         [morphs (set id-X e)]
         [idents (hash 'X id-X)]
         [sources (hash id-X 'X e 'X)]
         [targets (hash id-X 'X e 'X)])
    (category
     objs
     morphs
     (λ (o) (hash-ref idents o))
     (λ (n m)
       (cond
         [(equal? m id-X) n]
         [(equal? n id-X) m]
         [(and (equal? n e) (equal? m e)) e]
         [else (error "invalid composition in walking-idempotent")]))
     (λ (m) (hash-ref sources m))
     (λ (m) (hash-ref targets m)))))

(define walking-splitting
  (let* ([objs (set 'A 'X)]
         [id-A 'id-A]
         [id-X 'id-X]
         [s 's] ; A -> X (section)
         [r 'r] ; X -> A (retraction)
         [e 'e] ; X -> X (idempotent: s ∘ r)
         [morphs (set id-A id-X s r e)]
         [idents (hash 'A id-A 'X id-X)]
         [sources (hash id-A 'A id-X 'X s 'A r 'X e 'X)]
         [targets (hash id-A 'A id-X 'X s 'X r 'A e 'X)])
    (category
     objs
     morphs
     (λ (o) (hash-ref idents o))
     (λ (n m)
       (cond
         ;; Identity laws
         [(equal? m id-A) n] [(equal? m id-X) n]
         [(equal? n id-A) m] [(equal? n id-X) m]
         ;; Core split-idempotent equations
         [(and (equal? n r) (equal? m s)) id-A]  ; r ∘ s = id_A
         [(and (equal? n s) (equal? m r)) e]      ; s ∘ r = e
         [(and (equal? n e) (equal? m e)) e]      ; e ∘ e = e
         [(and (equal? n e) (equal? m s)) s]      ; e ∘ s = s
         [(and (equal? n r) (equal? m e)) r]      ; r ∘ e = r
         [else (error "invalid composition in walking-split-idempotent")]))
     (λ (m) (hash-ref sources m))
     (λ (m) (hash-ref targets m)))))



(define (slice-category cat A)
  ;; 1. Validate inputs using your strict checks
  (unless (category? cat)
    (error 'slice-category "expected a category?. Given: ~e" cat))
  (unless (set-member? (category-objects cat) A)
    (error 'slice-category "expected ~e to be an object in the category." A))

  (let* ([objs (category-objects cat)]
         [morphs (category-morphisms cat)]
         [src (category-source cat)]
         [tgt (category-target cat)]
         [comp (category-composition cat)]
         [idents (category-identities cat)]

         ;; 2. Objects of C/A: pairs (list X f) where f : X -> A
         [slice-objs
          (for*/set ([X (in-set objs)]
                     [f (in-set morphs)]
                     #:when (and (equal? (src f) X)
                                 (equal? (tgt f) A)))
            (list X f))]

         ;; 3. Morphisms of C/A: arrows h : X -> Y in C such that g ∘ h = f
         [slice-morphs
          (for*/set ([obj1 (in-set slice-objs)]
                     [obj2 (in-set slice-objs)]
                     [h (in-set morphs)]
                     #:when (let ([X (first obj1)]
                                  [f (second obj1)]
                                  [Y (first obj2)]
                                  [g (second obj2)])
                              (and (equal? (src h) X)
                                   (equal? (tgt h) Y)
                                   (equal? f (comp g h)))))
            (list h obj1 obj2))]


         ;; 4. Identities in C/A: id_X for each (X, f)
         [slice-idents
          (λ (obj)
            (define X (first obj))
            (define f (second obj))
            (list (idents X) obj obj))]

         ;; 5. Source and Target in C/A
         [slice-src (λ (m) (second m))]
         [slice-tgt (λ (m) (third m))]

         ;; 6. Composition in C/A: compose underlying arrows
         [slice-comp
          (λ (m2 m1)
            (define h1 (first m1))
            (define h2 (first m2))
            (list (comp h2 h1) (slice-src m1) (slice-tgt m2)))])

    ;; Feed it right into your struct; the guard will mathematically verify it!
    (category slice-objs slice-morphs slice-idents slice-comp slice-src slice-tgt)))


(define (coslice-category cat A)
  ;; 1. Validate inputs
  (unless (category? cat)
    (error 'coslice-category "expected a category?. Given: ~e" cat))
  (unless (set-member? (category-objects cat) A)
    (error 'coslice-category "expected ~e to be an object in the category." A))

  (let* ([objs (category-objects cat)]
         [morphs (category-morphisms cat)]
         [src (category-source cat)]
         [tgt (category-target cat)]
         [comp (category-composition cat)]
         [idents (category-identities cat)]

         ;; 2. Objects of A/C: pairs (list X f) where f : A -> X
         [coslice-objs
          (for*/set ([X (in-set objs)]
                     [f (in-set morphs)]
                     #:when (and (equal? (src f) A)
                                 (equal? (tgt f) X)))
            (list X f))]

         ;; 3. Morphisms of A/C: arrows h : X -> Y in C such that h ∘ f = g
         [coslice-morphs
          (for*/set ([obj1 (in-set coslice-objs)]
                     [obj2 (in-set coslice-objs)]
                     [h (in-set morphs)]
                     #:when (let ([X (first obj1)] [f (second obj1)]
                                                   [Y (first obj2)] [g (second obj2)])
                              (and (equal? (src h) X)
                                   (equal? (tgt h) Y)
                                   (equal? (comp h f) g)))) ; triangle commutes: h ∘ f = g
            (list h obj1 obj2))]

         ;; 4. Identities in A/C: id_X for each (X, f)
         [coslice-idents
          (λ (obj)
            (define X (first obj))
            (define f (second obj))
            (list (idents X) obj obj))]

         ;; 5. Source and Target in A/C
         [coslice-src (λ (m) (second m))]
         [coslice-tgt (λ (m) (third m))]

         ;; 6. Composition in A/C: compose underlying arrows
         [coslice-comp
          (λ (m2 m1)
            (define h1 (first m1))
            (define h2 (first m2))
            (list (comp h2 h1) (coslice-src m1) (coslice-tgt m2)))])

    ;; Hand it over to the struct guard for mathematical certification!
    (category coslice-objs coslice-morphs coslice-idents coslice-comp coslice-src coslice-tgt)))

(define (discrete-category objs)
  (unless (set? objs)
    (error 'discrete-category "expected a set for objects. Given: ~e" objs))

  (let* ([morphs objs] ; In a discrete category, morphisms can just be represented by the objects (or their identities)
         [idents (λ (o) o)]
         [sources (λ (m) m)]
         [targets (λ (m) m)]
         [comp (λ (n m) m)]) ; Since only identities compose, n and m are identical here

    (category objs morphs idents comp sources targets)))


(define (composer x y)
  (list (first y) (second x)
        (cond
          [(equal? identity (third x)) (third y)]
          [(equal? identity (third y)) (third x)]
          [else (flatten (list (third x) (third y)))])))

(define (identifier x)
  (list x x identity))

(define Empty
  (category (set) (set)
            identifier composer first second))

(define Unit
  (category (set 0) (set (list 0 0 identity))
            identifier composer first second))

(define Two
  (category (set 0 1)
            (set (list 1 1 identity)
                 (list 0 0 identity))
            identifier composer first second))

(define Arrow
  (category (set 0 1)
            (set (list 1 1 identity)
                 (list 0 1 add1)
                 (list 0 0 identity))
            identifier composer first second))

(define Triangle
  (category (set 0 1 2)
            (set (list 2 2 identity)
                 (list 1 2 add1)
                 (list 0 2 (list add1 add1))
                 (list 1 1 identity)
                 (list 0 1 add1)
                 (list 0 0 identity))
            identifier composer first second))

(define Tetrahedron
  (category (set 0 1 2 3)
            (set (list 3 3 identity)
                 (list 2 3 add1)
                 (list 1 3 (list add1 add1))
                 (list 0 3 (list add1 add1 add1))
                 (list 2 2 identity)
                 (list 1 2 add1)
                 (list 0 2 (list add1 add1))
                 (list 1 1 identity)
                 (list 0 1 add1)
                 (list 0 0 identity))
            identifier composer first second))

(define (linear-order n)
  (category
   (list->set (build-list (add1 n) identity))
   (for*/set ([i (in-range 0 (add1 n))]
              [j (in-range 0 (add1 i))])
     (list j i (cond
                 [(= j i) identity]
                 [(= (add1 j) i) add1]
                 [else (make-list (- i j) add1)])))
   identifier composer first second))

(provide (all-defined-out))