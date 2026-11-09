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
        (error this "expected source of ~e to equal source of ~e." nm nm))
      (unless (equal? (target n) (target nm))
        (error this "expected target of ~e to equal target of ~e." nm nm)))

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
  (and (equal? (category-objects cat1) (category-objects cat2))
       (equal? (category-morphisms cat1) (category-morphisms cat2))))

(define (opposite cat)
  (category (category-objects cat)
            (for/set ([m (in-set (category-morphisms cat))])
              (list (second m) (first m) (third m)))
            (category-identities cat)
            (λ (x y) ((category-composition cat) y x))
            (category-target cat) (category-source cat)))

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

(define (n-simplex n)
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