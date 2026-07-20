#lang racket
(require racket/struct
         "finite-set-theory.rkt"
         "function.rkt"
         "./relation.rkt")

(struct preorder
  (set relation)
  #:transparent
  #:guard
  (λ (set relation this)
    (unless (set? set)
      (error this "Expected a set. Given: ~a." set))
    (for*/and ([i (in-set set)]
               [j (in-set set)]
               [k (in-set set)])
      (unless (boolean? (relation i j))
        (error this "Expected a relation. Given: ~a." relation))
      (unless (relation i i)
        (error this "Expected a reflexive relation. Given: ~a." relation))
      (unless (implies
               (and (relation i j) (relation j k))
               (relation i k))
        (error this "Expected a transitive relation. Given: ~a." relation)))
    (values set relation))
  #:methods
  gen:custom-write
  [(define write-proc
     (make-constructor-style-printer
      (lambda (obj) 'preorder)
      (lambda (obj) (list (preorder-set obj)
                          (object-name (preorder-relation obj))))))])

(define (make-preorder-relation #:use-relation [rel #f] . rels)
  (if rel
      rel
      (λ (x y)
        (or (equal? x y)
            (for/or ([r (in-list rels)])
              (and (equal? x (first r))
                   (equal? y (second r))))
            (for*/or ([r1 (in-list rels)]
                      [r2 (in-list rels)])
              (equal? (second r1)
                      (first r2)))))))

(define (monotone-map f preord)
  (let* ([P (preorder-set preord)]
         [≤ (preorder-relation preord)])
    (preorder
     (list->set (map f (set->list P)))
     (make-preorder-relation
      (for/list ([i (in-set P)]
                 [j (in-set P)]
                 #:when (≤ i j))
        (list (f i) (f j)))))))

(define (antitone-map f preord)
  (let* ([P (preorder-set preord)]
         [≤ (preorder-relation preord)])
    (preorder
     (list->set (map f (set->list P)))
     (make-preorder-relation
      (for/list ([i (in-set P)]
                 [j (in-set P)]
                 #:when (≤ i j))
        (list (f j) (f i)))))))

(define (preorder=? preord1 preord2 . preords)
  (let ([P1 (preorder-set preord1)]
        [≤1 (preorder-relation preord1)]
        [P2 (preorder-set preord2)]
        [≤2 (preorder-relation preord2)])
    (if (null? preords)
        (or (equal? preord1 (preorder P1 ≤2))
            (equal? preord2 (preorder P2 ≤1)))
        (and (preorder=? preord1 preord2)
             (apply preorder=? preord2 preords)))))

(define (subpreorder? preord1 preord2)
  (let ([P1 (preorder-set preord1)]
        [P2 (preorder-set preord2)]
        [≤1 (preorder-relation preord1)]
        [≤2 (preorder-relation preord2)])
    (and (subset? P1 P2)
         (preorder=? preord2 (preorder P2 ≤1))
         (preorder=? preord1 (preorder P1 ≤2)))))

(define (proper-subpreorder? preord1 preord2)
  (let ([P1 (preorder-set preord1)]
        [P2 (preorder-set preord1)])
    (and (proper-subset? P1 P2)
         (subpreorder? P1 P2))))

(define (preorder->opposite-preorder preord)
  (let ([P (preorder-set preord)]
        [≤ (preorder-relation preord)])
    (preorder P (λ (x y)(≤ y x)))))

(define (set->power-set st)
  (preorder (list->set (combinations (set->list st))) subset?))

(define (minimal? preord x)
  (let ([P (preorder-set preord)]
        [≤ (preorder-relation preord)])
    (unless (set-member? P x)
      (error "~a must be an element of ~a." x P))
    (for/and ([e (in-set P)])
      (≤ x e))))

(define (maximal? preord x)
  (let ([P (preorder-set preord)]
        [≤ (preorder-relation preord)])
    (unless (set-member? P x)
      (error "~a must be an element of ~a." x P))
    (for/and ([e (in-set P)])
      (≤ e x))))

(define (lower-bounds preord st)
  (let ([P (preorder-set preord)]
        [≤ (preorder-relation preord)])
    (if (subset? st P)
        (for/set ([e1 (in-set P)]
                  #:when
                  (for/and ([e2 (in-set st)])
                    (≤ e1 e2)))
          e1)
        (error "~a is not a subset of ~a." st P))))

(define (upper-bounds preord st)
  (let ([P (preorder-set preord)]
        [≤ (preorder-relation preord)])
    (if (subset? st P)
        (for/set ([e1 (in-set P)]
                  #:when
                  (for/and ([e2 (in-set st)])
                    (≤ e2 e1)))
          e1)
        (error "~a is not a subset of ~a." st P))))

(define (least-element preord st)
  (let ([P (preorder-set preord)]
        [≤ (preorder-relation preord)])
    (if (subset? st P)
        (for/set ([e1 (in-set st)]
                  #:when
                  (for/and ([e2 (in-set st)])
                    (≤ e1 e2)))
          e1)
        (error "~a is not a subset of ~a." st P))))

(define (greatest-element preord st)
  (let ([P (preorder-set preord)]
        [≤ (preorder-relation preord)])
    (if (subset? st P)
        (for/set ([e1 (in-set st)]
                  #:when
                  (for/and ([e2 (in-set st)])
                    (≤ e2 e1)))
          e1)
        (error "~a is not a subset of ~a." st P))))

(define (bounded-below? preord st)
  (not (set-empty? (lower-bounds preord st))))

(define (bounded-above? preord st)
  (not (set-empty? (upper-bounds preord st))))

(define (bounded? preord st)
  (and (bounded-below? preord st)
       (bounded-above? preord st)))

(define (meet preord . m)
  (let* ([S (list->set m)]
         [LB (lower-bounds preord S)]
         [P (preorder-set preord)]
         [≤ (preorder-relation preord)])
    (if (subset? S P)
        (for/last ([e1 (in-set LB)]
                   #:when
                   (for/and ([e2 (in-set LB)])
                     (≤ e2 e1)))
          e1)
        (error "~a is not a subset of ~a" S P))))

(define (infimum preord st)
  (let ([P (preorder-set preord)])
    (if (subset? st P)
        (apply meet preord (set->list st))
        (error))))

(define (join preord . m)
  (let* ([S (list->set m)]
         [UB (upper-bounds preord S)]
         [P (preorder-set preord)]
         [≤ (preorder-relation preord)])
    (if (subset? S P)
        (for/last ([e1 (in-set UB)]
                   #:when
                   (for/and ([e2 (in-set UB)])
                     (≤ e1 e2)))
          e1)
        (error "~a is not a subset of ~a." S P))))

(define (supremum preord st)
  (let ([P (preorder-set preord)])
    (if (subset? st P)
        (apply join preord (set->list st))
        (error))))

(struct poset preorder ()
  #:guard
  (λ (set relation this)
    (if (not (for/and ([e1 (in-set set)]
                       [e2 (in-set set)])
               (implies (and (relation e1 e2)
                             (relation e2 e1))
                        (equal? e1 e2))))
        (error this "doesn't satisfy the poset conditions")
        (values set relation))))

(define (function->poset func)
  (if (not (function? func))
      (error 'function->poset "Expects ~a to be a function." func)
      (let* ([f (function-proc func)]
             [src (function-src func)]
             [tgt (function-tgt func)]
             [src+ (set-cartesian-product (set 0) src)]
             [tgt+ (set-cartesian-product (set 1) tgt)]
             [f+ (λ(x)(list 1 (f (second x))))])
        (poset
         (set-disjoint-union src tgt)
         (λ(x y)
           (or (and (set-member? src+ x)
                    (set-member? src+ y)
                    (equal? x y))
               (and (and (set-member? src+ x)
                         (set-member? tgt+ y)
                         (equal? (f+ x) y)))
               (and (set-member? tgt+ x)
                    (set-member? tgt+ y)
                    (equal? x y))))
         ))))

(define (principle-upper-set post x)
  (let ([P (preorder-set post)]
        [≤ (preorder-relation post)])
    (if (and (poset? post) (set-member? P x))
        (preorder
         (for/set ([e (in-set P)]
                   #:when (≤ x e))
           e)
         ≤)
        (error 'principle-upper-set "Expects ~a to be a poset, and ~a an element of ~a"
               post x P))))

(define (principle-down-set post x)
  (let ([P (preorder-set post)]
        [≤ (preorder-relation post)])
    (if (and (poset? post) (set-member? P x))
        (preorder
         (for/set ([e (in-set P)]
                   #:when (≤ e x))
           e)
         ≤)
        (error 'principle-down-set "Expects ~a to be a poset, and ~a an element of ~a"
               post x P))))
  
(define (bounded-poset? post)
  (and (poset? post)
       (bounded? post (preorder-set post))))

(define (covers? post x y)
  (let* ([P (preorder-set post)]
         [≤ (preorder-relation post)]
         [P< (λ (x y) (and (≤ x y)
                           (not (equal? x y))))])
    (cond [(not (poset? post))
           (error 'covers? "Expects a poset. Given ~a." post)]
          [(nand (set-member? P x)
                 (set-member? P y))
           (error 'covers? "~a and ~a must be elements of ~a."
                  x y P)]
          [else (not (for/or ([e (in-set P)])
                       (and (P< y e) (P< e x))))]
          )))

(define (join-semilattice? preord)
  (let* ([P (preorder-set preord)]
         [≤ (preorder-relation preord)])
    (for*/and ([e1 (in-set P)]
               [e2 (in-set P)])
      (not (not (join preord e1 e2))))))

(define (meet-semilattice? preord)
  (let* ([P (preorder-set preord)]
         [≤ (preorder-relation preord)])
    (for*/and ([e1 (in-set P)]
               [e2 (in-set P)])
      (not (not (meet preord e1 e2))))))

(define (lattice? preord)
  (and (meet-semilattice? preord)
       (join-semilattice? preord)))
      
(define (β rel)
  (for/set ([i (relation->rgraph rel)])
    (preorder (upper-bounds (set->power-set (relation->rgraph rel)) (set (list i)))
              subset?)))

(provide (all-defined-out))