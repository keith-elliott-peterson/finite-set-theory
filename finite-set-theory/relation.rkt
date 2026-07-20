#lang racket
(require racket/lazy-require)
(lazy-require ["function.rkt" (function-proc
                               function-src
                               function-tgt)])

(struct relation (proc src tgt)
  #:transparent
  #:guard
  (λ (proc src tgt this)
    (when (and (set? src)
               (set? tgt)
               (for*/and
                   ([i src]
                    [j tgt])
                 (boolean? (proc i j))))
      (values proc src tgt)))
  #:methods gen:equal+hash
  [(define equal-proc
     (λ (rel1 rel2 rec-equal?)
       (and (set=? (relation-src rel1)
                   (relation-src rel2))
            (set=? (relation-tgt rel1)
                   (relation-tgt rel2))
            (for/and ([i (in-set (relation-src rel1))]
                      [j (in-set (relation-tgt rel1))])
              (equal? ((relation-proc rel1) i j)
                      ((relation-proc rel2) i j))))))
   (define hash-proc
     (λ (rel recur-equal-hash)
       (+ (set-count (relation-src rel))
          (set-count (relation-tgt rel)))))
   (define hash2-proc
     (λ (rel recur-equal-hash)
       (+ (set-count (relation-src rel))
          (set-count (relation-tgt rel)))))]
  #:property prop:procedure
  
  (case-lambda
    [(r)
     (if (set=? (set)(relation-src r)(relation-tgt r))
         (set)
         (error))]
    [(r x y)
     (cond [(and (set-member? (relation-src r) x)
                 (set-member? (relation-tgt r) y))
            ((relation-proc r) x y)]
           [else
            (error)])]))

(define (compose-relations . rels)
  (define not-rels (filter-not relation? rels))
  (define non-composables
    (if (empty? rels)
        null
        (for/list
            ([i (rest rels)]
             [j rels]
             #:when
             (not (set=?
                   (relation-tgt j)
                   (relation-src i))))
          (list j i))
        ))
  (cond
    [(empty? rels)
     (raise-arity-error
      'compose-relations (arity-at-least 1))]
    [(not (empty? not-rels))
     (apply 
      (curry raise-arguments-error 'compose-relations
             (if (= 1 (length not-rels))
                 "the following argument is not a relation:"
                 "the following arguments are not relations:"))
      (flatten (map (curry cons "") not-rels)))]
    [(not (empty? non-composables))
     (apply 
      (curry raise-arguments-error 'compose-relations
             "the following relations are non-composable:")
      (foldr (λ(x y)(cons "" (cons x y)))
             '() non-composables))]
    [(empty? (rest rels))
     (first rels)]
    [else
     (apply
      compose-relations
      (cons (relation
             (λ (x y)
               (for/or
                   ([i (relation-tgt (first rels))])
                 (and
                  ((relation-proc (first rels)) x i)
                  ((relation-proc (second rels)) i y))))
             (relation-src (first rels))
             (relation-tgt (second rels)))
            (rest (rest rels))))]))

(define-values
  (homogeneous-relation
   homogeneous-relation?)
  (values (λ(proc st) (relation proc st st))
          (λ(rel)(set=? (relation-src rel)(relation-tgt rel)))))

(define-values
  (endorelation endorelation?)
  (values homogeneous-relation homogeneous-relation?))

(define (identity-relation st)
  (endorelation equal? st))

(define (function->relation func)
  (relation (λ (x y)
              (equal? ((function-proc func) x)
                      y))
            (function-src func)
            (function-tgt func)))

(provide (all-defined-out)
         (struct-out relation))