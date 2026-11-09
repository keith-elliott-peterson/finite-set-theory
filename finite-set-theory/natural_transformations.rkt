#lang racket

(require (file "categories.rkt")
         (file "functors.rkt"))

(struct Natural-Transformation
  (map source target)
  #:transparent
  #:guard
  (λ (map source target this)
    (unless (=category? (Functor-source source)
                        (Functor-source target))
      (error this "expected ~e and ~e to match on source categories."
             source target))
    (unless (=category? (Functor-target source)
                        (Functor-target target))
      (error this "expected ~e and ~e to match on target categories."
             source target))
    
    (define C (Functor-source source))
    (define D (Functor-target source))
    
    ;; 1. Check object components: map(A) : F(A) -> G(A) in D
    (for ([o (in-set (category-objects C))])
      (define component (map o))
      (unless (set-member? (category-morphisms D) component)
        (error this "expected ~e to be member of morphisms in ~e" component D))
      (unless (equal? ((category-source D) component) ((Functor-map source) o))
        (error this "expected source of ~e to equal ~e" component ((Functor-map source) o)))
      (unless (equal? ((category-target D) component) ((Functor-map target) o))
        (error this "expected target of ~e to equal ~e" component ((Functor-map target) o))))
    
    ;; 2. Check naturality condition: α_B ∘ F(f) = G(f) ∘ α_A
    (for ([m (in-set (category-morphisms C))])
      (define src-m ((category-source C) m))
      (define tgt-m ((category-target C) m))
      (define lhs ((category-composition D) (map tgt-m) ((Functor-map source) m)))
      (define rhs ((category-composition D) ((Functor-map target) m) (map src-m)))
      (unless (equal? lhs rhs)
        (error this "naturality condition failed on morphism ~e: ~e ≠ ~e" m lhs rhs)))
    
    (values map source target)))

(define (=Natural-Transformation? ntrans1 ntrans2)
  (and (=Functor? (Natural-Transformation-source ntrans1)
                  (Natural-Transformation-source ntrans2))
       (=Functor? (Natural-Transformation-target ntrans1)
                  (Natural-Transformation-target ntrans2))
       (for/and ([o (in-set (category-objects
                             (Functor-source (Natural-Transformation-source ntrans1))))])
         (equal? ((Natural-Transformation-map ntrans1) o)
                 ((Natural-Transformation-map ntrans2) o)))))

(define (IdentityNatTrans Funct)
  (Natural-Transformation
   (λ (x)
     (cond [(set-member? (category-objects (Functor-source Funct)) x)
            ((category-identities (Functor-target Funct))
             ((Functor-map Funct) x))]
           [(set-member? (category-morphisms (Functor-source Funct)) x)
            ((Functor-map Funct) x)]))
   Funct Funct))

(define (Cone Funct obj map)
  (Natural-Transformation
   map
   (ConstantFunct (Functor-source Funct) (Functor-target Funct) obj)
   Funct))

(define (CoCone Funct obj map)
  (Natural-Transformation
   map
   Funct
   (ConstantFunct (Functor-source Funct) (Functor-target Funct) obj)))

(define (LeftWhisker Funct ntrans)
  (unless (=category? (Functor-source Funct)
                      (Functor-target (Natural-Transformation-source ntrans)))
    (error "LeftWhisker: domain/codomain mismatch"))
  (Natural-Transformation
   (compose (Functor-map Funct) (Natural-Transformation-map ntrans))
   (FunctorCompose Funct (Natural-Transformation-source ntrans))
   (FunctorCompose Funct (Natural-Transformation-target ntrans))))

(define (RightWhisker ntrans Funct)
  (unless (=category? (Functor-target Funct)
                      (Functor-source (Natural-Transformation-source ntrans)))
    (error "RightWhisker: domain/codomain mismatch"))
  (Natural-Transformation
   (compose (Natural-Transformation-map ntrans) (Functor-map Funct))
   (FunctorCompose (Natural-Transformation-source ntrans) Funct)
   (FunctorCompose (Natural-Transformation-target ntrans) Funct)))

(define (NatTransCompose ntrans1 ntrans2)
  (define F1 (Natural-Transformation-source ntrans1))
  (define F2 (Natural-Transformation-target ntrans2))
  (unless (=Functor? F1 F2)
    (error "NatTransCompose: target of ntrans2 must equal source of ntrans1"))
  
  (cond
    [(=Natural-Transformation? ntrans1 (IdentityNatTrans F1)) ntrans2]
    [(=Natural-Transformation? ntrans2 (IdentityNatTrans F2)) ntrans1]
    [else
     (define D (Functor-target F1))
     (Natural-Transformation
      (λ (o)
        ;; Vertical composition component: (ntrans1 ∘ ntrans2)_o = ntrans1_o ∘ ntrans2_o
        ((category-composition D)
         ((Natural-Transformation-map ntrans1) o)
         ((Natural-Transformation-map ntrans2) o)))
      (Natural-Transformation-source ntrans2)
      (Natural-Transformation-target ntrans1))]))

(provide (all-defined-out))