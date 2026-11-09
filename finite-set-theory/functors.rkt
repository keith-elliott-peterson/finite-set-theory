#lang racket

(require (file "categories.rkt"))

(struct Functor (map source target)
  #:transparent
  #:guard
  (λ (map source target this)
    (unless (category? source)
      (error this "expected source to be category, given: ~e" source))
    (unless (category? target)
      (error this "expected target to be category, given: ~e" target))
    (for [(o (in-set (category-objects source)))]
      (unless (set-member? (category-objects target) (map o))
        (error this "expected ~e to be member of ~e" (map o)
               (category-objects target))))
    (for [(m (in-set (category-morphisms source)))]
      (unless (set-member? (category-morphisms target) (map m))
        (error this "expected ~e to be member of ~e" (map m)
               (category-morphisms target))))
    (for* ([m (in-set (category-morphisms source))]
           [n (in-set (category-morphisms source))])
      (when (equal? ((category-target source) m)
                    ((category-source source) n))
        (unless (equal?
                 ((category-composition target) (map n) (map m))
                 (map ((category-composition source) n m)))
          (error "~e doesn't satisfy functoriality." map))))
    (values map source target)))

(define (=Functor? Funct1 Funct2)
  (and
   (=category? (Functor-source Funct1) (Functor-source Funct2))
   (=category? (Functor-target Funct1) (Functor-target Funct2))
   (for/and ([o (in-set (category-objects (Functor-source Funct1)))])
     (equal? ((Functor-map Funct1) o) ((Functor-map Funct2) o)))
   (for/and ([m (in-set (category-morphisms (Functor-source Funct1)))])
     (equal? ((Functor-map Funct1) m) ((Functor-map Funct2) m)))))

(define ((IdentityFunctmap cat) x)
  (cond
    [(set-member? (category-objects cat) x) x]
    [(set-member? (category-morphisms cat) x) x]))

(define (IdentityFunct cat)
  (Functor (IdentityFunctmap cat) cat cat))

(define (IdentityFunct? Funct)
  (and
   (=category? (Functor-source Funct) (Functor-target Funct))
   (for/and ([o (in-set (category-objects (Functor-source Funct)))])
     (equal? o ((Functor-map Funct) o)))
   (for/and ([m (in-set (category-morphisms (Functor-source Funct)))])
     (equal? m ((Functor-map Funct) m)))))

(define (InclusionFunct cat1 cat2)
  (Functor (IdentityFunctmap cat1) cat1 cat2))

(define ((OppositeFunctmap cat) x)
  (cond
    [(set-member? (category-objects cat) x) x]
    [(set-member? (category-morphisms cat) x)
     (list (second x) (first x) (third x))]))

(define (OppositeFunct cat)
  (Functor (OppositeFunctmap cat) cat (opposite cat)))

(define ((!-Functmap cat) x)
  (cond
    [(set-member? (category-objects cat) x) 0]
    [(set-member? (category-morphisms cat) x) (list 0 0 identity)]))

(define (!-Funct cat)
  (Functor (!-Functmap cat) cat Unit))

(define ((ObjectFunctmap cat obj) x)
  (cond
    [(set-member? (category-objects Unit) x) obj]
    [(set-member? (category-morphisms Unit) x)
     ((category-identities cat) obj)]))

(define (ObjectFunct cat obj)
  (unless (set-member? (category-objects cat) obj)
    (error "expected ~e to be member of ~e." obj (category-objects cat)))
  (Functor (ObjectFunctmap cat obj) Unit cat))

(define (FunctorCompose Funct1 Funct2)
  (unless (=category? (Functor-source Funct1) (Functor-target Funct2))
    (error "expected source of" Funct1 "to match target of" Funct2))
  (cond
    [(IdentityFunct? Funct1) Funct2]
    [(IdentityFunct? Funct2) Funct1]
    [else (Functor (compose (Functor-map Funct1) (Functor-map Funct2))
                   (Functor-source Funct2)
                   (Functor-target Funct1))]))

(define (ConstantFunct src tgt obj)
  (FunctorCompose (ObjectFunct tgt obj) (!-Funct src)))

(define (FunctorApply Funct cat)
  (unless (=category? (Functor-source Funct) cat)
    (error "expected source of ~e to match category ~e." Funct cat))
  (if (IdentityFunct? Funct)
      cat
      (category
       (for/set ([o (in-set (category-objects cat))])
         ((Functor-map Funct) o))
       (for/set ([m (in-set (category-morphisms cat))])
         ((Functor-map Funct) m))
       (category-identities (Functor-target Funct))
       (category-composition (Functor-target Funct))
       (category-source (Functor-target Funct))
       (category-target (Functor-target Funct)))))

(define (hom-set cat A B)
  (for/set ([m (in-set (category-morphisms cat))]
            #:when (and (equal? ((category-source cat) m) A)
                        (equal? ((category-target cat) m) B)))
    m))

(define (faithfull? Funct)
  (define C (Functor-source Funct))
  (for*/and ([A (in-set (category-objects C))]
             [B (in-set (category-objects C))])
    (define hom (hom-set C A B))
    (define mapped-hom (for/set ([m (in-set hom)]) ((Functor-map Funct) m)))
    (= (set-count hom) (set-count mapped-hom))))

(define (full? Funct)
  (define C (Functor-source Funct))
  (define D (Functor-target Funct))
  (define F (Functor-map Funct))
  (for*/and ([A (in-set (category-objects C))]
             [B (in-set (category-objects C))])
    (define hom-C (hom-set C A B))
    (define hom-D (hom-set D (F A) (F B)))
    (define image-hom (for/set ([m (in-set hom-C)]) (F m)))
    (subset? hom-D image-hom)))

(define (fully-faithfull? Funct)
  (and (full? Funct) (faithfull? Funct)))

(provide (all-defined-out))