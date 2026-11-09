#lang racket

(require (file "categories.rkt")
         (file "functors.rkt")
         (file "natural_transformations.rkt"))

(struct adjunction
  (cat1 cat2 Funct1 Funct2 Unit coUnit)
  #:guard (λ (cat1 cat2 Funct1 Funct2 Unit coUnit this)
            (unless (=category? cat1 (Functor-source Funct1)
                            (Functor-target Funct2))
              (error))
            (unless (=category? cat2 (Functor-source Funct2)
                            (Functor-target Funct1))
              (error))
            (unless (=Functor? (FunctorCompose Funct2 Funct1)
                               (Natural-Transformation-target Unit))
              (error))
            (unless (=Functor? (FunctorCompose Funct1 Funct2)
                               (Natural-Transformation-source coUnit))
              (error))
            (values cat1 cat2 Funct1 Funct2 Unit coUnit))
  )