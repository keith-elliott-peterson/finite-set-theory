#lang racket
(require pict pict-abbrevs
         "./finite-set-theory.rkt"
         "./function.rkt"
         ;"./bundle-theory.rkt"
         )



(define dot
  #;(inset (disk 5) 5)
  (blank))

(define (->string x)
  (letrec
      ([rec-pred 
        (λ(p)(λ(x)(and (p x)
                       (andmap (disjoin string?
                                        number?
                                        char?
                                        symbol?
                                        boolean?
                                        stringable-list?
                                        stringable-set?)
                               (set->list x)))))]
       [stringable-list? (rec-pred list?)]
       [stringable-set? (rec-pred set?)])
    (cond
      [(string? x) x]
      [(number? x) (number->string x) ]
      [(char? x)(string x)]
      [(symbol? x)(string-append
                   "“"(symbol->string x) "”")]
      [(boolean? x)(if x "true" "false")]
      [(stringable-list? x)
       (string-join (map ->string x) ", "
                    #:before-first "("
                    #:after-last ")"
                    )]
      [(stringable-set? x)
       (string-join (map ->string (set->list x)) ", "
                    #:before-first "{"
                    #:after-last "}"
                    )]
      )))

(define (dot-list lst [style 'roman]
                  #:scale [scl 1]
                  #:appender [appender vc-append]
                  #:draw-element-sets? [draw-sets? #f])
  (map
   (λ(x)
     (inset (appender
             (cond
               [(and (or draw-sets?
                         (equal? draw-sets? 'recur))
                     (set? x))
                (launder 
                 (if (equal? draw-sets? 'recur)
                     (set-drawer (dot-list (set->list x) #:draw-element-sets? 'recur))
                     (set-drawer (dot-list (set->list x) #:draw-element-sets? draw-sets?)))
                 )]
               [(pict? x)
                (launder (scale x scl))]
               [(function? x)
                (launder
                 (add-rectangle-background
                  (scale (function-drawer x) scl)
                  #:draw-border? #t
                  #:x-margin 5 	 	 	 
                  #:y-margin 5))]
               [(and (list? x) (function? (first x)))
                (hc-append 1 (launder
                              (add-rectangle-background
                               (scale (function-drawer (first x)) scl)
                               #:draw-border? #t
                               #:x-margin 5 	 	 	 
                               #:y-margin 5))
                           (text (->string (rest x)) style (* scl 15)))]
               [else
                (text (->string x) style (* scl 15))])
             dot) 10))
   lst)
  )

;; canonical ordering so pics don’t jitter
(define (canon-list s) (sort (set->list s) symbol<?))
(define (dots s) (dot-list (canon-list s)))


(define (set-drawer dotlst #:lable [lable #f]
                    #:appender [appender vc-append])
  (let ([pict-set (add-rectangle-background
                   (apply appender 5 dotlst)
                   #:draw-border? #t
                   #:x-margin 10	 	 	 	 
                   #:y-margin 10)])
    (if (string? lable)
        (vc-append (text lable 'roman 30)
                   pict-set)
        pict-set)))


(define (function-drawer #:distance-between [w 200]
                         #:scale-in [scli 1]
                         #:scale-out [sclo 1]
                         #:use-as-input-dot-list [use-in-dots #f]
                         #:use-as-output-dot-list [use-out-dots #f]
                         #:use-as-input-pict [use-in-pict #f]
                         #:use-as-output-pict [use-out-pict #f]
                         #:src-finder [src-find rc-find]
                         #:tgt-finder [tgt-find lc-find]
                         #:start-angle  [start-angle 0]
                         #:end-angle  [end-angle 0]
                         #:appender [appender hc-append]
                         f)
  (if (function? f)
      (let* [(input (set->list (function-src f)))
             (output (set->list (function-tgt f)))
             (dot-in (if (list? use-in-dots)
                         use-in-dots
                         (dot-list input
                                   #:scale scli)))
             (dot-out (if (list? use-out-dots)
                          use-out-dots
                          (dot-list output
                                    #:scale sclo)))
             (dot-func (map (λ(x) (list-ref dot-out x))
                            (filter-not false?
                                        (map
                                         (λ(x)
                                           (index-of output (f x)))
                                         input))
                            ))]
        (foldr
         (λ(val1 val2 lst)
           (pin-arrow-line
            10 lst
            (if use-in-pict
                (list use-in-pict val1)
                val1)
            src-find
            (if use-out-pict
                (list use-out-pict val2)
                val2)
            tgt-find
            #:line-width 1
            #:start-angle  start-angle
            #:end-angle  end-angle
            ))
         (appender
          w (if (pict? use-in-pict)
                use-in-pict
                (set-drawer dot-in))
          (if (pict? use-out-pict)
              use-out-pict
              (set-drawer dot-out)))
         dot-in dot-func))
      (error 'function-drawer
             "expected a function, given ~a" f)
      ))

;; Highlight a single fibre f^{-1}({y*}) using the *same* geometry as function-drawer.
(define (function-drawer/highlight f y*
         #:distance-between [d 160]
         #:thickness [lw 3]
         #:start-angle [θ #f]
         #:end-angle   [φ #f]
         #:src-finder  [src-find rc-find]
         #:tgt-finder  [tgt-find lc-find]
         #:use-as-input-dot-list  [in-dots  #f]
         #:use-as-output-dot-list [out-dots #f])
  (define srcL (set->list (function-src f)))
  (define tgtL (set->list (function-tgt f)))
  (define idl  (or in-dots  (dot-list srcL)))
  (define odl  (or out-dots (dot-list tgtL)))

  ;; base, with the very same angles/finders
  (define base
    (function-drawer f
      #:use-as-input-dot-list  idl
      #:use-as-output-dot-list odl
      #:distance-between d
      #:src-finder src-find
      #:tgt-finder tgt-find
      #:start-angle θ
      #:end-angle   φ))

  ;; overdraw only the chosen fibre, thicker, same angles/finders
  (for/fold ([p base]) ([x (in-list srcL)])
    (define y (f x))
    (if (equal? y y*)
        (pin-arrow-line 10 p
          (list-ref idl (index-of srcL x)) rc-find
          (list-ref odl (index-of tgtL y))  lc-find
          #:start-angle θ
          #:end-angle   φ
          #:line-width  lw)
        p)))


(define (composable? f g)
  (and (function? f) (function? g)
       (set=? (function-tgt f) (function-src g))))

(define (composable-function-drawer
         #:distance-between [w 200]
         #:scale-in [scli 1]
         #:scale-out [sclo 1]
         #:use-as-input-dot-list [use-in-dots #f]
         #:use-as-output-dot-list [use-out-dots #f]
         #:use-as-input-pict [use-in-pict #f]
         #:use-as-output-pict [use-out-pict #f]
         #:src-finder [src-find rc-find]
         #:tgt-finder [tgt-find lc-find]
         #:start-angle [start-angle 0]
         #:end-angle   [end-angle 0]
         #:appender [appender hc-append]
         func . funcs)

  ;; Gather the chain
  (define fs (cons func funcs))

  ;; 1) All args must be functions
  (unless (andmap function? fs)
    (error 'composable-function-drawer "expected functions"))

  ;; 2) Adjacent sources/targets must match
  (unless (for/and ([f (in-list fs)]
                    [g (in-list (rest fs))])
            (set=? (function-tgt f) (function-src g)))
    (error 'composable-function-drawer
           "non-composable chain; targets/sources don’t match"))

  ;; Draw
  (cond
    [(empty? funcs)
     (function-drawer
      #:distance-between w
      #:scale-in scli
      #:scale-out sclo
      #:use-as-input-dot-list use-in-dots
      #:use-as-output-dot-list use-out-dots
      #:use-as-input-pict use-in-pict
      #:use-as-output-pict use-out-pict
      #:src-finder src-find
      #:tgt-finder tgt-find
      #:start-angle start-angle
      #:end-angle   end-angle
      #:appender appender
      func)]
    [(empty? (rest funcs))
     (let* ([dl (dot-list (set->list (function-tgt func)))]
            [g  (first funcs)])
       (function-drawer
        func
        #:distance-between w
        #:use-as-input-dot-list use-in-dots
        #:use-as-output-dot-list dl
        #:use-as-input-pict use-in-pict
        #:use-as-output-pict
        (function-drawer
         g
         #:distance-between w
         #:use-as-input-dot-list dl
         #:use-as-output-dot-list use-out-dots
         #:use-as-output-pict use-out-pict
         #:tgt-finder tgt-find
         #:end-angle end-angle
         #:appender appender)
        #:src-finder src-find
        #:start-angle start-angle
        #:appender appender))]
    [else
     (let ([dl (dot-list (set->list (function-tgt func)))])
       (function-drawer
        func
        #:distance-between w
        #:use-as-input-dot-list use-in-dots
        #:use-as-output-dot-list dl
        #:use-as-input-pict use-in-pict
        #:use-as-output-pict
        (apply composable-function-drawer
               #:distance-between w
               #:use-as-input-dot-list dl
               #:use-as-output-dot-list use-out-dots
               #:use-as-output-pict use-out-pict
               #:tgt-finder tgt-find
               #:end-angle end-angle
               #:appender appender
               (rest fs))
        #:src-finder src-find
        #:start-angle start-angle
        #:appender appender))]))

;; draw a whole chain and its composite, with stable layouts
;; returns two picts: chain, composite
(define (draw-chain+composite
         #:distance-between [d 160]
         #:start-angle [θ #f]
         f . fs)
  (define fs* (cons f fs))
  (define in-dots  (dots (function-src f)))
  (define out-dots (dots (function-tgt (last fs*))))
  (define chain
    (apply composable-function-drawer
           #:use-as-input-dot-list  in-dots
           #:use-as-output-dot-list out-dots
           #:distance-between d
           fs*))
  ;; compose left→right: (compose-functions f g k) = k ∘ g ∘ f
  (define h (apply compose-functions fs*))
  (define composite
    (function-drawer h
      #:use-as-input-dot-list  in-dots
      #:use-as-output-dot-list out-dots
      #:distance-between d
      #:start-angle θ))
  (values chain composite))

(define (isomorphism-drawer func #:direction [direction 'ltr])
  (let* ([srclst (set->list (function-src func))]
         [tgtlst (map func srclst)]
         [isolst (map list
                      (dot-list srclst #:draw-element-sets? #t)
                      (dot-list tgtlst))])
    (map (λ(x)(scale (pin-arrow-line
                      10 (hc-append 100 (first x) (second x))
                      (first x) rc-find
                      (second x) lc-find
                      #:line-width 1
                      #:start-angle 0
                      #:end-angle  0) 3/4))
         isolst)))


;; Draw a commuting square from a (commuting-square f g h k) struct
;; Layout:
;;     A --f--> B
;;     |         |
;;     g         h
;;     |         |
;;     C --k--> D
(define (commuting-square-drawer S
         #:h-distance      [dx 160]
         #:v-distance      [dy 120]
         #:scale-A         [sA 1]
         #:scale-B         [sB 1]
         #:scale-C         [sC 1]
         #:scale-D         [sD 1]
         ;; horizontal arrows (left→right) — same defaults as function-drawer
         #:h-src-finder    [h-src rc-find]
         #:h-tgt-finder    [h-tgt lc-find]
         #:h-start-angle   [hθ 0]
         #:h-end-angle     [hφ 0])

  (unless (commuting-square? S)
    (error 'commuting-square-drawer "expected a commuting-square, got ~a" S))

  (define f (commuting-square-f S)) ;; A→B
  (define g (commuting-square-g S)) ;; A→C
  (define h (commuting-square-h S)) ;; B→D
  (define k (commuting-square-k S)) ;; C→D

  ;; sets
  (define A (function-src f))
  (define B (function-tgt f))
  (define C (function-tgt g))
  (define D (function-tgt h)) ; (= function-tgt k)

  ;; elements (freeze an order so arrows index consistently)
  (define AL (set->list A))
  (define BL (set->list B))
  (define CL (set->list C))
  (define DL (set->list D))

  ;; dot geometry reusing function-drawer’s idioms
  (define Adots (dot-list AL #:scale sA))
  (define Bdots (dot-list BL #:scale sB))
  (define Cdots (dot-list CL #:scale sC))
  (define Ddots (dot-list DL #:scale sD))

  ;; boxed sets
  (define Aset (set-drawer Adots))
  (define Bset (set-drawer Bdots))
  (define Cset (set-drawer Cdots))
  (define Dset (set-drawer Ddots))

  ;; grid
  (define left-col  (vc-append dy Aset Cset))
  (define right-col (vc-append dy Bset Dset))
  (define base      (hc-append dx left-col right-col))

  ;; helper: find index
  (define (idx xs x)
    (let ([i (index-of xs x)])
      (if i i (error 'commuting-square-drawer "element not found: ~a" x))))

  ;; draw top: f : A→B
  (define with-f
    (for/fold ([p base]) ([a (in-list AL)])
      (define b ((function-proc f) a))
      (pin-arrow-line 10 p
        (list Aset (list-ref Adots (idx AL a))) h-src
        (list Bset (list-ref Bdots (idx BL b))) h-tgt
        #:line-width 1
        #:start-angle hθ
        #:end-angle   hφ)))

  ;; draw bottom: k : C→D
  (define with-k
    (for/fold ([p with-f]) ([c (in-list CL)])
      (define d ((function-proc k) c))
      (pin-arrow-line 10 p
        (list Cset (list-ref Cdots (idx CL c))) h-src
        (list Dset (list-ref Ddots (idx DL d))) h-tgt
        #:line-width 1
        #:start-angle hθ
        #:end-angle   hφ)))

  ;; draw left: g : A→C
  (define with-g
    (for/fold ([p with-k]) ([a (in-list AL)])
      (define c ((function-proc g) a))
      (pin-arrow-line 10 p
        (list Aset (list-ref Adots (idx AL a))) lc-find
        (list Cset (list-ref Cdots (idx CL c))) lc-find
        #:line-width 1
        #:start-angle pi
        #:end-angle   0)))

  ;; draw right: h : B→D
  (inset (for/fold ([p with-g]) ([b (in-list BL)])
    (define d ((function-proc h) b))
    (pin-arrow-line 10 p
      (list Bset (list-ref Bdots (idx BL b))) rc-find
      (list Dset (list-ref Ddots (idx DL d))) rc-find
      #:line-width 1
      #:start-angle 0
      #:end-angle   pi)) 100 0))



(provide (all-defined-out))
