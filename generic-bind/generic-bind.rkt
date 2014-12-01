#lang racket
(require syntax/parse
         syntax/parse/define
         racket/unsafe/ops
         "syntax-parse-utils.rkt"
         (for-syntax syntax/parse
                     racket/syntax
                     racket/match
                     racket/list ; append-map
                     racket/format
                     racket/function
                     syntax/parse/experimental/template
                     "stx-utils.rkt"
                     (only-in syntax/unsafe/for-transform expand-for-clause)
                     syntax/for-body))

;; TODO:
;; [x] 2013-08-26: ~let doesn't support ~vs DONE: 2013-08-26
;; [o] 2013-08-24: bug: creating "bound-ids" stx prop breaks ~define
;;                 (as in it doesn't recognize :bind classes anymore)
;; [o] 2013-08-22: get rid of suprious defines for generic binds nested in
;;                 generic ~v binding -- use splicing
;; [o] 2013-08-21: syntax object for ~m and ~vs is void? 
;;                 can I put anything useful here?
;; [o] 2013-08-21: create generic form for syntax to 
;;                 automatically define struct accessors?
;; [o] 2013-08-21: fix error msgs
;;                 - named ~let dup id references define

(provide ~vs $: $list $null $stx $and $c ; dont export ~m
         ~define ~lambda ~case-lambda ~case-define ~define/contract
         (rename-out [~lambda ~λ] [~lambda ~lam] [~lambda ~l] 
                     [~define ~def] [~define ~d]
                     [~m $] [~vs ⋈]
                     [~case-lambda ~case-lam] [~case-define ~case-def])
         ~let ~let* ~letrec
         ~for ~for/list ~for/vector ~for/fold ~for/lists ~for/first ~for/last 
         ~for/and ~for/or ~for/sum ~for/product 
         ~for/hash ~for/hasheq ~for/hasheqv
         ~for* ~for*/list ~for*/fold ~for*/vector ~for*/lists 
         ~for*/first ~for*/last ~for*/and ~for*/or ~for*/sum ~for*/product  
         ~for*/hash ~for*/hasheq ~for*/hasheqv
         define-match-bind ~struct)

(define-syntax-rule (values->list expr ...)
  (call-with-values (λ () expr ...) list))

;; ----------------------------------------------------------------------------
;; syntax classes

(begin-for-syntax
  ;; - need the following separate class because some instances 
  ;;   (ie anything involving values) needs the target of the bind to work
  ;; - for example, values can't be used in function defs
  ;; - so this is a subset of :bind/let, and is used in things like fn defs
  (define-syntax-class bind/non-let
    #:description "a generic bind instance for define contexts"
    #:auto-nested-attributes
    [pattern b
             #:attr get-info-struct (get-gen-bind-get-info/non-let #'b)
             #:when (gen-bind-get-info? (attribute get-info-struct))
             #:fail-when (gen-bind-get-info-let-only? (attribute get-info-struct))
             (format "can't use ~a pattern in non-let binding ctxt"
                     (syntax->datum #'b))
             #:attr get-info (gen-bind-get-info-get-info (attribute get-info-struct))
             #:attr get-info-stx (compose1 with-gen-bind-info-prop (attribute get-info))])
  (define-syntax-class bind/let
    #:description "a generic bind instance for let contexts"
    #:auto-nested-attributes
    [pattern b
             #:attr get-info-struct (get-gen-bind-get-info/let #'b)
             #:when (gen-bind-get-info? (attribute get-info-struct))
             #:attr get-info (gen-bind-get-info-get-info (attribute get-info-struct))
             #:attr get-info-stx (compose1 with-gen-bind-info-prop (attribute get-info))])
  (define-syntax-class id-or-bind/non-let
    #:description "a generic bind instance or id for define contexts"
    #:auto-nested-attributes
    [pattern :bind/non-let]
    [pattern x:id
             #:attr get-info (λ (b expr) (gen-bind-info/non-let #`(#,b) expr #'(begin)))
             #:attr get-info-struct (gen-bind-get-info/non-let (attribute get-info))
             #:attr get-info-stx (compose1 with-gen-bind-info-prop (attribute get-info))])
  (define-syntax-class id-or-bind/let
    #:description "a generic bind instance or id(s) for let contexts"
    #:auto-nested-attributes
    [pattern :bind/let]
    [pattern :id-or-bind/non-let]
    [pattern (~and ids (x:id ...))
             #:attr get-info (λ (b expr) (gen-bind-info/let-only b expr #'(begin)))
             #:attr get-info-struct (gen-bind-get-info/let-only (attribute get-info))
             #:attr get-info-stx (compose1 with-gen-bind-info-prop (attribute get-info))])
  (define-syntax-class info-stx
    [pattern info-stx
             #:attr info (syntax-property #'info-stx generic-bind-info-prop)
             #:when (gen-bind-info? (attribute info))
             #:with ids (gen-bind-info-ids (attribute info))
             #:with new-expr (gen-bind-info-new-expr (attribute info))
             #:with extra-def (gen-bind-info-extra-def (attribute info))
             #:attr let-only? (gen-bind-info-let-only? (attribute info))])
  (define-syntax-class info-stx/non-let
    #:auto-nested-attributes
    [pattern :info-stx
             #:when (not (attribute let-only?))
             #:with def (gen-bind-info-def (attribute info))])
  ) ;; end begin-for-syntax

;; ----------------------------------------------------------------------------
;; generic bind "instances"

;; match generic bind instance 
;; TODO: currently does not support nested generic binds

(define-syntax/parse ~m
  [(_ pat:expr)
   (bind-prop [(_ pat:expr) expr] #:def #'(match-define pat expr))])

(define-syntax/parse $stx
  [(_ pat pat-dir ...)
   (bind-prop [(_ pat pat-dir ...) expr] #:def #'(define/syntax-parse pat pat-dir ... expr))])

;; generic match bindings where the outer form is a list or cons
;; ie, just match list or match cons

(define-syntax/parse $list #:datum-literals (:)
  [(_ x ... : rst)
   (bind-prop [(_ x ... : rst) expr] #:def #'(match-define (list-rest x ... rst) expr))]
  [(_ x ...)
   (bind-prop [(_ x ...) expr] #:def #'(match-define (list x ...) expr))])

(define-syntax/parse $:
  [(_ x xs)
   (bind-prop [(_ x xs) expr] #:def #'(match-define (cons x xs) expr))])

(define-syntax/parse $null
  [_ (bind-prop [_ expr] #:def #'(match-define '() expr))])


(define-syntax/parse define-match-bind
  [(_ (name x ...))
   #:with $name (format-id #'name "$~a" #'name)
   #'(define-syntax/parse $name
       [(_ x ...) (bind-prop [(_ x ...) expr] #:def #'(match-define (name x ...) expr))])]
  [(_ name)
   #:with $name (format-id #'name "$~a" #'name)
   #:with ooo (quote-syntax ...)
   #'(define-syntax/parse $name
       [(_ x ooo) (bind-prop [(_ x ooo) expr] #:def #'(match-define (name x ooo) expr))])])


(begin-for-syntax ;; ~struct syntax classes
  (define-syntax-class struct-field
    [pattern field:id #:attr name #'field]
    [pattern [field:id opt ...] #:attr name #'field])
  ) ; end begin-for-syntax
(define-syntax/parse ~struct
  [(_ id:id super:id ... (field:struct-field ...) opt ...)
   #'(begin
       (struct id super ... (field ...) opt ...)
       (define-match-bind (id field.name ...)))])


;; values generic bind instance
;; - supports (one-level only) nested (non-let-restricted) generic binds
;;   (currently this is only the generic bind instance for match)
;;   (to support artitrary nesting, need to get the nested-defs of each x:v-bind)
(define-syntax/parse ~vs
  [(_ x:id-or-bind/non-let ...)
   (bind-prop [(_ x:id-or-bind/non-let ...) expr] #:let-only
              #:with (tmp ...) (generate-temporaries #'(x ...))
              #:with (def ...) (for/list ([get-info (in-list (attribute x.get-info))]
                                          [x (in-list (syntax->list #'(x ...)))]
                                          [tmp (in-list (syntax->list #'(tmp ...)))])
                                 (gen-bind-info-def (get-info x tmp)))
              #:ids #'(tmp ...)
              #:expr #'expr
              #:extra-def #'(begin def ...))])

;; $and
(define-syntax/parse $and
  [($and x:id-or-bind/non-let ...)
   (bind-prop [(_ x:id-or-bind/non-let ...) expr]
              #:with tmp (generate-temporary)
              #:with (def ...) (for/list ([get-info (in-list (attribute x.get-info))]
                                          [x (in-list (syntax->list #'(x ...)))])
                                 (gen-bind-info-def (get-info x #'tmp)))
              #:def #'(begin (define tmp expr) def ...))]
  [($and x:id-or-bind/let ...+)
   (bind-prop [(_ x:id-or-bind/let ...+) expr] #:let-only
              #:with lst (generate-temporary)
              #:ids #'(lst)
              #:expr #'(values->list expr)
              #:extra-def #'(begin (~define x (apply values lst)) ...))])



;; $c for contracts
(define-syntax/parse $c #:literals (values)
  [($c x:id c:expr)
   (bind-prop [(_ x:id c:expr) expr] #:def #'(define/contract x c expr))]
  [($c x:id-or-bind/non-let c:expr)
   (bind-prop [(_ x:id-or-bind/non-let c:expr) expr]
              #:with blame-id (syntax->identifier #'x)
              #:def #'(~define x (with-contract blame-id #:result c expr)))]
  [($c x:bind/let (values c:expr ...))
   (bind-prop [(_ x:bind/let (values c:expr ...)) expr] #:let-only
              #:with blame-id (syntax->identifier #'x)
              #:with ids (generate-temporaries #'(c ...))
              #:ids #'ids
              #:expr #'expr
              #:extra-def #'(~define x (with-contract blame-id #:results (c ...) (values . ids))))])

(define-for-syntax (syntax->identifier stx)
  (define sym (string->symbol (~s (syntax->datum stx))))
  (datum->syntax stx sym stx stx))


;; ----------------------------------------------------------------------------
;; ~define

;; syntax-classes for ~define
(begin-for-syntax
  (define-syntax-class def-function-header
    (pattern ((~or header:def-function-header name:id) . args:def-fn-args)
             #:attr new-header 
                    (template ((?? header.new-header name) . args.new-args))
             #:attr def #'args.def))

  ;; new-arg needs to be spliced bc of keywords
  (define-syntax-class def-fn-args
    [pattern (arg:fn-arg ...)
             #:attr new-args (template ((?@ . arg.new-arg) ...))
             #:attr def #'(begin arg.def ...)]
    [pattern (arg:fn-arg ... . rest:id)
             #:attr new-args (template ((?@ . arg.new-arg) ... . rest))
             #:attr def #'(begin arg.def ...)])
    
  ;; new-arg has to be list because keywords need to be spliced
  (define-splicing-syntax-class fn-arg
    #:auto-nested-attributes
    ;; need this here to avoid conflicting with arg-with-default
    ;; actually, this needs to be first, if I want to allow
    ;; generic binding identifiers
    [pattern (~and arg :bind/non-let)
             #:with tmp (generate-temporary)
             #:with new-arg #'(tmp)
             #:with def (gen-bind-info-def ((attribute get-info) #'arg #'tmp))]
    [pattern name:id 
             #:with new-arg #'(name)
             #:with def #'(begin)]
    [pattern [(~and arg :bind/non-let) default] 
             #:with tmp (generate-temporary)
             #:with new-arg #'([tmp default])
             #:with def (gen-bind-info-def ((attribute get-info) #'arg #'tmp))]
    [pattern [name:id default] 
             #:attr new-arg #'([name default])
             #:attr def #'(begin)]
    [pattern (~seq kw:keyword (~and arg :bind/non-let))
             #:attr tmp (generate-temporary)
             #:attr new-arg #'(kw tmp)
             #:attr def (gen-bind-info-def ((attribute get-info) #'arg #'tmp))]
    [pattern (~seq kw:keyword name:id) 
             #:attr new-arg #'(kw name)
             #:attr def #'(begin)]
    [pattern (~seq kw:keyword [(~and arg :bind/non-let) default])
             #:attr tmp (generate-temporary)
             #:attr new-arg #'(kw [tmp default])
             #:attr def (gen-bind-info-def ((attribute get-info) #'arg #'tmp))]
    [pattern (~seq kw:keyword [name:id default]) 
             #:attr new-arg #'(kw [name default])
             #:attr def #'(begin)])
    ) ;; end begin-for-syntax

;; ~define --------------------------------------------------------------------
(define-syntax/parse ~define #:stx stx
  [(_ b:bind/let body:expr)
   #:with b-info:info-stx ((attribute b.get-info-stx) #'b #'body)
   #'(begin (define-values b-info.ids b-info.new-expr) b-info.extra-def)]
  [(_ x:id body:expr) #'(define x body)]
  [(_ ?header:def-function-header ?body ...)
   #'(define ?header.new-header 
       ?header.def
       ?body ...)])

(define-syntax/parse ~define/contract #:stx stx
  [(_ b:bind/let c:expr body:expr)
   #'(~define ($c b c) body)]
  [(_ x:id c:expr body:expr)
   #'(define/contract x c body)]
  [(_ ?header:def-function-header c:expr ?body ...)
   #'(define/contract ?header.new-header c
       ?header.def
       ?body ...)])


;; ----------------------------------------------------------------------------
;; ~lambda

(begin-for-syntax
  (define-syntax-class lam-function-header
    [pattern args:lam-fn-args
             #:attr new-header #'args.new-args
             #:attr def #'args.def])

  ;; new-arg needs to be spliced bc of keywords
  (define-syntax-class lam-fn-args
    [pattern (arg:fn-arg ...)
             #:attr new-args (template ((?@ . arg.new-arg) ...))
             #:attr def #'(begin arg.def ...)]
    [pattern (arg0:fn-arg arg:fn-arg ... . rest:id)
             #:attr new-args 
                    (template 
                     ((?@ . arg0.new-arg) (?@ . arg.new-arg) ... . rest))
             #:attr def #'(begin arg0.def arg.def ...)])

    ;; ~case-lambda syntax-classes
    (define-syntax-class case-lam-function-header
      [pattern args:case-lam-fn-args
               #:attr new-header #'args.new-args
               #:attr def #'args.def])
    ;; new-arg needs to be spliced bc of keywords
    (define-syntax-class case-lam-fn-args
      [pattern (arg:case-lam-fn-arg ...)
               #:attr new-args (template ((?@ . arg.new-arg) ...))
               #:attr def #'(begin arg.def ...)]
      [pattern (arg0:case-lam-fn-arg arg:case-lam-fn-arg ... . rest:id)
               #:attr new-args 
               (template 
                ((?@ . arg0.new-arg) (?@ . arg.new-arg) ... . rest))
               #:attr def #'(begin arg0.def arg.def ...)])
    ;; new-arg has to be list because keywords need to be spliced
    ;; def must be list to accomodate args not requiring extra defs
    (define-splicing-syntax-class case-lam-fn-arg
      #:auto-nested-attributes
      ;; need this here to avoid conflicting with arg-with-default
      (pattern (~and arg :bind/non-let)
               #:with tmp (generate-temporary)
               #:attr new-arg #'(tmp)
               #:attr def (gen-bind-info-def ((attribute get-info) #'arg #'tmp)))
      (pattern name:id 
               #:attr new-arg #'(name)
               #:attr def #'(begin))
      (pattern [name:id default] 
               #:attr new-arg #'([name default])
               #:attr def #'(begin)))
  ) ; end define-for-syntax

(define-syntax/parse ~lambda #:stx stx
  [(_ b:bind/non-let body:expr ...)
   #:with tmp (generate-temporary #'b)
   #:with def (gen-bind-info-def ((attribute b.get-info) #'b #'tmp))
   #'(lambda (tmp) def body ...)]
  [(_ rst:id body:expr ...) #'(lambda rst body ...)]
  [(_ ?header:lam-function-header ?body ...)
   #'(lambda ?header.new-header 
       ?header.def
       ?body ...)])

(define-syntax/parse ~case-lambda
  [(_ [?header:case-lam-function-header ?body ...] ...)
   #:with (fn ...) (generate-temporaries #'(?header ...))
   #:with new-body 
   (let loop ([fns (syntax->list #'(fn ...))])
     (if (null? (cdr fns))
         #`(apply #,(car fns) args)
         #`(with-handlers ([exn:misc:match? (λ _ #,(loop (cdr fns)))])
             (apply #,(car fns) args))))
   #'(let ([fn (~lambda ?header ?body ...)] ...) (λ args new-body))])

(define-syntax/parse ~case-define #:datum-literals (→)
  [(_ f (x ... → body ...) ...)
   #'(define f (~case-lambda [(x ...) body ...] ...))]
  [(_ f clause ...) #'(define f (~case-lambda clause ...))])

;; ~let -----------------------------------------------------------------------
(begin-for-syntax
  (define-syntax-class let-bind-clause
    [pattern [x:id-or-bind/let e:expr]
             #:with x-info:info-stx ((attribute x.get-info-stx) #'x #'e)
             #:with norm #'[x-info.ids x-info.new-expr]
             #:with extra-def #'x-info.extra-def]))

(define-syntax/parse ~let
  ;; only non-let generic binds are allowed in named let
  ;; (same as other fn def forms)
  [(_ loop:id ([x:id-or-bind/non-let e] ...) body ...)
   #`(let ()
       (~define (loop x ...) body ...)
       (loop e ...))]
  [(_ (bc:let-bind-clause ...) body ...)
   #`(let-values (bc.norm ...)
       bc.extra-def ...
       body ...)])

(define-syntax/parse ~let*
  [(_ ([x:id-or-bind/let e]) body ...) 
   #'(~let ([x e]) body ...)]
  [(_ ([x:id-or-bind/let e] rst ...) body ...)
   #'(~let ([x e])
       (~let* (rst ...) body ...))])

(define-syntax/parse ~letrec
  [(_ ([x:id-or-bind/let e] ...) body ...)
   #'(let ()
       (~define x e) ...
       body ...)])

;; ~for forms -----------------------------------------------------------------
(begin-for-syntax
  (define-splicing-syntax-class seq-binding (pattern (b:for-binder seq:expr)))
  (define-splicing-syntax-class for-clause 
    [pattern :seq-binding] [pattern :when-or-break])
  (define-syntax-class for-binder
    [pattern :bind/let
             #:with tmp (generate-temporary)
             #:with optmpcp #'(tmp)
             #:with i:info-stx ((attribute get-info-stx) this-syntax #'optmpcp)
             #:fail-unless (and (eq? #'i.new-expr #'optmpcp) this-syntax)
             (format "~a cannot be used in a for clause" (syntax->datum this-syntax))
             #:with xs #'i.ids]
    [pattern :bind/non-let #:with xs (list (generate-temporary))]
    [pattern x:id #:attr xs #'(x)]
    [pattern (x:id ...) #:attr xs #'(x ...)])
  (define-splicing-syntax-class when-or-break 
    [pattern :when-clause] [pattern :break-or-final])
  (define-splicing-syntax-class when-clause
    #:attributes (test)
    [pattern (~seq #:when guard:expr) #:attr test #'guard]
    [pattern (~seq #:unless unless-guard:expr) #:attr test #'(not unless-guard)])
  (define-splicing-syntax-class break-clause [pattern (~seq #:break guard:expr)])
  (define-splicing-syntax-class final-clause [pattern (~seq #:final guard:expr)])
  (define-splicing-syntax-class break-or-final
    [pattern :break-clause] [pattern :final-clause])
  (define-splicing-syntax-class break/final-or-body 
    [pattern :break-or-final] [pattern body:expr])
  ) ; begin-for-syntax for ~for forms

(define-syntax/parse ~for/common ; essentially a foldl (ie uses an accum(s))
  ;; this clause allows naming of the accums so the body can reference them
  ;; -- used by for/fold and for/lists
  [(_ (~optional (~seq #:final final))
      combiner
      (~optional (~seq #:break? break?))
      ([accum base] ...)
      (c:for-clause ...) bb:break/final-or-body ...)
   #:with (body-res ...) (generate-temporaries #'(accum ...))
   #:with (b ...) (template ((?@ . bb) ...))
   #:with ((pre ...) (body ...)) (split-for-body #'(b ...) #'(b ...))
   #:with (pre-body:break/final-or-body ...) #'(pre ...)
   #:with expanded-for
   #`(let ([abort? #f] [accum base] ...)
       #,(let clauseloop ([cs #'(c ...)])
           (syntax-parse cs
             [() 
              #:with do-body
              ;; this must be a call-with-values because the number of results
              ;; is unpredictable (may be 0 values or multiple values)
              #`(call-with-values 
                 (lambda () body ...)
                 (lambda results (apply combiner accum ... results)))
              #`(let ()
                  ;; finalloop handles #:break and #:final in the body
                  #,(let finalloop ([pbs (syntax->list #'(pre-body ...))])
                      (if (null? pbs) #'do-body
                          (syntax-parse (car pbs)
                            [(#:break guard)
                             #`(if guard 
                                   (begin (set! abort? #t) (values accum ...))
                                   (let () #,(finalloop (cdr pbs))))]
                            [(#:final guard) 
                             #`(if guard 
                                   (begin (set! abort? #t) (let () #,(finalloop (cdr pbs))))
                                   (let () #,(finalloop (cdr pbs))))]
                            [(e:expr) #`(begin e #,(finalloop (cdr pbs)))]))))]
             [(([b:for-binder seq:expr]) ... (w:when-or-break) ... rst ...)
              (with-syntax* 
                  ([one-more-time (clauseloop #'(rst ...))]
                   [((ys ...) ...) #'(b.xs ...)]
                   [(([outer-binding ...]
                      outer-check
                      [loop-binding ...]
                      pos-guard
                      ;[inner-binding ...]
                      [[xs next] ...]
                      pre-guard
                      post-guard
                      [loop-arg ...]) ...)
                    (map (λ (x) (expand-for-clause x x)) (syntax->list #'([b.xs seq] ...)))]
                   [new-loop (generate-temporary)]
                   [its-done #'(values accum ...)]
                   [skip-it #`(if (and post-guard ...) 
                                  (if abort? 
                                      (values accum ...) 
                                      (new-loop accum ... loop-arg ... ...))
                                  its-done)]
                   [do-it 
                    #`(if (and post-guard ...) 
                          (let-values ([(accum ...) one-more-time])
                            (if abort?
                                (values accum ...)
                                (new-loop accum ... loop-arg ... ...)))
                          one-more-time)]
                   [conditional-body
                    (let whenloop ([ws (syntax->list #'(w ...))])
                      (if (null? ws)
                          #'do-it
                          (syntax-parse (car ws)
                            [(#:when guard) 
                             (if (eq? (syntax-e #'guard) #t)
                                 (whenloop (cdr ws))
                                 #`(if guard #,(whenloop (cdr ws)) skip-it))]
                            [(#:unless guard) #`(if guard skip-it #,(whenloop (cdr ws)))]
                            [(#:break guard) 
                             #`(if guard 
                                   (begin (set! abort? #t) its-done)
                                   #,(whenloop (cdr ws)))]
                            [(#:final guard) 
                             #`(if guard 
                                   (begin (set! abort? #t) #,(whenloop (cdr ws)))
                                   #,(whenloop (cdr ws)))])))])
                #`(let-values (outer-binding ... ...)
                    ;; must shadow accum in new loop, in case body references it
                    (let new-loop ([accum accum] ... loop-binding ... ...)
                      ;; must check break? first, bc more? pulls an item
                      (if (and #,@(if (attribute break?) #'((not (break? accum ...))) #'())
                               pos-guard ...)
                          (let-values ([xs next] ... ...)
                            (if (and pre-guard ...)
                                (~let ([b (values ys ...)] ...) conditional-body)
                                its-done))
                          its-done))))])))
   (if (attribute final)
       #'(let-values ([(accum ...) expanded-for]) (final accum ...))
       #'expanded-for)]
  ;; this clause has unnamed accums; name them and then call the first clause
  [(_ (~optional (~seq #:final final))
      combiner
      (~optional (~seq #:break? break?))
      (base ...) 
      (c:for-clause ...) bb:break/final-or-body ...)
   #:with (accum ...) (generate-temporaries #'(base ...))
   #`(~for/common #,@(if (attribute final) #'(#:final final) #'())
                  combiner 
                  #,@(if (attribute break?) #'(#:break? break?) #'())
                  ([accum base] ...) 
                  #,@(template (((?@ . c) ...) (?@ . bb) ...)))])

;; inserts #:when #t between each (non-#:when/unless) clause
(define-syntax/parse ~for*/common
  [(_ (~optional (~seq #:final fin))
      comb
      (~optional (~seq #:break? b?))
      (base ...) 
      ((~seq sb:seq-binding ... wb:when-or-break ...) ...) body ...)
   #:with ((new-sb ...) ...)
   ;; append accounts for list added by splicing-syntax-class
   (map (λ (ss) (append-map 
                 (λ (s) (append (syntax->list s) (list #'#:when #'#t)))
                 (syntax->list ss)))
        (syntax->list #'((sb ...) ...)))
   ;; wb is also a list (due to splicing-stx-class)
   #:with (new-clause ...) 
   (template ((?@ . (new-sb ... (?@ . ((?@ . wb) ...)))) ...))
   #`(~for/common #,@(if (attribute fin) #'(#:final fin) #'())
                  comb 
                  #,@(if (attribute b?) #'(#:break? b?) #'())
                  (base ...) (new-clause ...) body ...)])

(define-syntax/parse mk~for/
  [(_ name combiner (base ...)
      (~optional (~seq #:final fin))
      (~optional (~seq #:break? b?)))
   #:with new-name (format-id #'name "~~for/~a" #'name)
   #:with new-name* (format-id #'name "~~for*/~a" #'name)
   #`(begin 
       (define-syntax-rule (new-name x (... ...)) 
         (~for/common #,@(if (attribute fin) #'(#:final fin) #'())
                      combiner 
                      #,@(if (attribute b?) #'(#:break? b?) #'())
                      (base ...) x (... ...)))
       (define-syntax-rule (new-name* x (... ...)) 
         (~for*/common #,@(if (attribute fin) #'(#:final fin) #'()) 
                       combiner 
                       #,@(if (attribute b?) #'(#:break? b?) #'())
                       (base ...) x (... ...))))])

(define-syntax-rule (~for x ...) (~for/common void ((void)) x ...))
(define-syntax-rule (~for* x ...) (~for*/common void ((void)) x ...))

;; ~for/list ~for*/list and ~for/lists probably need a "right folding" for/common
;;   but for now, just reverse the output
;; - have to reverse args in cons bc acc is first
(mk~for/ list (λ (acc y) (unsafe-cons-list y acc)) (null) #:final reverse)
;; break as soon as we find something
(mk~for/ first (λ (acc y) y) (#f) #:break? identity)
(mk~for/ last (λ (acc y) y) (#f))
(mk~for/ and (λ (acc y) (and acc y)) (#t) #:break? not)
(mk~for/ or (λ (acc y) (or acc y)) (#f) #:break? identity)
(mk~for/ sum + (0))
(mk~for/ product * (1))
(mk~for/ hash hash-set ((hash)))
(mk~for/ hasheq hash-set ((hasheq)))
(mk~for/ hasheqv hash-set ((hasheqv)))

(define-syntax/parse ~for/fold ; foldl
  [(_ ([accum init] ...) (c:for-clause ...) bb:break/final-or-body ...)
   #:with (res ...) (generate-temporaries #'(accum ...))
   ;; combiner drops old accums and uses result(s) of body as current accums
   (template (~for/common
              #:final values (λ (accum ... res ...) (values res ...))
              ([accum init] ...) ((?@ . c) ...) (?@ . bb) ...))])
(define-syntax/parse ~for*/fold
  [(_ ([accum init] ...) (c:for-clause ...) bb:break/final-or-body ...)
   #:with (res ...) (generate-temporaries #'(accum ...))
   ;; combiner drops old accums and uses result(s) of body as current accums
   (template (~for*/common 
              #:final values (λ (accum ... res ...) (values res ...))
              ([accum init] ...) ((?@ . c) ...) (?@ . bb) ...))])

(define-syntax/parse ~for/lists
  [(_ (accum ...) (c:for-clause ...) bb:break/final-or-body ...)
   #:with (res ...) (generate-temporaries #'(accum ...))
   ;; combiner drops old accums and uses result(s) of body as current accums
   (template (~for/common 
              #:final (λ (accum ...) (values (reverse accum) ...))
              (λ (accum ... res ...) (values (unsafe-cons-list res accum) ...))
              ([accum null] ...) ((?@ . c) ...) (?@ . bb) ...))])

(define-syntax/parse ~for*/lists
  [(_ (accum ...) (c:for-clause ...) bb:break/final-or-body ...)
   #:with (res ...) (generate-temporaries #'(accum ...))
   ;; combiner drops old accums and uses result(s) of body as current accums
   (template (~for*/common 
              #:final (λ (accum ...) (values (reverse accum) ...))
              (λ (accum ... res ...) (values (unsafe-cons-list res accum) ...))
              ([accum null] ...) ((?@ . c) ...) (?@ . bb) ...))])

;; ~for/vector is an imperative mess
(define-syntax/parse ~for/vector
  [(_ (~optional (~seq (~seq #:length len) 
                       (~optional (~seq #:fill fill) #:defaults ([fill #'0]))))
      x ...)
   (if (attribute len)
       ;; if #:length is specified, then we need a break? because there may
       ;; be more iterations than #:length
       #'(let ([vec (make-vector len fill)]
               [vec-len len])
           (define i 0)
           (~for/common 
            #:final (λ _ vec)
            (λ (acc y) (unsafe-vector-set! vec i y) (set! i (add1 i))) ; combiner
            #:break? (λ _ (>= i vec-len))
            ((void)) ; base ...
            x ...))
       ;; repeatedly checking break? is slow so if no #:length is given,
       ;; first build list and then copy into a result vector
       #'(~for/common
          #:final 
          (λ (lst) 
            (let* ([vec-len (length lst)]
                   [vec (make-vector vec-len)])
              (let loop ([n vec-len] [lst lst])
                (if (zero? n) vec
                    (let ([n-1 (sub1 n)])
                      (unsafe-vector-set! vec n-1 (unsafe-car lst))
                      (loop n-1 (unsafe-cdr lst)))))))
          (λ (acc y) (unsafe-cons-list y acc))
          (null)
          x ...))])
(define-syntax/parse ~for*/vector
  [(_ (~optional (~seq (~seq #:length len) 
                       (~optional (~seq #:fill fill) #:defaults ([fill #'0]))))
      x ...)
   (if (attribute len)
       ;; if #:length is specified, then we need a break? because there may
       ;; be more iterations than #:length
       #'(let ([vec (make-vector len fill)]
               [vec-len len])
           (define i 0)
           (~for*/common 
            #:final (λ _ vec)
            (λ (acc y) (unsafe-vector-set! vec i y) (set! i (add1 i))) ; combiner
            #:break? (λ _ (>= i vec-len))
            ((void)) ; base ...
            x ...))
       ;; repeatedly checking break? is slow so if no #:length is given,
       ;; first build list and then copy into a result vector
       #'(~for*/common
          #:final 
          (λ (lst) 
            (let* ([vec-len (length lst)]
                   [vec (make-vector vec-len)])
              (let loop ([n vec-len] [lst lst])
                (if (zero? n) vec
                    (let ([n-1 (sub1 n)])
                      (unsafe-vector-set! vec n-1 (unsafe-car lst))
                      (loop n-1 (unsafe-cdr lst)))))))
          (λ (acc y) (unsafe-cons-list y acc))
          (null)
          x ...))])


;; this is a right-folding ~for/common
;;  it's currently unused, but would probably be faster for ~for/list
;#;(define-syntax (~for/common/foldr stx)
;  (syntax-parse stx
;    [(_ flatten combiner base (c:for-clause ...) bb:break-clause ... body:expr ...)
;     #:with expanded-for
;     (let ([depth 0])
;       (define res
;     (let stxloop ([cs #'(c ... bb ...)])
;       (syntax-parse cs
;         [() #'(begin body ...)]
;         [(([b:for-binder seq:expr]) ... (w:when-or-break) ... rst ...)
;;          #:with (s ...) (generate-temporaries #'(b ...))
;          #:with (seq-not-empty? ...) (generate-temporaries #'(b ...))
;          #:with (seq-next ...) (generate-temporaries #'(b ...))
;          #:with new-loop (generate-temporary)
;          #:with skip-it #'(new-loop) ;;#'(new-loop (seq-rst s) ...)
;          #:with do-it 
;;            #`(call-with-values 
;;               (λ () #,(stxloop #'(rst ...)))
;;               (λ this-iter (call-with-values 
;;                        (λ () skip-it)
;;                        (λ other-iters (combiner this-iter other-iters)))))
;          #`(let ([result #,(stxloop #'(rst ...))]) (combiner result skip-it))
;          #:with its-done #'base
;          #:with one-more-time 
;;            #`(call-with-values 
;;               (λ () #,(stxloop #'(rst ...)))
;;               (λ this-iter (call-with-values 
;;                             (λ () base)
;;                             (λ other-iters (combiner this-iter other-iters)))))
;            #`(let ([result #,(stxloop #'(rst ...))]) (combiner result base))
;          #:with conditional-body
;            (let whenloop ([ws (syntax->list #'((w) ...))])
;              (if (null? ws)
;                  #'do-it
;                  (syntax-parse (car ws)
;                    [((#:when guard)) #`(if guard #,(whenloop (cdr ws)) skip-it)]
;                    [((#:unless guard)) #`(if guard skip-it #,(whenloop (cdr ws)))]
;                    [((#:break guard)) #`(if guard its-done #,(whenloop (cdr ws)))]
;                    [((#:final guard)) #`(if guard one-more-time #,(whenloop (cdr ws)))])))
;            (set! depth (add1 depth))
;          #`(let-values ([(seq-not-empty? seq-next) (sequence-generate seq)] ...)
;               (let new-loop ()
;                 (if (and (seq-not-empty?) ...)
;                     (~let ([b.new-b (seq-next)] ...)
;;                       #,@(append-map syntax->list (syntax->list #'(b.nested-defs ...)))
;                           conditional-body)
;                     base)))])))
;       (let flatten-loop ([n (- depth 2)] [res res])
;         (if (<= n 0) res
;           (flatten-loop (sub1 n) #`(flatten #,res)))))
;     #'expanded-for]))
