#lang racket/base

(provide (all-defined-out))

(require racket/match
         syntax/parse
         racket/syntax
         "syntax-parse-utils.rkt"
         (for-template racket/base)
         (for-syntax racket/base
                     syntax/parse
                     ))

(define (->bool x)
  (if x #t #f))

(define current-generic-bind-let-context? (make-parameter #f ->bool))
(define (generic-bind-let-context?) (current-generic-bind-let-context?))

(define generic-bind-info-prop 'generic-bind-info)

(define (with-gen-bind-info-prop prop)
  (syntax-property #'(void) generic-bind-info-prop prop))

(struct gen-bind-get-info (get-info let-only?) #:transparent)
(struct gen-bind-info (ids new-expr extra-def let-only?) #:transparent)
(define (gen-bind-info-def info)
  (match-define (gen-bind-info ids expr extra-def _) info)
  #`(begin (define-values #,ids #,expr) #,extra-def))

(define-match-expander gen-bind-get-info/non-let
  (syntax-parser [(gen-bind-get-info/non-let get-info:expr)
                  #'(gen-bind-get-info get-info #f)])
  (syntax-parser [(gen-bind-get-info/non-let get-info:expr)
                  #'(gen-bind-get-info get-info #f)]))
(define-match-expander gen-bind-get-info/let-only
  (syntax-parser [(gen-bind-get-info/let-only get-info:expr)
                  #'(gen-bind-get-info get-info #t)])
  (syntax-parser [(gen-bind-get-info/let-only get-info:expr)
                  #'(gen-bind-get-info get-info #t)]))
(define-match-expander gen-bind-get-info/let
  (syntax-parser [(gen-bind-get-info/let get-info:expr)
                  #'(gen-bind-get-info get-info _)])
  (syntax-parser [(gen-bind-get-info/let get-info:expr)
                  #'(gen-bind-get-info get-info #t)]))

(define-match-expander gen-bind-info/non-let
  (syntax-parser [(gen-bind-info/non-let ids:expr new-expr:expr extra-def:expr)
                  #'(gen-bind-info ids new-expr extra-def #f)])
  (syntax-parser [(gen-bind-info/non-let ids:expr new-expr:expr extra-def:expr)
                  #'(gen-bind-info ids new-expr extra-def #f)]))
(define-match-expander gen-bind-info/let-only
  (syntax-parser [(gen-bind-info/let-only ids:expr new-expr:expr extra-def:expr)
                  #'(gen-bind-info ids new-expr extra-def #t)])
  (syntax-parser [(gen-bind-info/let-only ids:expr new-expr:expr extra-def:expr)
                  #'(gen-bind-info ids new-expr extra-def #t)]))
(define-match-expander gen-bind-info/let
  (syntax-parser [(gen-bind-info/let ids:expr new-expr:expr extra-def:expr)
                  #'(gen-bind-info ids new-expr extra-def _)])
  (syntax-parser [(gen-bind-info/let ids:expr new-expr:expr extra-def:expr)
                  #'(gen-bind-info ids new-expr extra-def #t)]))

;; get-gen-bind-get-info/non-let : Syntax Syntax -> (U Gen-Bind-Get-Info #f)
(define (get-gen-bind-get-info/non-let b)
  (define expanded-stx (try-local-expand b #:let #f))
  (cond [(not (syntax? expanded-stx)) #f]
        [else
         (define get-info-struct (syntax-property expanded-stx generic-bind-info-prop))
         (match get-info-struct
           [(gen-bind-get-info/non-let get-info-proc)
            (define (new-get-info b expr)
              (define info (get-info-proc b expr))
              (match info
                [(gen-bind-info/non-let ids new-expr extra-def) info]
                [(gen-bind-info/let-only ids new-expr extra-def)
                 (gen-bind-info/let-only #f #f #f)]))
            (gen-bind-get-info/non-let new-get-info)]
           [(gen-bind-get-info/let-only get-info-proc)
            (gen-bind-get-info/let-only #f)]
           [#f #f])]))

;; get-gen-bind-get-info/let : Syntax Syntax -> (U Gen-Bind-Get-Info #f)
(define (get-gen-bind-get-info/let b)
  (define expanded-stx (try-local-expand b #:let #t))
  (cond [(not (syntax? expanded-stx)) #f]
        [else
         (define get-info-struct (syntax-property expanded-stx generic-bind-info-prop))
         (match get-info-struct
           [(gen-bind-get-info _ _) get-info-struct]
           [#f #f])]))

(define (get-gen-bind-get-info b #:let [let-context? #f])
  (cond [let-context? (get-gen-bind-get-info/let b)]
        [else (get-gen-bind-get-info/non-let b)]))

;; need this to catch errors when expanding header of function defines
(define (try-local-expand stx #:let let-context?)
  (parameterize ([current-generic-bind-let-context? (and let-context? #t)])
    (with-handlers ([exn:fail:syntax:unbound? (λ _ #f)] ;; unbound var
                    [exn:fail:syntax? (λ _ #f)] ;; ie keyword as datum
                    [exn:fail? (λ (e) (printf "uh oh\n") (raise e))])
      (local-expand stx 'expression null))))

(begin-for-syntax
  (define-syntax-class bind-prop-clause/non-let
    [pattern [(b-pat tmp:id)
              stuff ...
              #:def def:expr]
             #:with norm
             #'[(b-pat e)
                #:with tmp (generate-temporary)
                stuff ...
                (gen-bind-info/non-let #'(tmp) #'e def)]]
    [pattern [(b-pat expr-pat)
              #:tmp tmp-pat
              stuff ...
              #:ids ids:expr
              #:expr new-expr:expr
              #:extra-def extra-def:expr]
             #:with norm
             #'[(b-pat expr-pat)
                #:with tmp-pat (generate-temporary)
                stuff ...
                (gen-bind-info/non-let ids new-expr extra-def)]]
    [pattern [(b-pat expr-pat)
              stuff ...
              #:ids ids:expr
              #:expr new-expr:expr
              #:extra-def extra-def:expr]
             #:with norm
             #'[(b-pat expr-pat)
                stuff ...
                (gen-bind-info/non-let ids new-expr extra-def)]])
  (define-syntax-class bind-prop-clause/let-only
    [pattern [(b-pat expr-pat)
              #:let-only
              stuff ...
              #:ids ids:expr
              #:expr new-expr:expr
              #:extra-def extra-def:expr]
             #:with norm
             #'[(b-pat expr-pat)
                stuff ...
                (gen-bind-info/let-only ids new-expr extra-def)]]))

(define-syntax/parse bind-prop
  [(bind-prop clause:bind-prop-clause/let-only ...+)
   #'(with-gen-bind-info-prop
      (gen-bind-get-info/let-only
       (lambda (b expr)
         (syntax-parse #`(#,b #,expr)
           clause.norm ...))))]
  [(bind-prop clause:bind-prop-clause/non-let ...+)
   #'(with-gen-bind-info-prop
      (gen-bind-get-info/non-let
       (lambda (b expr)
         (syntax-parse #`(#,b #,expr)
           clause.norm ...))))]
  [(bind-prop . clause:bind-prop-clause/let-only)
   #'(bind-prop clause)]
  [(bind-prop . clause:bind-prop-clause/non-let)
   #'(bind-prop clause)])

