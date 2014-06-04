#lang racket

(require
  "proofs.rkt"
  racket/stxparam
  (for-syntax syntax/parse))

(provide
  define/tactic
  return

  program
  contra
  obvious
  qed
  try)

(module+ test
  (require rackunit))

;; A Tactic is an any ... pfenv -> pfenv

;; Tactics modify the proof context and build programs, encoding the
;; changes information in the pfenv.

;; There is kind of an implicit failure monad in tactics, via `hole'
;; `try'.

;; define/tactic provides a simply way to define new tactics by pattern
;; matching on the pfenv, and provides monadic functions like return.
(define-syntax (define/tactic syn)
  (syntax-parse syn
    [(_ (name:id args:id ... pf:id)
        [(pat:expr ... (ctx:expr t:expr e:expr)) body:expr ...] ...)
     (for ([x (syntax->datum #'((pat ...) ...))])
          (let ([args (length (syntax->list #'(args ...)))]
                [pats (length x)])
            (unless (equal? args pats)
              (raise-syntax-error #f
                "number of arguments (~a) must match number of patterns (~a)"
                args pats))))
       #`(define (name args ... pf)
           (syntax-parameterize ([return (syntax-id-rules ()
                                           [(_ term)
                                            (replace-term pf term)])])
              (match (list args ... pf)
                [(list pat ... (pfenv ctx t e)) body ...] ...
                [_ (return hole)])))]))

;; return is used inside define/tactic to inject a term into the current
;; pfenv
(define-syntax-parameter return
  (lambda (stx)
    (raise-syntax-error (syntax-e stx) "can only be used in define/tactic")))

;; TODO: Should probably exist in proofs.rkt
(define (replace-term pf t)
  (pfenv (pfenv-ctx pf) t (pfenv-type pf)))

;; program is a special tactic that takes a representation of a program and
;; returns a pfenv.
;; TODO: Make macro to allow writing T instead of 'T?
(define (program term type)
  (pfenv '() term type))

;; TODO: Annotation should be optional if the type can be inferred, but I'm
;; not smart enough to infer the types
#;(module+ test
  (check-equal? (program 'true 'T) (pfenv '() 'true 'T))
  (check-equal? (program '(pair true true)) (pfenv '() '(pair true true) '(and T T)))
  (check-equal? (program '(λ (x) (((fst x) : (not α)) (snd x))))
                (pfenv '() '(λ (x) (((fst x) : (not α)) (snd x))) '(not (and (not α) α))))
  )
#;(define (infer-type t)
    (car (judgment-holds (synth-base mt ,t A) A)))

#;(begin-for-syntax
  (define (infer-type t)
    (car (judgment-holds (synth-base mt ,t A) A))))
#;(module+ test
   ;; TODO: Totally abusing my knowledge of representation of redex program,
   ;; breaking information hiding. I should make sure to use (term ...)
   ;; everywhere instead of quoating manually.
   (check-equal? (infer-type (term true)) (term T))
   (check-equal? (infer-type (term (pair true true))) (term (and T T))))

;; qed is a special tactic that takes a pfenv and returns a
;; representation of a program. 
;; TODO: It maybe shouldn't be called qed
(define qed pfenv-term)

;; TODO: Eventually, I'd like to support something like Coq's
;; `admitted'.
#;(define (UNSAFE-ASSUMPTION-THAT-IS-PROBABLY-FALSE)
  (UNSAFE-ASSUMPTION-THAT-IS-PROBABLY-FALSE))

;; TODO: An assume tactic
#;(define/match ((assume f) pf k)
  [((pfenv ctx e) (list x ': f) k)
   `(λ (x) ,(k (pfenv (cons `(,x ,f) ctx) 'F)))])

;; TODO: Lambda doesn't work that way in this language. To split and's
;; in the context is actually non-trivial
#;(define/tactic (split-and pf)
  [((ctx e t))
   (for/fold ([acc e])
             ([x ctx])
     (match x
       [`(,x (and ,e1 ,e2)) 
         `((λ (,(gensym x)) 
              ((λ (,(gensym x))
                  ,e) (fst ,x))) (snd ,x))]
       [_ (cons x acc)]))
   (let ([ctx ])
     (pfenv ctx e t))])
#;(module+ test
  (check-equal? 
    (length (pfenv-ctx (split-and (pfenv '((x (and α (not α)))) 'true 'T))))
    2))

;; TODO: Make contra even smart; or perhaps add `resolution'
(define/tactic (contra pf)
  [((ctx _ 'F))
   (or (for/or ([x ctx])
         (match x
           [`(,x (and ,e (not ,e)))
             (return `((snd ,x) (fst ,x)))]
           [`(,x (and (not ,e) ,e))
             (return `((fst ,x) (snd ,x)))]
           [_
             (for/first ([y ctx] #:when (equal? (second y) `(not ,(second x))))
                        (return `(,(first y) ,(first x))))]))
       (return hole))])


;; TODO: obvious is currently limited to filling in a hole. Another
;; tactic is needed to guide obvious down a term to the hole
(define (obvious pf)
  (obvious^ pf))

(define/tactic (obvious^ pf)
  [((_ _ 'T)) (return 'true)]
  [((_ _ 'F)) (contra pf)]
  [((ctx t `(and ,e1 ,e2)))
   (let ([x (obvious^ (pfenv ctx t e1))]
         [y (obvious^ (pfenv ctx t e2))])
     (return `(pair ,(pfenv-term x) ,(pfenv-term y))))]
  [((ctx t `(or ,e1 ,e2)))
   (return `((inj ,(try
                     [(obvious^ (pfenv ctx t e1)) => pfenv-term]
                     [(obvious^ (pfenv ctx t e2)) => pfenv-term])) : (or ,e1 ,e2)))]
  [((ctx t `(not ,e)))
    (let ([x (gensym 'x_)])
      (return `(λ (,x) ,(pfenv-term (obvious^ (pfenv (cons `(,x ,e) ctx) t 'F))))))])

;; try is kind of a tactic. It is formed like a cond, but the predicate
;; of each clause are expected to result in pfenvs
(define-syntax (try syn)
  (define (rewrite-clause clause)
    (syntax-case clause (=> else)
      [(else body) #`(else body)]
       ;; TODO: SO EFFICIENT!
      [(pred => body) #`((hole? (pfenv-term pred)) (body (pfenv-term pred)))]
      [(pred body) #`((hole? (pfenv-term pred)) body)]))
  (syntax-case syn ()
    [(try clauses ...)
     #`(cond #,@(map rewrite-clause (syntax->list #'(clauses ...))))]))

(module+ test
  (check-equal? (qed (obvious^ (pfenv '() hole 'T))) 'true)
  (check-equal? (qed (obvious^ (pfenv '() hole 'F))) hole)
  (check-equal? (qed (obvious^ (pfenv '() hole '(and T F)))) `(pair true ,hole))
  (check-equal? (qed (obvious^ (pfenv '((x α) (y (not α))) hole 'F))) '(y x))
  (check-equal? (qed (obvious^ (pfenv '((x α) (y (not α))) hole '(and T F))))
                '(pair true (y x)))
  )


;; Simplying assumption:
;; at-hole may behave unexpectedly if used with a tactic that modifies
;; the type or context at the hole.
#;(define/tactic (at-hole tactic pf)
  [((_ (? hole?) t))
   (tactic pf)]
  [((ctx `(,e : ,A) A))
   (let ([res (at-hole tactic (pfenv ctx e A))])
     (pfenv (pfenv-ctx res)
            `(,(pfenv-term res) : ,(pfenv-type res))
            (pfenv-type res)))]
  [((ctx `(λ (,x) ,e) `(not ,A)))
   ;; TODO: Perhaps only build the lambda if the result still has the
   ;; assumption around
   (let ([res (at-hole tactic (pfenv (cons `(,x ,A) ctx) e 'F))])
     (pfenv ctx `(λ (,x) ,(pfenv-term res)) `(not ,A)))]
  [((ctx `(pair ,e1 ,e2) `(and ,A ,B)))
   (let ([res1 (at-hole tactic (pfenv ctx e1 A))]
         [res2 (at-hole tactic (pfenv ctx e2 B))])
     ;; TODO: Perahps a union of the ctx
     (pfenv ctx `(pair ,(pfenv-term res1) ,(pfenv-term res2))
            `(and ,(pfenv-type res1) ,(pfenv-type res2))))]
  [((ctx `(inj ,e) `(or ,A ,B)))
   (define ((finishup t) pf)
     (pfenv ctx `(inj ,(pfenv-term pf)) (t (pfenv-type))))
   (try
     [(at-hole tactic (pfenv ctx e A)) =>
      (lambda (pf) ((finishup (lambda (t) `(or ,t ,B)))))]
     [(at-hole tactic (pfenv ctx e B)) =>]
      (lambda (pf) ((finishup (lambda (t) `(or ,A ,t))))))]
  [((ctx `(,e1 ,e2) 'F))
   ;; TODO: Might need ctx to infer type
   (let* ([res1 (at-hole tactic (pfenv ctx e1 (infer-type e1 #:hint (term (not A)))))]
          [res2 (at-hole tactic (pfenv ctx e2 (second (pfenv-type res1))))])
     (pfenv ctx `(,(pfenv-term res1) ,(pfenv-term res2)) 'F))]
  [((ctx `(fst ,e) A))
   (at-hold tactic (pfenv ctx e))]


  )
