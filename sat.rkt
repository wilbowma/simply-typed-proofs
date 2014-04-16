#lang racket

(require
  redex/reduction-semantics
  "base.rkt"
  "lib/helpers.rkt")

(provide
  sat-proofL
  ;; qsat is a bad name
  qsat-assign
  qsat-subst
  sat-quantify

  verify-satL
  verifier-sat
  verify-sat
  )
;------------------------------------------------------------------------

(define-extended-language sat-proofL base-proofL
  (p (pack (c p)) e)
  (φ (∃ α φ) A))

(define-metafunction sat-proofL
  qsat-assign : α c φ -> φ
  ;; NB: I am reimplementing subst. oops
  [(qsat-assign α c (∃ α φ)) (∃ α φ)]
  [(qsat-assign α_0 c (∃ α_1 φ)) (∃ α_1 (qsat-assign α_0 c φ))]
  [(qsat-assign α c A) (sat-assign α c A)])

(define-metafunction sat-proofL
  qsat-subst : γ φ -> φ
  [(qsat-subst γ φ)
   ,(foldr (λ (as φ) (term (qsat-assign ,(first as) ,(second as) ,φ)))
           (term φ) (term γ))])

(define-metafunction sat-proofL
  sat-quantify : A -> φ
  [(sat-quantify A)
   ,(foldr (λ (α A) (term (∃ ,α ,A))) (term A) (term (gather-αs A)))])

(module+ test
  (check (sat-quantify (not α)) (∃ α (not α)))
  (check (sat-quantify (or α (not α))) (∃ α (or α (not α))))
  (check (sat-quantify (or α_1 (not α_0))) (∃ α_0 (∃ α_1 (or α_1 (not α_0))))))

;;------------------------------------------------------------------------ 

(define-union-language verify-satL base-verifyL sat-proofL)

(define-syntax-rule (verifier-sat proof formula)
  (test-predicate values (judgment-holds (verify-sat-q proof formula))))

(define-judgment-form
  verify-satL
  #:mode (verify-sat-q I I)
  #:contract (verify-sat-q p A)

  [(verify-sat p (sat-quantify A))
   ----------------------
   (verify-sat-q p A)])

(define-judgment-form
  verify-satL
  #:mode (verify-sat I I)
  #:contract (verify-sat p φ)

  [(verify-base mt e A)
   ----------------------
   (verify-sat e A)]

  [(verify-sat p (qsat-assign α c φ))
   ----------------------
   (verify-sat (pack (c p)) (∃ α φ))])

(module+ test
  (test-true
    (judgment-holds (verify-sat (pack (T (inj true F))) (∃ α (or α F)))))
  (test-true
    (judgment-holds (verify-sat (pack (F (λ (x : F) x))) (∃ α (not α)))))
  (test-true
    (judgment-holds (verify-sat (pack (T true)) (∃ α α))))


  (test-true
    (judgment-holds (verify-sat (pack (F (inj F (λ (x : F) x))))
                            (∃ α (or α (not α))))))
  (test-true
    (judgment-holds (verify-sat (pack (T (inj true (not T))))
                            (∃ α (or α (not α))))))

  (verifier-sat (pack (F (inj F (λ (x : F) x)))) (or α (not α)))
  (verifier-sat (pack (F (λ (x : (and F (not F))) ((snd x) (fst x))))) (not (and α (not α)))))
