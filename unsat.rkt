#lang racket

(require
  redex/reduction-semantics
  "base.rkt"
  "lib/helpers.rkt")

(provide
  unsat-proofL
  qunsat-assign
  qunsat-subst
  unsat-quantify

  verify-unsatL
  verifier-unsat
  verify-unsat
  )

;------------------------------------------------------------------------

(define-extended-language unsat-proofL base-proofL
  (p (Λ (α) p) e)
  (φ (∀ α φ) (not A)))

(define-metafunction unsat-proofL
  qunsat-assign : α c φ -> φ
  ;; NB: I am reimplementing subst. oops
  [(qunsat-assign α c (∀ α φ)) (∀ α φ)]
  [(qunsat-assign α_0 c (∀ α_1 φ)) (∀ α_1 (qunsat-assign α_0 c φ))]
  [(qunsat-assign α c A) (sat-assign α c A)])

(define-metafunction unsat-proofL
  qunsat-subst : γ φ -> φ
  [(qunsat-subst γ φ)
   ,(foldr (λ (as φ) (term (qunsat-assign ,(first as) ,(second as) ,φ)))
           (term φ) (term γ))])

(define-metafunction unsat-proofL
  unsat-quantify : A -> φ
  [(unsat-quantify A)
   ,(foldr (λ (α A) (term (∀ ,α ,A))) (term (not A)) (term (gather-αs A)))])

(module+ test
  (check (unsat-quantify α) (∀ α (not α)))
  (check (unsat-quantify (or α (not α))) (∀ α (not (or α (not α)))))
  (check (unsat-quantify (or α_1 (not α_0))) (∀ α_0 (∀ α_1 (not (or α_1 (not α_0)))))))

;;------------------------------------------------------------------------

(define-extended-language deltaL base-verifyL
  (Δ mt (α Δ)))

(define-union-language verify-unsatL deltaL unsat-proofL)

(define-judgment-form
  verify-unsatL
  #:mode (verify-formula I I)
  #:contract (verify-formula Δ A)

  [----------------------
   (verify-formula Δ T)]

  [----------------------
   (verify-formula Δ F)]

  [----------------------
   (verify-formula (α Δ) α)]

  [(verify-formula Δ α_1)
   (side-condition (different-α α_0 α_1))
   ----------------------
   (verify-formula (α_0 Δ) α_1)]

  [(verify-formula Δ A_0)
   (verify-formula Δ A_1)
   ----------------------
   (verify-formula Δ (and A_0 A_1))]

  [(verify-formula Δ A_0)
   (verify-formula Δ A_1)
   ----------------------
   (verify-formula Δ (or A_0 A_1))]

  [(verify-formula Δ A_0)
   ----------------------
   (verify-formula Δ (not A_0))])

(module+ test
  (test-true (judgment-holds (verify-formula mt T)))
  (test-true (judgment-holds (verify-formula mt F)))
  (test-true (judgment-holds (verify-formula (α mt) α)))
  (test-true (judgment-holds (verify-formula (α mt) T)))
  (test-true (judgment-holds (verify-formula (α mt) (and T α))))
  (test-true (judgment-holds (verify-formula (α mt) (or T F))))
  (test-true (judgment-holds (verify-formula (α mt) (not (or α F))))))

;;------------------------------------------------------------------------

(define-syntax-rule (verifier-unsat proof formula)
  (test-predicate values (judgment-holds (verify-unsat-q proof formula))))

(define-judgment-form
  verify-unsatL
  #:mode (verify-unsat-q I I)
  #:contract (verify-unsat-q p A)

  [(verify-unsat mt p (unsat-quantify A))
   ----------------------
   (verify-unsat-q p A)])

(define-judgment-form
  verify-unsatL
  #:mode (verify-unsat I I I)
  #:contract (verify-unsat Δ p φ)

  [(verify-base mt e A)
   (verify-formula Δ A)
   ----------------------
   (verify-unsat Δ e A)]

  [(verify-unsat (α Δ) p φ)
   ----------------------
   (verify-unsat Δ (Λ (α) p) (∀ α φ))])

(module+ test
  (test-true
    (judgment-holds (verify-unsat mt (Λ (α) (λ (x : (and α (not α))) ((snd x) (fst x))))
                                  (∀ α (not (and α (not α)))))))
  (test-true (judgment-holds
    (verify-unsat
      mt
      (Λ (α_0) (Λ (α_1) (λ (x : (and (or α_0 α_1) (and (not α_0) (not α_1))))
                           (case (fst x) of
                             ;; α_0
                             (x_1 ((fst (snd x)) x_1))
                             ;; α_1 
                             (x_1 ((snd (snd x)) x_1))
                             ))))
      (∀ α_0 (∀ α_1 (not (and (or α_0 α_1) (and (not α_0) (not α_1)))))))))
  (test-true (judgment-holds
    (verify-unsat
      mt
      (Λ (α_0) (Λ (α_1) (λ (x : (and (and (or (not α_0) α_1) α_0) (not α_1)))
                           (case (fst (fst x)) of
                             ;; not α_0
                             (x_1 (x_1 (snd (fst x))))
                             ;; α_1
                             (x_1 ((snd x) x_1))))))
      (∀ α_0 (∀ α_1 (not (and (and (or (not α_0) α_1) α_0) (not α_1))))))))

  (verifier-unsat (Λ (α) (λ (x : (and α (not α))) ((snd x) (fst x))))
                  (and α (not α)))
  (verifier-unsat (Λ (α_0) (Λ (α_1) (λ (x : (and (and (or (not α_0) α_1) α_0) (not α_1)))
                                       (case (fst (fst x)) of
                                         ;; not α_0
                                         (x_1 (x_1 (snd (fst x))))
                                         ;; α_1
                                         (x_1 ((snd x) x_1))))))
                  (and (and (or (not α_0) α_1) α_0) (not α_1))))
