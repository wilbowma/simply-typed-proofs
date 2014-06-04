#lang racket

(require
  redex/reduction-semantics
  "base.rkt"
  "sat.rkt"
  "unsat.rkt")

(provide
  unified-proofL

  verify-unifiedJ
  verify-unified)

(module+ test
  (require rackunit))

;; TODO: This allows inter-mixing forall and exist, which I'm not sure
;; I can handle. I really should only allow either all foralls or all
;; exists (i.e. either sat or unsat formulas) in the language.
(define-union-language unified-proofL sat-proofL unsat-proofL)

(define-union-language verify-unifiedJL deltaL unified-proofL)

;; TODO: similar to the L language affix, perhaps all judgments should
;; have a J affix
(define-judgment-form
  verify-unifiedJL
  #:mode (verify-unifiedJ I I I)
  #:contract (verify-unifiedJ Δ p φ)

  [(verify-base mt e A) (verify-formula Δ A)
   ----------------------
   (verify-unifiedJ Δ e A)]

  [(verify-unifiedJ (α Δ) p φ)
   ----------------------
   (verify-unifiedJ Δ (Λ p) (∀ α φ))]

  [(verify-unifiedJ Δ p (qsat-assign α c φ))
   ----------------------
   (verify-unifiedJ Δ (pack (c p)) (∃ α φ))])

(define-syntax-rule (verify-unified proof formula)
  (judgment-holds (verify-unifiedJ mt proof formula)))

(module+ test
 (check-true (verify-unified (pack (T (inj true))) (∃ α (or α (not α)))))
 (check-true (verify-unified (Λ (λ (x) ((snd x) (fst x)))) (∀ α (not (and α (not α)))))))
