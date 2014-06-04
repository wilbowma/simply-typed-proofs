#lang racket

(require
  "unified.rkt"
  "proofs.rkt"
  "tactics.rkt"
  (only-in redex/reduction-semantics judgment-holds term))

(provide
  define-theorem)

(module+ test
  (require rackunit))

;; define-theorem lets you define a theorem and prove it. The proof is
;; then checked through the verifier, and the theorem's name bound to
;; the proof environment if and only if the proof is valid.

;; TODO: define-theorem currently works only with sat formulas. I should
;; probably provide 2 versions. I don't think the tactics are currently
;; sat specific.
(define-syntax (define-theorem syn)
  (syntax-case syn (:)
    [(_ name : theorem proof)
     #'(define name
         (let ([x proof])
           (if (verify-unified ,x theorem)
             (pfenv '() x 'theorem)
             (error 'define-theorem "~s not defined: ~s is not a proof of ~s"
                    'name x 'theorem))))]))
(module+ test
  (check-true (verify-unified true T))
  (define-theorem test1 : T 'true)
  (check-equal? (pfenv-term test1) 'true)

  (define-theorem test2 : (∃ α (not (and α (not α))))
    `(pack (F ,(qed (obvious (program hole '(not (and α (not α)))))))))
  (check-true (pfenv? test2))

  (define-theorem test3 : (∀ α (not (and α (not α))))
    `(Λ ,(qed (obvious (program hole '(not (and α (not α))))))))
  (check-true (pfenv? test3)))

;; Motivating design by pretending to use the system.
;; Pretend this isn't here
#|
(define-theorem example1 : (sat (not (and α (not α))))
  ;; Either I can write down a program
  `(λ (x) ((second x) (first x)))

  ;; TODO: wishlist
  (qed (obvious (program hole)))
  (qed (obvious (program (λ (x) hole))))

  ;; currently?
  (qed (assume (x : (and α (not α))) (program (hole : F))))
  (qed (obvious (assume (x : (and α (not α))) (program (hole : F)))))

  ;; UNSAFE-ASSUMPTION-THAT-IS-PROBABLY-FALSE is a tactic that takes a
  ;; formula, ignores it, and fills in the proof program with some undefined
  ;; program. Best not to use this.
  (UNSAFE-ASSUMPTION-THAT-IS-PROBABLY-FALSE)

  ;; The QED tactic will check your proof in the verifier. The UNSAFE
  ;; tactic will prevent future tactics from running, though.
  qed
  )
|#
