#lang racket/base

(provide
  pfenv
  pfenv-ctx
  pfenv-term
  pfenv-type
  pfenv?

  hole
  hole?)

;; What *is* a proof? Well, a term. Generally we're building proofs, and
;; we need to build in them in some kind of context or environment
(define-struct pfenv (ctx term type))

;; hole is an unknown piece of a program.

;; TODO: Perhaps a hole should always be paired with a type.
;; Currently this is achieved via (program hole type)
(define-struct ahole ())
(define hole (ahole))
(define hole? ahole?)
(module+ test
  (require rackunit)
  (check-equal? hole hole)
  (check-true (hole? hole)))
