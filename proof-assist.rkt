#lang racket

(require
  "theorems.rkt"
  "tactics.rkt"
  "proofs.rkt")

(provide 
  define-theorem

  define/tactic
  return

  program
  contra
  obvious
  qed

  pfenv
  pfenv-ctx
  pfenv-term
  pfenv-type
  pfenv?

  hole
  hole?)

