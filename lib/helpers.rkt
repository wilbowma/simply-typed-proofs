#lang racket

(require 
  redex/reduction-semantics)

(provide 
  check
  test-true)

(define-syntax-rule (check e1 e2) (test-equal (term e1) (term e2)))

(define-syntax-rule (test-true e) (test-predicate values e))
