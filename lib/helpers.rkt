#lang racket

(require
  redex/reduction-semantics
  (only-in rackunit check)
  (only-in racket/set set=?))

(provide
  test-redex-equal
  test-redex-set=?)

(define-syntax-rule (test-redex-equal e1 e2)
  (test-equal (term e1) (term e2)))
(define-syntax-rule (test-redex-set=? e1 e2)
  (check set=? (list->set (term e1)) (list->set (term e2))))
