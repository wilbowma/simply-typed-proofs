#lang racket

(require "proof-assist.rkt")

(module+ test
  ;; T is the type of true.
  ;; We can define a theorem for this by just writing the term:
  (define-theorem example0 : T
    `true)

  ;; But writing programs is kind of tedious. We could also use tactics
  ;; (i.e. meta-programs) to write them for us.

  ;; program is a tactic that takes a possibly incomplete program (where
  ;; hole is the missing part of the program) and a type. It generates a
  ;; proof environment in which the tactics will operate to generate a
  ;; program.

  ;; obvious is a tactic that tries to do the obvious thing.

  ;; qed is a tactic that ends the proof environment, returning a term.
  (define-theorem example1 : T
    (qed (obvious (program hole 'T))))

  (define-theorem example2 : (and T T)
    (qed (obvious (program hole '(and T T)))))

  ;; This term is open with respect to some variable α. We don't have a
  ;; tactic to try to pick a variable assignment yet, so we finish the
  ;; proof off manually.
  (define-theorem example3 : (∃ α (not (and α (not α))))
    `(pack (F ,(qed (obvious (program hole '(not (and α (not α)))))))))

  ;; We can also prove the same theorem for all α.
  (define-theorem example4 : (∀ α (not (and α (not α))))
    `(Λ ,(qed (obvious (program hole '(not (and α (not α)))))))))


(module+ test
  ;; Because I like to see "n tests passed"
  (require rackunit)
  (check-true (pfenv? example0))
  (check-true (pfenv? example1))
  (check-true (pfenv? example2))
  (check-true (pfenv? example3))
  (check-true (pfenv? example4)))
