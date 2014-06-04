#lang racket

(require
  redex/reduction-semantics
  redex/tut-subst
  racket/set
  "lib/helpers.rkt"
  )

(provide
  plus

  closed-formulasL
  land
  lor
  lnot
  true?
  reduce-formula
  gather-αs

  sat-formulasL
  sat?
  sat-subst
  sat-assign
  union
  formula-size

  base-proofL
  base-proof-size

  base-verifyL
  check-base
  synth-base
  verify-base

  base-proofL-eval
  base-->
  )

;;------------------------------------------------------------------------

;; A (base) language of closed boolean formulas
(define-language closed-formulasL
  (c ::= T F)
  (A ::= c (and A A) (or A A) (not A)))

;; Language-level addition
(define-metafunction closed-formulasL
  plus : natural ... -> natural
  [(plus natural_0 ... ) ,(apply + (term (natural_0 ...)))])

;; A language-level logical and
(define-metafunction closed-formulasL
  land : c c -> c
  [(land T T) T]
  [(land c_0 c_1) F])
(module+ test
  (test-redex-equal (land T F) F)
  (test-redex-equal (land T T) T))

;; A language-level logical or
(define-metafunction closed-formulasL
  lor : c c -> c
  [(lor T c_1) T]
  [(lor c_0 T) T]
  [(lor c_0 c_1) F])

;; A language-level logical not
(define-metafunction closed-formulasL
  lnot : c -> c
  [(lnot T) F]
  [(lnot F) T])

;; Convert language-level truth to meta-level truth
(define-metafunction closed-formulasL
  true? : A -> #t or #f
  [(true? T) #t]
  [(true? F) #f]
  [(true? A) (true? (reduce-formula A))])
(module+ test
  (test-redex-equal (true? T) #t)
  (test-redex-equal (true? (and T T)) #t)
  (test-redex-equal (true? (and T F)) #f)
  (test-redex-equal (true? (or F T)) #t)
  (test-redex-equal (true? (not (and T F))) #t))

;; Evaluate a closed boolean formula to language-level truth
(define-metafunction closed-formulasL
  reduce-formula : A -> c
  [(reduce-formula T) T]
  [(reduce-formula F) F]
  [(reduce-formula (and A_1 A_2))
   (land (reduce-formula A_1) (reduce-formula A_2))]
  [(reduce-formula (or A_1 A_2))
   (lor (reduce-formula A_1) (reduce-formula A_2))]
  [(reduce-formula (not A))
   (lnot (reduce-formula A))])
(module+ test
  (test-redex-equal (reduce-formula T) T)
  (test-redex-equal (reduce-formula (and T T)) T)
  (test-redex-equal (reduce-formula (and F T)) F)
  (test-redex-equal (reduce-formula (or F T)) T))

;;------------------------------------------------------------------------

;; A language of open boolean formulas, i.e., formulas with variables in
;; the clauses
(define-extended-language sat-formulasL closed-formulasL
  (α ::= (variable-prefix α))
  (γ ::= ((α c) ...))
  (A ::= .... α))

;; The size of an open formula is roughly equal to the number of
;; variables plus the number of clauses. Formally:
(define-metafunction sat-formulasL
  formula-size : A -> natural
  [(formula-size T) 1]
  [(formula-size F) 1]
  [(formula-size α) 1]
  [(formula-size (and A_1 A_2))
   (plus (formula-size A_1) (formula-size A_2))]
  [(formula-size (or A_1 A_2))
   (plus (formula-size A_1) (formula-size A_2))]
  [(formula-size (not A))
   (plus 1 (formula-size A))])
(module+ test
  (test-redex-equal (formula-size T) 1)
  (test-redex-equal (formula-size F) 1)
  (test-redex-equal (formula-size (and T T)) 2)
  (test-redex-equal (formula-size (or T F)) 2)
  (test-redex-equal (formula-size (not T)) 2))

;; Gather the free variables of a formula
(define-metafunction sat-formulasL
  gather-αs : A -> (α ...)
  [(gather-αs T) ()]
  [(gather-αs F) ()]
  [(gather-αs α) (α)]
  [(gather-αs (and A_0 A_1))
   (union (gather-αs A_0) (gather-αs A_1))]
  [(gather-αs (or A_0 A_1))
   (union (gather-αs A_0) (gather-αs A_1))]
  [(gather-αs (not A_0))
   (gather-αs A_0)])
(module+ test
  (test-redex-set=? (gather-αs (or α_0 α_1)) (α_1 α_0))
  (test-redex-set=? (gather-αs (and α_0 α_1)) (α_1 α_0))
  (test-redex-set=? (gather-αs (not α_0)) (α_0))
  (test-redex-set=? (gather-αs (not F)) ()))

(define α? (redex-match sat-formulasL α))

;; #t iff the formula A is satisfiable with the assignment γ
(define-metafunction sat-formulasL
  sat? : γ A -> #f or #t
  ;; assumes dom(γ) is unique
  [(sat? γ A) (true? (sat-subst γ A))])
(module+ test
  (test-redex-equal (sat? ((α_1 T)) α_1) #t)
  (test-redex-equal (sat? ((α_1 F)) α_1) #f)
  (test-redex-equal (sat? ((α_0 T) (α_1 F)) (and α_0 α_1)) #f)
  (test-redex-equal (sat? ((α_0 T) (α_1 T)) (and α_0 α_1)) #t))

;; Instantiate the open formula A with the substitution γ
(define-metafunction sat-formulasL
  sat-subst : γ A -> A
  [(sat-subst γ A)
   ,(subst/proc α? (map first (term γ)) (map second (term γ)) (term A))])

;; Replace α with c in A
(define-metafunction sat-formulasL
  sat-assign : α c A -> A
  [(sat-assign α c A) (sat-subst ((α c)) A)])

;; Union two sets of open variables
(define-metafunction sat-formulasL
  union : (α ...) (α ...) -> (α ...)
  [(union any_0 any_1)
   ,(set->list (set-union (list->set (term any_0))
                          (list->set (term any_1))))])

;;------------------------------------------------------------------------

;; A base language for proofs about sat or unsat formulas
(define-extended-language base-proofL sat-formulasL
  (x ::= variable-not-otherwise-mentioned)
  ;; TODO: FIX inj; needs {1,2} annotation for dynamic semantics
  (v ::= x true (e e) (λ (x) e) (pair e e) (inj e))
  (e ::= v (case e of (x e) (x e)) (fst e) (snd e) (e : A)))

;; The size of a proof is roughly equal to the sum of the size of each
;; subproof, and 1 for the trivial proof of true. Formally:
(define-metafunction base-proofL
  base-proof-size : e -> natural
  [(base-proof-size x) 1]
  [(base-proof-size true) 1]
  [(base-proof-size (pair e_0 e_1))
   (plus 1 (base-proof-size e_0) (base-proof-size e_1))]
  [(base-proof-size (inj e))
   (plus 1 (base-proof-size e))]
  #;[(base-proof-size (inj e A))
   (plus 1 (formula-size A) (base-proof-size e))]
  [(base-proof-size (λ (x) e))
   (plus 1 (base-proof-size e))]
  [(base-proof-size (e_0 e_1))
   (plus (base-proof-size e_0) (base-proof-size e_1))]
  [(base-proof-size (fst e))
   (plus 1 (base-proof-size e))]
  [(base-proof-size (snd e))
   (plus 1 (base-proof-size e))]
  [(base-proof-size (case e of (x e_1) (x e_2)))
   (plus (base-proof-size e)
         (base-proof-size e_1)
         (base-proof-size e_2))]
  [(base-proof-size (e : A))
   (plus (base-proof-size e)
         (formula-size A))])
(module+ test
  (test-redex-equal (base-proof-size (λ (x) true)) 2)
  (test-redex-equal (base-proof-size (λ (x) (λ (y) x))) 3)
  (test-redex-equal (base-proof-size (λ (x) (λ (y) (pair x y)))) 5)
  (test-redex-equal (base-proof-size (λ (x) (λ (y) (inj x)))) 4)
  (test-redex-equal (base-proof-size (true : T)) 2))

;;------------------------------------------------------------------------

;; A base language for verifying a given proof proves a given formula
(define-extended-language base-verifyL base-proofL
  (Γ ::= mt (x : A Γ)))

;; Bi-directional type checking for reduced annotations
;; Adapted to my weird setting from [1,2,3,4]; might be a little wrong.
;; [1] http://www.mpi-sws.org/~joshua/bitype.pdf
;; [2] http://itu.dk/people/drc/tutorials/bidirectional.pdf
;; [3] http://www.cis.upenn.edu/~bcpierce/papers/lti.pdf
;; [4] http://www.cs.cmu.edu/~fp/courses/15312-f04/handouts/15-bidirectional.pdf

;; Check a proof prove a formula
(define-judgment-form
  base-verifyL
  #:mode (check-base I I I)
  #:contract (check-base Γ e A)

  [----------------------
   (check-base Γ true T)]

  [(check-base Γ e_0 A_0)
   (check-base Γ e_1 A_1)
   ----------------------
   (check-base Γ (pair e_0 e_1) (and A_0 A_1))]

  [(check-base Γ e A_1)
   ----------------------
   (check-base Γ (inj e) (or A_0 A_1))]

  [(check-base Γ e A_0)
   ----------------------
   (check-base Γ (inj e) (or A_0 A_1))]

  [(check-base (x : A Γ) e F)
   ----------------------
   (check-base Γ (λ (x) e) (not A))]

  [(synth-base Γ e A)
   ----------------------
   (check-base Γ e A)]

  [(synth-base Γ e_1 A)
   (check-base Γ e_0 (not A))
   ----------------------
   (check-base Γ (e_0 e_1) F)]

  #;[----------------------
   (check-base (x : A Γ) x A)]

  #;[(check-base Γ x_0 A_0)
   (side-condition (different x_0 x_1))
   ----------------------
   (check-base (x_1 : A_1 Γ) x_0 A_0)]

  [(synth-base Γ e (and A_0 A_1))
   ----------------------
   (check-base Γ (fst e) A_0)]

  [(synth-base Γ e (and A_0 A_1))
   ----------------------
   (check-base Γ (snd e) A_1)]

  [(synth-base Γ e (or A_0 A_1))
   (check-base (x_0 : A_0 Γ) e_0 A_2)
   (check-base (x_1 : A_1 Γ) e_1 A_2)
   ----------------------
   (check-base Γ (case e of (x_0 e_0) (x_1 e_1)) A_2)]
  )

;; Given a proof, synthesize a formula that it proves
(define-judgment-form
  base-verifyL
  #:mode (synth-base I I O)
  #:contract (synth-base Γ e A)

  [----------------------
   (synth-base Γ true T)]

  [(check-base Γ e A)
   ----------------------
   (synth-base Γ (e : A) A)]

  [(synth-base Γ e_0 A_0)
   (synth-base Γ e_1 A_1)
   ----------------------
   (synth-base Γ (pair e_0 e_1) (and A_0 A_1))]

  #;[(synth-base Γ e A_1)
   ----------------------
   (synth-base Γ (inj A_0 e) (or A_0 A_1))]

  #;[(synth-base Γ e A_0)
   ----------------------
   (synth-base Γ (inj e A_1) (or A_0 A_1))]

  #;[(synth-base (x : A Γ) e F)
   ----------------------
   (synth-base Γ (λ (x) e) (not A))]

  [(synth-base Γ e_1 A)
   (check-base Γ e_0 (not A))
   ----------------------
   (synth-base Γ (e_0 e_1) F)]

  [----------------------
   (synth-base (x : A Γ) x A)]

  [(synth-base Γ x_0 A_0)
   (side-condition (different x_0 x_1))
   ----------------------
   (synth-base (x_1 : A_1 Γ) x_0 A_0)]

  [(synth-base Γ e (and A_0 A_1))
   ----------------------
   (synth-base Γ (fst e) A_0)]

  [(synth-base Γ e (and A_0 A_1))
   ----------------------
   (synth-base Γ (snd e) A_1)]

  [(synth-base Γ e (or A_0 A_1))
   (synth-base (x_0 : A_0 Γ) e_0 A_2)
   (synth-base (x_1 : A_1 Γ) e_1 A_2)
   ----------------------
   (synth-base Γ (case e of (x_0 e_0) (x_1 e_1)) A_2)]
  )

;; A public facing name for verifying that a proof is a proof
(define-judgment-form
  base-verifyL
  #:mode (verify-base I I I)
  #:contract (verify-base Γ e A)

  [(check-base Γ e A)
   ----------------------
   (verify-base Γ e A)])

(module+ test
  (require (only-in rackunit check-true))
  (check-true (judgment-holds (verify-base mt true T)))
  (check-true (judgment-holds (verify-base mt (λ (x) x) (not F))))
  (check-true
    (judgment-holds (verify-base mt (pair true true) (and T T))))
  (check-true
    (judgment-holds (verify-base mt (pair true (λ (x) x))
                                 (and T (not F)))))
  (check-true
    (judgment-holds (verify-base mt (inj true) (or T T))))
  (check-true
    (judgment-holds (verify-base mt (inj true) (or F T))))
  (check-true
    (judgment-holds (verify-base mt (inj true) (or T F))))
  (check-true
    (judgment-holds (verify-base mt (λ (x) (snd x))
                                   (not (and T F)))))
  (check-true
    (judgment-holds
      (verify-base mt
        (λ (x)
           (case (fst (fst x)) of
             ;; not α_0
             (x_1 (x_1 (snd (fst x))))
             ;; α_1
             (x_1 ((snd x) x_1))))
        (not (and (and (or (not α_0) α_1) α_0) (not α_1)))))))

;;------------------------------------------------------------------------

(define-extended-language base-proofL-eval base-proofL
  (E hole (fst E) (snd E) (case E (x e) (x e))))

(define base-->
  ;; TODO: FIX, when semantics needed
  (reduction-relation
    base-proofL-eval
    #:domain e

    (==> (fst (pair e_0 e_1)) e_0)
    (==> (snd (pair e_0 e_1)) e_1)

    (==> (case (inj A e) (x e_0) (x e_1))
         ,(error "Currently broken; inj need {1,2} annotation to fix")
         #;(proof-subst x e e_0))

    (==> (case (inj e A) (x e_0) (x e_1))
         ,(error "Currently broken; inj need {1,2} annotation to fix")
         #;(proof-subst x e e_1))

    with
    [(--> (in-hole E e_0) (in-hole E e_1))
     (==> e_0 e_1)]))

(define-metafunction base-proofL-eval
  proof-subst : x e -> e
  [(proof-subst x e_0 e_1)
   ,(subst/proc x? (list (term x)) (list (term e_0)) (term e_1))])

(define x? (redex-match base-proofL-eval x))
