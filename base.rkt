#lang racket

(require
  redex/reduction-semantics
  redex/tut-subst
  racket/set
  "lib/helpers.rkt"
  )

(provide
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
  verify-base

  base-proofL-eval
  base-->
  )

;;------------------------------------------------------------------------

(define-language closed-formulasL
  (c T F)
  (A c (and A A) (or A A) (not A)))

(define-metafunction closed-formulasL
  land : c c -> c
  [(land T T) T]
  [(land c_0 c_1) F])

(define-metafunction closed-formulasL
  lor : c c -> c
  [(lor T c_1) T]
  [(lor c_0 T) T]
  [(lor c_0 c_1) F])

(define-metafunction closed-formulasL
  lnot : c -> c
  [(lnot T) F]
  [(lnot F) T])

(define-metafunction closed-formulasL
  true? : A -> #t or #f
  [(true? T) #t]
  [(true? F) #f]
  [(true? A) (true? (reduce-formula A))])

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
  (test-redex-equal (land T F) F)
  (test-redex-equal (land T T) T)

  (test-redex-equal (reduce-formula T) T)
  (test-redex-equal (reduce-formula (and T T)) T)
  (test-redex-equal (reduce-formula (and F T)) F)
  (test-redex-equal (reduce-formula (or F T)) T)

  (test-redex-equal (true? T) #t)
  (test-redex-equal (true? (and T T)) #t)
  (test-redex-equal (true? (and T F)) #f)
  (test-redex-equal (true? (or F T)) #t)
  (test-redex-equal (true? (not (and T F))) #t))


;;------------------------------------------------------------------------

(define-extended-language sat-formulasL closed-formulasL
  (α (variable-prefix α))
  (γ ((α c) ...))
  (A .... α))

(define-metafunction sat-formulasL
  formula-size : A -> natural
  [(formula-size T) 1]
  [(formula-size F) 1]
  [(formula-size α) 1]
  [(formula-size (and A_1 A_2))
   ,(+ (term (formula-size A_1)) (term (formula-size A_2)))]
  [(formula-size (or A_1 A_2))
   ,(+ (term (formula-size A_1)) (term (formula-size A_2)))]
  [(formula-size (not A))
   ,(add1 (term (formula-size A)))])

(module+ test
  (test-redex-equal (formula-size T) 1)
  (test-redex-equal (formula-size F) 1)
  (test-redex-equal (formula-size (and T T)) 2)
  (test-redex-equal (formula-size (or T F)) 2)
  (test-redex-equal (formula-size (not T)) 2))

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

(define-metafunction sat-formulasL
  sat? : γ A -> #f or #t
  ;; assumes dom(γ) is unique
  [(sat? γ A) (true? (sat-subst γ A))])

(define-metafunction sat-formulasL
  sat-subst : γ A -> A
  [(sat-subst γ A)
   ,(subst/proc α? (map first (term γ)) (map second (term γ)) (term A))])

(define-metafunction sat-formulasL
  sat-assign : α c A -> A
  [(sat-assign α c A) (sat-subst ((α c)) A)])

(define-metafunction sat-formulasL
  union : (α ...) (α ...) -> (α ...)
  [(union any_0 any_1)
   ,(set->list (set-union (list->set (term any_0))
                          (list->set (term any_1))))])
(module+ test
  (test-redex-equal (sat? ((α_1 T)) α_1) #t)
  (test-redex-equal (sat? ((α_1 F)) α_1) #f)
  (test-redex-equal (sat? ((α_0 T) (α_1 F)) (and α_0 α_1)) #f)
  (test-redex-equal (sat? ((α_0 T) (α_1 T)) (and α_0 α_1)) #t))

;;------------------------------------------------------------------------

(define-extended-language base-proofL sat-formulasL
  (x variable-not-otherwise-mentioned)
  ;; TODO: Can bi-directional type-checking prevent these annotations?t ?
  (v x true (e e) (λ (x : A) e) (pair e e) (inj A e) (inj e A))
  (e v (case e of (x e) (x e)) (fst e) (snd e)))

(define-metafunction base-proofL
  base-proof-size : e -> natural
  [(base-proof-size x) 1]
  [(base-proof-size true) 1]
  [(base-proof-size (pair e_0 e_1)) 
   (+ (base-proof-size e_0) (base-proof-size e_1))]
  [(base-proof-size (inj A e))
   (+ 1 (formula-size A) (base-proof-size e))]
  [(base-proof-size (inj e A))
   (+ 1 (formula-size A) (base-proof-size e))]
  [(base-proof-size (λ (x : A) e))
   (+ 1 (formula-size A) (base-proof-size e))]
  [(base-proof-size (e_0 e_1))
   (+ (base-proof-size e_0) (base-proof-size e_1))]
  [(base-proof-size (fst e))
   (add1 (base-proof-size e))]
  [(base-proof-size (snd e))
   (add1 (base-proof-size e))]
  [(base-proof-size (case e of (x e_1) (x e_2)))
   (+ (base-proof-size e) 
      (base-proof-size e_1)
      (base-proof-size e_2))])

(define-extended-language base-verifyL base-proofL
  (Γ mt (x : A Γ)))

(define-judgment-form
  base-verifyL
  #:mode (verify-base I I O)
  #:contract (verify-base Γ e A)

  [----------------------
   (verify-base Γ true T)]

  [(verify-base Γ e_0 A_0)
   (verify-base Γ e_1 A_1)
   ----------------------
   (verify-base Γ (pair e_0 e_1) (and A_0 A_1))]

  [(verify-base Γ e A_1)
   ----------------------
   (verify-base Γ (inj A_0 e) (or A_0 A_1))]

  [(verify-base Γ e A_0)
   ----------------------
   (verify-base Γ (inj e A_1) (or A_0 A_1))]

  [(verify-base (x : A Γ) e F)
   ----------------------
   (verify-base Γ (λ (x : A) e) (not A))]

  [(verify-base Γ e_0 (not A))
   (verify-base Γ e_1 A)
   ----------------------
   (verify-base Γ (e_0 e_1) F)]

  [----------------------
   (verify-base (x : A Γ) x A)]

  [(verify-base Γ x_0 A_0)
   (side-condition (different x_0 x_1))
   ----------------------
   (verify-base (x_1 : A_1 Γ) x_0 A_0)]

  [(verify-base Γ e (and A_0 A_1))
   ----------------------
   (verify-base Γ (fst e) A_0)]

  [(verify-base Γ e (and A_0 A_1))
   ----------------------
   (verify-base Γ (snd e) A_1)]

  [(verify-base Γ e (or A_0 A_1))
   (verify-base (x_0 : A_0 Γ) e_0 A_2)
   (verify-base (x_1 : A_1 Γ) e_1 A_2)
   ----------------------
   (verify-base Γ (case e of (x_0 e_0) (x_1 e_1)) A_2)])

(module+ test
  (require (only-in rackunit check-true))
  (check-true (judgment-holds (verify-base mt true T)))
  (check-true (judgment-holds (verify-base mt (λ (x : F) x) (not F))))
  (check-true
    (judgment-holds (verify-base mt (pair true true) (and T T))))
  (check-true
    (judgment-holds (verify-base mt (pair true (λ (x : F) x))
                                   (and T (not F)))))
  (check-true
    (judgment-holds (verify-base mt (inj T true) (or T T))))
  (check-true
    (judgment-holds (verify-base mt (inj F true) (or F T))))
  (check-true
    (judgment-holds (verify-base mt (inj true F) (or T F))))
  (check-true
    (judgment-holds (verify-base mt (λ (x : (and T F)) (snd x))
                                   (not (and T F)))))
  (check-true
    (judgment-holds (verify-base mt
                                 (λ (x : (and (and (or (not α_0) α_1) α_0) (not α_1)))
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
  (reduction-relation
    base-proofL-eval
    #:domain e

    (==> (fst (pair e_0 e_1)) e_0)
    (==> (snd (pair e_0 e_1)) e_1)

    (==> (case (inj A e) (x e_0) (x e_1))
         (proof-subst x e e_0))

    (==> (case (inj e A) (x e_0) (x e_1))
         (proof-subst x e e_1))

    with
    [(--> (in-hole E e_0) (in-hole E e_1))
     (==> e_0 e_1)]))

(define-metafunction base-proofL-eval
  proof-subst : x e -> e
  [(proof-subst x e_0 e_1)
   ,(subst/proc x? (list (term x)) (list (term e_0)) (term e_1))])

(define x? (redex-match base-proofL-eval x))
