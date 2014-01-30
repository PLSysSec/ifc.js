#lang racket
(require redex)

(define-language λifc 

   (l ⊥ ⊤)
   (b #t #f)

   (v l
      b
      (lbv e e))

   (e v
      (join e e)
      (meet e e)
      (canFlowTo e e)
      getLabel
      getClerance
      (label e e)
      (unlabel e e))
   
   (E hole
      (join E e)
      (join v E)
      (meet E e)
      (meet v E)
      (canFlowTo E e)
      (canFlowTo v E)
      (label E e)
      (unlabel E))

)
(define →λifc (reduction-relation λifc

    (--> (l_1 l_2 (in-hole E (label l e)))
         (l_1 l_2 (in-hole E (lbv l e)))
         "E-label"
         (side-condition (and (label-guard (term (canFlowTo l l_2)))
                              (label-guard (term (canFlowTo l_1 l))))))

    (--> (l_1 l_2 (in-hole E (unlabel (lbv l e))))
         ((pure-eval→λifc (join l l_1)) l_2 (in-hole E e))
         "E-unlabel"
         (side-condition (label-guard (term (canFlowTo l l_2)))))

   ;; labels
   
   ; join 
   (==> (join l_1 l_2) ⊤ "E-join-⊤" (side-condition (or (equal? (term l_1) (term ⊤))
                                                        (equal? (term l_2) (term ⊤)))))
   (==> (join l ⊥) l "E-join-⊥-1")
   (==> (join ⊥ l) l "E-join-⊥-2")
   ; meet
   (==> (meet l_1 l_2) any "E-meet-⊥" (side-condition (or (equal? (term l_1) (term ⊥))
                                                          (equal? (term l_2) (term ⊥)))))
   (==> (meet l ⊤) l "E-meet-⊤-1")
   (==> (meet ⊤ l) l "E-meet-⊤-2")
   ; canFlowTo
   (==> (canFlowTo l ⊤) #t "E-canFlowTo-x⊤")
   (==> (canFlowTo ⊥ l) #t "E-canFlowTo-⊥x")
   (==> (canFlowTo ⊤ ⊥) #f "E-canFlowTo-⊤⊥")
   
   with
     [(--> (l_1 l_2 (in-hole E e_1)) (l_1 l_2 (in-hole E e_2)))
      (==> e_1 e_2)]
   
))

(define-metafunction λifc 
  [(pure-eval→λifc e) any
   (where (⊥ ⊥ any) ,(first-and-only (apply-reduction-relation* →λifc (term e))))])

;; perform a label check
(define (label-guard e)
   (let ([t (first-and-only (apply-reduction-relation* →λifc (term (⊥ ⊥ (unquote e)))))]) 
   (equal? t (term (⊥ ⊥ #t)))))

;; helper function: returns first element of list if it's the only 
;; element in the list, otherwise it throws an exception
(define (first-and-only xs)
  (if (equal? 1 (length xs))
      (first xs)
      (error 'first-and-only "list ~a is not a singleton!" xs)))

(traces →λifc '(⊥ ⊤ (unlabel (label ⊤ #t))))
