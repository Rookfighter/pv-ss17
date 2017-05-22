; dreadbury-mansion.lisp
;
; Created on: 22 May 2017
;     Author: Fabian Meyer
;
; Dreadbury Mansion mystery SMT solver solution for Z3.
;
; Problem
; =======
;
; * Someone who lived in Dreadbury Mansion killed Aunt Agatha.
; * Agatha, the Butler and Charles were the only people who lived in
;   Dreadbury Mansion.
; * A killer always hates his victim, and is never richer than his victim.
; * Charles hates no one that aunt Agatha hates.
; * Agatha hates everyone except the butler.
; * The butler hates everyone not richer than Aunt Agatha.
; * The butler also hates everyone Agatha hates.
; * No one hates everyone.
; * Agatha is not the butler.
; * Who killed Aunt Agatha?

(declare-sort Pers) ; Person type
(declare-const A Pers) ; Agatha
(declare-const B Pers) ; Butler
(declare-const C Pers) ; Charles
(declare-const M Pers) ; Murderer

(declare-fun L(Pers) Bool) ; predicate: "a" lives in Dreadbury Mansion
(declare-fun H(Pers Pers) Bool) ; predicate: "a" hates "b"
(declare-fun K(Pers Pers) Bool) ; predicate: "a" kills "b"
(declare-fun R(Pers Pers) Bool) ; predicate: "a" is richer than "b"

; Murderer lives in Dreadbury Mansion and killed Agatha
(assert (and (L M) (K M A)))
; if x lives in Dreadbury Mansion then it is either A, B or C
(assert (forall ((x Pers)) (=> (L x) (or (= x A) (= x B) (= x C)))))
; if x kills y, then x hates y and x is not richer than y
(assert
  (forall ((x Pers))
      (forall ((y Pers))
          (=> (K x y) (and (H x y) (not (R x y))))
)))
; if Agatha hates someone, then Charles does not hate that person
(assert (forall ((x Pers)) (=> (H A x) (not (H C x)))))
; x is Butler and Agatha does not hate him or Agatha hates x
(assert (forall ((x Pers)) (or (and (= x B) (not (H A x))) (H A x))))
; if x is not richer than Agatha, then the Butler hates x
(assert (forall ((x Pers)) (=> (not (R x A)) (H B x))))
; if Agatha hates x, then Butler hates x
(assert (forall ((x Pers)) (=> (H A x) (H B x))))
; no one hates all
(assert
    (forall ((x Pers))
        (not (forall ((y Pers))
            (H x y)
))))
; Agatha is not the Butler
(assert (not (= A B)))

(check-sat)
(get-model)
(exit)
