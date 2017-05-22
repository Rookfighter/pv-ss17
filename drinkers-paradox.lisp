; drinkers-paradox.lisp
;
; Created on: 22 May 2017
;     Author: Fabian Meyer
;
; Drinkers Paradox SMT solver solution for Z3.
;
; Problem
; =======
;
; There is someone in the pub such that, if he is drinking, everyone in the
; pub is drinking.
;
; Is satisfiable? Is valid?

(declare-sort Pers) ; Person type
(declare-const S Pers) ; Drinker

(declare-fun P(Pers) Bool) ; predicate: "a" is in the pub
(declare-fun D(Pers) Bool) ; predicate: "a" is drinking

; if S is drinking and x is in the Pub, then x is also drinking
(define-fun drinkpar () Bool
    (forall ((x Pers))  (=> (and (D S) (P x)) (D x)))
)

; S is in the pub
(assert (P S))

(push)
(echo "Satisfiable if 'sat'")
(assert drinkpar)
(check-sat)
(pop)

(push)
(echo "Valid if 'unsat'")
(assert (not drinkpar))
(check-sat)
(pop)
(exit)
