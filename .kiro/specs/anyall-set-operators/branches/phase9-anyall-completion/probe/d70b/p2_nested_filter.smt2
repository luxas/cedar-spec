; D-70 B probe 2: NESTED set.filter — element-vs-element transitivity over the same S
; for every x,y in S: y in anc(x) => anc(y) subset anc(x)
; outer filter binds x; the body must quantify over all y in S -> an INNER filter over S.
; Express "for all y in S: y in anc(x) => anc(y) ⊆ anc(x)" as:
;   filter(lambda y. (y in anc(x) => anc(y) ⊆ anc(x)), S) = S   -- the inner "forall over S"
; and the OUTER requires that to hold for every x in S:
;   filter(lambda x. (filter(lambda y. ...) S) = S, S) = S
(set-logic HO_ALL)
(declare-sort E 0)
(declare-fun anc (E) (Set E))
(declare-const S (Set E))
(assert
  (= (set.filter
       (lambda ((x E))
         (= (set.filter
              (lambda ((y E)) (=> (set.member y (anc x)) (set.subset (anc y) (anc x))))
              S)
            S))
       S)
     S))
(declare-const e E)
(assert (set.member e S))
(check-sat)
