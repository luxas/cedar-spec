; D-70 B probe 3: nested transitivity + acyclicity, with a forced 2-cycle => UNSAT
(set-logic HO_ALL)
(declare-sort E 0)
(declare-fun anc (E) (Set E))
(declare-const S (Set E))
(declare-const a E)
(declare-const b E)
; a,b in S, distinct
(assert (set.member a S))
(assert (set.member b S))
(assert (distinct a b))
; acyclicity over S
(assert (= (set.filter (lambda ((x E)) (not (set.member x (anc x)))) S) S))
; element-vs-element transitivity over S (nested)
(assert
  (= (set.filter
       (lambda ((x E))
         (= (set.filter
              (lambda ((y E)) (=> (set.member y (anc x)) (set.subset (anc y) (anc x))))
              S)
            S))
       S)
     S))
; FORCE a 2-cycle: b in anc(a) and a in anc(b).
(assert (set.member b (anc a)))
(assert (set.member a (anc b)))
; transitivity then forces anc(a) ⊆ anc(b) ⊆ anc(a) and a in anc(a) via b-step -> contradicts acyclicity
(check-sat)
