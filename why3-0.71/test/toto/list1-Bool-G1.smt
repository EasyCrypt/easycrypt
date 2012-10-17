;;; this is a prelude for Z3
(set-logic AUFNIRA)
(declare-sort uni 0)

(declare-sort deco 0)

(declare-sort ty 0)

(declare-fun sort (ty uni) deco)

(declare-fun int () ty)

(declare-fun real () ty)

(declare-fun bool () ty)

(declare-fun T () uni)

(declare-fun F () uni)

(declare-fun match_bool (deco deco deco) uni)

;; match_bool_T
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni))
  (= (sort a (match_bool (sort bool T) (sort a z) (sort a z1))) (sort a z)))))

;; match_bool_F
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni))
  (= (sort a (match_bool (sort bool F) (sort a z) (sort a z1))) (sort a z1)))))

(declare-fun index_bool (deco) Int)

;; index_bool_T
  (assert (= (index_bool (sort bool T)) 0))

;; index_bool_F
  (assert (= (index_bool (sort bool F)) 1))

;; bool_inversion
  (assert
  (forall ((u uni))
  (or (= (sort bool u) (sort bool T)) (= (sort bool u) (sort bool F)))))

(assert
;; G1
 ;; File "list1.why", line 3, characters 7-9
  (not (not (= (sort bool T) (sort bool F)))))
(check-sat)

