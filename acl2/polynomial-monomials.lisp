(in-package "ACL2")

(include-book "unit-square-power-index")

; Coefficient constructors and actual polynomial/grid evaluation for
; arbitrary monomials, with the winding index computed from the degree.

(local (defthm lw-pmo-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pmo-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pmo-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pmo-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pmo-times-negative (a b) (b a)))
                 :in-theory (disable lw-pmo-times-negative)))))

(local (defthm lw-pmo-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pmo-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pmo-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pmo-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pmo-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pmo-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pmo-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-pmo-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pmo-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pmo-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-pmo-left-commutes)))))

(defun lw-polynomial-monomial (leading degree)
 (declare (xargs :measure (nfix degree) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (zp degree) (list leading)
  (cons (cons 0 0) (lw-polynomial-monomial leading (- degree 1)))))

(defthm lw-polynomial-monomial-valid
 (implies (and (lw-complexp leading) (natp degree))
  (and (lw-complex-coefficientsp (lw-polynomial-monomial leading degree))
       (equal (len (lw-polynomial-monomial leading degree)) (+ 1 degree))))
 :hints (("Goal" :induct (lw-polynomial-monomial leading degree)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-monomial lw-complex-coefficientsp len (:executable-counterpart lw-complexp) lw-pmo-left-commutes lw-pmo-left-distributes lw-pmo-fold-constants lw-pmo-times-negative lw-pmo-negative-times lw-pmo-zero-times lw-pmo-minus-one lw-pmo-double-negative lw-pmo-add-cancel lw-pmo-double lw-pmo-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-pmo-consp
 (consp (lw-polynomial-monomial leading degree))
 :hints (("Goal" :expand ((lw-polynomial-monomial leading degree)) :in-theory (union-theories
 '(fold-consts-in-+ lw-pmo-left-commutes lw-pmo-left-distributes lw-pmo-fold-constants lw-pmo-times-negative lw-pmo-negative-times lw-pmo-zero-times lw-pmo-minus-one lw-pmo-double-negative lw-pmo-add-cancel lw-pmo-double lw-pmo-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-pmo-empty-polynomial
 (equal (lw-complex-polynomial nil point 0) (cons 0 0))
 :hints (("Goal" :expand ((lw-complex-polynomial nil point 0)) :in-theory (union-theories
 '(fold-consts-in-+ lw-pmo-left-commutes lw-pmo-left-distributes lw-pmo-fold-constants lw-pmo-times-negative lw-pmo-negative-times lw-pmo-zero-times lw-pmo-minus-one lw-pmo-double-negative lw-pmo-add-cancel lw-pmo-double lw-pmo-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-pmo-power-zero
 (implies (zp index) (equal (lw-complex-power point index) (cons 1 0)))
 :hints (("Goal" :expand ((lw-complex-power point index)) :in-theory (union-theories
 '(fold-consts-in-+ lw-pmo-left-commutes lw-pmo-left-distributes lw-pmo-fold-constants lw-pmo-times-negative lw-pmo-negative-times lw-pmo-zero-times lw-pmo-minus-one lw-pmo-double-negative lw-pmo-add-cancel lw-pmo-double lw-pmo-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-polynomial-monomial-evaluation
 (implies (and (lw-complexp leading) (lw-complexp point) (natp degree))
  (equal (lw-complex-polynomial (lw-polynomial-monomial leading degree) point 0)
         (lw-complex-mul leading (lw-complex-power point degree))))
 :hints (("Goal" :induct (lw-polynomial-monomial leading degree)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-monomial lw-pmo-consp lw-polynomial-monomial-valid lw-complex-coefficientsp (:executable-counterpart lw-complexp) lw-complex-polynomial-horner lw-complex-polynomial-rational lw-complex-power-rational lw-complex-ring-rational lw-complex-add-zero lw-complex-mul-zero lw-complex-mul-one lw-complex-mul-left-commutes lw-pmo-empty-polynomial lw-pmo-power-zero lw-pmo-left-commutes lw-pmo-left-distributes lw-pmo-fold-constants lw-pmo-times-negative lw-pmo-negative-times lw-pmo-zero-times lw-pmo-minus-one lw-pmo-double-negative lw-pmo-add-cancel lw-pmo-double lw-pmo-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) )
         (and stable-under-simplificationp
          '(:expand ((lw-complex-power point degree))
            :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-power-rational lw-complex-mul-left-commutes lw-complex-mul-one lw-pmo-power-zero lw-pmo-left-commutes lw-pmo-left-distributes lw-pmo-fold-constants lw-pmo-times-negative lw-pmo-negative-times lw-pmo-zero-times lw-pmo-minus-one lw-pmo-double-negative lw-pmo-add-cancel lw-pmo-double lw-pmo-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-polynomial-monomial-path
 (implies (and (lw-complexp leading) (natp degree) (lw-ray-pointsp points))
  (equal (lw-polynomial-path-values (lw-polynomial-monomial leading degree) points)
         (lw-ray-multiply-points leading (lw-ray-power-points points degree))))
 :hints (("Goal" :induct (lw-ray-power-points points degree)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-path-values lw-ray-multiply-points lw-ray-power-points lw-ray-pointsp lw-polynomial-monomial-evaluation lw-pmo-left-commutes lw-pmo-left-distributes lw-pmo-fold-constants lw-pmo-times-negative lw-pmo-negative-times lw-pmo-zero-times lw-pmo-minus-one lw-pmo-double-negative lw-pmo-add-cancel lw-pmo-double lw-pmo-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-polynomial-monomial-boundary-index
 (implies (and (natp degree) (lw-complexp leading) (not (equal leading (cons 0 0))))
  (equal (lw-ray-polygon-index
    (lw-polynomial-path-values (lw-polynomial-monomial leading degree)
     (lw-unit-square-boundary (lw-unit-square-power-count degree))))
   degree))
 :hints (("Goal"
  :use (lw-unit-square-leading-monomial-index lw-unit-square-power-boundary-data
        (:instance lw-ray-annulus-data
          (points (lw-unit-square-boundary (lw-unit-square-power-count degree))) (lower 1) (upper 2)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-monomial-path lw-pmo-left-commutes lw-pmo-left-distributes lw-pmo-fold-constants lw-pmo-times-negative lw-pmo-negative-times lw-pmo-zero-times lw-pmo-minus-one lw-pmo-double-negative lw-pmo-add-cancel lw-pmo-double lw-pmo-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-polynomial-monomial-grid-index
 (implies (and (natp degree) (lw-complexp leading) (not (equal leading (cons 0 0))))
  (equal (lw-ray-grid-boundary-index
    (lw-polynomial-grid (lw-polynomial-monomial leading degree)
     '(-1 . -1) 2 (lw-unit-square-power-count degree)))
   degree))
 :hints (("Goal"
  :use (lw-polynomial-monomial-boundary-index lw-unit-square-power-count-data
        (:instance lw-polynomial-grid-boundary-as-polygon
          (coefficients (lw-polynomial-monomial leading degree))
          (anchor '(-1 . -1)) (side 2) (count (lw-unit-square-power-count degree))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-unit-square-boundary-canonical lw-polynomial-monomial-valid (:executable-counterpart lw-complexp) lw-pmo-left-commutes lw-pmo-left-distributes lw-pmo-fold-constants lw-pmo-times-negative lw-pmo-negative-times lw-pmo-zero-times lw-pmo-minus-one lw-pmo-double-negative lw-pmo-add-cancel lw-pmo-double lw-pmo-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

