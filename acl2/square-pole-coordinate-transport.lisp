(in-package "ACL2")

(include-book "euler-model-pole-candidates")
(include-book "unit-square-pole-split")

; The coordinate change carries the selected sum to the physical pole list.

(local (defthm lw-spt-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-spt-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-spt-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-spt-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-spt-times-negative (a b) (b a)))
                 :in-theory (disable lw-spt-times-negative)))))

(local (defthm lw-spt-zero-times (equal (* 0 a) 0)))

(local (defthm lw-spt-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-spt-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-spt-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-spt-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-spt-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-spt-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-spt-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-spt-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-spt-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-spt-left-commutes)))))

(local (defthm lw-spt-forward-difference
 (implies (and (lw-complexp anchor) (rationalp side) (lw-complexp point) (lw-complexp root))
  (equal (lw-complex-sub (lw-polynomial-square-forward anchor side point) (lw-polynomial-square-forward anchor side root))
         (lw-complex-scale (* 1/2 side) (lw-complex-sub point root))))
 :hints (("Goal"
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-square-forward lw-polynomial-square-center lw-polynomial-square-slope lw-complex-add lw-complex-sub lw-complex-scale lw-complex-mul lw-complexp lw-spt-left-commutes lw-spt-left-distributes lw-spt-fold-constants lw-spt-times-negative lw-spt-negative-times lw-spt-zero-times lw-spt-minus-one lw-spt-double-negative lw-spt-add-cancel lw-spt-double lw-spt-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(local (defthm lw-spt-mul-real
 (implies (and (rationalp factor) (lw-complexp value))
  (equal (lw-complex-mul (cons factor 0) value) (lw-complex-scale factor value)))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-mul lw-complex-scale lw-complexp lw-spt-left-commutes lw-spt-left-distributes lw-spt-fold-constants lw-spt-times-negative lw-spt-negative-times lw-spt-zero-times lw-spt-minus-one lw-spt-double-negative lw-spt-add-cancel lw-spt-double lw-spt-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-spt-scaled-reciprocal
 (implies (and (rationalp factor) (not (equal factor 0)) (lw-complexp value))
  (equal (lw-complex-scale factor (lw-complex-reciprocal (lw-complex-scale factor value)))
         (lw-complex-reciprocal value)))
 :hints (("Goal" :cases ((equal value (cons 0 0)))
  :use ((:instance lw-complex-reciprocal-product (a (cons factor 0)) (b value))
        (:instance lw-complex-reciprocal-cancel-product
          (a (cons factor 0)) (b (lw-complex-reciprocal value)))
        (:instance lw-complex-reciprocal-rational (point value))
        (:instance lw-complex-reciprocal-rational
          (point (lw-complex-mul (cons factor 0) value))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-spt-mul-real lw-complex-scale-zero lw-complex-ring-rational lw-complex-reciprocal-rational lw-complexp (:executable-counterpart lw-complex-reciprocal) (:executable-counterpart lw-complex-scale) lw-spt-left-commutes lw-spt-left-distributes lw-spt-fold-constants lw-spt-times-negative lw-spt-negative-times lw-spt-zero-times lw-spt-minus-one lw-spt-double-negative lw-spt-add-cancel lw-spt-double lw-spt-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(local (defthm lw-spt-mapped-log-sum-rational
 (implies (and (lw-complexp anchor) (rationalp side) (lw-complexp point) (lw-ray-pointsp roots))
  (lw-complexp (lw-factor-model-log-sum (lw-polynomial-square-forward anchor side point) (lw-square-unit-pole-candidates anchor side roots))))
 :hints (("Goal" :induct (lw-square-unit-pole-candidates anchor side roots)
  :in-theory (union-theories
 '(fold-consts-in-+ lw-square-unit-pole-candidates lw-factor-model-log-sum lw-ray-pointsp lw-complex-ring-rational lw-complex-reciprocal-rational lw-complex-scale-rational lw-polynomial-square-map-data (:executable-counterpart lw-complexp) endp lw-spt-left-commutes lw-spt-left-distributes lw-spt-fold-constants lw-spt-times-negative lw-spt-negative-times lw-spt-zero-times lw-spt-minus-one lw-spt-double-negative lw-spt-add-cancel lw-spt-double lw-spt-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-square-unit-pole-sum-coordinate-identity
 (implies (and (lw-complexp anchor) (rationalp side) (< 0 side) (lw-complexp point) (lw-ray-pointsp roots))
  (equal (lw-complex-scale (* 1/2 side) (lw-factor-model-log-sum (lw-polynomial-square-forward anchor side point) (lw-square-unit-pole-candidates anchor side roots)))
         (lw-polynomial-factor-log-sum roots point)))
 :hints (("Goal" :induct (lw-square-unit-pole-candidates anchor side roots)
  :in-theory (union-theories
 '(fold-consts-in-+ lw-square-unit-pole-candidates lw-factor-model-log-sum lw-polynomial-factor-log-sum lw-ray-pointsp lw-spt-mapped-log-sum-rational lw-polynomial-square-map-data lw-spt-forward-difference lw-spt-scaled-reciprocal lw-complex-scale-add lw-complex-scale-zero lw-complex-scale-one lw-complex-scale-rational lw-complex-ring-rational lw-complex-reciprocal-rational endp lw-spt-left-commutes lw-spt-left-distributes lw-spt-fold-constants lw-spt-times-negative lw-spt-negative-times lw-spt-zero-times lw-spt-minus-one lw-spt-double-negative lw-spt-add-cancel lw-spt-double lw-spt-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))
