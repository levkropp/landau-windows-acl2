; Glue independently computed normalized models at common physical points.
(in-package "ACL2")
(include-book "euler-normalized-inner-series")
(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-reciprocal lw-complex-norm-square
                 lw-complex-l1 lw-rational-power lw-complex-exp-value lw-complex-exp-cap
                 lw-complex-exp-uniform-cap lw-exp-lipschitz-cap lw-log-bounds
                 lw-complex-laplace-point lw-complex-laplace-shifted-value
                 lw-complex-laplace-shifted-grid lw-complex-mul-subtract
                 lw-complex-mul-commutative lw-complex-mul-left-commutes
                 lw-exp-bounds lw-exp-neg-bounds lw-exp-index lw-exp-band lw-exp-sum lw-exp-term
                 lw-damped-phase-sample lw-phase-value
                 lw-complex-exp-integral-value lw-complex-exp-integral-grid
                 lw-complex-exp-primitive-value lw-complex-exp-grid
                 lw-complex-disk-enlarge lw-disk-enlarge lw-precision-fuel)))

(local (in-theory
 (disable lw-complex-log-ramp-start lw-complex-log-ramp-cap
          lw-complex-log-ramp-independent-exp lw-complex-log-ramp-independent-endpoint
          lw-complex-log-ramp-independent-model
          lw-complex-log-ramp-independent-model-identity
          lw-smoothed-ramp-log-error lw-smoothed-ramp-unit-error lw-mangoldt-bounds
          lw-complex-sub-add-first lw-complex-add-commutative lw-complex-add-left-commutes)))
(local (in-theory (disable lw-euler-value-clearance-check lw-euler-local-normalized-radius
 lw-euler-local-normalized-anchor lw-euler-local-normalized-polynomial
 lw-complex-euler-normalized-inner-series-value lw-mellin-euler-log-extended-value
 lw-complex-polynomial)))
(local (defthm lw-nov-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-nov-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-nov-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-nov-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-nov-times-negative (a b) (b a)))
                 :in-theory (disable lw-nov-times-negative)))))

(local (defthm lw-nov-zero-times (equal (* 0 a) 0)))

(local (defthm lw-nov-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-nov-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-nov-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-nov-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-nov-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-nov-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-nov-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-nov-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-nov-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-nov-left-commutes)))))
(local (defthm lw-nov-polynomial-overlap-margin
 (implies (and (lw-euler-value-clearance-check left-rate left-height left-anchor-error)
 (rationalp left-outer-radius) (< 0 left-outer-radius) (< left-outer-radius left-rate) (lw-euler-value-clearance-check right-rate right-height right-anchor-error)
 (rationalp right-outer-radius) (< 0 right-outer-radius) (< right-outer-radius right-rate) (lw-complex-diskp left-point (lw-euler-local-normalized-radius left-rate left-height left-outer-radius left-anchor-error)) (lw-complex-diskp right-point (lw-euler-local-normalized-radius right-rate right-height right-outer-radius right-anchor-error))
 (equal (+ left-rate (car left-point)) (+ right-rate (car right-point))) (equal (+ left-height (cdr left-point)) (+ right-height (cdr right-point)))
 (natp left-target) (natp right-target) (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error) (rationalp margin) (< 0 margin))
 (lw-complex-diskp (lw-complex-sub (lw-complex-polynomial (lw-euler-local-normalized-polynomial left-rate left-height left-outer-radius left-anchor-error left-target left-error) left-point 0) (lw-complex-polynomial (lw-euler-local-normalized-polynomial right-rate right-height right-outer-radius right-anchor-error right-target right-error) right-point 0)) (+ (* 1/2 (+ left-error right-error)) margin)))
 :hints (("Goal"
 :use ((:instance lw-euler-local-normalized-data (rate left-rate) (height left-height) (outer-radius left-outer-radius) (anchor-error left-anchor-error))
       (:instance lw-euler-local-normalized-data (rate right-rate) (height right-height) (outer-radius right-outer-radius) (anchor-error right-anchor-error))
       (:instance lw-euler-local-normalized-point-data (rate left-rate) (height left-height) (outer-radius left-outer-radius) (anchor-error left-anchor-error) (point left-point))
       (:instance lw-euler-local-normalized-point-data (rate right-rate) (height right-height) (outer-radius right-outer-radius) (anchor-error right-anchor-error) (point right-point))
       (:instance lw-euler-local-normalized-polynomial-valid (rate left-rate) (height left-height) (outer-radius left-outer-radius) (anchor-error left-anchor-error) (target left-target) (error left-error))
       (:instance lw-euler-local-normalized-polynomial-valid (rate right-rate) (height right-height) (outer-radius right-outer-radius) (anchor-error right-anchor-error) (target right-target) (error right-error))
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-local-normalized-polynomial left-rate left-height left-outer-radius left-anchor-error left-target left-error)) (point left-point) (offset 0))
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-local-normalized-polynomial right-rate right-height right-outer-radius right-anchor-error right-target right-error)) (point right-point) (offset 0))
       (:instance lw-mellin-euler-log-extended-value-rational (rate (+ left-rate (car left-point))) (height (+ left-height (cdr left-point)))
        (radius (* 1/2 (+ left-rate (car left-point)))) (anchor-error (lw-euler-local-normalized-anchor left-rate left-height left-anchor-error)) (error margin))
       (:instance lw-complex-euler-local-normalized-comparison (rate left-rate) (height left-height) (outer-radius left-outer-radius) (anchor-error left-anchor-error) (point left-point) (target left-target) (error left-error)
        (local-anchor (lw-euler-local-normalized-anchor left-rate left-height left-anchor-error)) (coefficient-radius (* 1/2 (+ left-rate (car left-point)))) (value-error margin))
       (:instance lw-complex-euler-local-normalized-comparison (rate right-rate) (height right-height) (outer-radius right-outer-radius) (anchor-error right-anchor-error) (point right-point) (target right-target) (error right-error)
        (local-anchor (lw-euler-local-normalized-anchor left-rate left-height left-anchor-error)) (coefficient-radius (* 1/2 (+ left-rate (car left-point)))) (value-error margin))
       (:instance lw-complex-difference-symmetric (left (lw-complex-polynomial (lw-euler-local-normalized-polynomial right-rate right-height right-outer-radius right-anchor-error right-target right-error) right-point 0)) (right (lw-mellin-euler-log-extended-value (+ left-rate (car left-point)) (+ left-height (cdr left-point)) (* 1/2 (+ left-rate (car left-point))) (lw-euler-local-normalized-anchor left-rate left-height left-anchor-error) margin)) (radius (* 1/2 (+ right-error margin))))
       (:instance lw-complex-difference-triangle (left (lw-complex-polynomial (lw-euler-local-normalized-polynomial left-rate left-height left-outer-radius left-anchor-error left-target left-error) left-point 0)) (middle (lw-mellin-euler-log-extended-value (+ left-rate (car left-point)) (+ left-height (cdr left-point)) (* 1/2 (+ left-rate (car left-point))) (lw-euler-local-normalized-anchor left-rate left-height left-anchor-error) margin)) (right (lw-complex-polynomial (lw-euler-local-normalized-polynomial right-rate right-height right-outer-radius right-anchor-error right-target right-error) right-point 0))
        (radius (* 1/2 (+ left-error margin))) (other-radius (* 1/2 (+ right-error margin)))))
 :in-theory (union-theories
 '(lw-complexp lw-nov-left-commutes lw-nov-left-distributes lw-nov-fold-constants lw-nov-times-negative lw-nov-negative-times lw-nov-zero-times lw-nov-minus-one lw-nov-double-negative lw-nov-add-cancel lw-nov-double lw-nov-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes nil))
(defthm lw-complex-euler-local-normalized-polynomial-overlap
 (implies (and (lw-euler-value-clearance-check left-rate left-height left-anchor-error)
 (rationalp left-outer-radius) (< 0 left-outer-radius) (< left-outer-radius left-rate) (lw-euler-value-clearance-check right-rate right-height right-anchor-error)
 (rationalp right-outer-radius) (< 0 right-outer-radius) (< right-outer-radius right-rate) (lw-complex-diskp left-point (lw-euler-local-normalized-radius left-rate left-height left-outer-radius left-anchor-error)) (lw-complex-diskp right-point (lw-euler-local-normalized-radius right-rate right-height right-outer-radius right-anchor-error))
 (equal (+ left-rate (car left-point)) (+ right-rate (car right-point))) (equal (+ left-height (cdr left-point)) (+ right-height (cdr right-point)))
 (natp left-target) (natp right-target) (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
 (lw-complex-diskp (lw-complex-sub (lw-complex-polynomial (lw-euler-local-normalized-polynomial left-rate left-height left-outer-radius left-anchor-error left-target left-error) left-point 0) (lw-complex-polynomial (lw-euler-local-normalized-polynomial right-rate right-height right-outer-radius right-anchor-error right-target right-error) right-point 0)) (* 1/2 (+ left-error right-error))))
 :hints (("Goal"
 :cases ((lw-complex-diskp (lw-complex-sub (lw-complex-polynomial (lw-euler-local-normalized-polynomial left-rate left-height left-outer-radius left-anchor-error left-target left-error) left-point 0) (lw-complex-polynomial (lw-euler-local-normalized-polynomial right-rate right-height right-outer-radius right-anchor-error right-target right-error) right-point 0)) (* 1/2 (+ left-error right-error))))
 :use ((:instance lw-euler-local-normalized-data (rate left-rate) (height left-height) (outer-radius left-outer-radius) (anchor-error left-anchor-error))
       (:instance lw-euler-local-normalized-data (rate right-rate) (height right-height) (outer-radius right-outer-radius) (anchor-error right-anchor-error))
       (:instance lw-euler-local-normalized-point-data (rate left-rate) (height left-height) (outer-radius left-outer-radius) (anchor-error left-anchor-error) (point left-point))
       (:instance lw-euler-local-normalized-point-data (rate right-rate) (height right-height) (outer-radius right-outer-radius) (anchor-error right-anchor-error) (point right-point))
       (:instance lw-euler-local-normalized-polynomial-valid (rate left-rate) (height left-height) (outer-radius left-outer-radius) (anchor-error left-anchor-error) (target left-target) (error left-error))
       (:instance lw-euler-local-normalized-polynomial-valid (rate right-rate) (height right-height) (outer-radius right-outer-radius) (anchor-error right-anchor-error) (target right-target) (error right-error))
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-local-normalized-polynomial left-rate left-height left-outer-radius left-anchor-error left-target left-error)) (point left-point) (offset 0))
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-local-normalized-polynomial right-rate right-height right-outer-radius right-anchor-error right-target right-error)) (point right-point) (offset 0))
       (:instance lw-complex-operations-rational (left (lw-complex-polynomial (lw-euler-local-normalized-polynomial left-rate left-height left-outer-radius left-anchor-error left-target left-error) left-point 0)) (right (lw-complex-polynomial (lw-euler-local-normalized-polynomial right-rate right-height right-outer-radius right-anchor-error right-target right-error) right-point 0)) (factor 1))
       (:instance lw-complex-disk-gap-refinement-excludes (point (lw-complex-sub (lw-complex-polynomial (lw-euler-local-normalized-polynomial left-rate left-height left-outer-radius left-anchor-error left-target left-error) left-point 0) (lw-complex-polynomial (lw-euler-local-normalized-polynomial right-rate right-height right-outer-radius right-anchor-error right-target right-error) right-point 0))) (radius (* 1/2 (+ left-error right-error))) (cost 1))
       (:instance lw-nov-polynomial-overlap-margin (margin (lw-disk-gap-refinement (lw-complex-sub (lw-complex-polynomial (lw-euler-local-normalized-polynomial left-rate left-height left-outer-radius left-anchor-error left-target left-error) left-point 0) (lw-complex-polynomial (lw-euler-local-normalized-polynomial right-rate right-height right-outer-radius right-anchor-error right-target right-error) right-point 0)) (* 1/2 (+ left-error right-error)) 1))))
 :in-theory (union-theories
 '( lw-nov-left-commutes lw-nov-left-distributes lw-nov-fold-constants lw-nov-times-negative lw-nov-negative-times lw-nov-zero-times lw-nov-minus-one lw-nov-double-negative lw-nov-add-cancel lw-nov-double lw-nov-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))


(local (defthm lw-nov-series-overlap-margin
 (implies (and (lw-euler-value-clearance-check left-rate left-height left-anchor-error)
 (rationalp left-outer-radius) (< 0 left-outer-radius) (< left-outer-radius left-rate) (lw-euler-value-clearance-check right-rate right-height right-anchor-error)
 (rationalp right-outer-radius) (< 0 right-outer-radius) (< right-outer-radius right-rate) (rationalp left-inner) (<= 0 left-inner) (< left-inner 1)
 (rationalp right-inner) (<= 0 right-inner) (< right-inner 1)
 (lw-complex-diskp left-point left-inner) (lw-complex-diskp right-point right-inner)
 (equal (+ left-rate (car (lw-complex-scale (lw-euler-local-normalized-radius left-rate left-height left-outer-radius left-anchor-error) left-point))) (+ right-rate (car (lw-complex-scale (lw-euler-local-normalized-radius right-rate right-height right-outer-radius right-anchor-error) right-point)))) (equal (+ left-height (cdr (lw-complex-scale (lw-euler-local-normalized-radius left-rate left-height left-outer-radius left-anchor-error) left-point))) (+ right-height (cdr (lw-complex-scale (lw-euler-local-normalized-radius right-rate right-height right-outer-radius right-anchor-error) right-point))))
 (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error) (rationalp margin) (< 0 margin))
 (lw-complex-diskp (lw-complex-sub (lw-complex-euler-normalized-inner-series-value left-rate left-height left-outer-radius left-anchor-error left-inner left-point left-error) (lw-complex-euler-normalized-inner-series-value right-rate right-height right-outer-radius right-anchor-error right-inner right-point right-error)) (+ (* 1/2 (+ left-error right-error)) margin)))
 :hints (("Goal"
 :use ((:instance lw-euler-local-normalized-data (rate left-rate) (height left-height) (outer-radius left-outer-radius) (anchor-error left-anchor-error))
       (:instance lw-euler-local-normalized-data (rate right-rate) (height right-height) (outer-radius right-outer-radius) (anchor-error right-anchor-error))
       (:instance lw-euler-normalized-inner-point-data (rate left-rate) (height left-height) (outer-radius left-outer-radius) (anchor-error left-anchor-error) (point left-point) (inner left-inner))
       (:instance lw-euler-normalized-inner-point-data (rate right-rate) (height right-height) (outer-radius right-outer-radius) (anchor-error right-anchor-error) (point right-point) (inner right-inner))
       (:instance lw-complex-euler-normalized-inner-series-value-rational (rate left-rate) (height left-height) (outer-radius left-outer-radius) (anchor-error left-anchor-error) (point left-point) (inner left-inner) (error left-error))
       (:instance lw-complex-euler-normalized-inner-series-value-rational (rate right-rate) (height right-height) (outer-radius right-outer-radius) (anchor-error right-anchor-error) (point right-point) (inner right-inner) (error right-error))
       (:instance lw-mellin-euler-log-extended-value-rational (rate (+ left-rate (car (lw-complex-scale (lw-euler-local-normalized-radius left-rate left-height left-outer-radius left-anchor-error) left-point)))) (height (+ left-height (cdr (lw-complex-scale (lw-euler-local-normalized-radius left-rate left-height left-outer-radius left-anchor-error) left-point))))
        (radius (* 1/2 (+ left-rate (car (lw-complex-scale (lw-euler-local-normalized-radius left-rate left-height left-outer-radius left-anchor-error) left-point))))) (anchor-error (lw-euler-local-normalized-anchor left-rate left-height left-anchor-error)) (error margin))
       (:instance lw-complex-euler-normalized-inner-series-value-agreement (rate left-rate) (height left-height) (outer-radius left-outer-radius) (anchor-error left-anchor-error) (point left-point) (inner left-inner) (error left-error)
        (local-anchor (lw-euler-local-normalized-anchor left-rate left-height left-anchor-error)) (coefficient-radius (* 1/2 (+ left-rate (car (lw-complex-scale (lw-euler-local-normalized-radius left-rate left-height left-outer-radius left-anchor-error) left-point))))) (value-error margin))
       (:instance lw-complex-euler-normalized-inner-series-value-agreement (rate right-rate) (height right-height) (outer-radius right-outer-radius) (anchor-error right-anchor-error) (point right-point) (inner right-inner) (error right-error)
        (local-anchor (lw-euler-local-normalized-anchor left-rate left-height left-anchor-error)) (coefficient-radius (* 1/2 (+ left-rate (car (lw-complex-scale (lw-euler-local-normalized-radius left-rate left-height left-outer-radius left-anchor-error) left-point))))) (value-error margin))
       (:instance lw-complex-difference-symmetric (left (lw-complex-euler-normalized-inner-series-value right-rate right-height right-outer-radius right-anchor-error right-inner right-point right-error)) (right (lw-mellin-euler-log-extended-value (+ left-rate (car (lw-complex-scale (lw-euler-local-normalized-radius left-rate left-height left-outer-radius left-anchor-error) left-point))) (+ left-height (cdr (lw-complex-scale (lw-euler-local-normalized-radius left-rate left-height left-outer-radius left-anchor-error) left-point))) (* 1/2 (+ left-rate (car (lw-complex-scale (lw-euler-local-normalized-radius left-rate left-height left-outer-radius left-anchor-error) left-point)))) (lw-euler-local-normalized-anchor left-rate left-height left-anchor-error) margin)) (radius (* 1/2 (+ right-error margin))))
       (:instance lw-complex-difference-triangle (left (lw-complex-euler-normalized-inner-series-value left-rate left-height left-outer-radius left-anchor-error left-inner left-point left-error)) (middle (lw-mellin-euler-log-extended-value (+ left-rate (car (lw-complex-scale (lw-euler-local-normalized-radius left-rate left-height left-outer-radius left-anchor-error) left-point))) (+ left-height (cdr (lw-complex-scale (lw-euler-local-normalized-radius left-rate left-height left-outer-radius left-anchor-error) left-point))) (* 1/2 (+ left-rate (car (lw-complex-scale (lw-euler-local-normalized-radius left-rate left-height left-outer-radius left-anchor-error) left-point)))) (lw-euler-local-normalized-anchor left-rate left-height left-anchor-error) margin)) (right (lw-complex-euler-normalized-inner-series-value right-rate right-height right-outer-radius right-anchor-error right-inner right-point right-error))
        (radius (* 1/2 (+ left-error margin))) (other-radius (* 1/2 (+ right-error margin)))))
 :in-theory (union-theories
 '(lw-complexp lw-nov-left-commutes lw-nov-left-distributes lw-nov-fold-constants lw-nov-times-negative lw-nov-negative-times lw-nov-zero-times lw-nov-minus-one lw-nov-double-negative lw-nov-add-cancel lw-nov-double lw-nov-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes nil))
(defthm lw-complex-euler-normalized-inner-series-overlap
 (implies (and (lw-euler-value-clearance-check left-rate left-height left-anchor-error)
 (rationalp left-outer-radius) (< 0 left-outer-radius) (< left-outer-radius left-rate) (lw-euler-value-clearance-check right-rate right-height right-anchor-error)
 (rationalp right-outer-radius) (< 0 right-outer-radius) (< right-outer-radius right-rate) (rationalp left-inner) (<= 0 left-inner) (< left-inner 1)
 (rationalp right-inner) (<= 0 right-inner) (< right-inner 1)
 (lw-complex-diskp left-point left-inner) (lw-complex-diskp right-point right-inner)
 (equal (+ left-rate (car (lw-complex-scale (lw-euler-local-normalized-radius left-rate left-height left-outer-radius left-anchor-error) left-point))) (+ right-rate (car (lw-complex-scale (lw-euler-local-normalized-radius right-rate right-height right-outer-radius right-anchor-error) right-point)))) (equal (+ left-height (cdr (lw-complex-scale (lw-euler-local-normalized-radius left-rate left-height left-outer-radius left-anchor-error) left-point))) (+ right-height (cdr (lw-complex-scale (lw-euler-local-normalized-radius right-rate right-height right-outer-radius right-anchor-error) right-point))))
 (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
 (lw-complex-diskp (lw-complex-sub (lw-complex-euler-normalized-inner-series-value left-rate left-height left-outer-radius left-anchor-error left-inner left-point left-error) (lw-complex-euler-normalized-inner-series-value right-rate right-height right-outer-radius right-anchor-error right-inner right-point right-error)) (* 1/2 (+ left-error right-error))))
 :hints (("Goal"
 :cases ((lw-complex-diskp (lw-complex-sub (lw-complex-euler-normalized-inner-series-value left-rate left-height left-outer-radius left-anchor-error left-inner left-point left-error) (lw-complex-euler-normalized-inner-series-value right-rate right-height right-outer-radius right-anchor-error right-inner right-point right-error)) (* 1/2 (+ left-error right-error))))
 :use ((:instance lw-euler-local-normalized-data (rate left-rate) (height left-height) (outer-radius left-outer-radius) (anchor-error left-anchor-error))
       (:instance lw-euler-local-normalized-data (rate right-rate) (height right-height) (outer-radius right-outer-radius) (anchor-error right-anchor-error))
       (:instance lw-euler-normalized-inner-point-data (rate left-rate) (height left-height) (outer-radius left-outer-radius) (anchor-error left-anchor-error) (point left-point) (inner left-inner))
       (:instance lw-euler-normalized-inner-point-data (rate right-rate) (height right-height) (outer-radius right-outer-radius) (anchor-error right-anchor-error) (point right-point) (inner right-inner))
       (:instance lw-complex-euler-normalized-inner-series-value-rational (rate left-rate) (height left-height) (outer-radius left-outer-radius) (anchor-error left-anchor-error) (point left-point) (inner left-inner) (error left-error))
       (:instance lw-complex-euler-normalized-inner-series-value-rational (rate right-rate) (height right-height) (outer-radius right-outer-radius) (anchor-error right-anchor-error) (point right-point) (inner right-inner) (error right-error))
       (:instance lw-complex-operations-rational (left (lw-complex-euler-normalized-inner-series-value left-rate left-height left-outer-radius left-anchor-error left-inner left-point left-error)) (right (lw-complex-euler-normalized-inner-series-value right-rate right-height right-outer-radius right-anchor-error right-inner right-point right-error)) (factor 1))
       (:instance lw-complex-disk-gap-refinement-excludes (point (lw-complex-sub (lw-complex-euler-normalized-inner-series-value left-rate left-height left-outer-radius left-anchor-error left-inner left-point left-error) (lw-complex-euler-normalized-inner-series-value right-rate right-height right-outer-radius right-anchor-error right-inner right-point right-error))) (radius (* 1/2 (+ left-error right-error))) (cost 1))
       (:instance lw-nov-series-overlap-margin (margin (lw-disk-gap-refinement (lw-complex-sub (lw-complex-euler-normalized-inner-series-value left-rate left-height left-outer-radius left-anchor-error left-inner left-point left-error) (lw-complex-euler-normalized-inner-series-value right-rate right-height right-outer-radius right-anchor-error right-inner right-point right-error)) (* 1/2 (+ left-error right-error)) 1))))
 :in-theory (union-theories
 '( lw-nov-left-commutes lw-nov-left-distributes lw-nov-fold-constants lw-nov-times-negative lw-nov-negative-times lw-nov-zero-times lw-nov-minus-one lw-nov-double-negative lw-nov-add-cancel lw-nov-double lw-nov-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

