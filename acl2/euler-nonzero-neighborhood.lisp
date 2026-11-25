; One accepted coarse Euler value check generates a whole nonzero neighborhood.
; All radii and constants below are computed from actual rational evaluators.
(in-package "ACL2")
(include-book "polynomial-disk-increments")
(include-book "polynomial-half-disk-slope")
(include-book "euler-value-clearance")
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

(local (in-theory (disable lw-complex-log-ramp-exp lw-complex-log-ramp-endpoint lw-complex-log-ramp-model)))

(local (in-theory (disable lw-euler-uniform-polynomial
 lw-complex-euler-continuation-value lw-polynomial-affine
 lw-polynomial-multiply-linear lw-polynomial-add-constant)))
(local (in-theory (disable lw-euler-value-clearance-check lw-euler-value-clearance-size
 lw-euler-value-clearance-lower lw-polynomial-disk-increment-cap lw-euler-rounding-precision
 lw-complex-polynomial)))
(local (defthm lw-enn-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-enn-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-enn-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-enn-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-enn-times-negative (a b) (b a)))
                 :in-theory (disable lw-enn-times-negative)))))

(local (defthm lw-enn-zero-times (equal (* 0 a) 0)))

(local (defthm lw-enn-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-enn-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-enn-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-enn-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-enn-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-enn-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-enn-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-enn-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-enn-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-enn-left-commutes)))))

(defun lw-euler-neighborhood-slope-cap (rate height outer-radius anchor-error)
 (lw-polynomial-half-disk-slope (lw-euler-uniform-polynomial rate height outer-radius 0 anchor-error) outer-radius))

(defun lw-euler-neighborhood-radius (rate height outer-radius anchor-error)
 (min (/ outer-radius 2)
      (lw-euler-rounding-precision (lw-euler-neighborhood-slope-cap rate height outer-radius anchor-error) (/ (lw-euler-value-clearance-size rate height anchor-error) 32))))

(local (in-theory (disable lw-euler-neighborhood-slope-cap lw-euler-neighborhood-radius)))

(defthm lw-euler-neighborhood-data
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate))
 (and (rationalp rate) (< 0 rate) (rationalp height)
      (rationalp anchor-error) (< 0 anchor-error)
      (rationalp (lw-euler-value-clearance-size rate height anchor-error)) (< 0 (lw-euler-value-clearance-size rate height anchor-error)) (<= anchor-error (* 1/16 (lw-euler-value-clearance-size rate height anchor-error)))
      (lw-complexp (lw-complex-euler-continuation-value rate height anchor-error)) (not (equal (lw-complex-euler-continuation-value rate height anchor-error) (cons 0 0)))
      (rationalp (lw-euler-neighborhood-slope-cap rate height outer-radius anchor-error)) (<= 0 (lw-euler-neighborhood-slope-cap rate height outer-radius anchor-error))
      (rationalp (lw-euler-neighborhood-radius rate height outer-radius anchor-error)) (< 0 (lw-euler-neighborhood-radius rate height outer-radius anchor-error)) (<= (lw-euler-neighborhood-radius rate height outer-radius anchor-error) 1)
      (<= (lw-euler-neighborhood-radius rate height outer-radius anchor-error) (/ outer-radius 2)) (< (lw-euler-neighborhood-radius rate height outer-radius anchor-error) outer-radius)
      (<= (* (lw-euler-neighborhood-slope-cap rate height outer-radius anchor-error) (lw-euler-neighborhood-radius rate height outer-radius anchor-error)) (* 1/64 (lw-euler-value-clearance-size rate height anchor-error)))))
 :hints (("Goal"
 :use (lw-euler-value-clearance-data
       (:instance lw-euler-uniform-polynomial-valid (radius outer-radius) (target 0) (error anchor-error))
       (:instance lw-polynomial-half-disk-slope-data (coefficients (lw-euler-uniform-polynomial rate height outer-radius 0 anchor-error)) (outer outer-radius))
       (:instance lw-euler-rounding-precision-valid (cost (lw-euler-neighborhood-slope-cap rate height outer-radius anchor-error)) (error (/ (lw-euler-value-clearance-size rate height anchor-error) 32)))
       (:instance lw-enn-multiply-order (a (lw-euler-neighborhood-radius rate height outer-radius anchor-error))
        (b (lw-euler-rounding-precision (lw-euler-neighborhood-slope-cap rate height outer-radius anchor-error) (/ (lw-euler-value-clearance-size rate height anchor-error) 32))) (factor (lw-euler-neighborhood-slope-cap rate height outer-radius anchor-error))))
 :in-theory (union-theories
 '(lw-euler-neighborhood-slope-cap lw-euler-neighborhood-radius lw-euler-value-clearance-lower min lw-enn-left-commutes lw-enn-left-distributes lw-enn-fold-constants lw-enn-times-negative lw-enn-negative-times lw-enn-zero-times lw-enn-minus-one lw-enn-double-negative lw-enn-add-cancel lw-enn-double lw-enn-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t)))

(local (defthm lw-enn-point-data
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (lw-complex-diskp point (lw-euler-neighborhood-radius rate height outer-radius anchor-error)))
 (and (lw-complexp point) (lw-complex-diskp point outer-radius)
      (rationalp (+ rate (car point))) (< 0 (+ rate (car point))) (rationalp (+ height (cdr point)))))
 :hints (("Goal"
 :use (lw-euler-neighborhood-data
       (:instance lw-complex-disk-data (radius (lw-euler-neighborhood-radius rate height outer-radius anchor-error)))
       (:instance lw-complex-disk-enlarge (radius (lw-euler-neighborhood-radius rate height outer-radius anchor-error)) (cap outer-radius))
       (:instance lw-euler-disk-point-data (radius outer-radius) (offset point)))
 :in-theory (union-theories
 '( lw-enn-left-commutes lw-enn-left-distributes lw-enn-fold-constants lw-enn-times-negative lw-enn-negative-times lw-enn-zero-times lw-enn-minus-one lw-enn-double-negative lw-enn-add-cancel lw-enn-double lw-enn-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-enn-coarse-anchor
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (lw-complex-diskp point (lw-euler-neighborhood-radius rate height outer-radius anchor-error)))
 (lw-complex-diskp (lw-complex-sub (lw-complex-polynomial (lw-euler-uniform-polynomial rate height outer-radius 0 anchor-error) point 0) (lw-complex-euler-continuation-value rate height anchor-error)) (* 1/8 (lw-euler-value-clearance-size rate height anchor-error))))
 :hints (("Goal"
 :use (lw-euler-neighborhood-data lw-enn-point-data
       (:instance lw-euler-uniform-polynomial-valid (radius outer-radius) (target 0) (error anchor-error))
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-uniform-polynomial rate height outer-radius 0 anchor-error)) (offset 0))
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-uniform-polynomial rate height outer-radius 0 anchor-error)) (point (cons 0 0)) (offset 0))
       (:instance lw-complex-zero-disk (radius outer-radius))
       (:instance lw-complex-polynomial-half-disk-increment-bound (outer outer-radius)
        (coefficients (lw-euler-uniform-polynomial rate height outer-radius 0 anchor-error)) (radius (lw-euler-neighborhood-radius rate height outer-radius anchor-error)))
       (:instance lw-complex-euler-uniform-polynomial-comparison
        (radius outer-radius) (target 0) (error anchor-error) (value-error anchor-error) (point (cons 0 0)))
       (:instance lw-complex-difference-triangle
        (left (lw-complex-polynomial (lw-euler-uniform-polynomial rate height outer-radius 0 anchor-error) point 0)) (middle (lw-complex-polynomial (lw-euler-uniform-polynomial rate height outer-radius 0 anchor-error) (cons 0 0) 0)) (right (lw-complex-euler-continuation-value rate height anchor-error))
        (radius (* (lw-euler-neighborhood-radius rate height outer-radius anchor-error) (lw-euler-neighborhood-slope-cap rate height outer-radius anchor-error))) (other-radius (+ anchor-error (* 1/4 anchor-error))))
       (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-polynomial (lw-euler-uniform-polynomial rate height outer-radius 0 anchor-error) point 0) (lw-complex-euler-continuation-value rate height anchor-error)))
        (radius (+ (* (lw-euler-neighborhood-radius rate height outer-radius anchor-error) (lw-euler-neighborhood-slope-cap rate height outer-radius anchor-error)) anchor-error (* 1/4 anchor-error))) (cap (* 1/8 (lw-euler-value-clearance-size rate height anchor-error)))))
 :in-theory (union-theories
 '(lw-euler-neighborhood-slope-cap (:executable-counterpart lw-complexp) lw-enn-left-commutes lw-enn-left-distributes lw-enn-fold-constants lw-enn-times-negative lw-enn-negative-times lw-enn-zero-times lw-enn-minus-one lw-enn-double-negative lw-enn-add-cancel lw-enn-double lw-enn-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(defthm lw-complex-euler-neighborhood-polynomial-anchor
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (lw-complex-diskp point (lw-euler-neighborhood-radius rate height outer-radius anchor-error))
  (natp target) (rationalp error) (< 0 error) (<= error anchor-error))
 (lw-complex-diskp (lw-complex-sub (lw-complex-polynomial (lw-euler-uniform-polynomial rate height outer-radius target error) point 0) (lw-complex-euler-continuation-value rate height anchor-error)) (* 1/4 (lw-euler-value-clearance-size rate height anchor-error))))
 :hints (("Goal"
 :use (lw-euler-neighborhood-data lw-enn-point-data lw-enn-coarse-anchor
       (:instance lw-euler-uniform-polynomial-valid (radius outer-radius))
       (:instance lw-euler-uniform-polynomial-valid (radius outer-radius) (target 0) (error anchor-error))
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-uniform-polynomial rate height outer-radius target error)) (offset 0))
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-uniform-polynomial rate height outer-radius 0 anchor-error)) (offset 0))
       (:instance lw-complex-euler-uniform-polynomial-cauchy
        (radius outer-radius) (left-target target) (right-target 0) (left-error error) (right-error anchor-error))
       (:instance lw-complex-difference-triangle (left (lw-complex-polynomial (lw-euler-uniform-polynomial rate height outer-radius target error) point 0)) (middle (lw-complex-polynomial (lw-euler-uniform-polynomial rate height outer-radius 0 anchor-error) point 0)) (right (lw-complex-euler-continuation-value rate height anchor-error))
        (radius (+ error anchor-error)) (other-radius (* 1/8 (lw-euler-value-clearance-size rate height anchor-error))))
       (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-polynomial (lw-euler-uniform-polynomial rate height outer-radius target error) point 0) (lw-complex-euler-continuation-value rate height anchor-error)))
        (radius (+ error anchor-error (* 1/8 (lw-euler-value-clearance-size rate height anchor-error)))) (cap (* 1/4 (lw-euler-value-clearance-size rate height anchor-error)))))
 :in-theory (union-theories
 '( lw-enn-left-commutes lw-enn-left-distributes lw-enn-fold-constants lw-enn-times-negative lw-enn-negative-times lw-enn-zero-times lw-enn-minus-one lw-enn-double-negative lw-enn-add-cancel lw-enn-double lw-enn-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-euler-neighborhood-value-anchor
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (lw-complex-diskp point (lw-euler-neighborhood-radius rate height outer-radius anchor-error))
  (rationalp error) (< 0 error) (<= error anchor-error))
 (lw-complex-diskp (lw-complex-sub (lw-complex-euler-continuation-value (+ rate (car point)) (+ height (cdr point)) error) (lw-complex-euler-continuation-value rate height anchor-error)) (* 1/4 (lw-euler-value-clearance-size rate height anchor-error))))
 :hints (("Goal"
 :use (lw-euler-neighborhood-data lw-enn-point-data lw-enn-coarse-anchor
       (:instance lw-euler-uniform-polynomial-valid (radius outer-radius) (target 0) (error anchor-error))
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-uniform-polynomial rate height outer-radius 0 anchor-error)) (offset 0))
       (:instance lw-complex-euler-continuation-value-rational (rate (+ rate (car point))) (height (+ height (cdr point))))
       (:instance lw-complex-euler-uniform-polynomial-comparison
        (radius outer-radius) (target 0) (error anchor-error) (value-error error))
       (:instance lw-complex-difference-symmetric (left (lw-complex-polynomial (lw-euler-uniform-polynomial rate height outer-radius 0 anchor-error) point 0)) (right (lw-complex-euler-continuation-value (+ rate (car point)) (+ height (cdr point)) error))
        (radius (+ anchor-error (* 1/4 error))))
       (:instance lw-complex-difference-triangle (left (lw-complex-euler-continuation-value (+ rate (car point)) (+ height (cdr point)) error)) (middle (lw-complex-polynomial (lw-euler-uniform-polynomial rate height outer-radius 0 anchor-error) point 0)) (right (lw-complex-euler-continuation-value rate height anchor-error))
        (radius (+ anchor-error (* 1/4 error))) (other-radius (* 1/8 (lw-euler-value-clearance-size rate height anchor-error))))
       (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-euler-continuation-value (+ rate (car point)) (+ height (cdr point)) error) (lw-complex-euler-continuation-value rate height anchor-error)))
        (radius (+ anchor-error (* 1/4 error) (* 1/8 (lw-euler-value-clearance-size rate height anchor-error)))) (cap (* 1/4 (lw-euler-value-clearance-size rate height anchor-error)))))
 :in-theory (union-theories
 '( lw-enn-left-commutes lw-enn-left-distributes lw-enn-fold-constants lw-enn-times-negative lw-enn-negative-times lw-enn-zero-times lw-enn-minus-one lw-enn-double-negative lw-enn-add-cancel lw-enn-double lw-enn-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t)))

(local (defthm lw-enn-disk-l1
 (implies (lw-complex-diskp point radius)
  (<= (lw-complex-l1 point) (* 2 radius)))
 :hints (("Goal" :use (lw-complex-disk-coordinates)
  :in-theory (union-theories
 '(lw-complex-l1 lw-enn-left-commutes lw-enn-left-distributes lw-enn-fold-constants lw-enn-times-negative lw-enn-negative-times lw-enn-zero-times lw-enn-minus-one lw-enn-double-negative lw-enn-add-cancel lw-enn-double lw-enn-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-enn-pair-reconstruction
 (implies (lw-complexp point) (equal (cons (car point) (cdr point)) point))
 :hints (("Goal" :in-theory (enable lw-complexp)))))

(local (defthm lw-enn-shift-identity
 (implies (and (lw-complexp point) (lw-complexp anchor))
  (equal (lw-complex-add anchor (lw-complex-sub point anchor)) point))
 :hints (("Goal"
  :in-theory (union-theories
 '(lw-complexp lw-complex-add lw-complex-sub lw-enn-pair-reconstruction lw-enn-left-commutes lw-enn-left-distributes lw-enn-fold-constants lw-enn-times-negative lw-enn-negative-times lw-enn-zero-times lw-enn-minus-one lw-enn-double-negative lw-enn-add-cancel lw-enn-double lw-enn-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(defthm lw-complex-disk-anchor-clearance
 (implies (and (lw-complexp anchor) (not (equal anchor (cons 0 0)))
  (lw-complexp point)
  (lw-complex-diskp (lw-complex-sub point anchor) (* 1/4 (lw-complex-l1 anchor))))
 (and (not (equal point (cons 0 0)))
      (<= (* 1/16 (lw-complex-l1 anchor) (lw-complex-l1 anchor)) (lw-complex-norm-square point))
      (lw-complex-diskp (lw-complex-reciprocal point) (/ (* 1/4 (lw-complex-l1 anchor))))
      (rationalp (lw-complex-l1 point))
      (<= (* 1/2 (lw-complex-l1 anchor)) (lw-complex-l1 point))))
 :hints (("Goal"
 :use ((:instance lw-complex-l1-clearance (point anchor))
       (:instance lw-complex-operations-rational (left point) (right anchor) (factor 1))
       (:instance lw-enn-disk-l1 (point (lw-complex-sub point anchor)) (radius (* 1/4 (lw-complex-l1 anchor))))
       (:instance lw-complex-small-shift-clearance (offset (lw-complex-sub point anchor)))
       (:instance lw-complex-l1-add-lower (offset (lw-complex-sub point anchor)))
       (:instance lw-complex-l1-bound))
 :in-theory (union-theories
 '(lw-enn-shift-identity lw-enn-left-commutes lw-enn-left-distributes lw-enn-fold-constants lw-enn-times-negative lw-enn-negative-times lw-enn-zero-times lw-enn-minus-one lw-enn-double-negative lw-enn-add-cancel lw-enn-double lw-enn-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-euler-neighborhood-value-clearance
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (lw-complex-diskp point (lw-euler-neighborhood-radius rate height outer-radius anchor-error))
  (rationalp error) (< 0 error) (<= error anchor-error))
 (and (lw-complexp (lw-complex-euler-continuation-value (+ rate (car point)) (+ height (cdr point)) error)) (not (equal (lw-complex-euler-continuation-value (+ rate (car point)) (+ height (cdr point)) error) (cons 0 0)))
      (<= (* 1/16 (lw-euler-value-clearance-size rate height anchor-error) (lw-euler-value-clearance-size rate height anchor-error)) (lw-complex-norm-square (lw-complex-euler-continuation-value (+ rate (car point)) (+ height (cdr point)) error)))
      (lw-complex-diskp (lw-complex-reciprocal (lw-complex-euler-continuation-value (+ rate (car point)) (+ height (cdr point)) error)) (/ (* 1/4 (lw-euler-value-clearance-size rate height anchor-error))))
      (rationalp (lw-complex-l1 (lw-complex-euler-continuation-value (+ rate (car point)) (+ height (cdr point)) error)))
      (<= (* 1/2 (lw-euler-value-clearance-size rate height anchor-error)) (lw-complex-l1 (lw-complex-euler-continuation-value (+ rate (car point)) (+ height (cdr point)) error)))))
 :hints (("Goal"
 :use (lw-euler-neighborhood-data lw-enn-point-data
       lw-complex-euler-neighborhood-value-anchor
       (:instance lw-complex-euler-continuation-value-rational (rate (+ rate (car point))) (height (+ height (cdr point))))
       (:instance lw-complex-disk-anchor-clearance (anchor (lw-complex-euler-continuation-value rate height anchor-error)) (point (lw-complex-euler-continuation-value (+ rate (car point)) (+ height (cdr point)) error))))
 :in-theory (union-theories
 '(lw-euler-value-clearance-size lw-enn-left-commutes lw-enn-left-distributes lw-enn-fold-constants lw-enn-times-negative lw-enn-negative-times lw-enn-zero-times lw-enn-minus-one lw-enn-double-negative lw-enn-add-cancel lw-enn-double lw-enn-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-euler-neighborhood-polynomial-clearance
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (lw-complex-diskp point (lw-euler-neighborhood-radius rate height outer-radius anchor-error))
  (natp target) (rationalp error) (< 0 error) (<= error anchor-error))
 (and (lw-complexp (lw-complex-polynomial (lw-euler-uniform-polynomial rate height outer-radius target error) point 0)) (not (equal (lw-complex-polynomial (lw-euler-uniform-polynomial rate height outer-radius target error) point 0) (cons 0 0)))
      (<= (* 1/16 (lw-euler-value-clearance-size rate height anchor-error) (lw-euler-value-clearance-size rate height anchor-error)) (lw-complex-norm-square (lw-complex-polynomial (lw-euler-uniform-polynomial rate height outer-radius target error) point 0)))
      (lw-complex-diskp (lw-complex-reciprocal (lw-complex-polynomial (lw-euler-uniform-polynomial rate height outer-radius target error) point 0)) (/ (* 1/4 (lw-euler-value-clearance-size rate height anchor-error))))))
 :hints (("Goal"
 :use (lw-euler-neighborhood-data lw-enn-point-data
       lw-complex-euler-neighborhood-polynomial-anchor
       (:instance lw-euler-uniform-polynomial-valid (radius outer-radius))
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-uniform-polynomial rate height outer-radius target error)) (offset 0))
       (:instance lw-complex-disk-anchor-clearance (anchor (lw-complex-euler-continuation-value rate height anchor-error)) (point (lw-complex-polynomial (lw-euler-uniform-polynomial rate height outer-radius target error) point 0))))
 :in-theory (union-theories
 '(lw-euler-value-clearance-size lw-enn-left-commutes lw-enn-left-distributes lw-enn-fold-constants lw-enn-times-negative lw-enn-negative-times lw-enn-zero-times lw-enn-minus-one lw-enn-double-negative lw-enn-add-cancel lw-enn-double lw-enn-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t)))

(defthm lw-euler-neighborhood-shifted-check
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (lw-complex-diskp point (lw-euler-neighborhood-radius rate height outer-radius anchor-error)))
 (and (lw-euler-value-clearance-check (+ rate (car point)) (+ height (cdr point)) (* 1/2 anchor-error))
      (<= (* 1/8 (lw-euler-value-clearance-size rate height anchor-error)) (lw-euler-value-clearance-lower (+ rate (car point)) (+ height (cdr point)) (* 1/2 anchor-error)))))
 :hints (("Goal"
 :use (lw-euler-neighborhood-data lw-enn-point-data
       (:instance lw-complex-euler-neighborhood-value-clearance (error (* 1/2 anchor-error))))
 :in-theory (union-theories
 '(lw-euler-value-clearance-check lw-euler-value-clearance-size lw-euler-value-clearance-lower lw-enn-left-commutes lw-enn-left-distributes lw-enn-fold-constants lw-enn-times-negative lw-enn-negative-times lw-enn-zero-times lw-enn-minus-one lw-enn-double-negative lw-enn-add-cancel lw-enn-double lw-enn-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t)))


