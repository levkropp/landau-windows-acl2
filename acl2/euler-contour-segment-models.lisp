; Actual polynomial models along every point of a covered segment.
(in-package "ACL2")
(include-book "euler-contour-patches")
(include-book "polynomial-affine")
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
(local (in-theory (disable lw-euler-contour-patchp lw-euler-contour-pointp lw-euler-contour-segmentp
 lw-euler-contour-center lw-euler-contour-radius lw-euler-contour-cap lw-euler-contour-anchor
 lw-euler-local-normalized-polynomial lw-polynomial-affine lw-complex-polynomial
 lw-mellin-euler-log-extended-value lw-complex-segment)))
(local (defthm lw-ecs-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ecs-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ecs-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ecs-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ecs-times-negative (a b) (b a)))
                 :in-theory (disable lw-ecs-times-negative)))))

(local (defthm lw-ecs-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ecs-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ecs-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ecs-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ecs-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ecs-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ecs-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ecs-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecs-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecs-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ecs-left-commutes)))))
(local (defthm lw-ecs-centered-affine
 (implies (and (lw-complexp left) (lw-complexp right) (lw-complexp center) (rationalp parameter))
 (equal (lw-complex-add (lw-complex-sub left center) (lw-complex-mul (lw-complex-sub right left) (cons parameter 0)))
        (lw-complex-sub (lw-complex-segment left right parameter) center)))
 :hints (("Goal"
 :use (lw-complex-segment-affine)
 :in-theory (union-theories
 '(lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-ecs-left-commutes lw-ecs-left-distributes lw-ecs-fold-constants lw-ecs-times-negative lw-ecs-negative-times lw-ecs-zero-times lw-ecs-minus-one lw-ecs-double-negative lw-ecs-add-cancel lw-ecs-double lw-ecs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))))
(defun lw-euler-contour-polynomial (patch left right target error)
 (lw-polynomial-affine (lw-euler-local-normalized-polynomial (nth 0 patch) (nth 1 patch) (nth 2 patch) (nth 3 patch) target error) (lw-complex-sub left (lw-euler-contour-center patch)) (lw-complex-sub right left)))
(local (in-theory (disable lw-euler-contour-polynomial)))
(defthm lw-euler-contour-polynomial-valid
 (implies (and (lw-euler-contour-patchp patch) (lw-complexp left) (lw-complexp right) (natp target) (rationalp error) (< 0 error))
 (lw-complex-coefficientsp (lw-euler-contour-polynomial patch left right target error)))
 :hints (("Goal"
 :use (lw-euler-contour-patch-data
       (:instance lw-complex-operations-rational (left left) (right (lw-euler-contour-center patch)) (factor 1))
       (:instance lw-complex-operations-rational (left right) (right left) (factor 1))
       (:instance lw-euler-local-normalized-polynomial-valid (rate (nth 0 patch)) (height (nth 1 patch)) (outer-radius (nth 2 patch)) (anchor-error (nth 3 patch)))
       (:instance lw-polynomial-affine-valid (coefficients (lw-euler-local-normalized-polynomial (nth 0 patch) (nth 1 patch) (nth 2 patch) (nth 3 patch) target error)) (center (lw-complex-sub left (lw-euler-contour-center patch))) (slope (lw-complex-sub right left))))
 :in-theory (union-theories
 '(lw-euler-contour-patchp lw-euler-contour-polynomial lw-ecs-left-commutes lw-ecs-left-distributes lw-ecs-fold-constants lw-ecs-times-negative lw-ecs-negative-times lw-ecs-zero-times lw-ecs-minus-one lw-ecs-double-negative lw-ecs-add-cancel lw-ecs-double lw-ecs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
(defthm lw-euler-contour-polynomial-evaluation
 (implies (and (lw-euler-contour-patchp patch) (lw-complexp left) (lw-complexp right) (rationalp parameter) (natp target) (rationalp error) (< 0 error))
 (equal (lw-complex-polynomial (lw-euler-contour-polynomial patch left right target error) (cons parameter 0) 0) (lw-complex-polynomial (lw-euler-local-normalized-polynomial (nth 0 patch) (nth 1 patch) (nth 2 patch) (nth 3 patch) target error) (lw-complex-sub (lw-complex-segment left right parameter) (lw-euler-contour-center patch)) 0)))
 :hints (("Goal"
 :use (lw-euler-contour-patch-data
       (:instance lw-complex-operations-rational (left left) (right (lw-euler-contour-center patch)) (factor 1))
       (:instance lw-complex-operations-rational (left right) (right left) (factor 1))
       (:instance lw-euler-local-normalized-polynomial-valid (rate (nth 0 patch)) (height (nth 1 patch)) (outer-radius (nth 2 patch)) (anchor-error (nth 3 patch)))
       (:instance lw-ecs-centered-affine (center (lw-euler-contour-center patch)))
       (:instance lw-polynomial-affine-evaluation (coefficients (lw-euler-local-normalized-polynomial (nth 0 patch) (nth 1 patch) (nth 2 patch) (nth 3 patch) target error)) (center (lw-complex-sub left (lw-euler-contour-center patch))) (slope (lw-complex-sub right left)) (point (cons parameter 0))))
 :in-theory (union-theories
 '(lw-euler-contour-patchp lw-euler-contour-polynomial lw-complexp lw-ecs-left-commutes lw-ecs-left-distributes lw-ecs-fold-constants lw-ecs-times-negative lw-ecs-negative-times lw-ecs-zero-times lw-ecs-minus-one lw-ecs-double-negative lw-ecs-add-cancel lw-ecs-double lw-ecs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
(defthm lw-complex-euler-contour-polynomial-cap
 (implies (and (lw-euler-contour-segmentp patch left right) (rationalp parameter) (<= 0 parameter) (<= parameter 1) (natp target) (rationalp error) (< 0 error))
 (lw-complex-diskp (lw-complex-polynomial (lw-euler-contour-polynomial patch left right target error) (cons parameter 0) 0) (lw-euler-contour-cap patch)))
 :hints (("Goal"
 :use (lw-euler-contour-patch-data lw-euler-contour-segment-coverage lw-euler-contour-polynomial-evaluation
       (:instance lw-complex-euler-local-normalized-polynomial-cap (rate (nth 0 patch)) (height (nth 1 patch)) (outer-radius (nth 2 patch)) (anchor-error (nth 3 patch)) (point (lw-complex-sub (lw-complex-segment left right parameter) (lw-euler-contour-center patch)))))
 :in-theory (union-theories
 '(lw-euler-contour-patchp lw-euler-contour-segmentp lw-euler-contour-pointp lw-euler-contour-radius lw-euler-contour-cap lw-ecs-left-commutes lw-ecs-left-distributes lw-ecs-fold-constants lw-ecs-times-negative lw-ecs-negative-times lw-ecs-zero-times lw-ecs-minus-one lw-ecs-double-negative lw-ecs-add-cancel lw-ecs-double lw-ecs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
(defthm lw-complex-euler-contour-polynomial-comparison
 (implies (and (lw-euler-contour-segmentp patch left right) (rationalp parameter) (<= 0 parameter) (<= parameter 1) (natp target) (rationalp error) (< 0 error)
 (lw-euler-value-clearance-check (car (lw-complex-segment left right parameter)) (cdr (lw-complex-segment left right parameter)) local-anchor)
 (rationalp coefficient-radius) (< 0 coefficient-radius) (< coefficient-radius (car (lw-complex-segment left right parameter)))
 (rationalp value-error) (< 0 value-error))
 (lw-complex-diskp (lw-complex-sub (lw-complex-polynomial (lw-euler-contour-polynomial patch left right target error) (cons parameter 0) 0) (lw-mellin-euler-log-extended-value (car (lw-complex-segment left right parameter)) (cdr (lw-complex-segment left right parameter)) coefficient-radius local-anchor value-error)) (* 1/2 (+ error value-error))))
 :hints (("Goal"
 :use (lw-euler-contour-patch-data lw-euler-contour-segment-coverage lw-euler-contour-polynomial-evaluation
       (:instance lw-euler-contour-point-data (point (lw-complex-segment left right parameter)))
       (:instance lw-complex-euler-local-normalized-comparison (rate (nth 0 patch)) (height (nth 1 patch)) (outer-radius (nth 2 patch)) (anchor-error (nth 3 patch)) (point (lw-complex-sub (lw-complex-segment left right parameter) (lw-euler-contour-center patch)))))
 :in-theory (union-theories
 '(lw-euler-contour-pointp lw-euler-contour-patchp lw-euler-contour-segmentp lw-euler-contour-center lw-euler-contour-radius lw-complexp lw-complex-sub lw-ecs-left-commutes lw-ecs-left-distributes lw-ecs-fold-constants lw-ecs-times-negative lw-ecs-negative-times lw-ecs-zero-times lw-ecs-minus-one lw-ecs-double-negative lw-ecs-add-cancel lw-ecs-double lw-ecs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))


(defthm lw-euler-contour-polynomial-rational
 (implies (and (lw-euler-contour-patchp patch) (lw-complexp left) (lw-complexp right) (rationalp parameter) (natp target) (rationalp error) (< 0 error))
 (lw-complexp (lw-complex-polynomial (lw-euler-contour-polynomial patch left right target error) (cons parameter 0) 0)))
 :hints (("Goal"
 :use (lw-euler-contour-polynomial-valid
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-contour-polynomial patch left right target error)) (point (cons parameter 0)) (offset 0)))
 :in-theory (union-theories
 '(lw-complexp lw-ecs-left-commutes lw-ecs-left-distributes lw-ecs-fold-constants lw-ecs-times-negative lw-ecs-negative-times lw-ecs-zero-times lw-ecs-minus-one lw-ecs-double-negative lw-ecs-add-cancel lw-ecs-double lw-ecs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
(defthm lw-complex-euler-contour-polynomial-cauchy
 (implies (and (lw-euler-contour-segmentp patch left right) (rationalp parameter) (<= 0 parameter) (<= parameter 1) (natp left-target) (natp right-target)
 (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
 (lw-complex-diskp (lw-complex-sub (lw-complex-polynomial (lw-euler-contour-polynomial patch left right left-target left-error) (cons parameter 0) 0) (lw-complex-polynomial (lw-euler-contour-polynomial patch left right right-target right-error) (cons parameter 0) 0)) (* 1/2 (+ left-error right-error))))
 :hints (("Goal"
 :use (lw-euler-contour-patch-data lw-euler-contour-segment-coverage
       (:instance lw-euler-contour-polynomial-evaluation (target left-target) (error left-error))
       (:instance lw-euler-contour-polynomial-evaluation (target right-target) (error right-error))
       (:instance lw-complex-euler-local-normalized-polynomial-cauchy (rate (nth 0 patch)) (height (nth 1 patch)) (outer-radius (nth 2 patch)) (anchor-error (nth 3 patch)) (point (lw-complex-sub (lw-complex-segment left right parameter) (lw-euler-contour-center patch)))))
 :in-theory (union-theories
 '(lw-euler-contour-patchp lw-euler-contour-segmentp lw-euler-contour-pointp lw-euler-contour-radius lw-ecs-left-commutes lw-ecs-left-distributes lw-ecs-fold-constants lw-ecs-times-negative lw-ecs-negative-times lw-ecs-zero-times lw-ecs-minus-one lw-ecs-double-negative lw-ecs-add-cancel lw-ecs-double lw-ecs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
(defthm lw-mellin-euler-log-extended-segment-cap
 (implies (and (lw-euler-contour-segmentp patch left right) (rationalp parameter) (<= 0 parameter) (<= parameter 1)
 (lw-euler-value-clearance-check (car (lw-complex-segment left right parameter)) (cdr (lw-complex-segment left right parameter)) local-anchor)
 (rationalp coefficient-radius) (< 0 coefficient-radius) (< coefficient-radius (car (lw-complex-segment left right parameter)))
 (rationalp value-error) (< 0 value-error) (<= value-error 1))
 (lw-complex-diskp (lw-mellin-euler-log-extended-value (car (lw-complex-segment left right parameter)) (cdr (lw-complex-segment left right parameter)) coefficient-radius local-anchor value-error) (+ 1 (lw-euler-contour-cap patch))))
 :hints (("Goal"
 :use (lw-euler-contour-patch-data lw-euler-contour-segment-coverage
       (:instance lw-euler-contour-point-data (point (lw-complex-segment left right parameter)))
       (:instance lw-mellin-euler-log-extended-neighborhood-cap (rate (nth 0 patch)) (height (nth 1 patch)) (outer-radius (nth 2 patch)) (anchor-error (nth 3 patch)) (point (lw-complex-sub (lw-complex-segment left right parameter) (lw-euler-contour-center patch)))))
 :in-theory (union-theories
 '(lw-euler-contour-patchp lw-euler-contour-segmentp lw-euler-contour-pointp lw-euler-contour-center lw-euler-contour-radius lw-euler-contour-cap lw-complexp lw-complex-sub lw-ecs-left-commutes lw-ecs-left-distributes lw-ecs-fold-constants lw-ecs-times-negative lw-ecs-negative-times lw-ecs-zero-times lw-ecs-minus-one lw-ecs-double-negative lw-ecs-add-cancel lw-ecs-double lw-ecs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

