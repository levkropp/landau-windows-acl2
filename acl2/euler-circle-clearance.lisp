; A finite covered circle supplies uniform denominator clearance.
(in-package "ACL2")
(include-book "euler-circle-models")
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
(local (in-theory (disable lw-euler-value-clearance-check
 lw-euler-local-normalized-radius lw-euler-local-normalized-cap lw-euler-local-normalized-anchor
 lw-complex-segment)))
(local (defthm lw-egc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-egc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-egc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-egc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-egc-times-negative (a b) (b a)))
                 :in-theory (disable lw-egc-times-negative)))))

(local (defthm lw-egc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-egc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-egc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-egc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-egc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-egc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-egc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-egc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-egc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-egc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-egc-left-commutes)))))
(defun lw-euler-circle-chart-anchor-min (arcs)
 (declare (xargs :measure (acl2-count arcs) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (endp arcs) 1
 (min (lw-euler-contour-anchor (lw-euler-circle-arc-patch (car arcs)))
      (lw-euler-circle-chart-anchor-min (cdr arcs)))))
(defun lw-euler-circle-anchor-min (plus-arcs minus-arcs)
 (min (lw-euler-circle-chart-anchor-min plus-arcs) (lw-euler-circle-chart-anchor-min minus-arcs)))
(defun lw-euler-circle-point-lower (center radius plus-arcs minus-arcs point)
 (lw-euler-value-clearance-lower (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) (lw-euler-contour-anchor (lw-euler-circle-cover-patch point plus-arcs minus-arcs))))
(defun lw-euler-circle-outer-radius (center radius) (* 1/2 (+ (car center) radius)))
(defun lw-euler-circle-outer-gap (center radius) (* 1/2 (- (lw-euler-circle-outer-radius center radius) radius)))
(local (in-theory (disable lw-euler-circle-chart-anchor-min lw-euler-circle-anchor-min lw-euler-circle-point-lower lw-euler-circle-outer-radius lw-euler-circle-outer-gap
 lw-euler-circle-coverp lw-euler-circle-chart-coverp lw-euler-circle-cover-arcs lw-euler-circle-cover-index lw-euler-circle-cover-arc lw-euler-circle-cover-patch
 lw-euler-contour-patchp lw-euler-contour-cap lw-euler-contour-anchor lw-euler-circle-arcp lw-euler-circle-arc-patch lw-euler-circle-arc-right
 lw-euler-value-clearance-lower lw-euler-value-clearance-size)))

(defthm lw-euler-circle-chart-anchor-min-data
 (implies (lw-euler-circle-chart-coverp center radius sign arcs left)
 (and (rationalp (lw-euler-circle-chart-anchor-min arcs)) (< 0 (lw-euler-circle-chart-anchor-min arcs))
      (<= (lw-euler-circle-chart-anchor-min arcs) 1)))
 :hints (("Goal" :induct (lw-euler-circle-chart-coverp center radius sign arcs left)
 :in-theory (union-theories
 '(lw-euler-circle-chart-coverp lw-euler-circle-chart-anchor-min min endp lw-egc-left-commutes lw-egc-left-distributes lw-egc-fold-constants lw-egc-times-negative lw-egc-negative-times lw-egc-zero-times lw-egc-minus-one lw-egc-double-negative lw-egc-add-cancel lw-egc-double lw-egc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
 (and stable-under-simplificationp
 '(:use ((:instance lw-euler-circle-arc-data (arc (car arcs)))
         (:instance lw-euler-contour-patch-data (patch (lw-euler-circle-arc-patch (car arcs)))))
 :do-not-induct t)))
 :rule-classes nil)

(local (defun lw-egc-nth-induct (arcs left index)
 (declare (xargs :measure (acl2-count arcs) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (or (endp arcs) (zp index)) (list arcs left index)
 (lw-egc-nth-induct (cdr arcs) (lw-euler-circle-arc-right (car arcs)) (- index 1)))))

(defthm lw-euler-circle-chart-anchor-min-nth
 (implies (and (lw-euler-circle-chart-coverp center radius sign arcs left) (natp index) (< index (len arcs)))
 (<= (lw-euler-circle-chart-anchor-min arcs) (lw-euler-contour-anchor (lw-euler-circle-arc-patch (nth index arcs)))))
 :hints (("Goal" :induct (lw-egc-nth-induct arcs left index)
 :in-theory (union-theories
 '((:induction lw-egc-nth-induct) lw-euler-circle-chart-coverp lw-euler-circle-chart-anchor-min min nth len endp lw-egc-left-commutes lw-egc-left-distributes lw-egc-fold-constants lw-egc-times-negative lw-egc-negative-times lw-egc-zero-times lw-egc-minus-one lw-egc-double-negative lw-egc-add-cancel lw-egc-double lw-egc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-euler-circle-anchor-min-data
 (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
 (lw-complexp point) (equal (lw-complex-norm-square point) 1))
 (and (rationalp (lw-euler-circle-anchor-min plus-arcs minus-arcs)) (< 0 (lw-euler-circle-anchor-min plus-arcs minus-arcs)) (<= (lw-euler-circle-anchor-min plus-arcs minus-arcs) 1)
      (rationalp (lw-euler-contour-anchor (lw-euler-circle-cover-patch point plus-arcs minus-arcs))) (< 0 (lw-euler-contour-anchor (lw-euler-circle-cover-patch point plus-arcs minus-arcs))) (<= (lw-euler-circle-anchor-min plus-arcs minus-arcs) (lw-euler-contour-anchor (lw-euler-circle-cover-patch point plus-arcs minus-arcs)))))
 :hints (("Goal"
 :cases ((equal (lw-unit-circle-sign point) 1))
 :use (lw-euler-circle-cover-selection lw-euler-circle-cover-selected-cap
       (:instance lw-euler-contour-patch-data (patch (lw-euler-circle-cover-patch point plus-arcs minus-arcs)))
       (:instance lw-euler-circle-chart-anchor-min-data (arcs plus-arcs) (sign 1) (left -2))
       (:instance lw-euler-circle-chart-anchor-min-data (arcs minus-arcs) (sign -1) (left -2))
       (:instance lw-euler-circle-chart-anchor-min-nth (arcs plus-arcs) (sign 1) (left -2) (index (lw-euler-circle-cover-index point plus-arcs minus-arcs)))
       (:instance lw-euler-circle-chart-anchor-min-nth (arcs minus-arcs) (sign -1) (left -2) (index (lw-euler-circle-cover-index point plus-arcs minus-arcs))))
 :in-theory (union-theories
 '(lw-euler-circle-coverp lw-euler-circle-anchor-min lw-euler-circle-cover-patch lw-euler-circle-cover-arc lw-euler-circle-cover-arcs min lw-egc-left-commutes lw-egc-left-distributes lw-egc-fold-constants lw-egc-times-negative lw-egc-negative-times lw-egc-zero-times lw-egc-minus-one lw-egc-double-negative lw-egc-add-cancel lw-egc-double lw-egc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t))
 :rule-classes nil)

(defthm lw-euler-circle-center-clearance
 (implies (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
 (and (lw-complexp center) (rationalp radius) (< 0 radius) (rationalp (car center)) (< radius (car center))))
 :hints (("Goal"
 :use (lw-euler-circle-cover-data
       (:instance lw-euler-circle-cover-shifted-check (point (cons -1 0))))
 :in-theory (union-theories
 '((:executable-counterpart lw-complexp) (:executable-counterpart lw-complex-norm-square) lw-complexp lw-complex-add lw-complex-scale lw-egc-left-commutes lw-egc-left-distributes lw-egc-fold-constants lw-egc-times-negative lw-egc-negative-times lw-egc-zero-times lw-egc-minus-one lw-egc-double-negative lw-egc-add-cancel lw-egc-double lw-egc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t))
 :rule-classes nil)

(defthm lw-euler-circle-outer-data
 (implies (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
 (and (lw-complexp center) (rationalp (car center)) (rationalp (cdr center))
      (rationalp radius) (< 0 radius)
      (rationalp (lw-euler-circle-outer-radius center radius)) (< radius (lw-euler-circle-outer-radius center radius)) (< (lw-euler-circle-outer-radius center radius) (car center))
      (rationalp (lw-euler-circle-outer-gap center radius)) (< 0 (lw-euler-circle-outer-gap center radius))))
 :hints (("Goal" :use (lw-euler-circle-center-clearance)
 :in-theory (union-theories
 '(lw-complexp lw-euler-circle-outer-radius lw-euler-circle-outer-gap lw-egc-left-commutes lw-egc-left-distributes lw-egc-fold-constants lw-egc-times-negative lw-egc-negative-times lw-egc-zero-times lw-egc-minus-one lw-egc-double-negative lw-egc-add-cancel lw-egc-double lw-egc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))
 :rule-classes nil)

(defthm lw-euler-circle-point-lower-data
 (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
 (lw-complexp point) (equal (lw-complex-norm-square point) 1))
 (and (lw-euler-value-clearance-check (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) (lw-euler-contour-anchor (lw-euler-circle-cover-patch point plus-arcs minus-arcs)))
      (rationalp (lw-euler-circle-point-lower center radius plus-arcs minus-arcs point)) (< 0 (lw-euler-circle-point-lower center radius plus-arcs minus-arcs point)) (<= (* 4 (lw-euler-circle-anchor-min plus-arcs minus-arcs)) (lw-euler-circle-point-lower center radius plus-arcs minus-arcs point))
      (<= (lw-euler-contour-anchor (lw-euler-circle-cover-patch point plus-arcs minus-arcs)) (* 1/4 (lw-euler-circle-point-lower center radius plus-arcs minus-arcs point)))))
 :hints (("Goal"
 :use (lw-euler-circle-cover-shifted-check lw-euler-circle-anchor-min-data
       (:instance lw-euler-value-clearance-data (rate (car (lw-complex-add center (lw-complex-scale radius point)))) (height (cdr (lw-complex-add center (lw-complex-scale radius point)))) (anchor-error (lw-euler-contour-anchor (lw-euler-circle-cover-patch point plus-arcs minus-arcs)))))
 :in-theory (union-theories
 '(lw-euler-circle-point-lower lw-egc-left-commutes lw-egc-left-distributes lw-egc-fold-constants lw-egc-times-negative lw-egc-negative-times lw-egc-zero-times lw-egc-minus-one lw-egc-double-negative lw-egc-add-cancel lw-egc-double lw-egc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes nil)

(local (defthm lw-egc-square-order
 (implies (and (rationalp left) (rationalp right) (<= 0 left) (<= left right))
 (<= (* left left) (* right right)))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defthm lw-euler-circle-native-value-clearance
 (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
 (lw-complexp point) (equal (lw-complex-norm-square point) 1) (rationalp request) (< 0 request) (<= request (* 1/4 (lw-euler-circle-point-lower center radius plus-arcs minus-arcs point))))
 (and (lw-complexp (lw-complex-euler-continuation-value (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) request)) (not (equal (lw-complex-euler-continuation-value (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) request) (cons 0 0)))
      (<= (* (lw-euler-circle-anchor-min plus-arcs minus-arcs) (lw-euler-circle-anchor-min plus-arcs minus-arcs)) (lw-complex-norm-square (lw-complex-euler-continuation-value (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) request)))
      (lw-complex-diskp (lw-complex-reciprocal (lw-complex-euler-continuation-value (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) request)) (/ (lw-euler-circle-anchor-min plus-arcs minus-arcs)))))
 :hints (("Goal"
 :use (lw-euler-circle-anchor-min-data lw-euler-circle-point-lower-data
       (:instance lw-complex-euler-value-clearance (rate (car (lw-complex-add center (lw-complex-scale radius point)))) (height (cdr (lw-complex-add center (lw-complex-scale radius point)))) (anchor-error (lw-euler-contour-anchor (lw-euler-circle-cover-patch point plus-arcs minus-arcs))))
       (:instance lw-egc-square-order (left (lw-euler-circle-anchor-min plus-arcs minus-arcs)) (right (lw-euler-circle-point-lower center radius plus-arcs minus-arcs point)))
       (:instance lw-complex-reciprocal-disk-bound (point (lw-complex-euler-continuation-value (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) request)) (lower (lw-euler-circle-anchor-min plus-arcs minus-arcs))))
 :in-theory (union-theories
 '(lw-euler-circle-point-lower lw-egc-left-commutes lw-egc-left-distributes lw-egc-fold-constants lw-egc-times-negative lw-egc-negative-times lw-egc-zero-times lw-egc-minus-one lw-egc-double-negative lw-egc-add-cancel lw-egc-double lw-egc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes nil)

