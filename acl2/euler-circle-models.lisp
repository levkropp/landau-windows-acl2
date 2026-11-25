; Construct spatial polynomial and native value models on a covered circle.
(in-package "ACL2")
(include-book "euler-circle-cover")
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
(local (defthm lw-ecm2-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ecm2-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ecm2-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ecm2-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ecm2-times-negative (a b) (b a)))
                 :in-theory (disable lw-ecm2-times-negative)))))

(local (defthm lw-ecm2-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ecm2-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ecm2-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ecm2-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ecm2-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ecm2-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ecm2-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ecm2-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecm2-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecm2-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ecm2-left-commutes)))))
(defun lw-euler-circle-polynomial (plus-arcs minus-arcs point target error)
 (let ((patch (lw-euler-circle-cover-patch point plus-arcs minus-arcs)))
 (lw-euler-local-normalized-polynomial (nth 0 patch) (nth 1 patch) (nth 2 patch) (nth 3 patch) target error)))
(defun lw-euler-circle-polynomial-value (center radius plus-arcs minus-arcs point target error)
 (lw-complex-polynomial (lw-euler-circle-polynomial plus-arcs minus-arcs point target error) (lw-complex-sub (lw-complex-add center (lw-complex-scale radius point)) (lw-euler-contour-center (lw-euler-circle-cover-patch point plus-arcs minus-arcs))) 0))
(defun lw-euler-circle-value (center radius plus-arcs minus-arcs point error)
 (lw-mellin-euler-log-extended-value (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point)))
 (* 1/2 (car (lw-complex-add center (lw-complex-scale radius point)))) (lw-euler-contour-anchor (lw-euler-circle-cover-patch point plus-arcs minus-arcs)) error))
(local (in-theory (disable lw-euler-circle-polynomial lw-euler-circle-polynomial-value lw-euler-circle-value lw-euler-circle-coverp lw-euler-circle-cover-patch lw-euler-circle-cover-cap
 lw-euler-contour-patchp lw-euler-contour-pointp lw-euler-contour-center lw-euler-contour-radius lw-euler-contour-cap lw-euler-contour-anchor)))

(defthm lw-euler-circle-polynomial-valid
 (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
 (lw-complexp point) (equal (lw-complex-norm-square point) 1) (natp target) (rationalp error) (< 0 error))
 (lw-complex-coefficientsp (lw-euler-circle-polynomial plus-arcs minus-arcs point target error)))
 :hints (("Goal"
 :use (lw-euler-circle-cover-selected-cap (:instance lw-euler-local-normalized-polynomial-valid (rate (nth 0 (lw-euler-circle-cover-patch point plus-arcs minus-arcs))) (height (nth 1 (lw-euler-circle-cover-patch point plus-arcs minus-arcs))) (outer-radius (nth 2 (lw-euler-circle-cover-patch point plus-arcs minus-arcs))) (anchor-error (nth 3 (lw-euler-circle-cover-patch point plus-arcs minus-arcs))) ))
 :in-theory (union-theories
 '(lw-euler-circle-polynomial lw-euler-contour-patchp lw-ecm2-left-commutes lw-ecm2-left-distributes lw-ecm2-fold-constants lw-ecm2-times-negative lw-ecm2-negative-times lw-ecm2-zero-times lw-ecm2-minus-one lw-ecm2-double-negative lw-ecm2-add-cancel lw-ecm2-double lw-ecm2-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-circle-polynomial-value-rational
 (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
 (lw-complexp point) (equal (lw-complex-norm-square point) 1) (natp target) (rationalp error) (< 0 error))
 (lw-complexp (lw-euler-circle-polynomial-value center radius plus-arcs minus-arcs point target error)))
 :hints (("Goal"
 :use (lw-euler-circle-cover-coverage lw-euler-circle-polynomial-valid
       (:instance lw-complex-disk-data (point (lw-complex-sub (lw-complex-add center (lw-complex-scale radius point)) (lw-euler-contour-center (lw-euler-circle-cover-patch point plus-arcs minus-arcs)))) (radius (lw-euler-contour-radius (lw-euler-circle-cover-patch point plus-arcs minus-arcs))))
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-circle-polynomial plus-arcs minus-arcs point target error)) (point (lw-complex-sub (lw-complex-add center (lw-complex-scale radius point)) (lw-euler-contour-center (lw-euler-circle-cover-patch point plus-arcs minus-arcs)))) (offset 0)))
 :in-theory (union-theories
 '(lw-euler-circle-polynomial-value lw-euler-contour-pointp lw-ecm2-left-commutes lw-ecm2-left-distributes lw-ecm2-fold-constants lw-ecm2-times-negative lw-ecm2-negative-times lw-ecm2-zero-times lw-ecm2-minus-one lw-ecm2-double-negative lw-ecm2-add-cancel lw-ecm2-double lw-ecm2-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-circle-polynomial-cap
 (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
 (lw-complexp point) (equal (lw-complex-norm-square point) 1) (natp target) (rationalp error) (< 0 error))
 (lw-complex-diskp (lw-euler-circle-polynomial-value center radius plus-arcs minus-arcs point target error) (lw-euler-circle-cover-cap plus-arcs minus-arcs)))
 :hints (("Goal"
 :use (lw-euler-circle-cover-data lw-euler-circle-cover-selected-cap
       (:instance lw-euler-contour-patch-data (patch (lw-euler-circle-cover-patch point plus-arcs minus-arcs)))
       lw-euler-circle-cover-coverage
       (:instance lw-complex-euler-local-normalized-polynomial-cap (rate (nth 0 (lw-euler-circle-cover-patch point plus-arcs minus-arcs))) (height (nth 1 (lw-euler-circle-cover-patch point plus-arcs minus-arcs))) (outer-radius (nth 2 (lw-euler-circle-cover-patch point plus-arcs minus-arcs))) (anchor-error (nth 3 (lw-euler-circle-cover-patch point plus-arcs minus-arcs))) (point (lw-complex-sub (lw-complex-add center (lw-complex-scale radius point)) (lw-euler-contour-center (lw-euler-circle-cover-patch point plus-arcs minus-arcs)))))
       (:instance lw-complex-disk-enlarge (point (lw-euler-circle-polynomial-value center radius plus-arcs minus-arcs point target error)) (radius (lw-euler-contour-cap (lw-euler-circle-cover-patch point plus-arcs minus-arcs))) (cap (lw-euler-circle-cover-cap plus-arcs minus-arcs))))
 :in-theory (union-theories
 '(lw-euler-circle-polynomial lw-euler-circle-polynomial-value lw-euler-contour-patchp lw-euler-contour-pointp lw-euler-contour-radius lw-euler-contour-cap lw-ecm2-left-commutes lw-ecm2-left-distributes lw-ecm2-fold-constants lw-ecm2-times-negative lw-ecm2-negative-times lw-ecm2-zero-times lw-ecm2-minus-one lw-ecm2-double-negative lw-ecm2-add-cancel lw-ecm2-double lw-ecm2-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-circle-general-comparison
 (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
 (lw-complexp point) (equal (lw-complex-norm-square point) 1) (natp target) (rationalp error) (< 0 error)
 (lw-euler-value-clearance-check (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) local-anchor)
 (rationalp coefficient-radius) (< 0 coefficient-radius) (< coefficient-radius (car (lw-complex-add center (lw-complex-scale radius point))))
 (rationalp value-error) (< 0 value-error))
 (lw-complex-diskp (lw-complex-sub (lw-euler-circle-polynomial-value center radius plus-arcs minus-arcs point target error)
 (lw-mellin-euler-log-extended-value (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) coefficient-radius local-anchor value-error))
 (* 1/2 (+ error value-error))))
 :hints (("Goal"
 :use (lw-euler-circle-cover-selected-cap
       (:instance lw-euler-contour-patch-data (patch (lw-euler-circle-cover-patch point plus-arcs minus-arcs)))
       lw-euler-circle-cover-coverage lw-euler-circle-cover-shifted-check
       (:instance lw-complex-euler-local-normalized-comparison (rate (nth 0 (lw-euler-circle-cover-patch point plus-arcs minus-arcs))) (height (nth 1 (lw-euler-circle-cover-patch point plus-arcs minus-arcs))) (outer-radius (nth 2 (lw-euler-circle-cover-patch point plus-arcs minus-arcs))) (anchor-error (nth 3 (lw-euler-circle-cover-patch point plus-arcs minus-arcs))) (point (lw-complex-sub (lw-complex-add center (lw-complex-scale radius point)) (lw-euler-contour-center (lw-euler-circle-cover-patch point plus-arcs minus-arcs))))))
 :in-theory (union-theories
 '(lw-euler-circle-polynomial lw-euler-circle-polynomial-value lw-euler-contour-patchp lw-euler-contour-pointp lw-euler-contour-center lw-euler-contour-radius lw-complexp lw-complex-sub lw-ecm2-left-commutes lw-ecm2-left-distributes lw-ecm2-fold-constants lw-ecm2-times-negative lw-ecm2-negative-times lw-ecm2-zero-times lw-ecm2-minus-one lw-ecm2-double-negative lw-ecm2-add-cancel lw-ecm2-double lw-ecm2-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-circle-value-rational
 (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
 (lw-complexp point) (equal (lw-complex-norm-square point) 1) (rationalp error) (< 0 error))
 (lw-complexp (lw-euler-circle-value center radius plus-arcs minus-arcs point error)))
 :hints (("Goal"
 :use (lw-euler-circle-cover-shifted-check
       (:instance lw-mellin-euler-log-extended-value-rational (rate (car (lw-complex-add center (lw-complex-scale radius point)))) (height (cdr (lw-complex-add center (lw-complex-scale radius point))))
        (radius (* 1/2 (car (lw-complex-add center (lw-complex-scale radius point))))) (anchor-error (lw-euler-contour-anchor (lw-euler-circle-cover-patch point plus-arcs minus-arcs)))))
 :in-theory (union-theories
 '(lw-euler-circle-value lw-ecm2-left-commutes lw-ecm2-left-distributes lw-ecm2-fold-constants lw-ecm2-times-negative lw-ecm2-negative-times lw-ecm2-zero-times lw-ecm2-minus-one lw-ecm2-double-negative lw-ecm2-add-cancel lw-ecm2-double lw-ecm2-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-circle-model-comparison
 (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
 (lw-complexp point) (equal (lw-complex-norm-square point) 1) (natp target) (rationalp error) (< 0 error) (rationalp value-error) (< 0 value-error))
 (lw-complex-diskp (lw-complex-sub (lw-euler-circle-polynomial-value center radius plus-arcs minus-arcs point target error) (lw-euler-circle-value center radius plus-arcs minus-arcs point value-error)) (* 1/2 (+ error value-error))))
 :hints (("Goal"
 :use (lw-euler-circle-cover-shifted-check
       (:instance lw-euler-circle-general-comparison (local-anchor (lw-euler-contour-anchor (lw-euler-circle-cover-patch point plus-arcs minus-arcs))) (coefficient-radius (* 1/2 (car (lw-complex-add center (lw-complex-scale radius point)))))))
 :in-theory (union-theories
 '(lw-euler-circle-value lw-ecm2-left-commutes lw-ecm2-left-distributes lw-ecm2-fold-constants lw-ecm2-times-negative lw-ecm2-negative-times lw-ecm2-zero-times lw-ecm2-minus-one lw-ecm2-double-negative lw-ecm2-add-cancel lw-ecm2-double lw-ecm2-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-circle-value-cap
 (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
 (lw-complexp point) (equal (lw-complex-norm-square point) 1) (rationalp value-error) (< 0 value-error) (<= value-error 1))
 (lw-complex-diskp (lw-euler-circle-value center radius plus-arcs minus-arcs point value-error) (+ 1 (lw-euler-circle-cover-cap plus-arcs minus-arcs))))
 :hints (("Goal"
 :use (lw-euler-circle-cover-data lw-euler-circle-cover-selected-cap
       (:instance lw-euler-contour-patch-data (patch (lw-euler-circle-cover-patch point plus-arcs minus-arcs)))
       lw-euler-circle-cover-coverage lw-euler-circle-cover-shifted-check
       (:instance lw-mellin-euler-log-extended-neighborhood-cap (rate (nth 0 (lw-euler-circle-cover-patch point plus-arcs minus-arcs))) (height (nth 1 (lw-euler-circle-cover-patch point plus-arcs minus-arcs))) (outer-radius (nth 2 (lw-euler-circle-cover-patch point plus-arcs minus-arcs))) (anchor-error (nth 3 (lw-euler-circle-cover-patch point plus-arcs minus-arcs))) (point (lw-complex-sub (lw-complex-add center (lw-complex-scale radius point)) (lw-euler-contour-center (lw-euler-circle-cover-patch point plus-arcs minus-arcs)))) (local-anchor (lw-euler-contour-anchor (lw-euler-circle-cover-patch point plus-arcs minus-arcs))) (coefficient-radius (* 1/2 (car (lw-complex-add center (lw-complex-scale radius point))))))
       (:instance lw-complex-disk-enlarge (point (lw-euler-circle-value center radius plus-arcs minus-arcs point value-error)) (radius (+ 1 (lw-euler-contour-cap (lw-euler-circle-cover-patch point plus-arcs minus-arcs)))) (cap (+ 1 (lw-euler-circle-cover-cap plus-arcs minus-arcs)))))
 :in-theory (union-theories
 '(lw-euler-circle-value lw-euler-contour-patchp lw-euler-contour-pointp lw-euler-contour-center lw-euler-contour-radius lw-euler-contour-cap lw-complexp lw-complex-sub lw-ecm2-left-commutes lw-ecm2-left-distributes lw-ecm2-fold-constants lw-ecm2-times-negative lw-ecm2-negative-times lw-ecm2-zero-times lw-ecm2-minus-one lw-ecm2-double-negative lw-ecm2-add-cancel lw-ecm2-double lw-ecm2-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-circle-value-cauchy
 (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
 (lw-complexp point) (equal (lw-complex-norm-square point) 1) (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
 (lw-complex-diskp (lw-complex-sub
 (lw-euler-circle-value center radius plus-arcs minus-arcs point left-error)
 (lw-euler-circle-value center radius plus-arcs minus-arcs point right-error)) (* 1/2 (+ left-error right-error))))
 :hints (("Goal"
 :use (lw-euler-circle-cover-shifted-check
       (:instance lw-mellin-euler-log-extended-value-cauchy (rate (car (lw-complex-add center (lw-complex-scale radius point)))) (height (cdr (lw-complex-add center (lw-complex-scale radius point))))
        (radius (* 1/2 (car (lw-complex-add center (lw-complex-scale radius point))))) (anchor-error (lw-euler-contour-anchor (lw-euler-circle-cover-patch point plus-arcs minus-arcs)))))
 :in-theory (union-theories
 '(lw-euler-circle-value lw-ecm2-left-commutes lw-ecm2-left-distributes lw-ecm2-fold-constants lw-ecm2-times-negative lw-ecm2-negative-times lw-ecm2-zero-times lw-ecm2-minus-one lw-ecm2-double-negative lw-ecm2-add-cancel lw-ecm2-double lw-ecm2-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))


(defthm lw-euler-circle-polynomial-cauchy
 (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
 (lw-complexp point) (equal (lw-complex-norm-square point) 1) (natp left-target) (natp right-target) (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
 (lw-complex-diskp
  (lw-complex-sub (lw-euler-circle-polynomial-value center radius plus-arcs minus-arcs point left-target left-error)
                  (lw-euler-circle-polynomial-value center radius plus-arcs minus-arcs point right-target right-error))
  (* 1/2 (+ left-error right-error))))
 :hints (("Goal"
 :use (lw-euler-circle-cover-selected-cap lw-euler-circle-cover-coverage
       (:instance lw-complex-euler-local-normalized-polynomial-cauchy (rate (nth 0 (lw-euler-circle-cover-patch point plus-arcs minus-arcs))) (height (nth 1 (lw-euler-circle-cover-patch point plus-arcs minus-arcs))) (outer-radius (nth 2 (lw-euler-circle-cover-patch point plus-arcs minus-arcs))) (anchor-error (nth 3 (lw-euler-circle-cover-patch point plus-arcs minus-arcs))) (point (lw-complex-sub (lw-complex-add center (lw-complex-scale radius point)) (lw-euler-contour-center (lw-euler-circle-cover-patch point plus-arcs minus-arcs))))))
 :in-theory (union-theories
 '(lw-euler-circle-polynomial-value lw-euler-circle-polynomial lw-euler-contour-patchp lw-euler-contour-pointp lw-euler-contour-radius lw-ecm2-left-commutes lw-ecm2-left-distributes lw-ecm2-fold-constants lw-ecm2-times-negative lw-ecm2-negative-times lw-ecm2-zero-times lw-ecm2-minus-one lw-ecm2-double-negative lw-ecm2-add-cancel lw-ecm2-double lw-ecm2-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-euler-circle-cover-agreement
 (implies (and (lw-euler-circle-coverp center radius left-plus left-minus)
 (lw-euler-circle-coverp center radius right-plus right-minus)
 (lw-complexp point) (equal (lw-complex-norm-square point) 1)
 (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
 (lw-complex-diskp
  (lw-complex-sub (lw-euler-circle-value center radius left-plus left-minus point left-error)
                  (lw-euler-circle-value center radius right-plus right-minus point right-error))
  (* 1/2 (+ left-error right-error))))
 :hints (("Goal"
 :use ((:instance lw-euler-circle-cover-shifted-check (plus-arcs left-plus) (minus-arcs left-minus))
       (:instance lw-euler-circle-cover-shifted-check (plus-arcs right-plus) (minus-arcs right-minus))
       (:instance lw-mellin-euler-log-extended-certificate-independence
        (rate (car (lw-complex-add center (lw-complex-scale radius point))))
        (height (cdr (lw-complex-add center (lw-complex-scale radius point))))
        (radius (* 1/2 (car (lw-complex-add center (lw-complex-scale radius point)))))
        (left-anchor (lw-euler-contour-anchor (lw-euler-circle-cover-patch point left-plus left-minus)))
        (right-anchor (lw-euler-contour-anchor (lw-euler-circle-cover-patch point right-plus right-minus)))))
 :in-theory (union-theories
 '(lw-euler-circle-value lw-ecm2-left-commutes lw-ecm2-left-distributes lw-ecm2-fold-constants lw-ecm2-times-negative lw-ecm2-negative-times lw-ecm2-zero-times lw-ecm2-minus-one lw-ecm2-double-negative lw-ecm2-add-cancel lw-ecm2-double lw-ecm2-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))


