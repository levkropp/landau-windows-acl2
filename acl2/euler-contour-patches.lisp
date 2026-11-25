; Finite local Euler patches certify every point of an assigned segment.
(in-package "ACL2")
(include-book "complex-segments")
(include-book "euler-local-normalized-model")
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
(local (defthm lw-ecp-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ecp-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ecp-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ecp-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ecp-times-negative (a b) (b a)))
                 :in-theory (disable lw-ecp-times-negative)))))

(local (defthm lw-ecp-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ecp-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ecp-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ecp-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ecp-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ecp-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ecp-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ecp-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecp-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecp-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ecp-left-commutes)))))
(defun lw-euler-contour-patch (rate height outer-radius anchor-error)
 (list rate height outer-radius anchor-error))
(defun lw-euler-contour-patchp (patch)
 (and (true-listp patch) (equal (len patch) 4)
  (lw-euler-value-clearance-check (nth 0 patch) (nth 1 patch) (nth 3 patch))
  (rationalp (nth 2 patch)) (< 0 (nth 2 patch)) (< (nth 2 patch) (nth 0 patch))))
(defun lw-euler-contour-center (patch) (cons (nth 0 patch) (nth 1 patch)))
(defun lw-euler-contour-radius (patch)
 (lw-euler-local-normalized-radius (nth 0 patch) (nth 1 patch) (nth 2 patch) (nth 3 patch)))
(defun lw-euler-contour-cap (patch)
 (lw-euler-local-normalized-cap (nth 0 patch) (nth 1 patch) (nth 2 patch) (nth 3 patch)))
(defun lw-euler-contour-anchor (patch)
 (lw-euler-local-normalized-anchor (nth 0 patch) (nth 1 patch) (nth 3 patch)))
(defun lw-euler-contour-pointp (patch point)
 (and (lw-complexp point) (lw-complex-diskp (lw-complex-sub point (lw-euler-contour-center patch)) (lw-euler-contour-radius patch))))
(defun lw-euler-contour-segmentp (patch left right)
 (and (lw-euler-contour-patchp patch)
      (lw-euler-contour-pointp patch left) (lw-euler-contour-pointp patch right)))
(local (in-theory (disable lw-euler-contour-patch lw-euler-contour-patchp
 lw-euler-contour-center lw-euler-contour-radius lw-euler-contour-cap lw-euler-contour-anchor
 lw-euler-contour-pointp lw-euler-contour-segmentp)))
(defthm lw-euler-contour-patch-valid
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate))
 (lw-euler-contour-patchp (lw-euler-contour-patch rate height outer-radius anchor-error)))
 :hints (("Goal"
 :in-theory (union-theories
 '(lw-euler-contour-patchp lw-euler-contour-patch true-listp len nth endp lw-ecp-left-commutes lw-ecp-left-distributes lw-ecp-fold-constants lw-ecp-times-negative lw-ecp-negative-times lw-ecp-zero-times lw-ecp-minus-one lw-ecp-double-negative lw-ecp-add-cancel lw-ecp-double lw-ecp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
(defthm lw-euler-contour-patch-data
 (implies (lw-euler-contour-patchp patch)
 (and (lw-complexp (lw-euler-contour-center patch)) (rationalp (nth 0 patch)) (< 0 (nth 0 patch)) (rationalp (nth 1 patch))
      (rationalp (lw-euler-contour-radius patch)) (< 0 (lw-euler-contour-radius patch)) (< (lw-euler-contour-radius patch) (nth 0 patch)) (<= (lw-euler-contour-radius patch) 1)
      (rationalp (lw-euler-contour-cap patch)) (< 0 (lw-euler-contour-cap patch)) (rationalp (lw-euler-contour-anchor patch)) (< 0 (lw-euler-contour-anchor patch))))
 :hints (("Goal"
 :use ((:instance lw-euler-local-normalized-data (rate (nth 0 patch)) (height (nth 1 patch)) (outer-radius (nth 2 patch)) (anchor-error (nth 3 patch))))
 :in-theory (union-theories
 '(lw-euler-contour-patchp lw-euler-contour-center lw-euler-contour-radius lw-euler-contour-cap lw-euler-contour-anchor lw-complexp lw-ecp-left-commutes lw-ecp-left-distributes lw-ecp-fold-constants lw-ecp-times-negative lw-ecp-negative-times lw-ecp-zero-times lw-ecp-minus-one lw-ecp-double-negative lw-ecp-add-cancel lw-ecp-double lw-ecp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
(defthm lw-euler-contour-point-data
 (implies (and (lw-euler-contour-patchp patch) (lw-euler-contour-pointp patch point))
 (and (lw-complexp point) (lw-complexp (lw-complex-sub point (lw-euler-contour-center patch))) (lw-complex-diskp (lw-complex-sub point (lw-euler-contour-center patch)) (lw-euler-contour-radius patch))
      (rationalp (car point)) (< 0 (car point)) (rationalp (cdr point))
      (lw-euler-value-clearance-check (car point) (cdr point) (lw-euler-contour-anchor patch))))
 :hints (("Goal"
 :use (lw-euler-contour-patch-data
       (:instance lw-euler-local-normalized-point-data (rate (nth 0 patch)) (height (nth 1 patch)) (outer-radius (nth 2 patch)) (anchor-error (nth 3 patch)) (point (lw-complex-sub point (lw-euler-contour-center patch)))))
 :in-theory (union-theories
 '(lw-euler-contour-patchp lw-euler-contour-pointp lw-euler-contour-center lw-euler-contour-radius lw-euler-contour-anchor lw-complexp lw-complex-sub lw-ecp-left-commutes lw-ecp-left-distributes lw-ecp-fold-constants lw-ecp-times-negative lw-ecp-negative-times lw-ecp-zero-times lw-ecp-minus-one lw-ecp-double-negative lw-ecp-add-cancel lw-ecp-double lw-ecp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
(defthm lw-euler-contour-segment-coverage
 (implies (and (lw-euler-contour-segmentp patch left right)
 (rationalp parameter) (<= 0 parameter) (<= parameter 1))
 (lw-euler-contour-pointp patch (lw-complex-segment left right parameter)))
 :hints (("Goal"
 :use (lw-euler-contour-patch-data
       (:instance lw-complex-segment-rational)
       (:instance lw-complex-segment-centered-disk (center (lw-euler-contour-center patch)) (radius (lw-euler-contour-radius patch))))
 :in-theory (union-theories
 '(lw-euler-contour-segmentp lw-euler-contour-pointp lw-ecp-left-commutes lw-ecp-left-distributes lw-ecp-fold-constants lw-ecp-times-negative lw-ecp-negative-times lw-ecp-zero-times lw-ecp-minus-one lw-ecp-double-negative lw-ecp-add-cancel lw-ecp-double lw-ecp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
