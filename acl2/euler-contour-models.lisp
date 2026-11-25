; Build all polynomial models for a finite covered contour.
(in-package "ACL2")
(include-book "euler-contour-cover")
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
(local (in-theory (disable lw-euler-contour-edgesp lw-euler-contour-edgep
 lw-euler-contour-edge-left lw-euler-contour-edge-right lw-euler-contour-edge-patch
 lw-euler-contour-patchp lw-euler-contour-pointp lw-euler-contour-segmentp
 lw-euler-contour-cap lw-euler-contour-cap-sum lw-euler-contour-cover-cap
 lw-euler-contour-anchor lw-euler-contour-cover-point
 lw-euler-contour-polynomial lw-mellin-euler-log-extended-value lw-complex-polynomial)))
(local (defthm lw-ecm-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ecm-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ecm-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ecm-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ecm-times-negative (a b) (b a)))
                 :in-theory (disable lw-ecm-times-negative)))))

(local (defthm lw-ecm-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ecm-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ecm-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ecm-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ecm-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ecm-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ecm-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ecm-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecm-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecm-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ecm-left-commutes)))))
(defun lw-euler-contour-cover-polynomial (edges index target error)
 (lw-euler-contour-polynomial (lw-euler-contour-edge-patch (nth index edges)) (lw-euler-contour-edge-left (nth index edges)) (lw-euler-contour-edge-right (nth index edges)) target error))
(defun lw-euler-contour-models (edges target error)
 (declare (xargs :measure (acl2-count edges) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (endp edges) nil
  (cons (lw-euler-contour-polynomial (lw-euler-contour-edge-patch (car edges))
         (lw-euler-contour-edge-left (car edges)) (lw-euler-contour-edge-right (car edges)) target error)
        (lw-euler-contour-models (cdr edges) target error))))
(defun lw-euler-contour-modelsp (models)
 (declare (xargs :measure (acl2-count models) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (endp models) (equal models nil)
  (and (lw-complex-coefficientsp (car models)) (lw-euler-contour-modelsp (cdr models)))))
(defun lw-euler-contour-cover-value (edges index parameter error)
 (lw-mellin-euler-log-extended-value (car (lw-euler-contour-cover-point edges index parameter)) (cdr (lw-euler-contour-cover-point edges index parameter))
  (* 1/2 (car (lw-euler-contour-cover-point edges index parameter))) (lw-euler-contour-anchor (lw-euler-contour-edge-patch (nth index edges))) error))
(local (in-theory (disable lw-euler-contour-cover-polynomial lw-euler-contour-models
 lw-euler-contour-modelsp lw-euler-contour-cover-value)))
(defthm lw-euler-contour-cover-polynomial-valid
 (implies (and (lw-euler-contour-edgesp edges) (natp index) (< index (len edges)) (natp target) (rationalp error) (< 0 error))
 (lw-complex-coefficientsp (lw-euler-contour-cover-polynomial edges index target error)))
 :hints (("Goal"
 :use (lw-euler-contour-edges-nth
       (:instance lw-euler-contour-edge-data (edge (nth index edges)))
       (:instance lw-euler-contour-polynomial-valid (patch (lw-euler-contour-edge-patch (nth index edges))) (left (lw-euler-contour-edge-left (nth index edges))) (right (lw-euler-contour-edge-right (nth index edges)))))
 :in-theory (union-theories
 '(lw-euler-contour-cover-polynomial lw-euler-contour-pointp lw-ecm-left-commutes lw-ecm-left-distributes lw-ecm-fold-constants lw-ecm-times-negative lw-ecm-negative-times lw-ecm-zero-times lw-ecm-minus-one lw-ecm-double-negative lw-ecm-add-cancel lw-ecm-double lw-ecm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
(local (defthm lw-ecm-edge-model-valid
 (implies (and (lw-euler-contour-edgep edge) (natp target) (rationalp error) (< 0 error))
 (lw-complex-coefficientsp (lw-euler-contour-polynomial (lw-euler-contour-edge-patch edge) (lw-euler-contour-edge-left edge) (lw-euler-contour-edge-right edge) target error)))
 :hints (("Goal"
 :use (lw-euler-contour-edge-data
       (:instance lw-euler-contour-polynomial-valid (patch (lw-euler-contour-edge-patch edge)) (left (lw-euler-contour-edge-left edge)) (right (lw-euler-contour-edge-right edge))))
 :in-theory (union-theories
 '(lw-euler-contour-pointp lw-ecm-left-commutes lw-ecm-left-distributes lw-ecm-fold-constants lw-ecm-times-negative lw-ecm-negative-times lw-ecm-zero-times lw-ecm-minus-one lw-ecm-double-negative lw-ecm-add-cancel lw-ecm-double lw-ecm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes (:rewrite :forward-chaining)))
(defthm lw-euler-contour-models-valid
 (implies (and (lw-euler-contour-edgesp edges) (natp target) (rationalp error) (< 0 error))
 (and (lw-euler-contour-modelsp (lw-euler-contour-models edges target error))
      (equal (len (lw-euler-contour-models edges target error)) (len edges))))
 :hints (("Goal" :induct (lw-euler-contour-models edges target error)
 :in-theory (union-theories
 '(lw-euler-contour-models lw-euler-contour-modelsp lw-euler-contour-edgesp lw-ecm-edge-model-valid len endp lw-ecm-left-commutes lw-ecm-left-distributes lw-ecm-fold-constants lw-ecm-times-negative lw-ecm-negative-times lw-ecm-zero-times lw-ecm-minus-one lw-ecm-double-negative lw-ecm-add-cancel lw-ecm-double lw-ecm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))
(defthm lw-euler-contour-models-nth
 (implies (and (lw-euler-contour-edgesp edges) (natp index) (< index (len edges)) (natp target) (rationalp error) (< 0 error))
 (equal (nth index (lw-euler-contour-models edges target error)) (lw-euler-contour-cover-polynomial edges index target error)))
 :hints (("Goal" :induct (nth index edges)
 :expand ((lw-euler-contour-models edges target error))
 :in-theory (union-theories
 '(lw-euler-contour-models lw-euler-contour-cover-polynomial lw-euler-contour-edgesp len nth endp lw-ecm-left-commutes lw-ecm-left-distributes lw-ecm-fold-constants lw-ecm-times-negative lw-ecm-negative-times lw-ecm-zero-times lw-ecm-minus-one lw-ecm-double-negative lw-ecm-add-cancel lw-ecm-double lw-ecm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))
(defthm lw-complex-euler-contour-cover-polynomial-cap
 (implies (and (lw-euler-contour-edgesp edges) (natp index) (< index (len edges)) (rationalp parameter) (<= 0 parameter) (<= parameter 1) (natp target) (rationalp error) (< 0 error))
 (lw-complex-diskp (lw-complex-polynomial (lw-euler-contour-cover-polynomial edges index target error) (cons parameter 0) 0) (lw-euler-contour-cover-cap edges)))
 :hints (("Goal"
 :use (lw-euler-contour-edges-data lw-euler-contour-edges-nth lw-euler-contour-selected-cap
       (:instance lw-euler-contour-edge-data (edge (nth index edges)))
       (:instance lw-complex-euler-contour-polynomial-cap (patch (lw-euler-contour-edge-patch (nth index edges))) (left (lw-euler-contour-edge-left (nth index edges))) (right (lw-euler-contour-edge-right (nth index edges))))
       (:instance lw-complex-disk-enlarge (point (lw-complex-polynomial (lw-euler-contour-cover-polynomial edges index target error) (cons parameter 0) 0)) (radius (lw-euler-contour-cap (lw-euler-contour-edge-patch (nth index edges)))) (cap (lw-euler-contour-cover-cap edges))))
 :in-theory (union-theories
 '(lw-euler-contour-cover-polynomial lw-euler-contour-cover-cap lw-ecm-left-commutes lw-ecm-left-distributes lw-ecm-fold-constants lw-ecm-times-negative lw-ecm-negative-times lw-ecm-zero-times lw-ecm-minus-one lw-ecm-double-negative lw-ecm-add-cancel lw-ecm-double lw-ecm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
(defthm lw-complex-euler-contour-cover-general-comparison
 (implies (and (lw-euler-contour-edgesp edges) (natp index) (< index (len edges)) (rationalp parameter) (<= 0 parameter) (<= parameter 1) (natp target) (rationalp error) (< 0 error)
 (lw-euler-value-clearance-check (car (lw-euler-contour-cover-point edges index parameter)) (cdr (lw-euler-contour-cover-point edges index parameter)) local-anchor)
 (rationalp coefficient-radius) (< 0 coefficient-radius) (< coefficient-radius (car (lw-euler-contour-cover-point edges index parameter)))
 (rationalp value-error) (< 0 value-error))
 (lw-complex-diskp (lw-complex-sub (lw-complex-polynomial (lw-euler-contour-cover-polynomial edges index target error) (cons parameter 0) 0) (lw-mellin-euler-log-extended-value (car (lw-euler-contour-cover-point edges index parameter)) (cdr (lw-euler-contour-cover-point edges index parameter)) coefficient-radius local-anchor value-error)) (* 1/2 (+ error value-error))))
 :hints (("Goal"
 :use (lw-euler-contour-edges-nth
       (:instance lw-euler-contour-edge-data (edge (nth index edges)))
       (:instance lw-complex-euler-contour-polynomial-comparison (patch (lw-euler-contour-edge-patch (nth index edges))) (left (lw-euler-contour-edge-left (nth index edges))) (right (lw-euler-contour-edge-right (nth index edges)))))
 :in-theory (union-theories
 '(lw-euler-contour-cover-polynomial lw-euler-contour-cover-point lw-ecm-left-commutes lw-ecm-left-distributes lw-ecm-fold-constants lw-ecm-times-negative lw-ecm-negative-times lw-ecm-zero-times lw-ecm-minus-one lw-ecm-double-negative lw-ecm-add-cancel lw-ecm-double lw-ecm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))


(defthm lw-euler-contour-cover-value-rational
 (implies (and (lw-euler-contour-edgesp edges) (natp index) (< index (len edges)) (rationalp parameter) (<= 0 parameter) (<= parameter 1) (rationalp error) (< 0 error))
 (lw-complexp (lw-euler-contour-cover-value edges index parameter error)))
 :hints (("Goal"
 :use (lw-euler-contour-cover-point-data
       (:instance lw-mellin-euler-log-extended-value-rational
        (rate (car (lw-euler-contour-cover-point edges index parameter))) (height (cdr (lw-euler-contour-cover-point edges index parameter))) (radius (* 1/2 (car (lw-euler-contour-cover-point edges index parameter)))) (anchor-error (lw-euler-contour-anchor (lw-euler-contour-edge-patch (nth index edges))))))
 :in-theory (union-theories
 '(lw-euler-contour-cover-value lw-ecm-left-commutes lw-ecm-left-distributes lw-ecm-fold-constants lw-ecm-times-negative lw-ecm-negative-times lw-ecm-zero-times lw-ecm-minus-one lw-ecm-double-negative lw-ecm-add-cancel lw-ecm-double lw-ecm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
(defthm lw-complex-euler-contour-cover-model-comparison
 (implies (and (lw-euler-contour-edgesp edges) (natp index) (< index (len edges)) (rationalp parameter) (<= 0 parameter) (<= parameter 1) (natp target) (rationalp error) (< 0 error) (rationalp value-error) (< 0 value-error))
 (lw-complex-diskp (lw-complex-sub (lw-complex-polynomial (lw-euler-contour-cover-polynomial edges index target error) (cons parameter 0) 0) (lw-euler-contour-cover-value edges index parameter value-error)) (* 1/2 (+ error value-error))))
 :hints (("Goal"
 :use (lw-euler-contour-cover-point-data
       (:instance lw-complex-euler-contour-cover-general-comparison (local-anchor (lw-euler-contour-anchor (lw-euler-contour-edge-patch (nth index edges)))) (coefficient-radius (* 1/2 (car (lw-euler-contour-cover-point edges index parameter))))))
 :in-theory (union-theories
 '(lw-euler-contour-cover-value lw-ecm-left-commutes lw-ecm-left-distributes lw-ecm-fold-constants lw-ecm-times-negative lw-ecm-negative-times lw-ecm-zero-times lw-ecm-minus-one lw-ecm-double-negative lw-ecm-add-cancel lw-ecm-double lw-ecm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
(defthm lw-euler-contour-cover-value-cap
 (implies (and (lw-euler-contour-edgesp edges) (natp index) (< index (len edges)) (rationalp parameter) (<= 0 parameter) (<= parameter 1) (rationalp error) (< 0 error) (<= error 1))
 (lw-complex-diskp (lw-euler-contour-cover-value edges index parameter error) (+ 1 (lw-euler-contour-cover-cap edges))))
 :hints (("Goal"
 :use (lw-euler-contour-edges-data lw-euler-contour-edges-nth lw-euler-contour-selected-cap lw-euler-contour-cover-point-data
       (:instance lw-euler-contour-edge-data (edge (nth index edges)))
       (:instance lw-mellin-euler-log-extended-segment-cap (patch (lw-euler-contour-edge-patch (nth index edges))) (left (lw-euler-contour-edge-left (nth index edges))) (right (lw-euler-contour-edge-right (nth index edges)))
        (local-anchor (lw-euler-contour-anchor (lw-euler-contour-edge-patch (nth index edges)))) (coefficient-radius (* 1/2 (car (lw-euler-contour-cover-point edges index parameter)))) (value-error error))
       (:instance lw-complex-disk-enlarge (point (lw-euler-contour-cover-value edges index parameter error)) (radius (+ 1 (lw-euler-contour-cap (lw-euler-contour-edge-patch (nth index edges))))) (cap (+ 1 (lw-euler-contour-cover-cap edges)))))
 :in-theory (union-theories
 '(lw-euler-contour-cover-value lw-euler-contour-cover-point lw-euler-contour-cover-cap lw-ecm-left-commutes lw-ecm-left-distributes lw-ecm-fold-constants lw-ecm-times-negative lw-ecm-negative-times lw-ecm-zero-times lw-ecm-minus-one lw-ecm-double-negative lw-ecm-add-cancel lw-ecm-double lw-ecm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
(defthm lw-euler-contour-cover-value-cauchy
 (implies (and (lw-euler-contour-edgesp edges) (natp index) (< index (len edges)) (rationalp parameter) (<= 0 parameter) (<= parameter 1) (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
 (lw-complex-diskp
  (lw-complex-sub (lw-euler-contour-cover-value edges index parameter left-error) (lw-euler-contour-cover-value edges index parameter right-error))
  (* 1/2 (+ left-error right-error))))
 :hints (("Goal"
 :use (lw-euler-contour-cover-point-data
       (:instance lw-mellin-euler-log-extended-value-cauchy
        (rate (car (lw-euler-contour-cover-point edges index parameter))) (height (cdr (lw-euler-contour-cover-point edges index parameter))) (radius (* 1/2 (car (lw-euler-contour-cover-point edges index parameter)))) (anchor-error (lw-euler-contour-anchor (lw-euler-contour-edge-patch (nth index edges))))))
 :in-theory (union-theories
 '(lw-euler-contour-cover-value lw-ecm-left-commutes lw-ecm-left-distributes lw-ecm-fold-constants lw-ecm-times-negative lw-ecm-negative-times lw-ecm-zero-times lw-ecm-minus-one lw-ecm-double-negative lw-ecm-add-cancel lw-ecm-double lw-ecm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

