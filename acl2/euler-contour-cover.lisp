; Finite endpoint checks certify complete rational segment covers.
(in-package "ACL2")
(include-book "euler-contour-segment-models")
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
 lw-euler-contour-cap lw-euler-contour-radius lw-euler-contour-anchor lw-complex-segment)))
(local (defthm lw-ecc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ecc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ecc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ecc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ecc-times-negative (a b) (b a)))
                 :in-theory (disable lw-ecc-times-negative)))))

(local (defthm lw-ecc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ecc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ecc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ecc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ecc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ecc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ecc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ecc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ecc-left-commutes)))))
(defun lw-euler-contour-edge (left right patch) (list left right patch))
(defun lw-euler-contour-edge-left (edge) (nth 0 edge))
(defun lw-euler-contour-edge-right (edge) (nth 1 edge))
(defun lw-euler-contour-edge-patch (edge) (nth 2 edge))
(defun lw-euler-contour-edgep (edge)
 (and (true-listp edge) (equal (len edge) 3)
  (lw-euler-contour-segmentp (lw-euler-contour-edge-patch edge)
   (lw-euler-contour-edge-left edge) (lw-euler-contour-edge-right edge))))
(defun lw-euler-contour-edgesp (edges)
 (declare (xargs :measure (acl2-count edges) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (endp edges) (equal edges nil)
  (and (lw-euler-contour-edgep (car edges)) (lw-euler-contour-edgesp (cdr edges)))))
(defun lw-euler-contour-cap-sum (edges)
 (declare (xargs :measure (acl2-count edges) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (endp edges) 0
  (+ (lw-euler-contour-cap (lw-euler-contour-edge-patch (car edges)))
     (lw-euler-contour-cap-sum (cdr edges)))))
(defun lw-euler-contour-cover-cap (edges) (+ 1 (lw-euler-contour-cap-sum edges)))
(defun lw-euler-contour-cover-point (edges index parameter)
 (lw-complex-segment (lw-euler-contour-edge-left (nth index edges)) (lw-euler-contour-edge-right (nth index edges)) parameter))
(local (in-theory (disable lw-euler-contour-edge lw-euler-contour-edge-left lw-euler-contour-edge-right
 lw-euler-contour-edge-patch lw-euler-contour-edgep lw-euler-contour-edgesp lw-euler-contour-cap-sum
 lw-euler-contour-cover-cap lw-euler-contour-cover-point)))
(defthm lw-euler-contour-edge-valid
 (implies (lw-euler-contour-segmentp patch left right)
 (lw-euler-contour-edgep (lw-euler-contour-edge left right patch)))
 :hints (("Goal"
 :in-theory (union-theories
 '(lw-euler-contour-edgep lw-euler-contour-edge lw-euler-contour-edge-left lw-euler-contour-edge-right lw-euler-contour-edge-patch true-listp len nth endp lw-ecc-left-commutes lw-ecc-left-distributes lw-ecc-fold-constants lw-ecc-times-negative lw-ecc-negative-times lw-ecc-zero-times lw-ecc-minus-one lw-ecc-double-negative lw-ecc-add-cancel lw-ecc-double lw-ecc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
(defthm lw-euler-contour-edge-data
 (implies (lw-euler-contour-edgep edge)
 (and (lw-euler-contour-segmentp (lw-euler-contour-edge-patch edge) (lw-euler-contour-edge-left edge) (lw-euler-contour-edge-right edge))
      (lw-euler-contour-patchp (lw-euler-contour-edge-patch edge))
      (lw-euler-contour-pointp (lw-euler-contour-edge-patch edge) (lw-euler-contour-edge-left edge))
      (lw-euler-contour-pointp (lw-euler-contour-edge-patch edge) (lw-euler-contour-edge-right edge))))
 :hints (("Goal"
 :in-theory (union-theories
 '(lw-euler-contour-edgep lw-euler-contour-segmentp lw-ecc-left-commutes lw-ecc-left-distributes lw-ecc-fold-constants lw-ecc-times-negative lw-ecc-negative-times lw-ecc-zero-times lw-ecc-minus-one lw-ecc-double-negative lw-ecc-add-cancel lw-ecc-double lw-ecc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
(defthm lw-euler-contour-edge-cap-data
 (implies (lw-euler-contour-edgep edge)
 (and (rationalp (lw-euler-contour-cap (lw-euler-contour-edge-patch edge)))
      (< 0 (lw-euler-contour-cap (lw-euler-contour-edge-patch edge)))))
 :hints (("Goal" :use (lw-euler-contour-edge-data
       (:instance lw-euler-contour-patch-data (patch (lw-euler-contour-edge-patch edge))))
 :in-theory (union-theories
 '( lw-ecc-left-commutes lw-ecc-left-distributes lw-ecc-fold-constants lw-ecc-times-negative lw-ecc-negative-times lw-ecc-zero-times lw-ecc-minus-one lw-ecc-double-negative lw-ecc-add-cancel lw-ecc-double lw-ecc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes (:rewrite :forward-chaining))

(defthm lw-euler-contour-edges-data
 (implies (lw-euler-contour-edgesp edges)
 (and (true-listp edges) (rationalp (lw-euler-contour-cap-sum edges)) (<= 0 (lw-euler-contour-cap-sum edges))
      (rationalp (lw-euler-contour-cover-cap edges)) (<= 1 (lw-euler-contour-cover-cap edges))))
 :hints (("Goal" :induct (lw-euler-contour-edgesp edges)
 :in-theory (union-theories
 '(lw-euler-contour-edge-cap-data lw-euler-contour-edgesp lw-euler-contour-cap-sum lw-euler-contour-cover-cap true-listp endp lw-euler-contour-edge-data lw-euler-contour-patch-data lw-ecc-left-commutes lw-ecc-left-distributes lw-ecc-fold-constants lw-ecc-times-negative lw-ecc-negative-times lw-ecc-zero-times lw-ecc-minus-one lw-ecc-double-negative lw-ecc-add-cancel lw-ecc-double lw-ecc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))
 :rule-classes (:rewrite :forward-chaining))
(defthm lw-euler-contour-edges-nth
 (implies (and (lw-euler-contour-edgesp edges) (natp index) (< index (len edges)))
 (lw-euler-contour-edgep (nth index edges)))
 :hints (("Goal" :induct (nth index edges)
 :in-theory (union-theories
 '(lw-euler-contour-edgesp nth len endp lw-ecc-left-commutes lw-ecc-left-distributes lw-ecc-fold-constants lw-ecc-times-negative lw-ecc-negative-times lw-ecc-zero-times lw-ecc-minus-one lw-ecc-double-negative lw-ecc-add-cancel lw-ecc-double lw-ecc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))
(defthm lw-euler-contour-selected-cap
 (implies (and (lw-euler-contour-edgesp edges) (natp index) (< index (len edges)))
 (<= (lw-euler-contour-cap (lw-euler-contour-edge-patch (nth index edges))) (lw-euler-contour-cap-sum edges)))
 :hints (("Goal" :induct (nth index edges)
 :in-theory (union-theories
 '(lw-euler-contour-edge-cap-data lw-euler-contour-edgesp lw-euler-contour-cap-sum nth len endp lw-euler-contour-edges-data lw-euler-contour-edge-data lw-euler-contour-patch-data lw-ecc-left-commutes lw-ecc-left-distributes lw-ecc-fold-constants lw-ecc-times-negative lw-ecc-negative-times lw-ecc-zero-times lw-ecc-minus-one lw-ecc-double-negative lw-ecc-add-cancel lw-ecc-double lw-ecc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))


(defthm lw-euler-contour-cover-point-data
 (implies (and (lw-euler-contour-edgesp edges) (natp index) (< index (len edges)) (rationalp parameter) (<= 0 parameter) (<= parameter 1))
 (and (lw-euler-contour-pointp (lw-euler-contour-edge-patch (nth index edges)) (lw-euler-contour-cover-point edges index parameter)) (lw-complexp (lw-euler-contour-cover-point edges index parameter))
      (rationalp (car (lw-euler-contour-cover-point edges index parameter))) (< 0 (car (lw-euler-contour-cover-point edges index parameter))) (rationalp (cdr (lw-euler-contour-cover-point edges index parameter)))
      (lw-euler-value-clearance-check (car (lw-euler-contour-cover-point edges index parameter)) (cdr (lw-euler-contour-cover-point edges index parameter)) (lw-euler-contour-anchor (lw-euler-contour-edge-patch (nth index edges))))))
 :hints (("Goal"
 :use (lw-euler-contour-edges-nth
       (:instance lw-euler-contour-edge-data (edge (nth index edges)))
       (:instance lw-euler-contour-segment-coverage (patch (lw-euler-contour-edge-patch (nth index edges))) (left (lw-euler-contour-edge-left (nth index edges))) (right (lw-euler-contour-edge-right (nth index edges))))
       (:instance lw-euler-contour-point-data (patch (lw-euler-contour-edge-patch (nth index edges))) (point (lw-euler-contour-cover-point edges index parameter))))
 :in-theory (union-theories
 '(lw-euler-contour-cover-point lw-ecc-left-commutes lw-ecc-left-distributes lw-ecc-fold-constants lw-ecc-times-negative lw-ecc-negative-times lw-ecc-zero-times lw-ecc-minus-one lw-ecc-double-negative lw-ecc-add-cancel lw-ecc-double lw-ecc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

