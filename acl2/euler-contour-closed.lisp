; Check closed contour chains and cyclic segment joins.
(in-package "ACL2")
(include-book "euler-contour-models")
(include-book "euler-normalized-overlap")
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
 lw-euler-contour-cap lw-euler-contour-anchor lw-euler-contour-center
 lw-euler-contour-cover-polynomial lw-euler-contour-polynomial lw-euler-contour-cover-point
 lw-complex-segment lw-complex-polynomial lw-mellin-euler-log-extended-value)))
(local (defthm lw-ecl-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ecl-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ecl-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ecl-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ecl-times-negative (a b) (b a)))
                 :in-theory (disable lw-ecl-times-negative)))))

(local (defthm lw-ecl-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ecl-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ecl-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ecl-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ecl-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ecl-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ecl-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ecl-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecl-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecl-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ecl-left-commutes)))))
(defun lw-euler-contour-chainp (edges)
 (declare (xargs :measure (acl2-count edges) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (or (endp edges) (endp (cdr edges))) t
  (and (equal (lw-euler-contour-edge-right (car edges)) (lw-euler-contour-edge-left (cadr edges)))
       (lw-euler-contour-chainp (cdr edges)))))
(defun lw-euler-contour-start (edges) (lw-euler-contour-edge-left (car edges)))
(defun lw-euler-contour-finish (edges) (lw-euler-contour-edge-right (nth (- (len edges) 1) edges)))
(defun lw-euler-contour-closedp (edges)
 (and (consp edges) (lw-euler-contour-edgesp edges) (lw-euler-contour-chainp edges)
      (equal (lw-euler-contour-start edges) (lw-euler-contour-finish edges))))
(defun lw-euler-contour-successor (edges index)
 (if (< (+ 1 index) (len edges)) (+ 1 index) 0))
(local (in-theory (disable lw-euler-contour-chainp lw-euler-contour-start
 lw-euler-contour-finish lw-euler-contour-closedp lw-euler-contour-successor)))
(local (defthm lw-ecl-length-natural
 (natp (len edges))
 :hints (("Goal" :induct (len edges) :in-theory (theory 'ground-zero)))
 :rule-classes (:rewrite :type-prescription)))
(local (defthm lw-ecl-nth-zero
 (equal (nth 0 edges) (car edges))
 :hints (("Goal" :in-theory (theory 'ground-zero)))))
(defthm lw-euler-contour-closed-data
 (implies (lw-euler-contour-closedp edges)
 (and (consp edges) (lw-euler-contour-edgesp edges) (lw-euler-contour-chainp edges)
      (equal (lw-euler-contour-start edges) (lw-euler-contour-finish edges))))
 :hints (("Goal" :in-theory (union-theories
 '(lw-euler-contour-closedp lw-ecl-left-commutes lw-ecl-left-distributes lw-ecl-fold-constants lw-ecl-times-negative lw-ecl-negative-times lw-ecl-zero-times lw-ecl-minus-one lw-ecl-double-negative lw-ecl-add-cancel lw-ecl-double lw-ecl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
(defthm lw-euler-contour-chain-nth
 (implies (and (lw-euler-contour-chainp edges) (natp index) (< (+ 1 index) (len edges)))
 (equal (lw-euler-contour-edge-right (nth index edges))
        (lw-euler-contour-edge-left (nth (+ 1 index) edges))))
 :hints (("Goal" :induct (nth index edges)
 :expand ((lw-euler-contour-chainp edges) (nth index edges) (nth (+ 1 index) edges) (len edges))
 :in-theory (union-theories
 '(lw-euler-contour-chainp lw-ecl-nth-zero nth len endp lw-ecl-left-commutes lw-ecl-left-distributes lw-ecl-fold-constants lw-ecl-times-negative lw-ecl-negative-times lw-ecl-zero-times lw-ecl-minus-one lw-ecl-double-negative lw-ecl-add-cancel lw-ecl-double lw-ecl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))
(defthm lw-euler-contour-successor-data
 (implies (and (natp index) (< index (len edges)))
 (and (natp (lw-euler-contour-successor edges index))
      (< (lw-euler-contour-successor edges index) (len edges))))
 :hints (("Goal" :use (lw-ecl-length-natural)
 :in-theory (union-theories
 '(lw-euler-contour-successor lw-ecl-left-commutes lw-ecl-left-distributes lw-ecl-fold-constants lw-ecl-times-negative lw-ecl-negative-times lw-ecl-zero-times lw-ecl-minus-one lw-ecl-double-negative lw-ecl-add-cancel lw-ecl-double lw-ecl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
(defthm lw-euler-contour-closed-junction
 (implies (and (lw-euler-contour-closedp edges) (natp index) (< index (len edges)))
 (equal (lw-euler-contour-edge-right (nth index edges))
        (lw-euler-contour-edge-left (nth (lw-euler-contour-successor edges index) edges))))
 :hints (("Goal" :cases ((< (+ 1 index) (len edges)))
 :use (lw-ecl-length-natural lw-euler-contour-closed-data lw-euler-contour-chain-nth)
 :in-theory (union-theories
 '(lw-euler-contour-closedp lw-euler-contour-start lw-euler-contour-finish lw-euler-contour-successor lw-ecl-nth-zero lw-ecl-left-commutes lw-ecl-left-distributes lw-ecl-fold-constants lw-ecl-times-negative lw-ecl-negative-times lw-ecl-zero-times lw-ecl-minus-one lw-ecl-double-negative lw-ecl-add-cancel lw-ecl-double lw-ecl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))


(defthm lw-complex-euler-contour-edge-junction
 (implies (and (lw-euler-contour-edgep left-edge) (lw-euler-contour-edgep right-edge)
 (equal (lw-euler-contour-edge-right left-edge) (lw-euler-contour-edge-left right-edge)) (natp left-target) (natp right-target)
 (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
 (lw-complex-diskp (lw-complex-sub (lw-complex-polynomial (lw-euler-contour-polynomial (lw-euler-contour-edge-patch left-edge) (lw-euler-contour-edge-left left-edge) (lw-euler-contour-edge-right left-edge) left-target left-error) (cons 1 0) 0) (lw-complex-polynomial (lw-euler-contour-polynomial (lw-euler-contour-edge-patch right-edge) (lw-euler-contour-edge-left right-edge) (lw-euler-contour-edge-right right-edge) right-target right-error) (cons 0 0) 0)) (* 1/2 (+ left-error right-error))))
 :hints (("Goal"
 :use ((:instance lw-euler-contour-edge-data (edge left-edge))
       (:instance lw-euler-contour-edge-data (edge right-edge))
       (:instance lw-euler-contour-patch-data (patch (lw-euler-contour-edge-patch left-edge)))
       (:instance lw-euler-contour-patch-data (patch (lw-euler-contour-edge-patch right-edge)))
       (:instance lw-euler-contour-polynomial-evaluation (patch (lw-euler-contour-edge-patch left-edge)) (left (lw-euler-contour-edge-left left-edge)) (right (lw-euler-contour-edge-right left-edge)) (parameter 1) (target left-target) (error left-error))
       (:instance lw-euler-contour-polynomial-evaluation (patch (lw-euler-contour-edge-patch right-edge)) (left (lw-euler-contour-edge-left right-edge)) (right (lw-euler-contour-edge-right right-edge)) (parameter 0) (target right-target) (error right-error))
       (:instance lw-complex-euler-local-normalized-polynomial-overlap (left-rate (nth 0 (lw-euler-contour-edge-patch left-edge))) (left-height (nth 1 (lw-euler-contour-edge-patch left-edge))) (left-outer-radius (nth 2 (lw-euler-contour-edge-patch left-edge))) (left-anchor-error (nth 3 (lw-euler-contour-edge-patch left-edge)))
        (right-rate (nth 0 (lw-euler-contour-edge-patch right-edge))) (right-height (nth 1 (lw-euler-contour-edge-patch right-edge))) (right-outer-radius (nth 2 (lw-euler-contour-edge-patch right-edge))) (right-anchor-error (nth 3 (lw-euler-contour-edge-patch right-edge)))
        (left-point (lw-complex-sub (lw-euler-contour-edge-right left-edge) (lw-euler-contour-center (lw-euler-contour-edge-patch left-edge)))) (right-point (lw-complex-sub (lw-euler-contour-edge-left right-edge) (lw-euler-contour-center (lw-euler-contour-edge-patch right-edge))))))
 :in-theory (union-theories
 '(lw-euler-contour-pointp lw-euler-contour-patchp lw-euler-contour-center lw-euler-contour-radius lw-complex-segment-endpoints lw-complexp lw-complex-sub lw-ecl-left-commutes lw-ecl-left-distributes lw-ecl-fold-constants lw-ecl-times-negative lw-ecl-negative-times lw-ecl-zero-times lw-ecl-minus-one lw-ecl-double-negative lw-ecl-add-cancel lw-ecl-double lw-ecl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))


(defthm lw-complex-euler-contour-closed-model-junction
 (implies (and (lw-euler-contour-closedp edges) (natp index) (< index (len edges)) (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error) (natp left-target) (natp right-target))
 (lw-complex-diskp
  (lw-complex-sub (lw-complex-polynomial (lw-euler-contour-cover-polynomial edges index left-target left-error) (cons 1 0) 0) (lw-complex-polynomial (lw-euler-contour-cover-polynomial edges (lw-euler-contour-successor edges index) right-target right-error) (cons 0 0) 0))
  (* 1/2 (+ left-error right-error))))
 :hints (("Goal"
 :use (lw-euler-contour-closed-data lw-euler-contour-closed-junction lw-euler-contour-successor-data lw-euler-contour-edges-nth
       (:instance lw-euler-contour-edges-nth (index (lw-euler-contour-successor edges index)))
       (:instance lw-complex-euler-contour-edge-junction (left-edge (nth index edges)) (right-edge (nth (lw-euler-contour-successor edges index) edges))))
 :in-theory (union-theories
 '(lw-euler-contour-cover-polynomial lw-ecl-left-commutes lw-ecl-left-distributes lw-ecl-fold-constants lw-ecl-times-negative lw-ecl-negative-times lw-ecl-zero-times lw-ecl-minus-one lw-ecl-double-negative lw-ecl-add-cancel lw-ecl-double lw-ecl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
(defthm lw-euler-contour-closed-value-junction
 (implies (and (lw-euler-contour-closedp edges) (natp index) (< index (len edges)) (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
 (lw-complex-diskp (lw-complex-sub (lw-euler-contour-cover-value edges index 1 left-error) (lw-euler-contour-cover-value edges (lw-euler-contour-successor edges index) 0 right-error)) (* 1/2 (+ left-error right-error))))
 :hints (("Goal"
 :use (lw-euler-contour-closed-data lw-euler-contour-closed-junction lw-euler-contour-successor-data lw-euler-contour-edges-nth
       (:instance lw-euler-contour-edges-nth (index (lw-euler-contour-successor edges index)))
       (:instance lw-euler-contour-edge-data (edge (nth index edges)))
       (:instance lw-euler-contour-edge-data (edge (nth (lw-euler-contour-successor edges index) edges)))
       (:instance lw-euler-contour-cover-point-data (parameter 1))
       (:instance lw-euler-contour-cover-point-data (index (lw-euler-contour-successor edges index)) (parameter 0))
       (:instance lw-mellin-euler-log-extended-certificate-independence
        (rate (car (lw-euler-contour-cover-point edges index 1))) (height (cdr (lw-euler-contour-cover-point edges index 1))) (radius (* 1/2 (car (lw-euler-contour-cover-point edges index 1))))
        (left-anchor (lw-euler-contour-anchor (lw-euler-contour-edge-patch (nth index edges))))
        (right-anchor (lw-euler-contour-anchor (lw-euler-contour-edge-patch (nth (lw-euler-contour-successor edges index) edges))))))
 :in-theory (union-theories
 '(lw-euler-contour-cover-value lw-euler-contour-cover-point lw-complex-segment-endpoints lw-euler-contour-pointp lw-ecl-left-commutes lw-ecl-left-distributes lw-ecl-fold-constants lw-ecl-times-negative lw-ecl-negative-times lw-ecl-zero-times lw-ecl-minus-one lw-ecl-double-negative lw-ecl-add-cancel lw-ecl-double lw-ecl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))


