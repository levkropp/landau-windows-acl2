; Finite chart chains compute a covering patch for every rational circle point.
(in-package "ACL2")
(include-book "euler-circle-arcs")
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
(local (defthm lw-ecv-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ecv-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ecv-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ecv-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ecv-times-negative (a b) (b a)))
                 :in-theory (disable lw-ecv-times-negative)))))

(local (defthm lw-ecv-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ecv-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ecv-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ecv-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ecv-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ecv-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ecv-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ecv-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecv-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecv-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ecv-left-commutes)))))
(defun lw-euler-circle-chart-coverp (center radius sign arcs left)
 (if (endp arcs) (and (equal arcs nil) (equal left 2))
 (and (rationalp left) (<= -2 left)
      (lw-euler-circle-arcp center radius (car arcs))
      (equal (lw-euler-circle-arc-sign (car arcs)) sign)
      (equal (lw-euler-circle-arc-left (car arcs)) left)
      (lw-euler-circle-chart-coverp center radius sign (cdr arcs) (lw-euler-circle-arc-right (car arcs))))))
(defun lw-euler-circle-chart-index (arcs parameter)
 (if (endp arcs) 0
  (if (<= parameter (lw-euler-circle-arc-right (car arcs))) 0
   (+ 1 (lw-euler-circle-chart-index (cdr arcs) parameter)))))
(defun lw-euler-circle-chart-cap (arcs)
 (if (endp arcs) 0
 (+ (lw-euler-contour-cap (lw-euler-circle-arc-patch (car arcs))) (lw-euler-circle-chart-cap (cdr arcs)))))
(defun lw-euler-circle-coverp (center radius plus-arcs minus-arcs)
 (and (lw-complexp center) (rationalp radius) (< 0 radius)
 (lw-euler-circle-chart-coverp center radius 1 plus-arcs -2)
 (lw-euler-circle-chart-coverp center radius -1 minus-arcs -2)))
(defun lw-euler-circle-cover-arcs (point plus-arcs minus-arcs)
 (if (equal (lw-unit-circle-sign point) 1) plus-arcs minus-arcs))
(defun lw-euler-circle-cover-index (point plus-arcs minus-arcs)
 (lw-euler-circle-chart-index (lw-euler-circle-cover-arcs point plus-arcs minus-arcs) (lw-unit-circle-parameter point)))
(defun lw-euler-circle-cover-arc (point plus-arcs minus-arcs)
 (nth (lw-euler-circle-cover-index point plus-arcs minus-arcs) (lw-euler-circle-cover-arcs point plus-arcs minus-arcs)))
(defun lw-euler-circle-cover-patch (point plus-arcs minus-arcs)
 (lw-euler-circle-arc-patch (lw-euler-circle-cover-arc point plus-arcs minus-arcs)))
(defun lw-euler-circle-cover-cap (plus-arcs minus-arcs)
 (+ 1 (lw-euler-circle-chart-cap plus-arcs) (lw-euler-circle-chart-cap minus-arcs)))
(local (in-theory (disable lw-euler-circle-chart-coverp lw-euler-circle-chart-index lw-euler-circle-chart-cap lw-euler-circle-coverp lw-euler-circle-cover-arcs lw-euler-circle-cover-index lw-euler-circle-cover-arc lw-euler-circle-cover-patch lw-euler-circle-cover-cap lw-euler-circle-arcp
 lw-euler-circle-arc-point lw-euler-circle-arc-sign lw-euler-circle-arc-left lw-euler-circle-arc-right lw-euler-circle-arc-patch
 lw-euler-contour-patchp lw-euler-contour-pointp lw-euler-contour-cap lw-euler-contour-radius lw-euler-contour-center lw-euler-contour-anchor)))

(local (defthm lw-ecv-length-natural (natp (len values))
 :hints (("Goal" :induct (len values) :in-theory (union-theories
 '(len endp lw-ecv-left-commutes lw-ecv-left-distributes lw-ecv-fold-constants lw-ecv-times-negative lw-ecv-negative-times lw-ecv-zero-times lw-ecv-minus-one lw-ecv-double-negative lw-ecv-add-cancel lw-ecv-double lw-ecv-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-euler-circle-chart-index-natural
 (natp (lw-euler-circle-chart-index arcs parameter))
 :hints (("Goal" :induct (lw-euler-circle-chart-index arcs parameter)
 :in-theory (union-theories
 '(lw-euler-circle-chart-index lw-ecv-left-commutes lw-ecv-left-distributes lw-ecv-fold-constants lw-ecv-times-negative lw-ecv-negative-times lw-ecv-zero-times lw-ecv-minus-one lw-ecv-double-negative lw-ecv-add-cancel lw-ecv-double lw-ecv-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-euler-circle-chart-cap-data
 (implies (lw-euler-circle-chart-coverp center radius sign arcs left)
 (and (true-listp arcs) (rationalp (lw-euler-circle-chart-cap arcs)) (<= 0 (lw-euler-circle-chart-cap arcs))))
 :hints (("Goal" :induct (lw-euler-circle-chart-coverp center radius sign arcs left)
 :in-theory (union-theories
 '(lw-euler-circle-chart-coverp lw-euler-circle-chart-cap true-listp endp lw-ecv-left-commutes lw-ecv-left-distributes lw-ecv-fold-constants lw-ecv-times-negative lw-ecv-negative-times lw-ecv-zero-times lw-ecv-minus-one lw-ecv-double-negative lw-ecv-add-cancel lw-ecv-double lw-ecv-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
 (and stable-under-simplificationp
 '(:use ((:instance lw-euler-circle-arc-data (arc (car arcs)))
         (:instance lw-euler-contour-patch-data (patch (lw-euler-circle-arc-patch (car arcs)))))
 :do-not-induct t)))
 :rule-classes nil)

(defthm lw-euler-circle-chart-selection
 (implies (and (lw-euler-circle-chart-coverp center radius sign arcs left)
 (rationalp left) (< left 2) (rationalp parameter) (<= left parameter) (<= parameter 2))
 (let ((index (lw-euler-circle-chart-index arcs parameter)))
 (and (natp index) (< index (len arcs))
      (lw-euler-circle-arcp center radius (nth index arcs))
      (equal (lw-euler-circle-arc-sign (nth index arcs)) sign)
      (<= (lw-euler-circle-arc-left (nth index arcs)) parameter)
      (<= parameter (lw-euler-circle-arc-right (nth index arcs))))))
 :hints (("Goal" :induct (lw-euler-circle-chart-coverp center radius sign arcs left)
 :in-theory (union-theories
 '(lw-euler-circle-chart-coverp lw-euler-circle-chart-index nth len endp lw-ecv-left-commutes lw-ecv-left-distributes lw-ecv-fold-constants lw-ecv-times-negative lw-ecv-negative-times lw-ecv-zero-times lw-ecv-minus-one lw-ecv-double-negative lw-ecv-add-cancel lw-ecv-double lw-ecv-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
 (and stable-under-simplificationp
 '(:use ((:instance lw-euler-circle-arc-data (arc (car arcs)))
         (:instance lw-euler-circle-chart-index-natural (arcs (cdr arcs)))
         (:instance lw-ecv-length-natural (values (cdr arcs))))
 :do-not-induct t)))
 :rule-classes nil)


(local (defun lw-ecv-nth-induct (arcs left index)
 (declare (xargs :measure (acl2-count arcs) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (or (endp arcs) (zp index)) (list arcs left index)
 (lw-ecv-nth-induct (cdr arcs) (lw-euler-circle-arc-right (car arcs)) (- index 1)))))

(defthm lw-euler-circle-chart-nth-data
 (implies (and (lw-euler-circle-chart-coverp center radius sign arcs left)
 (natp index) (< index (len arcs)))
 (and (lw-euler-circle-arcp center radius (nth index arcs))
      (equal (lw-euler-circle-arc-sign (nth index arcs)) sign)
      (<= (lw-euler-contour-cap (lw-euler-circle-arc-patch (nth index arcs))) (lw-euler-circle-chart-cap arcs))))
 :hints (("Goal" :induct (lw-ecv-nth-induct arcs left index)
 :in-theory (union-theories
 '((:induction lw-ecv-nth-induct) lw-euler-circle-chart-coverp lw-euler-circle-chart-cap nth len endp lw-ecv-left-commutes lw-ecv-left-distributes lw-ecv-fold-constants lw-ecv-times-negative lw-ecv-negative-times lw-ecv-zero-times lw-ecv-minus-one lw-ecv-double-negative lw-ecv-add-cancel lw-ecv-double lw-ecv-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
 (and stable-under-simplificationp
 '(:use ((:instance lw-euler-circle-arc-data (arc (car arcs)))
         (:instance lw-euler-contour-patch-data (patch (lw-euler-circle-arc-patch (car arcs))))
         (:instance lw-euler-circle-chart-cap-data (arcs (cdr arcs)) (left (lw-euler-circle-arc-right (car arcs)))))
 :do-not-induct t)))
 :rule-classes nil)

(defthm lw-euler-circle-cover-data
 (implies (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
 (and (lw-complexp center) (rationalp radius) (< 0 radius)
      (true-listp plus-arcs) (true-listp minus-arcs)
      (rationalp (lw-euler-circle-cover-cap plus-arcs minus-arcs)) (< 0 (lw-euler-circle-cover-cap plus-arcs minus-arcs))
      (<= (lw-euler-circle-chart-cap plus-arcs) (lw-euler-circle-cover-cap plus-arcs minus-arcs))
      (<= (lw-euler-circle-chart-cap minus-arcs) (lw-euler-circle-cover-cap plus-arcs minus-arcs))))
 :hints (("Goal"
 :use ((:instance lw-euler-circle-chart-cap-data (sign 1) (arcs plus-arcs) (left -2))
       (:instance lw-euler-circle-chart-cap-data (sign -1) (arcs minus-arcs) (left -2)))
 :in-theory (union-theories
 '(lw-euler-circle-coverp lw-euler-circle-cover-cap lw-ecv-left-commutes lw-ecv-left-distributes lw-ecv-fold-constants lw-ecv-times-negative lw-ecv-negative-times lw-ecv-zero-times lw-ecv-minus-one lw-ecv-double-negative lw-ecv-add-cancel lw-ecv-double lw-ecv-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t))
 :rule-classes nil)

(defthm lw-euler-circle-cover-selection
 (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
 (lw-complexp point) (equal (lw-complex-norm-square point) 1))
 (and (natp (lw-euler-circle-cover-index point plus-arcs minus-arcs)) (< (lw-euler-circle-cover-index point plus-arcs minus-arcs) (len (lw-euler-circle-cover-arcs point plus-arcs minus-arcs)))
      (lw-euler-circle-arcp center radius (lw-euler-circle-cover-arc point plus-arcs minus-arcs))
      (equal (lw-euler-circle-arc-sign (lw-euler-circle-cover-arc point plus-arcs minus-arcs)) (lw-unit-circle-sign point))
      (<= (lw-euler-circle-arc-left (lw-euler-circle-cover-arc point plus-arcs minus-arcs)) (lw-unit-circle-parameter point))
      (<= (lw-unit-circle-parameter point) (lw-euler-circle-arc-right (lw-euler-circle-cover-arc point plus-arcs minus-arcs)))))
 :hints (("Goal"
 :cases ((equal (lw-unit-circle-sign point) 1))
 :use (lw-unit-circle-chart-data
       (:instance lw-euler-circle-chart-selection (sign 1) (arcs plus-arcs) (left -2) (parameter (lw-unit-circle-parameter point)))
       (:instance lw-euler-circle-chart-selection (sign -1) (arcs minus-arcs) (left -2) (parameter (lw-unit-circle-parameter point))))
 :in-theory (union-theories
 '(lw-euler-circle-coverp lw-euler-circle-cover-index lw-euler-circle-cover-arcs lw-euler-circle-cover-arc lw-ecv-left-commutes lw-ecv-left-distributes lw-ecv-fold-constants lw-ecv-times-negative lw-ecv-negative-times lw-ecv-zero-times lw-ecv-minus-one lw-ecv-double-negative lw-ecv-add-cancel lw-ecv-double lw-ecv-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t))
 :rule-classes nil)

(defthm lw-euler-circle-cover-selected-cap
 (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
 (lw-complexp point) (equal (lw-complex-norm-square point) 1))
 (and (lw-euler-contour-patchp (lw-euler-circle-cover-patch point plus-arcs minus-arcs))
      (rationalp (lw-euler-contour-cap (lw-euler-circle-cover-patch point plus-arcs minus-arcs)))
      (< 0 (lw-euler-contour-cap (lw-euler-circle-cover-patch point plus-arcs minus-arcs)))
      (<= (lw-euler-contour-cap (lw-euler-circle-cover-patch point plus-arcs minus-arcs)) (lw-euler-circle-cover-cap plus-arcs minus-arcs))))
 :hints (("Goal"
 :cases ((equal (lw-unit-circle-sign point) 1))
 :use (lw-euler-circle-cover-data lw-euler-circle-cover-selection
       (:instance lw-euler-circle-arc-data (arc (lw-euler-circle-cover-arc point plus-arcs minus-arcs)))
       (:instance lw-euler-contour-patch-data (patch (lw-euler-circle-cover-patch point plus-arcs minus-arcs)))
       (:instance lw-euler-circle-chart-nth-data (sign 1) (arcs plus-arcs) (left -2) (index (lw-euler-circle-cover-index point plus-arcs minus-arcs)))
       (:instance lw-euler-circle-chart-nth-data (sign -1) (arcs minus-arcs) (left -2) (index (lw-euler-circle-cover-index point plus-arcs minus-arcs))))
 :in-theory (union-theories
 '(lw-euler-circle-coverp lw-euler-circle-cover-patch lw-euler-circle-cover-arcs lw-euler-circle-cover-arc lw-ecv-left-commutes lw-ecv-left-distributes lw-ecv-fold-constants lw-ecv-times-negative lw-ecv-negative-times lw-ecv-zero-times lw-ecv-minus-one lw-ecv-double-negative lw-ecv-add-cancel lw-ecv-double lw-ecv-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t))
 :rule-classes nil)

(defthm lw-euler-circle-cover-coverage
 (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
 (lw-complexp point) (equal (lw-complex-norm-square point) 1))
 (lw-euler-contour-pointp (lw-euler-circle-cover-patch point plus-arcs minus-arcs) (lw-complex-add center (lw-complex-scale radius point))))
 :hints (("Goal"
 :use (lw-euler-circle-cover-data lw-euler-circle-cover-selection lw-unit-circle-chart-data
       (:instance lw-euler-circle-arc-coverage (arc (lw-euler-circle-cover-arc point plus-arcs minus-arcs)) (parameter (lw-unit-circle-parameter point)))
       (:instance lw-complex-circle-chart-reconstruction))
 :in-theory (union-theories
 '(lw-euler-circle-cover-patch lw-euler-circle-arc-point lw-ecv-left-commutes lw-ecv-left-distributes lw-ecv-fold-constants lw-ecv-times-negative lw-ecv-negative-times lw-ecv-zero-times lw-ecv-minus-one lw-ecv-double-negative lw-ecv-add-cancel lw-ecv-double lw-ecv-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-euler-circle-cover-shifted-check
 (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
 (lw-complexp point) (equal (lw-complex-norm-square point) 1))
 (and (lw-complexp (lw-complex-add center (lw-complex-scale radius point))) (rationalp (car (lw-complex-add center (lw-complex-scale radius point)))) (< 0 (car (lw-complex-add center (lw-complex-scale radius point)))) (rationalp (cdr (lw-complex-add center (lw-complex-scale radius point))))
      (lw-euler-value-clearance-check (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) (lw-euler-contour-anchor (lw-euler-circle-cover-patch point plus-arcs minus-arcs)))))
 :hints (("Goal"
 :use (lw-euler-circle-cover-selected-cap lw-euler-circle-cover-coverage
       (:instance lw-euler-contour-point-data (patch (lw-euler-circle-cover-patch point plus-arcs minus-arcs)) (point (lw-complex-add center (lw-complex-scale radius point)))))
 :in-theory (union-theories
 '( lw-ecv-left-commutes lw-ecv-left-distributes lw-ecv-fold-constants lw-ecv-times-negative lw-ecv-negative-times lw-ecv-zero-times lw-ecv-minus-one lw-ecv-double-negative lw-ecv-add-cancel lw-ecv-double lw-ecv-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes nil)


(defthm lw-euler-circle-cover-cauchy-sample
 (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs) (natp degree) (natp sample))
 (and (lw-euler-contour-patchp (lw-euler-circle-cover-patch (lw-complex-power (lw-cauchy-orbit-rotation degree) sample) plus-arcs minus-arcs))
      (lw-euler-contour-pointp (lw-euler-circle-cover-patch (lw-complex-power (lw-cauchy-orbit-rotation degree) sample) plus-arcs minus-arcs) (lw-complex-add center (lw-complex-scale radius (lw-complex-power (lw-cauchy-orbit-rotation degree) sample))))
      (rationalp (car (lw-complex-add center (lw-complex-scale radius (lw-complex-power (lw-cauchy-orbit-rotation degree) sample))))) (< 0 (car (lw-complex-add center (lw-complex-scale radius (lw-complex-power (lw-cauchy-orbit-rotation degree) sample))))) (rationalp (cdr (lw-complex-add center (lw-complex-scale radius (lw-complex-power (lw-cauchy-orbit-rotation degree) sample)))))
      (lw-euler-value-clearance-check (car (lw-complex-add center (lw-complex-scale radius (lw-complex-power (lw-cauchy-orbit-rotation degree) sample)))) (cdr (lw-complex-add center (lw-complex-scale radius (lw-complex-power (lw-cauchy-orbit-rotation degree) sample)))) (lw-euler-contour-anchor (lw-euler-circle-cover-patch (lw-complex-power (lw-cauchy-orbit-rotation degree) sample) plus-arcs minus-arcs)))))
 :hints (("Goal"
 :use (lw-cauchy-orbit-data lw-cauchy-orbit-power-norm-one
       (:instance lw-complex-power-rational (point (lw-cauchy-orbit-rotation degree)) (index sample))
       (:instance lw-cauchy-orbit-power-norm-one (index sample))
       (:instance lw-euler-circle-cover-selected-cap (point (lw-complex-power (lw-cauchy-orbit-rotation degree) sample)))
       (:instance lw-euler-circle-cover-coverage (point (lw-complex-power (lw-cauchy-orbit-rotation degree) sample)))
       (:instance lw-euler-circle-cover-shifted-check (point (lw-complex-power (lw-cauchy-orbit-rotation degree) sample))))
 :in-theory (union-theories
 '( lw-ecv-left-commutes lw-ecv-left-distributes lw-ecv-fold-constants lw-ecv-times-negative lw-ecv-negative-times lw-ecv-zero-times lw-ecv-minus-one lw-ecv-double-negative lw-ecv-add-cancel lw-ecv-double lw-ecv-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes nil)



