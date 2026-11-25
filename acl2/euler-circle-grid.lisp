; Uniform rational grids construct circular covers from finite coarse checks.
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
(local (defthm lw-ecg-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ecg-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ecg-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ecg-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ecg-times-negative (a b) (b a)))
                 :in-theory (disable lw-ecg-times-negative)))))

(local (defthm lw-ecg-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ecg-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ecg-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ecg-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ecg-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ecg-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ecg-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ecg-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecg-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecg-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ecg-left-commutes)))))
(defun lw-circle-grid-parameter (count index) (+ -2 (* 4 index (/ count))))
(defun lw-circle-grid-midpoint (count index) (+ -2 (* (+ (* 4 index) 2) (/ count))))
(defun lw-circle-grid-reach (radius count) (* 2 radius (/ count)))
(defun lw-circle-grid-point (center radius sign count index)
 (lw-complex-circle-point center radius sign (lw-circle-grid-midpoint count index)))
(defun lw-euler-circle-grid-patch (center radius sign count error index)
 (let ((point (lw-circle-grid-point center radius sign count index)))
 (lw-euler-contour-patch (car point) (cdr point) (* 1/2 (car point)) error)))
(defun lw-euler-circle-grid-arc (center radius sign count error index)
 (lw-euler-circle-arc sign (lw-circle-grid-parameter count index) (lw-circle-grid-parameter count (+ 1 index))
 (lw-euler-circle-grid-patch center radius sign count error index)))
(defun lw-euler-circle-grid-node-check (center radius sign count error index)
 (let ((point (lw-circle-grid-point center radius sign count index)))
 (and (lw-euler-value-clearance-check (car point) (cdr point) error)
 (<= (lw-circle-grid-reach radius count)
     (lw-euler-contour-radius (lw-euler-circle-grid-patch center radius sign count error index))))))
(defun lw-euler-circle-grid-arcs (center radius sign count error offset remaining)
 (declare (xargs :measure (nfix remaining) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (zp remaining) nil
 (cons (lw-euler-circle-grid-arc center radius sign count error offset)
       (lw-euler-circle-grid-arcs center radius sign count error (+ 1 offset) (- remaining 1)))))
(defun lw-euler-circle-grid-check (center radius sign count error offset remaining)
 (declare (xargs :measure (nfix remaining) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (zp remaining) t
 (and (lw-euler-circle-grid-node-check center radius sign count error offset)
      (lw-euler-circle-grid-check center radius sign count error (+ 1 offset) (- remaining 1)))))
(defun lw-euler-circle-grid (center radius count error)
 (list (lw-euler-circle-grid-arcs center radius 1 count error 0 count)
       (lw-euler-circle-grid-arcs center radius -1 count error 0 count)))
(local (in-theory (disable lw-circle-grid-parameter lw-circle-grid-midpoint lw-circle-grid-reach lw-circle-grid-point lw-euler-circle-grid-patch lw-euler-circle-grid-arc lw-euler-circle-grid-node-check lw-euler-circle-grid-arcs lw-euler-circle-grid-check lw-euler-circle-grid lw-euler-circle-coverp lw-euler-circle-chart-coverp lw-euler-circle-arcp
 lw-euler-circle-arc lw-euler-circle-arc-sign lw-euler-circle-arc-left lw-euler-circle-arc-right lw-euler-circle-arc-midpoint lw-euler-circle-arc-reach lw-euler-circle-arc-point lw-euler-circle-arc-patch
 lw-euler-contour-patch lw-euler-contour-patchp lw-euler-contour-center lw-euler-contour-radius)))

(local (defthm lw-ecg-inverse-positive
 (implies (posp count) (< 0 (/ count)))
 :hints (("Goal" :use ((:instance inverse-of-* (x count)))
 :in-theory (union-theories
 '( lw-ecg-left-commutes lw-ecg-left-distributes lw-ecg-fold-constants lw-ecg-times-negative lw-ecg-negative-times lw-ecg-zero-times lw-ecg-minus-one lw-ecg-double-negative lw-ecg-add-cancel lw-ecg-double lw-ecg-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :nonlinearp t))
 :rule-classes nil))
(defthm lw-circle-grid-parameter-data
 (implies (and (posp count) (natp index) (<= index count))
 (and (rationalp (lw-circle-grid-parameter count index))
      (<= -2 (lw-circle-grid-parameter count index))
      (<= (lw-circle-grid-parameter count index) 2)))
 :hints (("Goal"
 :use (lw-ecg-inverse-positive
       (:instance inverse-of-* (x count))
       (:instance lw-ecg-multiply-order (a 0) (b index) (factor (/ count)))
       (:instance lw-ecg-multiply-order (a index) (b count) (factor (/ count))))
 :in-theory (union-theories
 '(lw-circle-grid-parameter lw-ecg-left-commutes lw-ecg-left-distributes lw-ecg-fold-constants lw-ecg-times-negative lw-ecg-negative-times lw-ecg-zero-times lw-ecg-minus-one lw-ecg-double-negative lw-ecg-add-cancel lw-ecg-double lw-ecg-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))
(defthm lw-circle-grid-endpoints
 (implies (posp count)
 (and (equal (lw-circle-grid-parameter count 0) -2)
      (equal (lw-circle-grid-parameter count count) 2)))
 :hints (("Goal" :use ((:instance inverse-of-* (x count)))
 :in-theory (union-theories
 '(lw-circle-grid-parameter lw-ecg-left-commutes lw-ecg-left-distributes lw-ecg-fold-constants lw-ecg-times-negative lw-ecg-negative-times lw-ecg-zero-times lw-ecg-minus-one lw-ecg-double-negative lw-ecg-add-cancel lw-ecg-double lw-ecg-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))
(defthm lw-circle-grid-cell-data
 (implies (and (posp count) (natp index) (< index count) (rationalp radius) (< 0 radius))
 (and (rationalp (lw-circle-grid-midpoint count index))
      (rationalp (lw-circle-grid-reach radius count)) (< 0 (lw-circle-grid-reach radius count))
      (equal (lw-circle-grid-midpoint count index)
             (* 1/2 (+ (lw-circle-grid-parameter count index) (lw-circle-grid-parameter count (+ 1 index)))))
      (equal (lw-circle-grid-reach radius count)
             (* 1/2 radius (- (lw-circle-grid-parameter count (+ 1 index)) (lw-circle-grid-parameter count index))))
      (<= -2 (lw-circle-grid-parameter count index))
      (< (lw-circle-grid-parameter count index) (lw-circle-grid-parameter count (+ 1 index)))
      (<= (lw-circle-grid-parameter count (+ 1 index)) 2)))
 :hints (("Goal"
 :use (lw-ecg-inverse-positive lw-circle-grid-parameter-data
       (:instance lw-circle-grid-parameter-data (index (+ 1 index)))
       (:instance lw-ecg-positive-product (a radius) (b (/ count))))
 :in-theory (union-theories
 '(lw-circle-grid-parameter lw-circle-grid-midpoint lw-circle-grid-reach lw-ecg-left-commutes lw-ecg-left-distributes lw-ecg-fold-constants lw-ecg-times-negative lw-ecg-negative-times lw-ecg-zero-times lw-ecg-minus-one lw-ecg-double-negative lw-ecg-add-cancel lw-ecg-double lw-ecg-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))
(defthm lw-circle-grid-point-rational
 (implies (and (lw-complexp center) (rationalp radius) (rationalp sign) (posp count) (natp index))
 (lw-complexp (lw-circle-grid-point center radius sign count index)))
 :hints (("Goal"
 :use ((:instance lw-complex-circle-point-rational (parameter (lw-circle-grid-midpoint count index))))
 :in-theory (union-theories
 '(lw-circle-grid-point lw-circle-grid-midpoint lw-ecg-left-commutes lw-ecg-left-distributes lw-ecg-fold-constants lw-ecg-times-negative lw-ecg-negative-times lw-ecg-zero-times lw-ecg-minus-one lw-ecg-double-negative lw-ecg-add-cancel lw-ecg-double lw-ecg-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))


(defthm lw-euler-circle-grid-arc-data
 (implies (and (lw-complexp center) (rationalp radius) (< 0 radius) (or (equal sign 1) (equal sign -1)) (posp count) (natp index) (< index count))
 (and (true-listp (lw-euler-circle-grid-arc center radius sign count error index)) (equal (len (lw-euler-circle-grid-arc center radius sign count error index)) 4)
      (equal (lw-euler-circle-arc-sign (lw-euler-circle-grid-arc center radius sign count error index)) sign)
      (equal (lw-euler-circle-arc-left (lw-euler-circle-grid-arc center radius sign count error index)) (lw-circle-grid-parameter count index))
      (equal (lw-euler-circle-arc-right (lw-euler-circle-grid-arc center radius sign count error index)) (lw-circle-grid-parameter count (+ 1 index)))
      (equal (lw-euler-circle-arc-midpoint (lw-euler-circle-grid-arc center radius sign count error index)) (lw-circle-grid-midpoint count index))
      (equal (lw-euler-circle-arc-reach radius (lw-euler-circle-grid-arc center radius sign count error index)) (lw-circle-grid-reach radius count))
      (equal (lw-euler-circle-arc-patch (lw-euler-circle-grid-arc center radius sign count error index)) (lw-euler-circle-grid-patch center radius sign count error index))
      (equal (lw-euler-contour-center (lw-euler-circle-grid-patch center radius sign count error index)) (lw-circle-grid-point center radius sign count index))
      (equal (lw-euler-circle-arc-point center radius (lw-euler-circle-grid-arc center radius sign count error index) (lw-euler-circle-arc-midpoint (lw-euler-circle-grid-arc center radius sign count error index))) (lw-circle-grid-point center radius sign count index))))
 :hints (("Goal" :use (lw-circle-grid-cell-data lw-circle-grid-point-rational)
 :in-theory (union-theories
 '(lw-euler-circle-grid-arc lw-euler-circle-grid-patch lw-euler-contour-patch lw-euler-contour-center lw-euler-circle-arc lw-euler-circle-arc-sign lw-euler-circle-arc-left lw-euler-circle-arc-right lw-euler-circle-arc-patch lw-euler-circle-arc-midpoint lw-euler-circle-arc-reach lw-euler-circle-arc-point lw-circle-grid-point lw-complexp true-listp len nth endp lw-ecg-left-commutes lw-ecg-left-distributes lw-ecg-fold-constants lw-ecg-times-negative lw-ecg-negative-times lw-ecg-zero-times lw-ecg-minus-one lw-ecg-double-negative lw-ecg-add-cancel lw-ecg-double lw-ecg-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t))
 :rule-classes nil)

(defthm lw-euler-circle-grid-node-patch-valid
 (implies (and (lw-complexp center) (rationalp radius) (< 0 radius) (or (equal sign 1) (equal sign -1)) (posp count) (natp index) (< index count) (lw-euler-circle-grid-node-check center radius sign count error index))
 (lw-euler-contour-patchp (lw-euler-circle-grid-patch center radius sign count error index)))
 :hints (("Goal"
 :use ((:instance lw-euler-value-clearance-data (rate (car (lw-circle-grid-point center radius sign count index))) (height (cdr (lw-circle-grid-point center radius sign count index))) (anchor-error error))
       (:instance lw-euler-contour-patch-valid (rate (car (lw-circle-grid-point center radius sign count index))) (height (cdr (lw-circle-grid-point center radius sign count index))) (outer-radius (* 1/2 (car (lw-circle-grid-point center radius sign count index)))) (anchor-error error)))
 :in-theory (union-theories
 '(lw-euler-circle-grid-patch lw-euler-circle-grid-node-check lw-ecg-left-commutes lw-ecg-left-distributes lw-ecg-fold-constants lw-ecg-times-negative lw-ecg-negative-times lw-ecg-zero-times lw-ecg-minus-one lw-ecg-double-negative lw-ecg-add-cancel lw-ecg-double lw-ecg-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-euler-circle-grid-arc-valid
 (implies (and (lw-complexp center) (rationalp radius) (< 0 radius) (or (equal sign 1) (equal sign -1)) (posp count) (natp index) (< index count) (lw-euler-circle-grid-node-check center radius sign count error index))
 (lw-euler-circle-arcp center radius (lw-euler-circle-grid-arc center radius sign count error index)))
 :hints (("Goal"
 :use (lw-circle-grid-parameter-data
       (:instance lw-circle-grid-parameter-data (index (+ 1 index)))
       lw-circle-grid-cell-data lw-circle-grid-point-rational lw-euler-circle-grid-arc-data lw-euler-circle-grid-node-patch-valid
       (:instance lw-euler-contour-patch-data (patch (lw-euler-circle-grid-patch center radius sign count error index)))
       (:instance lw-complex-zero-disk (radius (- (lw-euler-contour-radius (lw-euler-circle-grid-patch center radius sign count error index)) (lw-circle-grid-reach radius count)))))
 :in-theory (union-theories
 '(lw-euler-circle-arcp lw-euler-circle-grid-node-check lw-complexp lw-complex-sub lw-ecg-left-commutes lw-ecg-left-distributes lw-ecg-fold-constants lw-ecg-times-negative lw-ecg-negative-times lw-ecg-zero-times lw-ecg-minus-one lw-ecg-double-negative lw-ecg-add-cancel lw-ecg-double lw-ecg-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))


(defthm lw-euler-circle-grid-arcs-data
 (implies (natp remaining) (and (true-listp (lw-euler-circle-grid-arcs center radius sign count error offset remaining)) (equal (len (lw-euler-circle-grid-arcs center radius sign count error offset remaining)) remaining)))
 :hints (("Goal" :induct (lw-euler-circle-grid-arcs center radius sign count error offset remaining)
 :in-theory (union-theories
 '(lw-euler-circle-grid-arcs true-listp len endp lw-ecg-left-commutes lw-ecg-left-distributes lw-ecg-fold-constants lw-ecg-times-negative lw-ecg-negative-times lw-ecg-zero-times lw-ecg-minus-one lw-ecg-double-negative lw-ecg-add-cancel lw-ecg-double lw-ecg-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-ecg-arc-fields
 (and (equal (lw-euler-circle-arc-sign (lw-euler-circle-grid-arc center radius sign count error index)) sign)
      (equal (lw-euler-circle-arc-left (lw-euler-circle-grid-arc center radius sign count error index)) (lw-circle-grid-parameter count index))
      (equal (lw-euler-circle-arc-right (lw-euler-circle-grid-arc center radius sign count error index)) (lw-circle-grid-parameter count (+ 1 index))))
 :hints (("Goal" :in-theory (union-theories
 '(lw-euler-circle-grid-arc lw-euler-circle-arc lw-euler-circle-arc-sign lw-euler-circle-arc-left lw-euler-circle-arc-right nth endp lw-ecg-left-commutes lw-ecg-left-distributes lw-ecg-fold-constants lw-ecg-times-negative lw-ecg-negative-times lw-ecg-zero-times lw-ecg-minus-one lw-ecg-double-negative lw-ecg-add-cancel lw-ecg-double lw-ecg-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-euler-circle-grid-chart-valid
 (implies (and (lw-complexp center) (rationalp radius) (< 0 radius) (or (equal sign 1) (equal sign -1)) (posp count) (natp offset) (natp remaining) (equal (+ offset remaining) count)
 (lw-euler-circle-grid-check center radius sign count error offset remaining))
 (lw-euler-circle-chart-coverp center radius sign (lw-euler-circle-grid-arcs center radius sign count error offset remaining) (lw-circle-grid-parameter count offset)))
 :hints (("Goal" :induct (lw-euler-circle-grid-arcs center radius sign count error offset remaining)
 :in-theory (union-theories
 '(lw-ecg-arc-fields lw-circle-grid-endpoints lw-circle-grid-parameter-data lw-euler-circle-grid-arc-valid lw-euler-circle-grid-arcs lw-euler-circle-grid-check lw-euler-circle-chart-coverp endp lw-ecg-left-commutes lw-ecg-left-distributes lw-ecg-fold-constants lw-ecg-times-negative lw-ecg-negative-times lw-ecg-zero-times lw-ecg-minus-one lw-ecg-double-negative lw-ecg-add-cancel lw-ecg-double lw-ecg-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))
 :rule-classes nil)

(defthm lw-euler-circle-grid-valid
 (implies (and (lw-complexp center) (rationalp radius) (< 0 radius) (posp count)
 (lw-euler-circle-grid-check center radius 1 count error 0 count)
 (lw-euler-circle-grid-check center radius -1 count error 0 count))
 (and (lw-euler-circle-coverp center radius (car (lw-euler-circle-grid center radius count error)) (cadr (lw-euler-circle-grid center radius count error)))
      (true-listp (car (lw-euler-circle-grid center radius count error))) (true-listp (cadr (lw-euler-circle-grid center radius count error))) (equal (len (car (lw-euler-circle-grid center radius count error))) count) (equal (len (cadr (lw-euler-circle-grid center radius count error))) count)))
 :hints (("Goal"
 :use (lw-circle-grid-endpoints
       (:instance lw-euler-circle-grid-chart-valid (sign 1) (offset 0) (remaining count))
       (:instance lw-euler-circle-grid-chart-valid (sign -1) (offset 0) (remaining count))
       (:instance lw-euler-circle-grid-arcs-data (sign 1) (offset 0) (remaining count))
       (:instance lw-euler-circle-grid-arcs-data (sign -1) (offset 0) (remaining count)))
 :in-theory (union-theories
 '(lw-euler-circle-grid lw-euler-circle-coverp lw-ecg-left-commutes lw-ecg-left-distributes lw-ecg-fold-constants lw-ecg-times-negative lw-ecg-negative-times lw-ecg-zero-times lw-ecg-minus-one lw-ecg-double-negative lw-ecg-add-cancel lw-ecg-double lw-ecg-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes nil)

(defthm lw-euler-circle-grid-cauchy-sample
 (implies (and (lw-complexp center) (rationalp radius) (< 0 radius) (posp count)
 (lw-euler-circle-grid-check center radius 1 count error 0 count)
 (lw-euler-circle-grid-check center radius -1 count error 0 count)
 (natp degree) (natp sample) (rationalp value-error) (< 0 value-error) (<= value-error 1))
 (and (lw-euler-contour-patchp (lw-euler-circle-cover-patch (lw-complex-power (lw-cauchy-orbit-rotation degree) sample) (car (lw-euler-circle-grid center radius count error)) (cadr (lw-euler-circle-grid center radius count error))))
      (lw-euler-contour-pointp (lw-euler-circle-cover-patch (lw-complex-power (lw-cauchy-orbit-rotation degree) sample) (car (lw-euler-circle-grid center radius count error)) (cadr (lw-euler-circle-grid center radius count error))) (lw-complex-add center (lw-complex-scale radius (lw-complex-power (lw-cauchy-orbit-rotation degree) sample))))
      (lw-euler-value-clearance-check (car (lw-complex-add center (lw-complex-scale radius (lw-complex-power (lw-cauchy-orbit-rotation degree) sample)))) (cdr (lw-complex-add center (lw-complex-scale radius (lw-complex-power (lw-cauchy-orbit-rotation degree) sample)))) (lw-euler-contour-anchor (lw-euler-circle-cover-patch (lw-complex-power (lw-cauchy-orbit-rotation degree) sample) (car (lw-euler-circle-grid center radius count error)) (cadr (lw-euler-circle-grid center radius count error)))))
      (rationalp (lw-euler-circle-cover-cap (car (lw-euler-circle-grid center radius count error)) (cadr (lw-euler-circle-grid center radius count error)))) (< 0 (lw-euler-circle-cover-cap (car (lw-euler-circle-grid center radius count error)) (cadr (lw-euler-circle-grid center radius count error))))
      (lw-complex-diskp (lw-euler-circle-value center radius (car (lw-euler-circle-grid center radius count error)) (cadr (lw-euler-circle-grid center radius count error)) (lw-complex-power (lw-cauchy-orbit-rotation degree) sample) value-error) (+ 1 (lw-euler-circle-cover-cap (car (lw-euler-circle-grid center radius count error)) (cadr (lw-euler-circle-grid center radius count error)))))))
 :hints (("Goal"
 :use (lw-euler-circle-grid-valid lw-cauchy-orbit-data
       (:instance lw-cauchy-orbit-power-norm-one (index sample))
       (:instance lw-complex-power-rational (point (lw-cauchy-orbit-rotation degree)) (index sample))
       (:instance lw-euler-circle-cover-data (plus-arcs (car (lw-euler-circle-grid center radius count error))) (minus-arcs (cadr (lw-euler-circle-grid center radius count error))))
       (:instance lw-euler-circle-cover-cauchy-sample (plus-arcs (car (lw-euler-circle-grid center radius count error))) (minus-arcs (cadr (lw-euler-circle-grid center radius count error))))
       (:instance lw-euler-circle-value-cap (plus-arcs (car (lw-euler-circle-grid center radius count error))) (minus-arcs (cadr (lw-euler-circle-grid center radius count error))) (point (lw-complex-power (lw-cauchy-orbit-rotation degree) sample))))
 :in-theory (union-theories
 '( lw-ecg-left-commutes lw-ecg-left-distributes lw-ecg-fold-constants lw-ecg-times-negative lw-ecg-negative-times lw-ecg-zero-times lw-ecg-minus-one lw-ecg-double-negative lw-ecg-add-cancel lw-ecg-double lw-ecg-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes nil)



