; Complete native Euler small-value covers on any square in the positive half-plane.
(in-package "ACL2")
(include-book "positive-square-disk")
(include-book "euler-square-clearance")
(include-book "polynomial-affine")
(local (in-theory (disable lw-complexp lw-complex-polynomial lw-complex-sub lw-complex-diskp
 lw-complex-euler-continuation-value lw-euler-uniform-polynomial lw-polynomial-affine
 lw-square-containsp lw-positive-squarep lw-positive-square-center-rate lw-positive-square-center-height
 lw-positive-square-disk-radius lw-positive-square-translation lw-positive-square-offset
 lw-square-cover-containsp lw-polynomial-resolved-cover lw-polynomial-resolved-cover-count lw-square-cell-address
 lw-euler-value-clearance-check lw-euler-value-clearance-size lw-euler-value-clearance-lower
 lw-complex-l1 lw-complex-norm-square lw-complex-reciprocal)))
(local (defthm lw-eps-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-eps-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-eps-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-eps-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-eps-times-negative (a b) (b a)))
                 :in-theory (disable lw-eps-times-negative)))))

(local (defthm lw-eps-zero-times (equal (* 0 a) 0)))

(local (defthm lw-eps-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-eps-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-eps-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-eps-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-eps-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-eps-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-eps-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-eps-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-eps-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-eps-left-commutes)))))
(defun lw-euler-positive-square-polynomial (anchor side error)
 (lw-polynomial-affine
  (lw-euler-uniform-polynomial (lw-positive-square-center-rate anchor side)
   (lw-positive-square-center-height anchor side) (lw-positive-square-disk-radius anchor side) 0 (/ error 4))
  (lw-positive-square-translation anchor side) (cons 1 0)))
(defun lw-euler-positive-square-cover-count (anchor side width error)
 (lw-polynomial-resolved-cover-count (lw-euler-positive-square-polynomial anchor side error) anchor side width error))
(defun lw-euler-positive-square-cover (anchor side width error)
 (lw-polynomial-resolved-cover (lw-euler-positive-square-polynomial anchor side error) anchor side width error))
(defun lw-euler-positive-square-uncoveredp (anchor side width error point)
 (and (lw-positive-squarep anchor side) (lw-square-containsp anchor side point)
      (rationalp width) (< 0 width) (rationalp error) (< 0 error)
      (not (lw-square-cover-containsp anchor side (lw-euler-positive-square-cover-count anchor side width error) point
       (lw-euler-positive-square-cover anchor side width error)))))
(local (in-theory (disable lw-euler-positive-square-polynomial lw-euler-positive-square-cover-count
 lw-euler-positive-square-cover lw-euler-positive-square-uncoveredp)))

(defthm lw-euler-positive-square-point-data
 (implies (and (lw-positive-squarep anchor side) (lw-square-containsp anchor side point))
 (and (rationalp (car point)) (< 0 (car point)) (rationalp (cdr point))))
 :hints (("Goal" :use lw-positive-square-point-data :in-theory (union-theories
 '(lw-complexp lw-eps-left-commutes lw-eps-left-distributes lw-eps-fold-constants lw-eps-times-negative lw-eps-negative-times lw-eps-zero-times lw-eps-minus-one lw-eps-double-negative lw-eps-add-cancel lw-eps-double lw-eps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-positive-square-polynomial-valid
 (implies (and (lw-positive-squarep anchor side) (rationalp error) (< 0 error))
 (lw-complex-coefficientsp (lw-euler-positive-square-polynomial anchor side error)))
 :hints (("Goal"
 :use (lw-positive-square-disk-data
       (:instance lw-euler-uniform-polynomial-valid
        (rate (lw-positive-square-center-rate anchor side)) (height (lw-positive-square-center-height anchor side))
        (radius (lw-positive-square-disk-radius anchor side)) (target 0) (error (/ error 4)))
       (:instance lw-polynomial-affine-valid
        (coefficients (lw-euler-uniform-polynomial (lw-positive-square-center-rate anchor side)
         (lw-positive-square-center-height anchor side) (lw-positive-square-disk-radius anchor side) 0 (/ error 4)))
        (center (lw-positive-square-translation anchor side)) (slope (cons 1 0))))
 :in-theory (union-theories
 '(lw-euler-positive-square-polynomial lw-positive-square-translation lw-complexp lw-eps-left-commutes lw-eps-left-distributes lw-eps-fold-constants lw-eps-times-negative lw-eps-negative-times lw-eps-zero-times lw-eps-minus-one lw-eps-double-negative lw-eps-add-cancel lw-eps-double lw-eps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-positive-square-polynomial-comparison
 (implies (and (lw-positive-squarep anchor side) (lw-square-containsp anchor side point)
 (rationalp error) (< 0 error) (rationalp value-error) (< 0 value-error))
 (lw-complex-diskp
 (lw-complex-sub (lw-complex-polynomial (lw-euler-positive-square-polynomial anchor side error) point 0)
                 (lw-complex-euler-continuation-value (car point) (cdr point) value-error))
 (+ (* 1/4 error) (* 1/4 value-error))))
 :hints (("Goal"
 :use (lw-positive-square-disk-data lw-positive-square-offset-in-disk
       lw-positive-square-coordinate-recovery lw-positive-square-affine-point
       (:instance lw-euler-uniform-polynomial-valid
        (rate (lw-positive-square-center-rate anchor side)) (height (lw-positive-square-center-height anchor side))
        (radius (lw-positive-square-disk-radius anchor side)) (target 0) (error (/ error 4)))
       (:instance lw-polynomial-affine-evaluation
        (coefficients (lw-euler-uniform-polynomial (lw-positive-square-center-rate anchor side)
         (lw-positive-square-center-height anchor side) (lw-positive-square-disk-radius anchor side) 0 (/ error 4)))
        (center (lw-positive-square-translation anchor side)) (slope (cons 1 0)))
       (:instance lw-complex-euler-uniform-polynomial-comparison
        (rate (lw-positive-square-center-rate anchor side)) (height (lw-positive-square-center-height anchor side))
        (radius (lw-positive-square-disk-radius anchor side)) (target 0) (error (/ error 4))
        (point (lw-positive-square-offset anchor side point))))
 :in-theory (union-theories
 '(lw-euler-positive-square-polynomial lw-square-containsp lw-complexp lw-eps-left-commutes lw-eps-left-distributes lw-eps-fold-constants lw-eps-times-negative lw-eps-negative-times lw-eps-zero-times lw-eps-minus-one lw-eps-double-negative lw-eps-add-cancel lw-eps-double lw-eps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-positive-square-cover-count-data
 (implies (and (lw-positive-squarep anchor side)
 (rationalp width) (< 0 width) (rationalp error) (< 0 error))
 (let ((count (lw-euler-positive-square-cover-count anchor side width error)))
 (and (posp count) (rationalp (lw-polynomial-grid-step side count))
      (< 0 (lw-polynomial-grid-step side count)) (<= (lw-polynomial-grid-step side count) width))))
 :hints (("Goal" :use (lw-euler-positive-square-polynomial-valid
       (:instance lw-polynomial-resolved-cover-count-data
        (coefficients (lw-euler-positive-square-polynomial anchor side error)) (epsilon error)))
 :in-theory (union-theories
 '(lw-positive-squarep lw-euler-positive-square-cover-count lw-eps-left-commutes lw-eps-left-distributes lw-eps-fold-constants lw-eps-times-negative lw-eps-negative-times lw-eps-zero-times lw-eps-minus-one lw-eps-double-negative lw-eps-add-cancel lw-eps-double lw-eps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-positive-square-cover-data
 (implies (and (lw-positive-squarep anchor side)
 (rationalp width) (< 0 width) (rationalp error) (< 0 error))
 (let ((count (lw-euler-positive-square-cover-count anchor side width error)))
 (and (lw-square-address-listp (lw-euler-positive-square-cover anchor side width error) count)
      (<= (len (lw-euler-positive-square-cover anchor side width error)) (* count count)))))
 :hints (("Goal" :use (lw-euler-positive-square-polynomial-valid
       (:instance lw-polynomial-resolved-cover-data
        (coefficients (lw-euler-positive-square-polynomial anchor side error)) (epsilon error)))
 :in-theory (union-theories
 '(lw-positive-squarep lw-euler-positive-square-cover-count lw-euler-positive-square-cover lw-eps-left-commutes lw-eps-left-distributes lw-eps-fold-constants lw-eps-times-negative lw-eps-negative-times lw-eps-zero-times lw-eps-minus-one lw-eps-double-negative lw-eps-add-cancel lw-eps-double lw-eps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(local (defthm lw-eps-near-transfer
 (implies (and (lw-complexp left) (lw-complexp right)
 (lw-complex-diskp (lw-complex-sub left right) radius))
 (and (implies (lw-complex-diskp left bound) (lw-complex-diskp right (+ bound radius)))
      (implies (lw-complex-diskp right bound) (lw-complex-diskp left (+ bound radius)))))
 :hints (("Goal"
 :use ((:instance lw-complex-sub-disk (left left) (right (lw-complex-sub left right)) (radius bound) (other-radius radius))
       (:instance lw-complex-subtract-cancel (a left) (b right))
       (:instance lw-complex-difference-symmetric)
       (:instance lw-complex-sub-disk (left right) (right (lw-complex-sub right left)) (radius bound) (other-radius radius))
       (:instance lw-complex-subtract-cancel (a right) (b left)))
 :in-theory (union-theories
 '( lw-eps-left-commutes lw-eps-left-distributes lw-eps-fold-constants lw-eps-times-negative lw-eps-negative-times lw-eps-zero-times lw-eps-minus-one lw-eps-double-negative lw-eps-add-cancel lw-eps-double lw-eps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)) :rule-classes nil))

(defthm lw-euler-positive-square-small-sample-polynomial
 (implies (and (lw-positive-squarep anchor side) (lw-square-containsp anchor side point)
 (rationalp error) (< 0 error) (rationalp value-error) (< 0 value-error) (<= value-error error)
 (lw-complex-diskp (lw-complex-euler-continuation-value (car point) (cdr point) value-error) (/ error 2)))
 (lw-complex-diskp (lw-complex-polynomial (lw-euler-positive-square-polynomial anchor side error) point 0) error))
 :hints (("Goal"
 :use (lw-euler-positive-square-polynomial-valid lw-euler-positive-square-polynomial-comparison lw-euler-positive-square-point-data
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-positive-square-polynomial anchor side error)) (offset 0))
       (:instance lw-complex-euler-continuation-value-rational (rate (car point)) (height (cdr point)) (error value-error))
       (:instance lw-eps-near-transfer
        (left (lw-complex-polynomial (lw-euler-positive-square-polynomial anchor side error) point 0))
        (right (lw-complex-euler-continuation-value (car point) (cdr point) value-error))
        (radius (+ (* 1/4 error) (* 1/4 value-error))) (bound (/ error 2)))
       (:instance lw-complex-disk-enlarge
        (point (lw-complex-polynomial (lw-euler-positive-square-polynomial anchor side error) point 0))
        (radius (+ (/ error 2) (* 1/4 error) (* 1/4 value-error))) (cap error)))
 :in-theory (union-theories
 '(lw-square-containsp lw-eps-left-commutes lw-eps-left-distributes lw-eps-fold-constants lw-eps-times-negative lw-eps-negative-times lw-eps-zero-times lw-eps-minus-one lw-eps-double-negative lw-eps-add-cancel lw-eps-double lw-eps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-positive-square-cover-complete
 (implies (and (lw-positive-squarep anchor side) (lw-square-containsp anchor side point)
 (rationalp width) (< 0 width) (rationalp error) (< 0 error)
 (rationalp value-error) (< 0 value-error) (<= value-error error)
 (lw-complex-diskp (lw-complex-euler-continuation-value (car point) (cdr point) value-error) (/ error 2)))
 (and (member-equal (lw-square-cell-address anchor side
                     (lw-euler-positive-square-cover-count anchor side width error) point)
                   (lw-euler-positive-square-cover anchor side width error))
      (lw-square-cover-containsp anchor side
                     (lw-euler-positive-square-cover-count anchor side width error) point
                     (lw-euler-positive-square-cover anchor side width error))))
 :hints (("Goal" :use (lw-euler-positive-square-polynomial-valid lw-euler-positive-square-small-sample-polynomial
       (:instance lw-polynomial-resolved-cover-complete
        (coefficients (lw-euler-positive-square-polynomial anchor side error)) (epsilon error)))
 :in-theory (union-theories
 '(lw-euler-positive-square-cover lw-euler-positive-square-cover-count lw-eps-left-commutes lw-eps-left-distributes lw-eps-fold-constants lw-eps-times-negative lw-eps-negative-times lw-eps-zero-times lw-eps-minus-one lw-eps-double-negative lw-eps-add-cancel lw-eps-double lw-eps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-positive-square-cover-value-bound
 (implies (and (lw-positive-squarep anchor side)
 (rationalp width) (< 0 width) (rationalp error) (< 0 error)
 (rationalp value-error) (< 0 value-error)
 (lw-square-cover-containsp anchor side
                     (lw-euler-positive-square-cover-count anchor side width error) point
                     (lw-euler-positive-square-cover anchor side width error)))
 (lw-complex-diskp (lw-complex-euler-continuation-value (car point) (cdr point) value-error)
                  (+ (* 13/4 error) (* 1/4 value-error))))
 :hints (("Goal"
 :use ((:instance lw-complex-disk-enlarge
        (point (lw-complex-euler-continuation-value (car point) (cdr point) value-error))
        (radius (+ (* 3 error) (* 1/4 error) (* 1/4 value-error)))
        (cap (+ (* 13/4 error) (* 1/4 value-error))))
       lw-euler-positive-square-polynomial-valid lw-euler-positive-square-polynomial-comparison lw-euler-positive-square-point-data
       (:instance lw-polynomial-resolved-cover-value-bound
        (coefficients (lw-euler-positive-square-polynomial anchor side error)) (epsilon error))
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-positive-square-polynomial anchor side error)) (offset 0))
       (:instance lw-complex-euler-continuation-value-rational (rate (car point)) (height (cdr point)) (error value-error))
       (:instance lw-eps-near-transfer
        (left (lw-complex-polynomial (lw-euler-positive-square-polynomial anchor side error) point 0))
        (right (lw-complex-euler-continuation-value (car point) (cdr point) value-error))
        (radius (+ (* 1/4 error) (* 1/4 value-error))) (bound (* 3 error))))
 :in-theory (union-theories
 '(lw-euler-positive-square-cover lw-euler-positive-square-cover-count lw-positive-squarep lw-square-containsp lw-eps-left-commutes lw-eps-left-distributes lw-eps-fold-constants lw-eps-times-negative lw-eps-negative-times lw-eps-zero-times lw-eps-minus-one lw-eps-double-negative lw-eps-add-cancel lw-eps-double lw-eps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-euler-positive-square-cover-complement
 (implies (and (lw-positive-squarep anchor side) (lw-square-containsp anchor side point)
 (rationalp width) (< 0 width) (rationalp error) (< 0 error)
 (rationalp value-error) (< 0 value-error) (<= value-error error)
 (not (lw-square-cover-containsp anchor side
                     (lw-euler-positive-square-cover-count anchor side width error) point
                     (lw-euler-positive-square-cover anchor side width error))))
 (not (lw-complex-diskp (lw-complex-euler-continuation-value (car point) (cdr point) value-error) (/ error 2))))
 :hints (("Goal" :use lw-euler-positive-square-cover-complete :in-theory (union-theories
 '( lw-eps-left-commutes lw-eps-left-distributes lw-eps-fold-constants lw-eps-times-negative lw-eps-negative-times lw-eps-zero-times lw-eps-minus-one lw-eps-double-negative lw-eps-add-cancel lw-eps-double lw-eps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-positive-empty-square-cover-excludes-small
 (implies (and (lw-positive-squarep anchor side) (lw-square-containsp anchor side point)
 (rationalp width) (< 0 width) (rationalp error) (< 0 error)
 (rationalp value-error) (< 0 value-error) (<= value-error error)
 (not (consp (lw-euler-positive-square-cover anchor side width error))))
 (not (lw-complex-diskp (lw-complex-euler-continuation-value (car point) (cdr point) value-error) (/ error 2))))
 :hints (("Goal" :use lw-euler-positive-square-cover-complete
 :in-theory (union-theories
 '(lw-square-cover-containsp endp lw-eps-left-commutes lw-eps-left-distributes lw-eps-fold-constants lw-eps-times-negative lw-eps-negative-times lw-eps-zero-times lw-eps-minus-one lw-eps-double-negative lw-eps-add-cancel lw-eps-double lw-eps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(local (defthm lw-eps-not-small-l1
 (implies (and (lw-complexp value) (rationalp error) (< 0 error)
 (not (lw-complex-diskp value (/ error 2))))
 (< (/ error 2) (lw-complex-l1 value)))
 :hints (("Goal"
 :use ((:instance lw-complex-l1-bound (point value))
       (:instance lw-complex-disk-enlarge (point value) (radius (lw-complex-l1 value)) (cap (/ error 2))))
 :in-theory (union-theories
 '( lw-eps-left-commutes lw-eps-left-distributes lw-eps-fold-constants lw-eps-times-negative lw-eps-negative-times lw-eps-zero-times lw-eps-minus-one lw-eps-double-negative lw-eps-add-cancel lw-eps-double lw-eps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)) :rule-classes nil))

(defun lw-euler-positive-square-regular-radius (anchor side width error point)
 (declare (ignore anchor side width))
 (lw-euler-neighborhood-radius (car point) (cdr point)
                              (/ (car point) 2) (/ error 64)))
(local (in-theory (disable lw-euler-positive-square-regular-radius)))

(defthm lw-euler-positive-square-uncovered-check
 (implies (lw-euler-positive-square-uncoveredp anchor side width error point)
 (and (lw-euler-value-clearance-check (car point) (cdr point) (/ error 64))
      (<= (/ error 8)
       (lw-euler-value-clearance-lower (car point) (cdr point) (/ error 64)))))
 :hints (("Goal"
 :use ((:instance lw-euler-positive-square-cover-complement (value-error (/ error 64)))
       lw-euler-positive-square-point-data
       (:instance lw-complex-euler-continuation-value-rational
        (rate (car point)) (height (cdr point)) (error (/ error 64)))
       (:instance lw-eps-not-small-l1
        (value (lw-complex-euler-continuation-value (car point) (cdr point) (/ error 64)))))
 :in-theory (union-theories
 '(lw-euler-positive-square-uncoveredp lw-euler-value-clearance-check lw-euler-value-clearance-size lw-euler-value-clearance-lower lw-eps-left-commutes lw-eps-left-distributes lw-eps-fold-constants lw-eps-times-negative lw-eps-negative-times lw-eps-zero-times lw-eps-minus-one lw-eps-double-negative lw-eps-add-cancel lw-eps-double lw-eps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(local (defthm lw-eps-square-order
 (implies (and (rationalp a) (rationalp b) (<= 0 a) (<= a b))
 (<= (* a a) (* b b)))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defthm lw-euler-positive-square-uncovered-denominator-clearance
 (implies (and (lw-euler-positive-square-uncoveredp anchor side width error point)
 (rationalp request) (< 0 request) (<= request (/ error 32)))
 (let ((value (lw-complex-euler-continuation-value (car point) (cdr point) request)))
 (and (lw-complexp value) (not (equal value (cons 0 0)))
      (<= (* (/ error 8) (/ error 8)) (lw-complex-norm-square value))
      (lw-complex-diskp (lw-complex-reciprocal value) (/ (/ error 8))))))
 :hints (("Goal"
 :use (lw-euler-positive-square-uncovered-check
       (:instance lw-euler-value-clearance-data
        (rate (car point)) (height (cdr point)) (anchor-error (/ error 64)))
       (:instance lw-complex-euler-value-clearance
        (rate (car point)) (height (cdr point)) (anchor-error (/ error 64)))
       (:instance lw-eps-square-order (a (/ error 8))
        (b (lw-euler-value-clearance-lower (car point) (cdr point) (/ error 64))))
       (:instance lw-complex-reciprocal-disk-bound
        (point (lw-complex-euler-continuation-value (car point) (cdr point) request))
        (lower (/ error 8))))
 :in-theory (union-theories
 '(lw-euler-positive-square-uncoveredp lw-eps-left-commutes lw-eps-left-distributes lw-eps-fold-constants lw-eps-times-negative lw-eps-negative-times lw-eps-zero-times lw-eps-minus-one lw-eps-double-negative lw-eps-add-cancel lw-eps-double lw-eps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))


(defthm lw-euler-positive-square-regular-radius-data
 (implies (lw-euler-positive-square-uncoveredp anchor side width error point)
 (let ((radius (lw-euler-positive-square-regular-radius anchor side width error point)))
 (and (rationalp radius) (< 0 radius) (<= radius 1) (<= radius (/ (car point) 4)))))
 :hints (("Goal"
 :use (lw-euler-positive-square-uncovered-check lw-euler-positive-square-point-data
       (:instance lw-euler-neighborhood-data
        (rate (car point)) (height (cdr point)) (outer-radius (/ (car point) 2))
        (anchor-error (/ error 64))))
 :in-theory (union-theories
 '(lw-positive-squarep lw-square-containsp lw-complexp lw-euler-positive-square-uncoveredp lw-euler-positive-square-regular-radius lw-eps-left-commutes lw-eps-left-distributes lw-eps-fold-constants lw-eps-times-negative lw-eps-negative-times lw-eps-zero-times lw-eps-minus-one lw-eps-double-negative lw-eps-add-cancel lw-eps-double lw-eps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-positive-square-regular-shifted-check
 (implies (and (lw-euler-positive-square-uncoveredp anchor side width error point)
 (lw-complex-diskp offset (lw-euler-positive-square-regular-radius anchor side width error point)))
 (and (lw-euler-value-clearance-check (+ (car point) (car offset)) (+ (cdr point) (cdr offset)) (/ error 128))
      (<= (/ error 16)
       (lw-euler-value-clearance-lower (+ (car point) (car offset)) (+ (cdr point) (cdr offset)) (/ error 128)))))
 :hints (("Goal"
 :use (lw-euler-positive-square-uncovered-check lw-euler-positive-square-point-data
       (:instance lw-euler-neighborhood-shifted-check
        (rate (car point)) (height (cdr point)) (outer-radius (/ (car point) 2))
        (anchor-error (/ error 64)) (point offset)))
 :in-theory (union-theories
 '(lw-positive-squarep lw-square-containsp lw-complexp lw-euler-positive-square-uncoveredp lw-euler-positive-square-regular-radius lw-euler-value-clearance-lower lw-eps-left-commutes lw-eps-left-distributes lw-eps-fold-constants lw-eps-times-negative lw-eps-negative-times lw-eps-zero-times lw-eps-minus-one lw-eps-double-negative lw-eps-add-cancel lw-eps-double lw-eps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))
