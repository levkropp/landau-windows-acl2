; Computed finite small-value covers for the actual Euler Cauchy evaluator.
(in-package "ACL2")
(include-book "polynomial-resolved-cover")
(include-book "euler-uniform-polynomial")
(local (in-theory (disable lw-complexp lw-complex-polynomial lw-complex-sub lw-complex-diskp
 lw-complex-euler-continuation-value lw-euler-uniform-polynomial lw-square-radius lw-square-containsp
 lw-square-cover-containsp lw-polynomial-resolved-cover lw-polynomial-resolved-cover-count lw-square-cell-address)))
(local (defthm lw-esc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-esc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-esc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-esc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-esc-times-negative (a b) (b a)))
                 :in-theory (disable lw-esc-times-negative)))))

(local (defthm lw-esc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-esc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-esc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-esc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-esc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-esc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-esc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-esc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-esc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-esc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-esc-left-commutes)))))
(defun lw-euler-square-domainp (rate height anchor side)
 (and (rationalp rate) (rationalp height) (lw-complexp anchor) (rationalp side) (< 0 side)
      (< (lw-square-radius anchor side) rate)))
(defun lw-euler-square-polynomial (rate height anchor side error)
 (lw-euler-uniform-polynomial rate height (lw-square-radius anchor side) 0 (/ error 4)))
(defun lw-euler-square-cover-count (rate height anchor side width error)
 (lw-polynomial-resolved-cover-count (lw-euler-square-polynomial rate height anchor side error)
                                    anchor side width error))
(defun lw-euler-square-cover (rate height anchor side width error)
 (lw-polynomial-resolved-cover (lw-euler-square-polynomial rate height anchor side error)
                              anchor side width error))
(local (in-theory (disable lw-euler-square-domainp lw-euler-square-polynomial lw-euler-square-cover-count lw-euler-square-cover)))

(defthm lw-euler-square-point-data
 (implies (and (lw-euler-square-domainp rate height anchor side) (lw-square-containsp anchor side point))
 (and (rationalp (+ rate (car point))) (< 0 (+ rate (car point)))
      (rationalp (+ height (cdr point)))))
 :hints (("Goal"
 :use (lw-square-radius-data lw-square-contained-in-tight-disk
       (:instance lw-euler-disk-point-data (radius (lw-square-radius anchor side)) (offset point)))
 :in-theory (union-theories
 '(lw-euler-square-domainp lw-square-containsp lw-esc-left-commutes lw-esc-left-distributes lw-esc-fold-constants lw-esc-times-negative lw-esc-negative-times lw-esc-zero-times lw-esc-minus-one lw-esc-double-negative lw-esc-add-cancel lw-esc-double lw-esc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-square-polynomial-valid
 (implies (and (lw-euler-square-domainp rate height anchor side) (rationalp error) (< 0 error))
 (lw-complex-coefficientsp (lw-euler-square-polynomial rate height anchor side error)))
 :hints (("Goal"
 :use (lw-square-radius-data
       (:instance lw-euler-uniform-polynomial-valid (radius (lw-square-radius anchor side)) (target 0) (error (/ error 4))))
 :in-theory (union-theories
 '(lw-euler-square-domainp lw-euler-square-polynomial lw-esc-left-commutes lw-esc-left-distributes lw-esc-fold-constants lw-esc-times-negative lw-esc-negative-times lw-esc-zero-times lw-esc-minus-one lw-esc-double-negative lw-esc-add-cancel lw-esc-double lw-esc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-square-polynomial-comparison
 (implies (and (lw-euler-square-domainp rate height anchor side) (lw-square-containsp anchor side point)
 (rationalp error) (< 0 error) (rationalp value-error) (< 0 value-error))
 (lw-complex-diskp
 (lw-complex-sub
  (lw-complex-polynomial (lw-euler-square-polynomial rate height anchor side error) point 0)
  (lw-complex-euler-continuation-value (+ rate (car point)) (+ height (cdr point)) value-error))
 (+ (* 1/4 error) (* 1/4 value-error))))
 :hints (("Goal"
 :use (lw-square-radius-data lw-square-contained-in-tight-disk
       (:instance lw-complex-euler-uniform-polynomial-comparison (radius (lw-square-radius anchor side)) (target 0) (error (/ error 4))))
 :in-theory (union-theories
 '(lw-euler-square-domainp lw-euler-square-polynomial lw-esc-left-commutes lw-esc-left-distributes lw-esc-fold-constants lw-esc-times-negative lw-esc-negative-times lw-esc-zero-times lw-esc-minus-one lw-esc-double-negative lw-esc-add-cancel lw-esc-double lw-esc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-square-cover-count-data
 (implies (and (lw-euler-square-domainp rate height anchor side)
 (rationalp width) (< 0 width) (rationalp error) (< 0 error))
 (let ((count (lw-euler-square-cover-count rate height anchor side width error)))
 (and (posp count) (rationalp (lw-polynomial-grid-step side count))
      (< 0 (lw-polynomial-grid-step side count)) (<= (lw-polynomial-grid-step side count) width))))
 :hints (("Goal" :use (lw-euler-square-polynomial-valid
       (:instance lw-polynomial-resolved-cover-count-data
        (coefficients (lw-euler-square-polynomial rate height anchor side error)) (epsilon error)))
 :in-theory (union-theories
 '(lw-euler-square-domainp lw-euler-square-cover-count lw-esc-left-commutes lw-esc-left-distributes lw-esc-fold-constants lw-esc-times-negative lw-esc-negative-times lw-esc-zero-times lw-esc-minus-one lw-esc-double-negative lw-esc-add-cancel lw-esc-double lw-esc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-square-cover-data
 (implies (and (lw-euler-square-domainp rate height anchor side)
 (rationalp width) (< 0 width) (rationalp error) (< 0 error))
 (let ((count (lw-euler-square-cover-count rate height anchor side width error)))
 (and (lw-square-address-listp (lw-euler-square-cover rate height anchor side width error) count)
      (<= (len (lw-euler-square-cover rate height anchor side width error)) (* count count)))))
 :hints (("Goal" :use (lw-euler-square-polynomial-valid
       (:instance lw-polynomial-resolved-cover-data
        (coefficients (lw-euler-square-polynomial rate height anchor side error)) (epsilon error)))
 :in-theory (union-theories
 '(lw-euler-square-domainp lw-euler-square-cover-count lw-euler-square-cover lw-esc-left-commutes lw-esc-left-distributes lw-esc-fold-constants lw-esc-times-negative lw-esc-negative-times lw-esc-zero-times lw-esc-minus-one lw-esc-double-negative lw-esc-add-cancel lw-esc-double lw-esc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(local (defthm lw-esc-near-transfer
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
 '( lw-esc-left-commutes lw-esc-left-distributes lw-esc-fold-constants lw-esc-times-negative lw-esc-negative-times lw-esc-zero-times lw-esc-minus-one lw-esc-double-negative lw-esc-add-cancel lw-esc-double lw-esc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)) :rule-classes nil))

(defthm lw-euler-square-small-sample-polynomial
 (implies (and (lw-euler-square-domainp rate height anchor side) (lw-square-containsp anchor side point)
 (rationalp error) (< 0 error) (rationalp value-error) (< 0 value-error) (<= value-error error)
 (lw-complex-diskp (lw-complex-euler-continuation-value (+ rate (car point)) (+ height (cdr point)) value-error) (/ error 2)))
 (lw-complex-diskp (lw-complex-polynomial (lw-euler-square-polynomial rate height anchor side error) point 0) error))
 :hints (("Goal"
 :use (lw-euler-square-polynomial-valid lw-euler-square-polynomial-comparison lw-euler-square-point-data
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-square-polynomial rate height anchor side error)) (offset 0))
       (:instance lw-complex-euler-continuation-value-rational (rate (+ rate (car point))) (height (+ height (cdr point))) (error value-error))
       (:instance lw-esc-near-transfer
        (left (lw-complex-polynomial (lw-euler-square-polynomial rate height anchor side error) point 0))
        (right (lw-complex-euler-continuation-value (+ rate (car point)) (+ height (cdr point)) value-error))
        (radius (+ (* 1/4 error) (* 1/4 value-error))) (bound (/ error 2)))
       (:instance lw-complex-disk-enlarge
        (point (lw-complex-polynomial (lw-euler-square-polynomial rate height anchor side error) point 0))
        (radius (+ (/ error 2) (* 1/4 error) (* 1/4 value-error))) (cap error)))
 :in-theory (union-theories
 '(lw-square-containsp lw-esc-left-commutes lw-esc-left-distributes lw-esc-fold-constants lw-esc-times-negative lw-esc-negative-times lw-esc-zero-times lw-esc-minus-one lw-esc-double-negative lw-esc-add-cancel lw-esc-double lw-esc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-square-cover-complete
 (implies (and (lw-euler-square-domainp rate height anchor side) (lw-square-containsp anchor side point)
 (rationalp width) (< 0 width) (rationalp error) (< 0 error)
 (rationalp value-error) (< 0 value-error) (<= value-error error)
 (lw-complex-diskp (lw-complex-euler-continuation-value (+ rate (car point)) (+ height (cdr point)) value-error) (/ error 2)))
 (and (member-equal (lw-square-cell-address anchor side
                     (lw-euler-square-cover-count rate height anchor side width error) point)
                   (lw-euler-square-cover rate height anchor side width error))
      (lw-square-cover-containsp anchor side
                     (lw-euler-square-cover-count rate height anchor side width error) point
                     (lw-euler-square-cover rate height anchor side width error))))
 :hints (("Goal" :use (lw-euler-square-polynomial-valid lw-euler-square-small-sample-polynomial
       (:instance lw-polynomial-resolved-cover-complete
        (coefficients (lw-euler-square-polynomial rate height anchor side error)) (epsilon error)))
 :in-theory (union-theories
 '(lw-euler-square-cover lw-euler-square-cover-count lw-esc-left-commutes lw-esc-left-distributes lw-esc-fold-constants lw-esc-times-negative lw-esc-negative-times lw-esc-zero-times lw-esc-minus-one lw-esc-double-negative lw-esc-add-cancel lw-esc-double lw-esc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-square-cover-value-bound
 (implies (and (lw-euler-square-domainp rate height anchor side)
 (rationalp width) (< 0 width) (rationalp error) (< 0 error)
 (rationalp value-error) (< 0 value-error)
 (lw-square-cover-containsp anchor side
                     (lw-euler-square-cover-count rate height anchor side width error) point
                     (lw-euler-square-cover rate height anchor side width error)))
 (lw-complex-diskp (lw-complex-euler-continuation-value (+ rate (car point)) (+ height (cdr point)) value-error)
                  (+ (* 13/4 error) (* 1/4 value-error))))
 :hints (("Goal"
 :use ((:instance lw-complex-disk-enlarge
        (point (lw-complex-euler-continuation-value (+ rate (car point)) (+ height (cdr point)) value-error))
        (radius (+ (* 3 error) (* 1/4 error) (* 1/4 value-error)))
        (cap (+ (* 13/4 error) (* 1/4 value-error))))
       lw-euler-square-polynomial-valid lw-euler-square-polynomial-comparison lw-euler-square-point-data
       (:instance lw-polynomial-resolved-cover-value-bound
        (coefficients (lw-euler-square-polynomial rate height anchor side error)) (epsilon error))
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-square-polynomial rate height anchor side error)) (offset 0))
       (:instance lw-complex-euler-continuation-value-rational (rate (+ rate (car point))) (height (+ height (cdr point))) (error value-error))
       (:instance lw-esc-near-transfer
        (left (lw-complex-polynomial (lw-euler-square-polynomial rate height anchor side error) point 0))
        (right (lw-complex-euler-continuation-value (+ rate (car point)) (+ height (cdr point)) value-error))
        (radius (+ (* 1/4 error) (* 1/4 value-error))) (bound (* 3 error))))
 :in-theory (union-theories
 '(lw-euler-square-cover lw-euler-square-cover-count lw-euler-square-domainp lw-square-containsp lw-esc-left-commutes lw-esc-left-distributes lw-esc-fold-constants lw-esc-times-negative lw-esc-negative-times lw-esc-zero-times lw-esc-minus-one lw-esc-double-negative lw-esc-add-cancel lw-esc-double lw-esc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-euler-square-cover-complement
 (implies (and (lw-euler-square-domainp rate height anchor side) (lw-square-containsp anchor side point)
 (rationalp width) (< 0 width) (rationalp error) (< 0 error)
 (rationalp value-error) (< 0 value-error) (<= value-error error)
 (not (lw-square-cover-containsp anchor side
                     (lw-euler-square-cover-count rate height anchor side width error) point
                     (lw-euler-square-cover rate height anchor side width error))))
 (not (lw-complex-diskp (lw-complex-euler-continuation-value (+ rate (car point)) (+ height (cdr point)) value-error) (/ error 2))))
 :hints (("Goal" :use lw-euler-square-cover-complete :in-theory (union-theories
 '( lw-esc-left-commutes lw-esc-left-distributes lw-esc-fold-constants lw-esc-times-negative lw-esc-negative-times lw-esc-zero-times lw-esc-minus-one lw-esc-double-negative lw-esc-add-cancel lw-esc-double lw-esc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-empty-square-cover-excludes-small
 (implies (and (lw-euler-square-domainp rate height anchor side) (lw-square-containsp anchor side point)
 (rationalp width) (< 0 width) (rationalp error) (< 0 error)
 (rationalp value-error) (< 0 value-error) (<= value-error error)
 (not (consp (lw-euler-square-cover rate height anchor side width error))))
 (not (lw-complex-diskp (lw-complex-euler-continuation-value (+ rate (car point)) (+ height (cdr point)) value-error) (/ error 2))))
 :hints (("Goal" :use lw-euler-square-cover-complete
 :in-theory (union-theories
 '(lw-square-cover-containsp endp lw-esc-left-commutes lw-esc-left-distributes lw-esc-fold-constants lw-esc-times-negative lw-esc-negative-times lw-esc-zero-times lw-esc-minus-one lw-esc-double-negative lw-esc-add-cancel lw-esc-double lw-esc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
