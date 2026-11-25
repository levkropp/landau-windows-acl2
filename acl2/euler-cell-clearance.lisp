; Native Euler clearance on every point of an individually discarded cell.
(in-package "ACL2")
(include-book "euler-positive-square-cover")
(include-book "polynomial-cover-index")
(local (in-theory (disable lw-positive-squarep lw-square-cell-containsp lw-square-containsp
 lw-complexp lw-complex-diskp lw-complex-polynomial lw-complex-sub lw-complex-l1 lw-complex-norm-square
 lw-complex-reciprocal lw-complex-euler-continuation-value lw-polynomial-cell-activep
 lw-euler-positive-square-polynomial lw-euler-positive-square-cover-count lw-euler-positive-square-cover
 lw-polynomial-resolved-cover lw-polynomial-resolved-cover-count lw-polynomial-cell-index
 lw-euler-value-clearance-check lw-euler-value-clearance-size lw-euler-value-clearance-lower
 lw-euler-positive-square-regular-radius lw-euler-neighborhood-radius)))
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
(defun lw-euler-discarded-cellp (anchor side width error row column)
 (and (lw-positive-squarep anchor side) (rationalp width) (< 0 width) (rationalp error) (< 0 error)
      (natp row) (< row (lw-euler-positive-square-cover-count anchor side width error)) (natp column) (< column (lw-euler-positive-square-cover-count anchor side width error))
      (not (lw-polynomial-cell-activep (lw-euler-positive-square-polynomial anchor side error) anchor side (lw-euler-positive-square-cover-count anchor side width error) error row column))))
(local (in-theory (disable lw-euler-discarded-cellp)))

(defthm lw-euler-discarded-cell-excludes-small
 (implies (and (lw-euler-discarded-cellp anchor side width error row column)
 (lw-square-cell-containsp anchor side (lw-euler-positive-square-cover-count anchor side width error) row column point)
 (rationalp value-error) (< 0 value-error) (<= value-error error))
 (not (lw-complex-diskp (lw-complex-euler-continuation-value (car point) (cdr point) value-error) (/ error 2))))
 :hints (("Goal"
 :use ((:instance lw-square-cell-in-square (count (lw-euler-positive-square-cover-count anchor side width error)))
       lw-euler-positive-square-polynomial-valid
       lw-euler-positive-square-small-sample-polynomial
       (:instance lw-polynomial-inactive-cell-excludes-small (coefficients (lw-euler-positive-square-polynomial anchor side error)) (count (lw-euler-positive-square-cover-count anchor side width error)) (epsilon error)))
 :in-theory (union-theories
 '(lw-euler-discarded-cellp lw-ecc-left-commutes lw-ecc-left-distributes lw-ecc-fold-constants lw-ecc-times-negative lw-ecc-negative-times lw-ecc-zero-times lw-ecc-minus-one lw-ecc-double-negative lw-ecc-add-cancel lw-ecc-double lw-ecc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(local (defthm lw-ecc-not-small-l1
 (implies (and (lw-complexp value) (rationalp error) (< 0 error)
 (not (lw-complex-diskp value (/ error 2))))
 (< (/ error 2) (lw-complex-l1 value)))
 :hints (("Goal"
 :use ((:instance lw-complex-l1-bound (point value))
       (:instance lw-complex-disk-enlarge (point value) (radius (lw-complex-l1 value)) (cap (/ error 2))))
 :in-theory (union-theories
 '( lw-ecc-left-commutes lw-ecc-left-distributes lw-ecc-fold-constants lw-ecc-times-negative lw-ecc-negative-times lw-ecc-zero-times lw-ecc-minus-one lw-ecc-double-negative lw-ecc-add-cancel lw-ecc-double lw-ecc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)) :rule-classes nil))

(defthm lw-euler-discarded-cell-check
 (implies (and (lw-euler-discarded-cellp anchor side width error row column)
 (lw-square-cell-containsp anchor side (lw-euler-positive-square-cover-count anchor side width error) row column point))
 (and (lw-euler-value-clearance-check (car point) (cdr point) (/ error 64))
      (<= (/ error 8) (lw-euler-value-clearance-lower (car point) (cdr point) (/ error 64)))))
 :hints (("Goal"
 :use ((:instance lw-euler-discarded-cell-excludes-small (value-error (/ error 64)))
       (:instance lw-square-cell-in-square (count (lw-euler-positive-square-cover-count anchor side width error)))
       lw-euler-positive-square-point-data
       (:instance lw-complex-euler-continuation-value-rational (rate (car point)) (height (cdr point)) (error (/ error 64)))
       (:instance lw-ecc-not-small-l1
        (value (lw-complex-euler-continuation-value (car point) (cdr point) (/ error 64)))))
 :in-theory (union-theories
 '(lw-euler-discarded-cellp lw-euler-value-clearance-check lw-euler-value-clearance-size lw-euler-value-clearance-lower lw-ecc-left-commutes lw-ecc-left-distributes lw-ecc-fold-constants lw-ecc-times-negative lw-ecc-negative-times lw-ecc-zero-times lw-ecc-minus-one lw-ecc-double-negative lw-ecc-add-cancel lw-ecc-double lw-ecc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(local (defthm lw-ecc-square-order
 (implies (and (rationalp a) (rationalp b) (<= 0 a) (<= a b))
 (<= (* a a) (* b b)))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defthm lw-euler-discarded-cell-denominator-clearance
 (implies (and (lw-euler-discarded-cellp anchor side width error row column)
 (lw-square-cell-containsp anchor side (lw-euler-positive-square-cover-count anchor side width error) row column point)
 (rationalp request) (< 0 request) (<= request (/ error 32)))
 (let ((value (lw-complex-euler-continuation-value (car point) (cdr point) request)))
 (and (lw-complexp value) (not (equal value (cons 0 0)))
      (<= (* (/ error 8) (/ error 8)) (lw-complex-norm-square value))
      (lw-complex-diskp (lw-complex-reciprocal value) (/ (/ error 8))))))
 :hints (("Goal"
 :use (lw-euler-discarded-cell-check
       (:instance lw-euler-value-clearance-data (rate (car point)) (height (cdr point)) (anchor-error (/ error 64)))
       (:instance lw-complex-euler-value-clearance (rate (car point)) (height (cdr point)) (anchor-error (/ error 64)))
       (:instance lw-ecc-square-order (a (/ error 8)) (b (lw-euler-value-clearance-lower (car point) (cdr point) (/ error 64))))
       (:instance lw-complex-reciprocal-disk-bound
        (point (lw-complex-euler-continuation-value (car point) (cdr point) request)) (lower (/ error 8))))
 :in-theory (union-theories
 '(lw-euler-discarded-cellp lw-ecc-left-commutes lw-ecc-left-distributes lw-ecc-fold-constants lw-ecc-times-negative lw-ecc-negative-times lw-ecc-zero-times lw-ecc-minus-one lw-ecc-double-negative lw-ecc-add-cancel lw-ecc-double lw-ecc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-discarded-cell-radius-data
 (implies (and (lw-euler-discarded-cellp anchor side width error row column)
 (lw-square-cell-containsp anchor side (lw-euler-positive-square-cover-count anchor side width error) row column point))
 (let ((radius (lw-euler-positive-square-regular-radius anchor side width error point)))
 (and (rationalp radius) (< 0 radius) (<= radius 1) (<= radius (/ (car point) 4)))))
 :hints (("Goal"
 :use (lw-euler-discarded-cell-check
       (:instance lw-square-cell-in-square (count (lw-euler-positive-square-cover-count anchor side width error)))
       lw-euler-positive-square-point-data
       (:instance lw-euler-neighborhood-data (rate (car point)) (height (cdr point))
        (outer-radius (/ (car point) 2)) (anchor-error (/ error 64))))
 :in-theory (union-theories
 '(lw-euler-discarded-cellp lw-positive-squarep lw-square-cell-containsp lw-square-containsp lw-complexp lw-euler-positive-square-regular-radius lw-ecc-left-commutes lw-ecc-left-distributes lw-ecc-fold-constants lw-ecc-times-negative lw-ecc-negative-times lw-ecc-zero-times lw-ecc-minus-one lw-ecc-double-negative lw-ecc-add-cancel lw-ecc-double lw-ecc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-discarded-cell-shifted-check
 (implies (and (lw-euler-discarded-cellp anchor side width error row column)
 (lw-square-cell-containsp anchor side (lw-euler-positive-square-cover-count anchor side width error) row column point)
 (lw-complex-diskp offset (lw-euler-positive-square-regular-radius anchor side width error point)))
 (and (lw-euler-value-clearance-check (+ (car point) (car offset)) (+ (cdr point) (cdr offset)) (/ error 128))
      (<= (/ error 16)
       (lw-euler-value-clearance-lower (+ (car point) (car offset)) (+ (cdr point) (cdr offset)) (/ error 128)))))
 :hints (("Goal"
 :use (lw-euler-discarded-cell-check
       (:instance lw-square-cell-in-square (count (lw-euler-positive-square-cover-count anchor side width error)))
       lw-euler-positive-square-point-data
       (:instance lw-euler-neighborhood-shifted-check (rate (car point)) (height (cdr point))
        (outer-radius (/ (car point) 2)) (anchor-error (/ error 64)) (point offset)))
 :in-theory (union-theories
 '(lw-euler-discarded-cellp lw-positive-squarep lw-square-cell-containsp lw-square-containsp lw-complexp lw-euler-positive-square-regular-radius lw-euler-value-clearance-lower lw-ecc-left-commutes lw-ecc-left-distributes lw-ecc-fold-constants lw-ecc-times-negative lw-ecc-negative-times lw-ecc-zero-times lw-ecc-minus-one lw-ecc-double-negative lw-ecc-add-cancel lw-ecc-double lw-ecc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-discarded-cell-index-zero
 (implies (lw-euler-discarded-cellp anchor side width error row column)
 (equal (lw-polynomial-cell-index (lw-euler-positive-square-polynomial anchor side error) anchor side (lw-euler-positive-square-cover-count anchor side width error) row column) 0))
 :hints (("Goal"
 :use (lw-euler-positive-square-polynomial-valid lw-euler-positive-square-cover-count-data
       (:instance lw-polynomial-inactive-cell-index-zero (coefficients (lw-euler-positive-square-polynomial anchor side error)) (count (lw-euler-positive-square-cover-count anchor side width error)) (epsilon error)))
 :in-theory (union-theories
 '(lw-euler-discarded-cellp lw-positive-squarep lw-ecc-left-commutes lw-ecc-left-distributes lw-ecc-fold-constants lw-ecc-times-negative lw-ecc-negative-times lw-ecc-zero-times lw-ecc-minus-one lw-ecc-double-negative lw-ecc-add-cancel lw-ecc-double lw-ecc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-positive-cover-index-conservation
 (implies (and (lw-positive-squarep anchor side) (rationalp width) (< 0 width) (rationalp error) (< 0 error))
 (equal (lw-polynomial-cover-index (lw-euler-positive-square-polynomial anchor side error) anchor side (lw-euler-positive-square-cover-count anchor side width error) (lw-euler-positive-square-cover anchor side width error))
        (lw-ray-grid-boundary-index (lw-polynomial-grid (lw-euler-positive-square-polynomial anchor side error) anchor side (lw-euler-positive-square-cover-count anchor side width error)))))
 :hints (("Goal"
 :use (lw-euler-positive-square-polynomial-valid lw-euler-positive-square-cover-count-data
       (:instance lw-polynomial-sublevel-cover-index-conservation (coefficients (lw-euler-positive-square-polynomial anchor side error)) (count (lw-euler-positive-square-cover-count anchor side width error)) (epsilon error)))
 :in-theory (union-theories
 '(lw-euler-positive-square-cover lw-euler-positive-square-cover-count lw-polynomial-resolved-cover lw-positive-squarep lw-ecc-left-commutes lw-ecc-left-distributes lw-ecc-fold-constants lw-ecc-times-negative lw-ecc-negative-times lw-ecc-zero-times lw-ecc-minus-one lw-ecc-double-negative lw-ecc-add-cancel lw-ecc-double lw-ecc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))
