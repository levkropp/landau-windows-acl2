; Uniform native Euler circle clearance from its computed small-value cover.
(in-package "ACL2")
(include-book "euler-positive-square-cover")
(include-book "square-cover-circles")
(include-book "square-circle-geometry")
(local (in-theory (disable lw-complexp lw-circle-pointp lw-circle-contained-in-squarep
 lw-positive-squarep lw-euler-positive-square-cover-count lw-euler-positive-square-cover
 lw-euler-positive-square-uncoveredp lw-square-containsp lw-square-cover-containsp
 lw-boxes-avoid-circlep lw-square-cover-boxes lw-complex-euler-continuation-value
 lw-euler-value-clearance-check lw-euler-value-clearance-lower lw-complex-diskp
 lw-complex-reciprocal lw-complex-norm-square lw-euler-positive-square-regular-radius
 lw-cauchy-circle-point lw-complex-circle-point)))
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
(defun lw-euler-square-circle-check (anchor side width error center radius)
 (and (lw-positive-squarep anchor side)
      (rationalp width) (< 0 width) (rationalp error) (< 0 error)
      (lw-circle-contained-in-squarep anchor side center radius)
      (lw-boxes-avoid-circlep (car center) (cdr center) (* radius radius)
       (lw-square-cover-boxes anchor side
        (lw-euler-positive-square-cover-count anchor side width error)
        (lw-euler-positive-square-cover anchor side width error)))))
(local (in-theory (disable lw-euler-square-circle-check)))

(defthm lw-euler-square-circle-uncovered
 (implies (and (lw-euler-square-circle-check anchor side width error center radius)
               (lw-circle-pointp center radius point))
 (lw-euler-positive-square-uncoveredp anchor side width error point))
 :hints (("Goal"
 :use (lw-euler-positive-square-cover-count-data lw-euler-positive-square-cover-data
       lw-circle-point-in-square
       (:instance lw-square-cover-avoids-circle
        (count (lw-euler-positive-square-cover-count anchor side width error)) (addresses (lw-euler-positive-square-cover anchor side width error))
        (sigma (car center)) (height (cdr center)) (radius-square (* radius radius))))
 :in-theory (union-theories
 '(lw-euler-square-circle-check lw-circle-pointp lw-circle-contained-in-squarep lw-positive-squarep lw-euler-positive-square-uncoveredp lw-complexp lw-esc-left-commutes lw-esc-left-distributes lw-esc-fold-constants lw-esc-times-negative lw-esc-negative-times lw-esc-zero-times lw-esc-minus-one lw-esc-double-negative lw-esc-add-cancel lw-esc-double lw-esc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-euler-square-circle-value-check
 (implies (and (lw-euler-square-circle-check anchor side width error center radius)
               (lw-circle-pointp center radius point))
 (and (lw-euler-value-clearance-check (car point) (cdr point) (/ error 64))
      (<= (/ error 8)
       (lw-euler-value-clearance-lower (car point) (cdr point) (/ error 64)))))
 :hints (("Goal" :use (lw-euler-square-circle-uncovered lw-euler-positive-square-uncovered-check)
 :in-theory (union-theories
 '( lw-esc-left-commutes lw-esc-left-distributes lw-esc-fold-constants lw-esc-times-negative lw-esc-negative-times lw-esc-zero-times lw-esc-minus-one lw-esc-double-negative lw-esc-add-cancel lw-esc-double lw-esc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-square-circle-denominator-clearance
 (implies (and (lw-euler-square-circle-check anchor side width error center radius)
               (lw-circle-pointp center radius point)
               (rationalp request) (< 0 request) (<= request (/ error 32)))
 (let ((value (lw-complex-euler-continuation-value (car point) (cdr point) request)))
 (and (lw-complexp value) (not (equal value (cons 0 0)))
      (<= (* (/ error 8) (/ error 8)) (lw-complex-norm-square value))
      (lw-complex-diskp (lw-complex-reciprocal value) (/ (/ error 8))))))
 :hints (("Goal"
 :use (lw-euler-square-circle-uncovered lw-euler-positive-square-uncovered-denominator-clearance)
 :in-theory (union-theories
 '( lw-esc-left-commutes lw-esc-left-distributes lw-esc-fold-constants lw-esc-times-negative lw-esc-negative-times lw-esc-zero-times lw-esc-minus-one lw-esc-double-negative lw-esc-add-cancel lw-esc-double lw-esc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-square-circle-chart-clearance
 (implies (and (lw-euler-square-circle-check anchor side width error center radius)
               (or (equal sign 1) (equal sign -1)) (rationalp parameter))
 (let ((point (lw-complex-circle-point center radius sign parameter)))
 (and (lw-euler-positive-square-uncoveredp anchor side width error point)
      (lw-euler-value-clearance-check (car point) (cdr point) (/ error 64))
      (<= (/ error 8)
       (lw-euler-value-clearance-lower (car point) (cdr point) (/ error 64))))))
 :hints (("Goal"
 :use (lw-circle-chart-point
       (:instance lw-euler-square-circle-uncovered (point (lw-complex-circle-point center radius sign parameter)))
       (:instance lw-euler-square-circle-value-check (point (lw-complex-circle-point center radius sign parameter))))
 :in-theory (union-theories
 '(lw-euler-square-circle-check lw-circle-contained-in-squarep lw-esc-left-commutes lw-esc-left-distributes lw-esc-fold-constants lw-esc-times-negative lw-esc-negative-times lw-esc-zero-times lw-esc-minus-one lw-esc-double-negative lw-esc-add-cancel lw-esc-double lw-esc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-square-circle-orbit-clearance
 (implies (and (lw-euler-square-circle-check anchor side width error center radius)
               (natp degree) (natp sample)
               (rationalp request) (< 0 request) (<= request (/ error 32)))
 (let* ((point (lw-cauchy-circle-point center radius degree sample))
        (value (lw-complex-euler-continuation-value (car point) (cdr point) request)))
 (and (lw-euler-positive-square-uncoveredp anchor side width error point)
      (lw-euler-value-clearance-check (car point) (cdr point) (/ error 64))
      (<= (/ error 8)
       (lw-euler-value-clearance-lower (car point) (cdr point) (/ error 64)))
      (lw-complexp value) (not (equal value (cons 0 0)))
      (<= (* (/ error 8) (/ error 8)) (lw-complex-norm-square value))
      (lw-complex-diskp (lw-complex-reciprocal value) (/ (/ error 8))))))
 :hints (("Goal"
 :use (lw-cauchy-circle-point-on-circle
       (:instance lw-euler-square-circle-uncovered (point (lw-cauchy-circle-point center radius degree sample)))
       (:instance lw-euler-square-circle-value-check (point (lw-cauchy-circle-point center radius degree sample)))
       (:instance lw-euler-square-circle-denominator-clearance (point (lw-cauchy-circle-point center radius degree sample))))
 :in-theory (union-theories
 '(lw-euler-square-circle-check lw-circle-contained-in-squarep lw-esc-left-commutes lw-esc-left-distributes lw-esc-fold-constants lw-esc-times-negative lw-esc-negative-times lw-esc-zero-times lw-esc-minus-one lw-esc-double-negative lw-esc-add-cancel lw-esc-double lw-esc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-square-circle-regular-neighborhood
 (implies (and (lw-euler-square-circle-check anchor side width error center radius)
               (lw-circle-pointp center radius point)
               (lw-complex-diskp offset
                (lw-euler-positive-square-regular-radius anchor side width error point)))
 (let ((local-radius (lw-euler-positive-square-regular-radius anchor side width error point)))
 (and (rationalp local-radius) (< 0 local-radius) (<= local-radius 1) (<= local-radius (/ (car point) 4))
      (lw-euler-value-clearance-check (+ (car point) (car offset)) (+ (cdr point) (cdr offset)) (/ error 128))
      (<= (/ error 16)
       (lw-euler-value-clearance-lower (+ (car point) (car offset)) (+ (cdr point) (cdr offset)) (/ error 128))))))
 :hints (("Goal" :use (lw-euler-square-circle-uncovered
                      lw-euler-positive-square-regular-radius-data lw-euler-positive-square-regular-shifted-check)
 :in-theory (union-theories
 '( lw-esc-left-commutes lw-esc-left-distributes lw-esc-fold-constants lw-esc-times-negative lw-esc-negative-times lw-esc-zero-times lw-esc-minus-one lw-esc-double-negative lw-esc-add-cancel lw-esc-double lw-esc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

