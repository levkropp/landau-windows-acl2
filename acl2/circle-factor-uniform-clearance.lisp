(in-package "ACL2")

(include-book "circle-reflected-boundary-budget")
(include-book "circle-bounded-radius-selection")
(include-book "circle-reflected-factor-comparison")

; The contour radius can depend on the factor list. Its positive
; value floor depends only on the fixed input budgets.

(local (defthm lw-cfuc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-cfuc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-cfuc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-cfuc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-cfuc-times-negative (a b) (b a)))
                 :in-theory (disable lw-cfuc-times-negative)))))

(local (defthm lw-cfuc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-cfuc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-cfuc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-cfuc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-cfuc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-cfuc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-cfuc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-cfuc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cfuc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cfuc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-cfuc-left-commutes)))))

(defun lw-circle-factor-uniform-clearance-square
    (lower upper cutoff-square scale center-lower cap budget)
  (let ((gap (lw-circle-bounded-radius-gap lower upper cutoff-square budget))
        (reflected (lw-circle-reflected-square-lower center-lower (lw-circle-reflected-boundary-square-cap cap scale) (/ upper scale))))
    (* reflected (lw-rational-power (lw-circle-reflection-retention gap) budget))))

(local
 (defthm lw-cfuc-scale-width
   (implies (and (rationalp scale) (< 0 scale) (< (* scale scale) 1)
                 (rationalp upper) (<= 0 upper) (< upper scale))
            (and (< scale 1) (rationalp (/ upper scale)) (<= 0 (/ upper scale)) (< (/ upper scale) 1)))
   :hints (("Goal"
            :use ((:instance lw-cfuc-multiply-order (a 1) (b scale) (factor scale))
                  (:instance lw-reciprocal-positive (value scale))
                  (:instance lw-cfuc-multiply-order (a 0) (b upper) (factor (/ scale)))
                  (:instance lw-cfuc-positive-product (a (- scale upper)) (b (/ scale)))
                  (:instance inverse-of-* (x scale)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)

              lw-cfuc-left-commutes lw-cfuc-left-distributes lw-cfuc-fold-constants
              lw-cfuc-times-negative lw-cfuc-negative-times lw-cfuc-zero-times
              lw-cfuc-minus-one lw-cfuc-double-negative lw-cfuc-add-cancel lw-cfuc-double lw-cfuc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-cfuc-scale-compose
   (implies (and (rationalp outer) (rationalp inner) (lw-complexp point))
            (equal (lw-complex-scale outer (lw-complex-scale inner point))
                   (lw-complex-scale (* outer inner) point)))
   :hints (("Goal" :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complexp lw-complex-scale
              lw-cfuc-left-commutes lw-cfuc-left-distributes lw-cfuc-fold-constants
              lw-cfuc-times-negative lw-cfuc-negative-times lw-cfuc-zero-times
              lw-cfuc-minus-one lw-cfuc-double-negative lw-cfuc-add-cancel lw-cfuc-double lw-cfuc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                   :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-cfuc-rescale-point
   (implies (and (lw-complex-diskp point upper) (rationalp scale) (< 0 scale))
            (and (lw-complex-diskp (lw-complex-scale (/ scale) point) (/ upper scale))
                 (equal (lw-complex-scale scale (lw-complex-scale (/ scale) point)) point)))
   :hints (("Goal"
            :use ((:instance lw-complex-disk-data (radius upper))
                  (:instance lw-reciprocal-positive (value scale))
                  (:instance lw-complex-scale-disk (factor (/ scale)) (radius upper))
                  (:instance lw-cfuc-scale-compose (outer scale) (inner (/ scale)))
                  (:instance inverse-of-* (x scale)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complex-scale-one abs
              lw-cfuc-left-commutes lw-cfuc-left-distributes lw-cfuc-fold-constants
              lw-cfuc-times-negative lw-cfuc-negative-times lw-cfuc-zero-times
              lw-cfuc-minus-one lw-cfuc-double-negative lw-cfuc-add-cancel lw-cfuc-double lw-cfuc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-cfuc-zero-leading
   (implies (and (lw-ray-pointsp roots) (lw-complexp point))
            (equal (lw-polynomial-linear-factor-value roots (cons 0 0) point) (cons 0 0)))
   :hints (("Goal"
            :induct (lw-polynomial-linear-factor-value roots (cons 0 0) point)
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              (:induction lw-polynomial-linear-factor-value) lw-polynomial-linear-factor-value
              lw-complex-ring-rational lw-complex-mul-zero lw-ray-pointsp endp
              lw-cfuc-left-commutes lw-cfuc-left-distributes lw-cfuc-fold-constants
              lw-cfuc-times-negative lw-cfuc-negative-times lw-cfuc-zero-times
              lw-cfuc-minus-one lw-cfuc-double-negative lw-cfuc-add-cancel lw-cfuc-double lw-cfuc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not '(generalize fertilize)))))

(defthm lw-circle-factor-positive-center-leading
  (implies (and (lw-ray-pointsp roots) (lw-complexp leading)
                (< 0 (lw-complex-norm-square
                       (lw-complex-polynomial (lw-polynomial-factor-coefficients roots leading) (cons 0 0) 0))))
           (not (equal leading (cons 0 0))))
  :hints (("Goal"
           :use ((:instance lw-polynomial-factor-coefficients-evaluation (point (cons 0 0)))
                 (:instance lw-cfuc-zero-leading (point (cons 0 0))))
           :in-theory (union-theories
           '(fold-consts-in-+ (:executable-counterpart lw-complexp)
             (:executable-counterpart lw-complex-norm-square)
             lw-cfuc-left-commutes lw-cfuc-left-distributes lw-cfuc-fold-constants
             lw-cfuc-times-negative lw-cfuc-negative-times lw-cfuc-zero-times
             lw-cfuc-minus-one lw-cfuc-double-negative lw-cfuc-add-cancel lw-cfuc-double lw-cfuc-add-double
             natp posp zp fix car-cons cdr-cons
             commutativity-of-* associativity-of-*
             commutativity-of-+ commutativity-2-of-+ associativity-of-+
             distributivity distributivity-of-minus-over-+
             inverse-of-+ unicity-of-0 unicity-of-1)
           (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(defthm lw-circle-factor-uniform-clearance
  (implies (and (lw-ray-pointsp roots) (lw-complexp leading)
                (rationalp lower) (<= 0 lower) (rationalp upper) (< lower upper)
                (rationalp scale) (< upper scale)
                (rationalp cutoff-square) (< (* scale scale) cutoff-square) (< cutoff-square 1)
                (rationalp cap) (<= 0 cap) (lw-circle-factor-boundary-check roots leading cutoff-square cap)
                (rationalp center-lower) (< 0 center-lower)
                (<= center-lower (lw-complex-norm-square (lw-complex-polynomial (lw-polynomial-factor-coefficients roots leading) (cons 0 0) 0)))
                (natp budget) (<= (lw-circle-inner-factor-count roots cutoff-square) budget)
                (lw-complexp point) (equal (lw-complex-norm-square point) (* (car (lw-circle-bounded-radius roots lower upper cutoff-square budget)) (car (lw-circle-bounded-radius roots lower upper cutoff-square budget)))))
           (and (rationalp (lw-circle-factor-uniform-clearance-square lower upper cutoff-square scale center-lower cap budget)) (< 0 (lw-circle-factor-uniform-clearance-square lower upper cutoff-square scale center-lower cap budget))
                (<= (lw-circle-factor-uniform-clearance-square lower upper cutoff-square scale center-lower cap budget) (lw-complex-norm-square (lw-complex-polynomial (lw-polynomial-factor-coefficients roots leading) point 0)))))
  :hints (("Goal"
           :use ((:instance lw-cfuc-positive-product (a scale) (b scale))
                 (:instance lw-cfuc-multiply-order (a upper) (b scale) (factor upper))
                 (:instance lw-cfuc-multiply-order (a upper) (b scale) (factor scale))
                 lw-cfuc-scale-width lw-circle-bounded-radius-valid lw-circle-factor-positive-center-leading
                 (:instance lw-complex-disk-norm-square (radius (car (lw-circle-bounded-radius roots lower upper cutoff-square budget))))
                 (:instance lw-complex-disk-enlarge (radius (car (lw-circle-bounded-radius roots lower upper cutoff-square budget))) (cap upper))
                 lw-cfuc-rescale-point
                 (:instance lw-circle-reflected-lower-from-original-boundary (point (lw-complex-scale (/ scale) point)) (inner (/ upper scale)))
                 (:instance lw-circle-reflected-factor-lower-transfer
                   (radius (car (lw-circle-bounded-radius roots lower upper cutoff-square budget))) (gap (cdr (lw-circle-bounded-radius roots lower upper cutoff-square budget))) (reflected-square (lw-circle-reflected-square-lower center-lower (lw-circle-reflected-boundary-square-cap cap scale) (/ upper scale)))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-factor-uniform-clearance-square lw-circle-reflected-value-square lw-circle-bounded-radius
              lw-cfuc-left-commutes lw-cfuc-left-distributes lw-cfuc-fold-constants
              lw-cfuc-times-negative lw-cfuc-negative-times lw-cfuc-zero-times
              lw-cfuc-minus-one lw-cfuc-double-negative lw-cfuc-add-cancel lw-cfuc-double lw-cfuc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(defthm lw-circle-reflected-square-lower-positive
  (and (rationalp (lw-circle-reflected-square-lower center-lower boundary-cap inner))
       (< 0 (lw-circle-reflected-square-lower center-lower boundary-cap inner)))
  :hints (("Goal"
           :use ((:instance lw-rational-power-positive (base 2)
                   (exponent (+ 1 (lw-signed-log-lower-steps (+ 1 (/ center-lower)
                     (lw-circle-reflected-log-interior-variation center-lower boundary-cap inner))))))
                 (:instance lw-reciprocal-positive
                   (value (lw-rational-power 2 (+ 1 (lw-signed-log-lower-steps (+ 1 (/ center-lower)
                     (lw-circle-reflected-log-interior-variation center-lower boundary-cap inner))))))))
           :in-theory (union-theories
           '(fold-consts-in-+ (:executable-counterpart lw-complexp)
             lw-circle-reflected-square-lower lw-signed-log-value-lower lw-rational-power-rational
             lw-cfuc-left-commutes lw-cfuc-left-distributes lw-cfuc-fold-constants
             lw-cfuc-times-negative lw-cfuc-negative-times lw-cfuc-zero-times
             lw-cfuc-minus-one lw-cfuc-double-negative lw-cfuc-add-cancel lw-cfuc-double lw-cfuc-add-double
             natp posp zp fix car-cons cdr-cons
             commutativity-of-* associativity-of-*
             commutativity-of-+ commutativity-2-of-+ associativity-of-+
             distributivity distributivity-of-minus-over-+
             inverse-of-+ unicity-of-0 unicity-of-1)
           (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm lw-cfuc-retention-positive
   (implies (and (rationalp gap) (< 0 gap))
            (and (rationalp (lw-circle-reflection-retention gap)) (< 0 (lw-circle-reflection-retention gap))))
   :hints (("Goal"
            :use ((:instance lw-circle-radial-clearance-budget (radius 1))
                  (:instance lw-cfuc-positive-product (a (lw-circle-radial-clearance 1 gap)) (b (lw-circle-radial-clearance 1 gap)))
                  (:instance lw-cfuc-positive-product (a 1/4) (b (* (lw-circle-radial-clearance 1 gap) (lw-circle-radial-clearance 1 gap)))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-reflection-retention
              lw-cfuc-left-commutes lw-cfuc-left-distributes lw-cfuc-fold-constants
              lw-cfuc-times-negative lw-cfuc-negative-times lw-cfuc-zero-times
              lw-cfuc-minus-one lw-cfuc-double-negative lw-cfuc-add-cancel lw-cfuc-double lw-cfuc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-circle-factor-uniform-clearance-square-positive
  (implies (and (rationalp lower) (<= 0 lower) (rationalp upper) (< lower upper)
                (rationalp cutoff-square) (< (* upper upper) cutoff-square)
                (natp budget))
           (and (rationalp (lw-circle-factor-uniform-clearance-square lower upper cutoff-square scale center-lower cap budget)) (< 0 (lw-circle-factor-uniform-clearance-square lower upper cutoff-square scale center-lower cap budget))))
  :hints (("Goal"
           :use ((:instance lw-circle-bounded-radius-valid (roots nil))
                 (:instance lw-cfuc-retention-positive (gap (lw-circle-bounded-radius-gap lower upper cutoff-square budget)))
                 (:instance lw-circle-reflected-square-lower-positive
                   (boundary-cap (lw-circle-reflected-boundary-square-cap cap scale)) (inner (/ upper scale)))
                 (:instance lw-rational-power-positive (base (lw-circle-reflection-retention (lw-circle-bounded-radius-gap lower upper cutoff-square budget))) (exponent budget))
                 (:instance lw-cfuc-positive-product
                   (a (lw-circle-reflected-square-lower center-lower (lw-circle-reflected-boundary-square-cap cap scale) (/ upper scale))) (b (lw-rational-power (lw-circle-reflection-retention (lw-circle-bounded-radius-gap lower upper cutoff-square budget)) budget))))
           :expand ((lw-circle-inner-factor-count nil cutoff-square))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-factor-uniform-clearance-square lw-circle-bounded-radius
              (:executable-counterpart lw-ray-pointsp) (:executable-counterpart lw-circle-inner-factor-count)
              lw-rational-power-rational
              lw-cfuc-left-commutes lw-cfuc-left-distributes lw-cfuc-fold-constants
              lw-cfuc-times-negative lw-cfuc-negative-times lw-cfuc-zero-times
              lw-cfuc-minus-one lw-cfuc-double-negative lw-cfuc-add-cancel lw-cfuc-double lw-cfuc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(defun lw-circle-square-floor-to-distance (square)
  (/ square (+ 1 square)))

(defthm lw-circle-square-floor-to-distance-valid
  (implies (and (rationalp square) (< 0 square))
           (let ((distance (lw-circle-square-floor-to-distance square)))
             (and (rationalp distance) (< 0 distance) (<= distance 1)
                  (<= (* distance distance) square))))
  :hints (("Goal"
           :use ((:instance lw-reciprocal-positive (value (+ 1 square)))
                 (:instance lw-cfuc-positive-product (a square) (b (/ (+ 1 square))))
                 (:instance lw-cfuc-multiply-order (a square) (b (+ 1 square)) (factor (/ (+ 1 square))))
                 (:instance lw-cfuc-inverse-factor (divisor (+ 1 square)) (coefficient 1))
                 (:instance lw-cfuc-multiply-order (a (lw-circle-square-floor-to-distance square)) (b 1)
                   (factor (lw-circle-square-floor-to-distance square)))
                 (:instance lw-cfuc-multiply-order (a (/ (+ 1 square))) (b 1) (factor square))
                 (:instance lw-reciprocal-antitone (left 1) (right (+ 1 square))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-square-floor-to-distance
              lw-cfuc-left-commutes lw-cfuc-left-distributes lw-cfuc-fold-constants
              lw-cfuc-times-negative lw-cfuc-negative-times lw-cfuc-zero-times
              lw-cfuc-minus-one lw-cfuc-double-negative lw-cfuc-add-cancel lw-cfuc-double lw-cfuc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
