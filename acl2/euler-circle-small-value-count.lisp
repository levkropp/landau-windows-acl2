(in-package "ACL2")

(include-book "circle-no-inner-factors")
(include-book "euler-circle-uniform-anchor")

; An interior Euler value below the floor forces an inner factor.

(local (defthm lw-ecsv-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ecsv-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ecsv-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ecsv-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ecsv-times-negative (a b) (b a)))
                 :in-theory (disable lw-ecsv-times-negative)))))

(local (defthm lw-ecsv-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ecsv-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ecsv-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ecsv-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ecsv-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ecsv-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ecsv-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ecsv-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecsv-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecsv-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ecsv-left-commutes)))))

(defun lw-euler-circle-inner-square-floor (rate height radius scale inner anchor-error)
  (let ((size (* 1/8 (lw-euler-value-clearance-size rate height anchor-error))))
    (lw-circle-reflected-square-lower (* size size)
      (lw-circle-reflected-boundary-square-cap (+ 1 (lw-euler-uniform-coefficient-cap rate height radius)) scale) inner)))

(defun lw-euler-circle-inner-distance-floor (rate height radius scale inner anchor-error)
  (lw-circle-square-floor-to-distance (lw-euler-circle-inner-square-floor rate height radius scale inner anchor-error)))

(defthm lw-euler-circle-inner-distance-floor-data
  (and (rationalp (lw-euler-circle-inner-distance-floor rate height radius scale inner anchor-error)) (< 0 (lw-euler-circle-inner-distance-floor rate height radius scale inner anchor-error)) (<= (lw-euler-circle-inner-distance-floor rate height radius scale inner anchor-error) 1)
       (<= (* (lw-euler-circle-inner-distance-floor rate height radius scale inner anchor-error) (lw-euler-circle-inner-distance-floor rate height radius scale inner anchor-error)) (lw-euler-circle-inner-square-floor rate height radius scale inner anchor-error)))
  :hints (("Goal"
           :use ((:instance lw-circle-reflected-square-lower-positive
                   (center-lower (* (* 1/8 (lw-euler-value-clearance-size rate height anchor-error)) (* 1/8 (lw-euler-value-clearance-size rate height anchor-error))))
                   (boundary-cap (lw-circle-reflected-boundary-square-cap (+ 1 (lw-euler-uniform-coefficient-cap rate height radius)) scale)))
                 (:instance lw-circle-square-floor-to-distance-valid (square (lw-euler-circle-inner-square-floor rate height radius scale inner anchor-error))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-circle-inner-distance-floor lw-euler-circle-inner-square-floor
              lw-ecsv-left-commutes lw-ecsv-left-distributes lw-ecsv-fold-constants
              lw-ecsv-times-negative lw-ecsv-negative-times lw-ecsv-zero-times
              lw-ecsv-minus-one lw-ecsv-double-negative lw-ecsv-add-cancel lw-ecsv-double lw-ecsv-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(defthm lw-complex-scale-unit-disk-from-inner
   (implies (and (rationalp scale) (< 0 scale)
                 (< (* scale scale) 1) (lw-complex-diskp point inner) (< inner 1))
            (lw-complex-diskp (lw-complex-scale scale point) 1))
   :hints (("Goal"
            :use ((:instance lw-complex-disk-data (radius inner))
                  (:instance lw-ecsv-multiply-order (a inner) (b 1) (factor scale))
                  (:instance lw-ecsv-multiply-order (a 1) (b scale) (factor scale))
                  (:instance lw-complex-scale-disk (factor scale) (radius inner))
                  (:instance lw-complex-disk-enlarge (point (lw-complex-scale scale point)) (radius (* scale inner)) (cap 1)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              abs
              lw-ecsv-left-commutes lw-ecsv-left-distributes lw-ecsv-fold-constants
              lw-ecsv-times-negative lw-ecsv-negative-times lw-ecsv-zero-times
              lw-ecsv-minus-one lw-ecsv-double-negative lw-ecsv-add-cancel lw-ecsv-double lw-ecsv-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
  :rule-classes nil)

(defthm lw-circle-inner-count-from-small-estimate
  (implies
   (and (lw-ray-pointsp roots) (lw-complexp leading)
        (rationalp cutoff-square) (< 0 cutoff-square) (< cutoff-square 1)
        (rationalp scale) (< 0 scale) (< (* scale scale) cutoff-square)
        (rationalp cap) (<= 0 cap)
        (lw-circle-factor-boundary-check roots leading cutoff-square cap)
        (rationalp center-lower) (< 0 center-lower)
        (<= center-lower (lw-complex-norm-square
                           (lw-complex-polynomial (lw-polynomial-factor-coefficients roots leading) (cons 0 0) 0)))
        (lw-complex-diskp point inner) (< inner 1)
        (lw-complex-diskp estimate (* 1/2 (lw-circle-square-floor-to-distance (lw-circle-reflected-square-lower center-lower (lw-circle-reflected-boundary-square-cap cap scale) inner))))
        (lw-complex-diskp (lw-complex-sub (lw-complex-polynomial (lw-polynomial-factor-coefficients roots leading) (lw-complex-scale scale point) 0) estimate) (* 1/2 (lw-circle-square-floor-to-distance (lw-circle-reflected-square-lower center-lower (lw-circle-reflected-boundary-square-cap cap scale) inner)))))
   (< 0 (lw-circle-inner-factor-count roots cutoff-square)))
  :hints (("Goal"
           :cases ((equal (lw-circle-inner-factor-count roots cutoff-square) 0))
           :use (lw-circle-factor-positive-center-leading lw-circle-no-inner-factors-lower
                 (:instance lw-circle-square-floor-to-distance-valid (square (lw-circle-reflected-square-lower center-lower (lw-circle-reflected-boundary-square-cap cap scale) inner)))
                 (:instance lw-complex-disk-data (point estimate) (radius (* 1/2 (lw-circle-square-floor-to-distance (lw-circle-reflected-square-lower center-lower (lw-circle-reflected-boundary-square-cap cap scale) inner)))))
                 (:instance lw-complex-disk-data (radius inner))
                 (:instance lw-complex-scale-rational (factor scale))
                 lw-polynomial-factor-coefficients-valid
                 (:instance lw-complex-polynomial-rational (coefficients (lw-polynomial-factor-coefficients roots leading))
                   (point (lw-complex-scale scale point)) (offset 0))
                 (:instance lw-complex-sub-zero (point estimate))
                 (:instance lw-complex-sub-zero (point (lw-complex-polynomial (lw-polynomial-factor-coefficients roots leading) (lw-complex-scale scale point) 0)))
                 (:instance lw-complex-difference-triangle (left (lw-complex-polynomial (lw-polynomial-factor-coefficients roots leading) (lw-complex-scale scale point) 0)) (middle estimate) (right (cons 0 0))
                   (radius (* 1/2 (lw-circle-square-floor-to-distance (lw-circle-reflected-square-lower center-lower (lw-circle-reflected-boundary-square-cap cap scale) inner)))) (other-radius (* 1/2 (lw-circle-square-floor-to-distance (lw-circle-reflected-square-lower center-lower (lw-circle-reflected-boundary-square-cap cap scale) inner)))))
                 (:instance lw-complex-disk-norm-square (point (lw-complex-polynomial (lw-polynomial-factor-coefficients roots leading) (lw-complex-scale scale point) 0)) (radius (lw-circle-square-floor-to-distance (lw-circle-reflected-square-lower center-lower (lw-circle-reflected-boundary-square-cap cap scale) inner)))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-inner-factor-count-natural
              lw-ecsv-left-commutes lw-ecsv-left-distributes lw-ecsv-fold-constants
              lw-ecsv-times-negative lw-ecsv-negative-times lw-ecsv-zero-times
              lw-ecsv-minus-one lw-ecsv-double-negative lw-ecsv-add-cancel lw-ecsv-double lw-ecsv-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm lw-ecsv-native-close
   (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate)
       (lw-euler-value-clearance-check rate height anchor-error)
       (rationalp scale) (< 0 scale) (rationalp cutoff-square)
       (< (* scale scale) cutoff-square) (< cutoff-square 1)
       (lw-complex-diskp point inner) (< inner 1) (natp target) (rationalp error) (< 0 error) (<= error 1)
       (rationalp factor-error) (< 0 factor-error) (<= factor-error 1)
       (<= error (* 1/64 (lw-euler-value-clearance-size rate height anchor-error)))
       (<= factor-error (* 1/64 (lw-euler-value-clearance-size rate height anchor-error))) (rationalp value-error) (< 0 value-error)
        (<= error (* 1/8 (lw-euler-circle-inner-distance-floor rate height radius scale inner anchor-error)))
        (<= factor-error (* 1/8 (lw-euler-circle-inner-distance-floor rate height radius scale inner anchor-error)))
        (<= value-error (* 1/8 (lw-euler-circle-inner-distance-floor rate height radius scale inner anchor-error))))
            (lw-complex-diskp (lw-complex-sub (lw-complex-polynomial (lw-polynomial-disk-factor-polynomial (lw-euler-coefficient-polynomial rate height radius target error) 1 factor-error) (lw-complex-scale scale point) 0) (lw-complex-euler-continuation-value (+ rate (car (lw-complex-scale radius (lw-complex-scale scale point)))) (+ height (cdr (lw-complex-scale radius (lw-complex-scale scale point)))) value-error)) (* 1/2 (lw-euler-circle-inner-distance-floor rate height radius scale inner anchor-error))))
   :hints (("Goal"
            :use (lw-euler-circle-inner-distance-floor-data lw-complex-scale-unit-disk-from-inner
                  (:instance lw-euler-disk-factor-native-comparison (outer-radius radius) (point (lw-complex-scale scale point)) (anchor-error value-error))
                  (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-polynomial (lw-polynomial-disk-factor-polynomial (lw-euler-coefficient-polynomial rate height radius target error) 1 factor-error) (lw-complex-scale scale point) 0) (lw-complex-euler-continuation-value (+ rate (car (lw-complex-scale radius (lw-complex-scale scale point)))) (+ height (cdr (lw-complex-scale radius (lw-complex-scale scale point)))) value-error)))
                    (radius (+ factor-error error (* 1/4 value-error))) (cap (* 1/2 (lw-euler-circle-inner-distance-floor rate height radius scale inner anchor-error)))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              
              lw-ecsv-left-commutes lw-ecsv-left-distributes lw-ecsv-fold-constants
              lw-ecsv-times-negative lw-ecsv-negative-times lw-ecsv-zero-times
              lw-ecsv-minus-one lw-ecsv-double-negative lw-ecsv-add-cancel lw-ecsv-double lw-ecsv-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-euler-circle-small-value-positive-factor-count
  (implies
   (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate)
       (lw-euler-value-clearance-check rate height anchor-error)
       (rationalp scale) (< 0 scale) (rationalp cutoff-square)
       (< (* scale scale) cutoff-square) (< cutoff-square 1)
       (lw-complex-diskp point inner) (< inner 1) (natp target) (rationalp error) (< 0 error) (<= error 1)
       (rationalp factor-error) (< 0 factor-error) (<= factor-error 1)
       (<= error (* 1/64 (lw-euler-value-clearance-size rate height anchor-error)))
       (<= factor-error (* 1/64 (lw-euler-value-clearance-size rate height anchor-error))) (rationalp value-error) (< 0 value-error)
        (<= error (* 1/8 (lw-euler-circle-inner-distance-floor rate height radius scale inner anchor-error)))
        (<= factor-error (* 1/8 (lw-euler-circle-inner-distance-floor rate height radius scale inner anchor-error)))
        (<= value-error (* 1/8 (lw-euler-circle-inner-distance-floor rate height radius scale inner anchor-error)))
        (lw-complex-diskp (lw-complex-euler-continuation-value (+ rate (car (lw-complex-scale radius (lw-complex-scale scale point)))) (+ height (cdr (lw-complex-scale radius (lw-complex-scale scale point)))) value-error) (* 1/2 (lw-euler-circle-inner-distance-floor rate height radius scale inner anchor-error))))
   (< 0 (lw-circle-inner-factor-count (lw-polynomial-normalized-factor-roots (lw-euler-coefficient-polynomial rate height radius target error) 1 factor-error) cutoff-square)))
  :hints (("Goal"
           :use (lw-ecsv-native-close lw-euler-circle-factor-model-data
                 (:instance lw-circle-inner-count-from-small-estimate
                   (roots (lw-polynomial-normalized-factor-roots (lw-euler-coefficient-polynomial rate height radius target error) 1 factor-error)) (leading (lw-polynomial-leading (lw-polynomial-trim (lw-euler-coefficient-polynomial rate height radius target error)))) (cap (+ 1 (lw-euler-uniform-coefficient-cap rate height radius))) (center-lower (* (* 1/8 (lw-euler-value-clearance-size rate height anchor-error)) (* 1/8 (lw-euler-value-clearance-size rate height anchor-error)))) (estimate (lw-complex-euler-continuation-value (+ rate (car (lw-complex-scale radius (lw-complex-scale scale point)))) (+ height (cdr (lw-complex-scale radius (lw-complex-scale scale point)))) value-error))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-polynomial-disk-factor-polynomial lw-euler-circle-inner-distance-floor lw-euler-circle-inner-square-floor
              lw-ecsv-left-commutes lw-ecsv-left-distributes lw-ecsv-fold-constants
              lw-ecsv-times-negative lw-ecsv-negative-times lw-ecsv-zero-times
              lw-ecsv-minus-one lw-ecsv-double-negative lw-ecsv-add-cancel lw-ecsv-double lw-ecsv-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
