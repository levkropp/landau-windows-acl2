(in-package "ACL2")

(include-book "euler-real-axis-clearance")
(include-book "euler-neighborhood-uniform-slope")
(include-book "euler-neighborhood-uniform-radius")
(include-book "euler-circle-regular-geometry")
(include-book "euler-circle-factor-anchor")

; The real-axis bound extends to a fixed-width strip inside an Euler disk.

(local (defthm lw-enrc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-enrc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-enrc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-enrc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-enrc-times-negative (a b) (b a)))
                 :in-theory (disable lw-enrc-times-negative)))))

(local (defthm lw-enrc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-enrc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-enrc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-enrc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-enrc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-enrc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-enrc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-enrc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-enrc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-enrc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-enrc-left-commutes)))))

(local (deftheory lw-enrc-arithmetic (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              
              lw-enrc-left-commutes lw-enrc-left-distributes lw-enrc-fold-constants
              lw-enrc-times-negative lw-enrc-negative-times lw-enrc-zero-times
              lw-enrc-minus-one lw-enrc-double-negative lw-enrc-add-cancel lw-enrc-double lw-enrc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))

(defun lw-euler-near-real-request (lower)
  (min (lw-euler-real-axis-request lower) (* 1/32 (lw-euler-real-axis-floor lower))))

(defun lw-euler-near-real-radius (rate outer-radius radius)
  (lw-euler-uniform-neighborhood-radius (lw-euler-circle-local-outer radius outer-radius) (* 1/2 (lw-euler-real-axis-floor (- rate outer-radius))) (* 4 (+ 5 (lw-euler-uniform-coefficient-cap rate 0 outer-radius)) (/ (lw-euler-circle-local-outer radius outer-radius)))))

(defthm lw-euler-near-real-request-data
  (implies (and (rationalp lower) (< 0 lower))
           (and (rationalp (lw-euler-near-real-request lower)) (< 0 (lw-euler-near-real-request lower)) (<= (lw-euler-near-real-request lower) 1)
                (<= (lw-euler-near-real-request lower) (lw-euler-real-axis-request lower))
                (<= (lw-euler-near-real-request lower) (* 1/32 (lw-euler-real-axis-floor lower)))))
  :hints (("Goal"
           :use (lw-euler-real-axis-budget-data)
           :in-theory (union-theories '(lw-euler-near-real-request min) (theory 'lw-enrc-arithmetic))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm lw-enrc-budget-data
   (implies (and (rationalp rate) (rationalp radius) (<= 0 radius)
       (rationalp outer-radius) (< radius outer-radius) (< outer-radius rate))
            (and (rationalp (lw-euler-circle-local-outer radius outer-radius)) (< 0 (lw-euler-circle-local-outer radius outer-radius)) (<= (+ radius (lw-euler-circle-local-outer radius outer-radius)) outer-radius)
                 (rationalp (* 4 (+ 5 (lw-euler-uniform-coefficient-cap rate 0 outer-radius)) (/ (lw-euler-circle-local-outer radius outer-radius)))) (< 0 (* 4 (+ 5 (lw-euler-uniform-coefficient-cap rate 0 outer-radius)) (/ (lw-euler-circle-local-outer radius outer-radius))))))
   :hints (("Goal"
            :use ((:instance lw-euler-uniform-coefficient-cap-valid (height 0) (radius outer-radius))
                  (:instance lw-reciprocal-positive (value (lw-euler-circle-local-outer radius outer-radius)))
                  (:instance lw-enrc-positive-product
                    (a (+ 5 (lw-euler-uniform-coefficient-cap rate 0 outer-radius))) (b (/ (lw-euler-circle-local-outer radius outer-radius)))))
            :in-theory (union-theories '(lw-euler-circle-local-outer) (theory 'lw-enrc-arithmetic))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-euler-near-real-radius-positive
  (implies (and (rationalp rate) (rationalp radius) (<= 0 radius)
       (rationalp outer-radius) (< radius outer-radius) (< outer-radius rate))
           (and (rationalp (lw-euler-near-real-radius rate outer-radius radius)) (< 0 (lw-euler-near-real-radius rate outer-radius radius))))
  :hints (("Goal"
           :use (lw-enrc-budget-data
                 (:instance lw-euler-real-axis-budget-data (lower (- rate outer-radius)))
                 (:instance lw-euler-uniform-neighborhood-radius-positive
                   (outer-radius (lw-euler-circle-local-outer radius outer-radius)) (floor (* 1/2 (lw-euler-real-axis-floor (- rate outer-radius)))) (slope (* 4 (+ 5 (lw-euler-uniform-coefficient-cap rate 0 outer-radius)) (/ (lw-euler-circle-local-outer radius outer-radius))))))
           :in-theory (union-theories '(lw-euler-near-real-radius) (theory 'lw-enrc-arithmetic))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm lw-enrc-square-order
   (implies (and (rationalp a) (<= 0 a) (rationalp b) (<= a b))
            (<= (* a a) (* b b)))
   :hints (("Goal"
            :use ((:instance lw-enrc-multiply-order (factor a)) (:instance lw-enrc-multiply-order (factor b)))
            :in-theory (theory 'lw-enrc-arithmetic)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-enrc-real-location
   (implies (and (rationalp rate) (rationalp radius) (<= 0 radius)
       (rationalp outer-radius) (< radius outer-radius) (< outer-radius rate) (rationalp point-rate) (<= (abs (- point-rate rate)) radius))
            (and (<= (- rate outer-radius) point-rate) (< (lw-euler-circle-local-outer radius outer-radius) point-rate)
                 (lw-complex-diskp (lw-complex-sub (cons point-rate 0) (cons rate 0)) radius)))
   :hints (("Goal"
            :use (lw-enrc-budget-data
                  (:instance lw-enrc-square-order (a (abs (- point-rate rate))) (b radius))
                  (:instance lw-complex-disk-norm-square
                    (point (lw-complex-sub (cons point-rate 0) (cons rate 0)))))
            :in-theory (union-theories '(lw-complex-sub lw-complexp lw-complex-norm-square abs) (theory 'lw-enrc-arithmetic))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-enrc-real-anchor
   (implies (and (rationalp rate) (rationalp radius) (<= 0 radius)
       (rationalp outer-radius) (< radius outer-radius) (< outer-radius rate) (rationalp point-rate) (<= (abs (- point-rate rate)) radius))
            (and (lw-euler-value-clearance-check point-rate 0 (lw-euler-near-real-request (- rate outer-radius)))
                 (<= (* 1/2 (lw-euler-real-axis-floor (- rate outer-radius))) (lw-euler-value-clearance-size point-rate 0 (lw-euler-near-real-request (- rate outer-radius))))))
   :hints (("Goal"
            :use (lw-enrc-real-location
                  (:instance lw-euler-near-real-request-data (lower (- rate outer-radius)))
                  (:instance lw-euler-real-axis-budget-data (lower (- rate outer-radius)))
                  (:instance lw-complex-euler-real-axis-clearance (lower (- rate outer-radius)) (rate point-rate) (error (lw-euler-near-real-request (- rate outer-radius))))
                  (:instance lw-complex-euler-continuation-value-rational (rate point-rate) (height 0) (error (lw-euler-near-real-request (- rate outer-radius))))
                  (:instance lw-complex-sub-zero (point (lw-complex-euler-continuation-value point-rate 0 (lw-euler-near-real-request (- rate outer-radius)))))
                  (:instance lw-complex-zero-disk (radius (* 1/4 (lw-euler-real-axis-floor (- rate outer-radius)))))
                  (:instance lw-euler-value-clearance-from-approximation
                    (rate point-rate) (height 0) (lower (lw-euler-real-axis-floor (- rate outer-radius))) (model (lw-complex-euler-continuation-value point-rate 0 (lw-euler-near-real-request (- rate outer-radius)))) (error (lw-euler-near-real-request (- rate outer-radius)))))
            :in-theory (theory 'lw-enrc-arithmetic)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-enrc-shared-neighborhood
   (implies (and (rationalp rate) (rationalp radius) (<= 0 radius)
       (rationalp outer-radius) (< radius outer-radius) (< outer-radius rate) (rationalp point-rate) (<= (abs (- point-rate rate)) radius))
            (<= (lw-euler-near-real-radius rate outer-radius radius) (lw-euler-neighborhood-radius point-rate 0 (lw-euler-circle-local-outer radius outer-radius) (lw-euler-near-real-request (- rate outer-radius)))))
   :hints (("Goal"
            :use (lw-enrc-budget-data lw-enrc-real-location lw-enrc-real-anchor
                  (:instance lw-euler-near-real-request-data (lower (- rate outer-radius)))
                  (:instance lw-euler-real-axis-budget-data (lower (- rate outer-radius)))
                  (:instance lw-euler-neighborhood-uniform-slope
                    (rate point-rate) (height 0) (outer-radius (lw-euler-circle-local-outer radius outer-radius)) (error (lw-euler-near-real-request (- rate outer-radius)))
                    (global-rate rate) (global-height 0) (global-radius outer-radius) (displacement radius))
                  (:instance lw-euler-neighborhood-radius-uniform-lower
                    (rate point-rate) (height 0) (outer-radius (lw-euler-circle-local-outer radius outer-radius)) (anchor-error (lw-euler-near-real-request (- rate outer-radius)))
                    (floor (* 1/2 (lw-euler-real-axis-floor (- rate outer-radius)))) (slope (* 4 (+ 5 (lw-euler-uniform-coefficient-cap rate 0 outer-radius)) (/ (lw-euler-circle-local-outer radius outer-radius))))))
            :in-theory (union-theories '(lw-euler-near-real-radius) (theory 'lw-enrc-arithmetic))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-complex-euler-near-real-clearance
  (implies
   (and (rationalp rate) (rationalp radius) (<= 0 radius)
       (rationalp outer-radius) (< radius outer-radius) (< outer-radius rate) (rationalp point-rate) (<= (abs (- point-rate rate)) radius)
        (rationalp height) (<= (abs height) (lw-euler-near-real-radius rate outer-radius radius))
        (rationalp error) (< 0 error) (<= error (lw-euler-near-real-request (- rate outer-radius))))
   (<= (* (* 1/8 (lw-euler-real-axis-floor (- rate outer-radius))) (* 1/8 (lw-euler-real-axis-floor (- rate outer-radius))))
       (lw-complex-norm-square (lw-complex-euler-continuation-value point-rate height error))))
  :hints (("Goal"
           :use (lw-euler-near-real-radius-positive lw-enrc-shared-neighborhood
                 lw-enrc-budget-data lw-enrc-real-location lw-enrc-real-anchor
                 (:instance lw-euler-real-axis-budget-data (lower (- rate outer-radius)))
                 (:instance lw-complex-disk-norm-square (point (cons 0 height)) (radius (lw-euler-near-real-radius rate outer-radius radius)))
                 (:instance lw-enrc-square-order (a (abs height)) (b (lw-euler-near-real-radius rate outer-radius radius)))
                 (:instance lw-complex-disk-enlarge (point (cons 0 height)) (radius (lw-euler-near-real-radius rate outer-radius radius)) (cap (lw-euler-neighborhood-radius point-rate 0 (lw-euler-circle-local-outer radius outer-radius) (lw-euler-near-real-request (- rate outer-radius)))))
                 (:instance lw-complex-euler-neighborhood-value-clearance
                   (rate point-rate) (height 0) (outer-radius (lw-euler-circle-local-outer radius outer-radius)) (anchor-error (lw-euler-near-real-request (- rate outer-radius))) (point (cons 0 height)))
                 (:instance lw-euler-neighborhood-data (rate point-rate) (height 0) (outer-radius (lw-euler-circle-local-outer radius outer-radius)) (anchor-error (lw-euler-near-real-request (- rate outer-radius))))
                 (:instance lw-enrc-square-order (a (* 1/8 (lw-euler-real-axis-floor (- rate outer-radius)))) (b (* 1/4 (lw-euler-value-clearance-size point-rate 0 (lw-euler-near-real-request (- rate outer-radius)))))))
           :in-theory (union-theories '(lw-complexp lw-complex-norm-square abs) (theory 'lw-enrc-arithmetic))
           :do-not-induct t))
  :rule-classes nil)
