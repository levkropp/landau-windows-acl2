(in-package "ACL2")

(include-book "euler-physical-factor-comparison")
(include-book "euler-value-clearance")
(include-book "euler-circle-small-value-count")

; Both the center lower bound and the boundary cap apply to the same physical factors.

(local (defthm lw-epfm-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-epfm-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-epfm-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-epfm-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-epfm-times-negative (a b) (b a)))
                 :in-theory (disable lw-epfm-times-negative)))))

(local (defthm lw-epfm-zero-times (equal (* 0 a) 0)))

(local (defthm lw-epfm-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-epfm-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-epfm-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-epfm-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-epfm-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-epfm-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-epfm-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-epfm-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-epfm-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-epfm-left-commutes)))))

(local (deftheory lw-epfm-arithmetic (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              
              lw-epfm-left-commutes lw-epfm-left-distributes lw-epfm-fold-constants
              lw-epfm-times-negative lw-epfm-negative-times lw-epfm-zero-times
              lw-epfm-minus-one lw-epfm-double-negative lw-epfm-add-cancel lw-epfm-double lw-epfm-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))

(defthm lw-euler-physical-factor-center-lower
  (implies
   (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate)
       (natp target) (rationalp error) (< 0 error)
       (rationalp factor-error) (< 0 factor-error) (lw-euler-value-clearance-check rate height anchor-error)
       (<= error (* 1/64 (lw-euler-value-clearance-size rate height anchor-error)))
       (<= factor-error (* 1/64 (lw-euler-value-clearance-size rate height anchor-error))))
   (and (rationalp (* (* 1/8 (lw-euler-value-clearance-size rate height anchor-error)) (* 1/8 (lw-euler-value-clearance-size rate height anchor-error)))) (< 0 (* (* 1/8 (lw-euler-value-clearance-size rate height anchor-error)) (* 1/8 (lw-euler-value-clearance-size rate height anchor-error))))
        (<= (* (* 1/8 (lw-euler-value-clearance-size rate height anchor-error)) (* 1/8 (lw-euler-value-clearance-size rate height anchor-error))) (lw-complex-norm-square (lw-complex-polynomial (lw-euler-physical-factor-polynomial rate height radius target error factor-error) (cons 0 0) 0)))))
  :hints (("Goal"
           :cases ((< (lw-complex-norm-square (lw-complex-polynomial (lw-euler-physical-factor-polynomial rate height radius target error factor-error) (cons 0 0) 0)) (* (* 1/8 (lw-euler-value-clearance-size rate height anchor-error)) (* 1/8 (lw-euler-value-clearance-size rate height anchor-error)))))
           :use (lw-euler-value-clearance-data
                 (:instance lw-complex-euler-value-clearance (request anchor-error))
                 (:instance lw-complex-zero-disk (radius 1))
                 (:instance lw-euler-physical-factor-native-comparison (point (cons 0 0)) (value-error anchor-error))
                 (:instance lw-epfm-positive-product (a (lw-euler-value-clearance-size rate height anchor-error)) (b (lw-euler-value-clearance-size rate height anchor-error)))
                 (:instance lw-complex-disk-norm-square (point (lw-complex-polynomial (lw-euler-physical-factor-polynomial rate height radius target error factor-error) (cons 0 0) 0)) (radius (* 1/8 (lw-euler-value-clearance-size rate height anchor-error))))
                 (:instance lw-complex-sub-zero (point (lw-complex-polynomial (lw-euler-physical-factor-polynomial rate height radius target error factor-error) (cons 0 0) 0)))
                 (:instance lw-complex-sub-zero (point (lw-complex-euler-continuation-value rate height anchor-error)))
                 (:instance lw-complex-difference-symmetric
                   (left (lw-complex-polynomial (lw-euler-physical-factor-polynomial rate height radius target error factor-error) (cons 0 0) 0)) (right (lw-complex-euler-continuation-value rate height anchor-error)) (radius (+ factor-error error (* 1/4 anchor-error))))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-complex-sub (lw-complex-euler-continuation-value rate height anchor-error) (lw-complex-polynomial (lw-euler-physical-factor-polynomial rate height radius target error factor-error) (cons 0 0) 0)))
                   (radius (+ factor-error error (* 1/4 anchor-error))) (cap (* 1/16 (lw-euler-value-clearance-size rate height anchor-error))))
                 (:instance lw-complex-difference-triangle (left (lw-complex-euler-continuation-value rate height anchor-error)) (middle (lw-complex-polynomial (lw-euler-physical-factor-polynomial rate height radius target error factor-error) (cons 0 0) 0)) (right (cons 0 0))
                   (radius (* 1/16 (lw-euler-value-clearance-size rate height anchor-error))) (other-radius (* 1/8 (lw-euler-value-clearance-size rate height anchor-error))))
                 (:instance lw-complex-disk-norm-square (point (lw-complex-euler-continuation-value rate height anchor-error)) (radius (+ (* 1/16 (lw-euler-value-clearance-size rate height anchor-error)) (* 1/8 (lw-euler-value-clearance-size rate height anchor-error))))))
           :in-theory (union-theories '(lw-euler-value-clearance-lower lw-complex-scale-zero) (theory 'lw-epfm-arithmetic))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm lw-epfm-boundary-samples
   (implies
    (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate)
       (natp target) (rationalp error) (< 0 error)
       (rationalp factor-error) (< 0 factor-error) (<= error 1) (<= factor-error 1) (lw-complex-diskp rotation 1))
    (lw-cauchy-boundary-check (lw-euler-physical-factor-polynomial rate height radius target error factor-error) rotation 0 count (+ 1 (lw-euler-uniform-coefficient-cap rate height radius))))
   :hints (("Goal"
            :induct (lw-cauchy-boundary-check (lw-euler-physical-factor-polynomial rate height radius target error factor-error) rotation 0 count (+ 1 (lw-euler-uniform-coefficient-cap rate height radius)))
            :in-theory (union-theories '(lw-cauchy-boundary-check) (theory 'lw-epfm-arithmetic)))
           (and stable-under-simplificationp
                '(:use ((:instance lw-complex-unit-power (point rotation) (index (- count 1)))
                        (:instance lw-euler-physical-factor-unit-cap (point (lw-complex-power rotation (- count 1))))))))
   :rule-classes nil))

(defthm lw-euler-physical-factor-model-data
  (implies
   (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate)
       (natp target) (rationalp error) (< 0 error)
       (rationalp factor-error) (< 0 factor-error) (<= error 1) (<= factor-error 1) (lw-euler-value-clearance-check rate height anchor-error)
       (<= error (* 1/64 (lw-euler-value-clearance-size rate height anchor-error)))
       (<= factor-error (* 1/64 (lw-euler-value-clearance-size rate height anchor-error))))
   (and (lw-ray-pointsp (lw-polynomial-normalized-factor-roots (lw-euler-uniform-polynomial rate height radius target error) radius factor-error))
        (lw-ray-pointsp (lw-circle-scale-factor-roots (lw-polynomial-normalized-factor-roots (lw-euler-uniform-polynomial rate height radius target error) radius factor-error) (/ radius))) (lw-complexp (lw-circle-rescale-factor-leading (lw-polynomial-normalized-factor-roots (lw-euler-uniform-polynomial rate height radius target error) radius factor-error) (lw-polynomial-leading (lw-polynomial-trim (lw-euler-uniform-polynomial rate height radius target error))) radius))
        (rationalp (+ 1 (lw-euler-uniform-coefficient-cap rate height radius))) (<= 0 (+ 1 (lw-euler-uniform-coefficient-cap rate height radius)))
        (rationalp (* (* 1/8 (lw-euler-value-clearance-size rate height anchor-error)) (* 1/8 (lw-euler-value-clearance-size rate height anchor-error)))) (< 0 (* (* 1/8 (lw-euler-value-clearance-size rate height anchor-error)) (* 1/8 (lw-euler-value-clearance-size rate height anchor-error)))) (<= (* (* 1/8 (lw-euler-value-clearance-size rate height anchor-error)) (* 1/8 (lw-euler-value-clearance-size rate height anchor-error))) (lw-complex-norm-square (lw-complex-polynomial (lw-euler-physical-factor-polynomial rate height radius target error factor-error) (cons 0 0) 0)))
        (lw-circle-factor-boundary-check (lw-circle-scale-factor-roots (lw-polynomial-normalized-factor-roots (lw-euler-uniform-polynomial rate height radius target error) radius factor-error) (/ radius)) (lw-circle-rescale-factor-leading (lw-polynomial-normalized-factor-roots (lw-euler-uniform-polynomial rate height radius target error) radius factor-error) (lw-polynomial-leading (lw-polynomial-trim (lw-euler-uniform-polynomial rate height radius target error))) radius) cutoff-square (+ 1 (lw-euler-uniform-coefficient-cap rate height radius)))))
  :hints (("Goal"
           :use (lw-euler-physical-factor-center-lower
                 lw-euler-uniform-coefficient-cap-valid lw-euler-uniform-polynomial-valid
                 (:instance lw-polynomial-disk-factor-data (coefficients (lw-euler-uniform-polynomial rate height radius target error)) (outer-radius radius) (epsilon factor-error))
                 (:instance lw-circle-scale-factor-roots-data (roots (lw-polynomial-normalized-factor-roots (lw-euler-uniform-polynomial rate height radius target error) radius factor-error)) (factor (/ radius)))
                 (:instance lw-circle-rescale-factor-leading-rational (roots (lw-polynomial-normalized-factor-roots (lw-euler-uniform-polynomial rate height radius target error) radius factor-error)) (leading (lw-polynomial-leading (lw-polynomial-trim (lw-euler-uniform-polynomial rate height radius target error)))) (scale radius))
                 (:instance lw-cauchy-orbit-data (degree (len (lw-circle-reflected-factor-polynomial (lw-circle-scale-factor-roots (lw-polynomial-normalized-factor-roots (lw-euler-uniform-polynomial rate height radius target error) radius factor-error) (/ radius)) (lw-circle-rescale-factor-leading (lw-polynomial-normalized-factor-roots (lw-euler-uniform-polynomial rate height radius target error) radius factor-error) (lw-polynomial-leading (lw-polynomial-trim (lw-euler-uniform-polynomial rate height radius target error))) radius) cutoff-square))))
                 (:instance lw-epfm-boundary-samples (rotation (lw-cauchy-orbit-rotation (len (lw-circle-reflected-factor-polynomial (lw-circle-scale-factor-roots (lw-polynomial-normalized-factor-roots (lw-euler-uniform-polynomial rate height radius target error) radius factor-error) (/ radius)) (lw-circle-rescale-factor-leading (lw-polynomial-normalized-factor-roots (lw-euler-uniform-polynomial rate height radius target error) radius factor-error) (lw-polynomial-leading (lw-polynomial-trim (lw-euler-uniform-polynomial rate height radius target error))) radius) cutoff-square))))
                   (count (lw-cauchy-coefficient-count (lw-circle-reflected-factor-polynomial (lw-circle-scale-factor-roots (lw-polynomial-normalized-factor-roots (lw-euler-uniform-polynomial rate height radius target error) radius factor-error) (/ radius)) (lw-circle-rescale-factor-leading (lw-polynomial-normalized-factor-roots (lw-euler-uniform-polynomial rate height radius target error) radius factor-error) (lw-polynomial-leading (lw-polynomial-trim (lw-euler-uniform-polynomial rate height radius target error))) radius) cutoff-square) (len (lw-circle-reflected-factor-polynomial (lw-circle-scale-factor-roots (lw-polynomial-normalized-factor-roots (lw-euler-uniform-polynomial rate height radius target error) radius factor-error) (/ radius)) (lw-circle-rescale-factor-leading (lw-polynomial-normalized-factor-roots (lw-euler-uniform-polynomial rate height radius target error) radius factor-error) (lw-polynomial-leading (lw-polynomial-trim (lw-euler-uniform-polynomial rate height radius target error))) radius) cutoff-square)) 1))))
           :in-theory (union-theories '(lw-euler-physical-factor-polynomial lw-circle-normalized-factor-polynomial
              lw-circle-factor-boundary-check (:type-prescription len)) (theory 'lw-epfm-arithmetic))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm lw-epfm-native-small-error
   (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate)
       (natp target) (rationalp error) (< 0 error)
       (rationalp factor-error) (< 0 factor-error) (rationalp scale) (< 0 scale)
       (rationalp cutoff-square) (< (* scale scale) cutoff-square) (< cutoff-square 1)
       (lw-complex-diskp point inner) (< inner 1) (rationalp value-error) (< 0 value-error)
       (<= error (* 1/8 (lw-euler-circle-inner-distance-floor rate height radius scale inner anchor-error)))
       (<= factor-error (* 1/8 (lw-euler-circle-inner-distance-floor rate height radius scale inner anchor-error)))
       (<= value-error (* 1/8 (lw-euler-circle-inner-distance-floor rate height radius scale inner anchor-error))))
            (lw-complex-diskp (lw-complex-sub (lw-complex-polynomial (lw-euler-physical-factor-polynomial rate height radius target error factor-error) (lw-complex-scale scale point) 0) (lw-complex-euler-continuation-value (+ rate (car (lw-complex-scale radius (lw-complex-scale scale point)))) (+ height (cdr (lw-complex-scale radius (lw-complex-scale scale point)))) value-error)) (* 1/2 (lw-euler-circle-inner-distance-floor rate height radius scale inner anchor-error))))
   :hints (("Goal"
            :use (lw-euler-circle-inner-distance-floor-data lw-complex-scale-unit-disk-from-inner
                  (:instance lw-euler-physical-factor-native-comparison (point (lw-complex-scale scale point)))
                  (:instance lw-complex-disk-enlarge
                    (point (lw-complex-sub (lw-complex-polynomial (lw-euler-physical-factor-polynomial rate height radius target error factor-error) (lw-complex-scale scale point) 0) (lw-complex-euler-continuation-value (+ rate (car (lw-complex-scale radius (lw-complex-scale scale point)))) (+ height (cdr (lw-complex-scale radius (lw-complex-scale scale point)))) value-error)))
                    (radius (+ factor-error error (* 1/4 value-error))) (cap (* 1/2 (lw-euler-circle-inner-distance-floor rate height radius scale inner anchor-error)))))
            :in-theory (theory 'lw-epfm-arithmetic)
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-euler-physical-factor-small-value-positive-count
  (implies
   (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate)
       (natp target) (rationalp error) (< 0 error)
       (rationalp factor-error) (< 0 factor-error) (<= error 1) (<= factor-error 1) (lw-euler-value-clearance-check rate height anchor-error)
       (<= error (* 1/64 (lw-euler-value-clearance-size rate height anchor-error)))
       (<= factor-error (* 1/64 (lw-euler-value-clearance-size rate height anchor-error))) (rationalp scale) (< 0 scale)
       (rationalp cutoff-square) (< (* scale scale) cutoff-square) (< cutoff-square 1)
       (lw-complex-diskp point inner) (< inner 1) (rationalp value-error) (< 0 value-error)
       (<= error (* 1/8 (lw-euler-circle-inner-distance-floor rate height radius scale inner anchor-error)))
       (<= factor-error (* 1/8 (lw-euler-circle-inner-distance-floor rate height radius scale inner anchor-error)))
       (<= value-error (* 1/8 (lw-euler-circle-inner-distance-floor rate height radius scale inner anchor-error)))
        (lw-complex-diskp (lw-complex-euler-continuation-value (+ rate (car (lw-complex-scale radius (lw-complex-scale scale point)))) (+ height (cdr (lw-complex-scale radius (lw-complex-scale scale point)))) value-error) (* 1/2 (lw-euler-circle-inner-distance-floor rate height radius scale inner anchor-error))))
   (< 0 (lw-circle-inner-factor-count (lw-circle-scale-factor-roots (lw-polynomial-normalized-factor-roots (lw-euler-uniform-polynomial rate height radius target error) radius factor-error) (/ radius)) cutoff-square)))
  :hints (("Goal"
           :use (lw-epfm-native-small-error lw-euler-physical-factor-model-data
                 (:instance lw-circle-inner-count-from-small-estimate
                   (roots (lw-circle-scale-factor-roots (lw-polynomial-normalized-factor-roots (lw-euler-uniform-polynomial rate height radius target error) radius factor-error) (/ radius))) (leading (lw-circle-rescale-factor-leading (lw-polynomial-normalized-factor-roots (lw-euler-uniform-polynomial rate height radius target error) radius factor-error) (lw-polynomial-leading (lw-polynomial-trim (lw-euler-uniform-polynomial rate height radius target error))) radius)) (cap (+ 1 (lw-euler-uniform-coefficient-cap rate height radius))) (center-lower (* (* 1/8 (lw-euler-value-clearance-size rate height anchor-error)) (* 1/8 (lw-euler-value-clearance-size rate height anchor-error)))) (estimate (lw-complex-euler-continuation-value (+ rate (car (lw-complex-scale radius (lw-complex-scale scale point)))) (+ height (cdr (lw-complex-scale radius (lw-complex-scale scale point)))) value-error))))
           :in-theory (union-theories
             '(lw-euler-physical-factor-polynomial lw-circle-normalized-factor-polynomial
               lw-euler-circle-inner-distance-floor lw-euler-circle-inner-square-floor)
             (theory 'lw-epfm-arithmetic))
           :do-not-induct t))
  :rule-classes nil)
