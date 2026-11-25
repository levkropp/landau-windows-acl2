(in-package "ACL2")

(include-book "euler-circle-interior-probe")
(include-book "euler-circle-small-value-count")

; A larger reference model with no inner factors certifies an empty checked circle.

(local (defthm lw-ecew-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ecew-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ecew-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ecew-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ecew-times-negative (a b) (b a)))
                 :in-theory (disable lw-ecew-times-negative)))))

(local (defthm lw-ecew-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ecew-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ecew-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ecew-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ecew-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ecew-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ecew-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ecew-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecew-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecew-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ecew-left-commutes)))))

(local (deftheory lw-ecew-arithmetic (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              
              lw-ecew-left-commutes lw-ecew-left-distributes lw-ecew-fold-constants
              lw-ecew-times-negative lw-ecew-negative-times lw-ecew-zero-times
              lw-ecew-minus-one lw-ecew-double-negative lw-ecew-add-cancel lw-ecew-double lw-ecew-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))

(local
 (defthm lw-ecew-normalize-probe
   (implies (and (rationalp outer-radius) (< 0 outer-radius)
       (rationalp scale) (< 0 scale) (rationalp inner) (<= 0 inner)
       (<= radius (* outer-radius scale inner)) (lw-complex-diskp offset radius))
            (and (lw-complex-diskp (lw-complex-scale (/ (* outer-radius scale)) offset) inner)
                 (equal (lw-complex-scale outer-radius (lw-complex-scale scale (lw-complex-scale (/ (* outer-radius scale)) offset)))
                        offset)))
   :hints (("Goal"
            :use ((:instance lw-complex-disk-data (point offset))
                  (:instance lw-ecew-positive-product (a outer-radius) (b scale))
                  (:instance lw-reciprocal-positive (value (* outer-radius scale)))
                  (:instance lw-positive-division-bound
                    (numerator radius) (divisor (* outer-radius scale)) (bound inner))
                  (:instance lw-complex-scale-disk (factor (/ (* outer-radius scale))) (point offset))
                  (:instance lw-complex-disk-enlarge
                    (point (lw-complex-scale (/ (* outer-radius scale)) offset)) (radius (* radius (/ (* outer-radius scale)))) (cap inner))
                  (:instance lw-complex-scale-rational (point offset) (factor (/ (* outer-radius scale))))
                  (:instance lw-complex-scale-compose (left outer-radius) (right scale) (point (lw-complex-scale (/ (* outer-radius scale)) offset)))
                  (:instance lw-complex-scale-compose (left (* outer-radius scale)) (right (/ (* outer-radius scale))) (point offset))
                  (:instance inverse-of-* (x (* outer-radius scale))))
            :in-theory (union-theories '(lw-complex-scale-one abs) (theory 'lw-ecew-arithmetic))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-euler-circle-empty-count-from-reference-model
  (implies
   (and (lw-euler-circle-coverp (cons rate height) radius plus-arcs minus-arcs)
        (lw-euler-value-clearance-check rate height anchor-error)
        (rationalp outer-radius) (< 0 outer-radius)
       (rationalp scale) (< 0 scale) (rationalp inner) (<= 0 inner)
       (<= radius (* outer-radius scale inner))
        (< outer-radius rate) (< inner 1)
        (rationalp cutoff-square) (< (* scale scale) cutoff-square) (< cutoff-square 1)
        (natp target)
        (rationalp error) (< 0 error) (<= error 1)
        (rationalp factor-error) (< 0 factor-error) (<= factor-error 1)
        (<= error (* 1/64 (lw-euler-value-clearance-size rate height anchor-error))) (<= factor-error (* 1/64 (lw-euler-value-clearance-size rate height anchor-error)))
        (<= error (* 1/8 (lw-euler-circle-inner-distance-floor rate height outer-radius scale inner anchor-error))) (<= factor-error (* 1/8 (lw-euler-circle-inner-distance-floor rate height outer-radius scale inner anchor-error)))
        (equal (lw-circle-inner-factor-count (lw-polynomial-normalized-factor-roots (lw-euler-coefficient-polynomial rate height outer-radius target error) 1 factor-error) cutoff-square) 0))
   (equal (lw-euler-circle-interior-count (cons rate height) radius plus-arcs minus-arcs) 0))
  :hints (("Goal"
           :cases ((< 0 (lw-euler-circle-interior-count (cons rate height) radius plus-arcs minus-arcs)))
           :use ((:instance lw-euler-circle-outer-data (center (cons rate height)))
                 (:instance lw-euler-circle-inner-distance-floor-data (radius outer-radius))
                 (:instance lw-euler-circle-interior-probe-small-value
                   (center (cons rate height)) (tolerance (* 1/8 (lw-euler-circle-inner-distance-floor rate height outer-radius scale inner anchor-error))) (value-error (* 1/8 (lw-euler-circle-inner-distance-floor rate height outer-radius scale inner anchor-error))))
                 (:instance lw-ecew-normalize-probe (offset (lw-euler-circle-interior-probe-offset (cons rate height) radius plus-arcs minus-arcs (* 1/8 (lw-euler-circle-inner-distance-floor rate height outer-radius scale inner anchor-error)))))
                 (:instance lw-complex-disk-enlarge (point (lw-complex-euler-continuation-value (+ rate (car (lw-euler-circle-interior-probe-offset (cons rate height) radius plus-arcs minus-arcs (* 1/8 (lw-euler-circle-inner-distance-floor rate height outer-radius scale inner anchor-error))))) (+ height (cdr (lw-euler-circle-interior-probe-offset (cons rate height) radius plus-arcs minus-arcs (* 1/8 (lw-euler-circle-inner-distance-floor rate height outer-radius scale inner anchor-error))))) (* 1/8 (lw-euler-circle-inner-distance-floor rate height outer-radius scale inner anchor-error)))) (radius (* 1/8 (lw-euler-circle-inner-distance-floor rate height outer-radius scale inner anchor-error))) (cap (* 1/2 (lw-euler-circle-inner-distance-floor rate height outer-radius scale inner anchor-error))))
                 (:instance lw-euler-circle-small-value-positive-factor-count
                   (radius outer-radius) (point (lw-complex-scale (/ (* outer-radius scale)) (lw-euler-circle-interior-probe-offset (cons rate height) radius plus-arcs minus-arcs (* 1/8 (lw-euler-circle-inner-distance-floor rate height outer-radius scale inner anchor-error))))) (value-error (* 1/8 (lw-euler-circle-inner-distance-floor rate height outer-radius scale inner anchor-error)))))
           :in-theory (union-theories '(lw-euler-circle-interior-count (:type-prescription len)) (theory 'lw-ecew-arithmetic))
           :do-not-induct t))
  :rule-classes nil)
