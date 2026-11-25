(in-package "ACL2")

(include-book "euler-coefficient-bounds")

; One coarse polynomial bounds all fine native values on a fixed disk.

(local (defthm lw-edvc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-edvc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-edvc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-edvc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-edvc-times-negative (a b) (b a)))
                 :in-theory (disable lw-edvc-times-negative)))))

(local (defthm lw-edvc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-edvc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-edvc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-edvc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-edvc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-edvc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-edvc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-edvc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-edvc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local
 (defthm lw-edvc-unit-coordinates
   (implies (and (lw-complex-diskp point radius) (< 0 radius))
            (and (lw-complexp (lw-complex-scale (/ radius) point)) (lw-complex-diskp (lw-complex-scale (/ radius) point) 1)
                 (equal (lw-complex-scale radius (lw-complex-scale (/ radius) point)) point)))
   :hints (("Goal"
            :use (lw-complex-disk-data
                  (:instance lw-reciprocal-positive (value radius))
                  (:instance lw-complex-scale-disk (factor (/ radius)))
                  (:instance lw-complex-scale-rational (factor (/ radius)))
                  (:instance lw-complex-scale-compose (left radius) (right (/ radius)))
                  (:instance inverse-of-* (x radius)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complex-scale-one abs
              lw-edvc-left-commutes lw-edvc-left-distributes lw-edvc-fold-constants
              lw-edvc-times-negative lw-edvc-negative-times lw-edvc-zero-times
              lw-edvc-minus-one lw-edvc-double-negative lw-edvc-add-cancel lw-edvc-double lw-edvc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-edvc-coarse-cap
   (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate)
                 (lw-complex-diskp point radius))
            (lw-complex-diskp (lw-complex-polynomial (lw-euler-uniform-polynomial rate height radius 0 1) point 0) (lw-euler-uniform-coefficient-cap rate height radius)))
   :hints (("Goal"
            :use (lw-edvc-unit-coordinates lw-euler-uniform-coefficient-cap-valid
                  (:instance lw-euler-uniform-polynomial-valid (target 0) (error 1))
                  (:instance lw-polynomial-rescale-evaluation
                    (coefficients (lw-euler-uniform-polynomial rate height radius 0 1)) (factor radius) (offset 0) (point (lw-complex-scale (/ radius) point)))
                  (:instance lw-complex-euler-polynomial-uniform-cap
                    (target 0) (error 1) (point (lw-complex-scale (/ radius) point))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-coefficient-polynomial
              lw-edvc-left-commutes lw-edvc-left-distributes lw-edvc-fold-constants
              lw-edvc-times-negative lw-edvc-negative-times lw-edvc-zero-times
              lw-edvc-minus-one lw-edvc-double-negative lw-edvc-add-cancel lw-edvc-double lw-edvc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-euler-disk-native-value-cap
  (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate)
                (lw-complex-diskp point radius) (rationalp error) (< 0 error) (<= error 1))
           (lw-complex-diskp (lw-complex-euler-continuation-value (+ rate (car point)) (+ height (cdr point)) error) (+ 2 (lw-euler-uniform-coefficient-cap rate height radius))))
  :hints (("Goal"
           :use (lw-edvc-coarse-cap lw-euler-uniform-coefficient-cap-valid
                 (:instance lw-complex-disk-data)
                 (:instance lw-euler-uniform-polynomial-valid (target 0) (error 1))
                 (:instance lw-complex-polynomial-rational (coefficients (lw-euler-uniform-polynomial rate height radius 0 1)) (offset 0))
                 (:instance lw-euler-disk-point-data (offset point))
                 (:instance lw-complex-euler-continuation-value-rational
                   (rate (+ rate (car point))) (height (+ height (cdr point))))
                 (:instance lw-complex-euler-uniform-polynomial-comparison (target 0) (error 1) (value-error error))
                 (:instance lw-complex-difference-symmetric (left (lw-complex-polynomial (lw-euler-uniform-polynomial rate height radius 0 1) point 0)) (right (lw-complex-euler-continuation-value (+ rate (car point)) (+ height (cdr point)) error)) (radius (+ 1 (* 1/4 error))))
                 (:instance lw-complex-sub-zero (point (lw-complex-polynomial (lw-euler-uniform-polynomial rate height radius 0 1) point 0)))
                 (:instance lw-complex-sub-zero (point (lw-complex-euler-continuation-value (+ rate (car point)) (+ height (cdr point)) error)))
                 (:instance lw-complex-difference-triangle
                   (left (lw-complex-euler-continuation-value (+ rate (car point)) (+ height (cdr point)) error)) (middle (lw-complex-polynomial (lw-euler-uniform-polynomial rate height radius 0 1) point 0)) (right (cons 0 0))
                   (radius (+ 1 (* 1/4 error))) (other-radius (lw-euler-uniform-coefficient-cap rate height radius)))
                 (:instance lw-complex-disk-enlarge (point (lw-complex-euler-continuation-value (+ rate (car point)) (+ height (cdr point)) error)) (radius (+ 1 (* 1/4 error) (lw-euler-uniform-coefficient-cap rate height radius))) (cap (+ 2 (lw-euler-uniform-coefficient-cap rate height radius)))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)

              lw-edvc-left-commutes lw-edvc-left-distributes lw-edvc-fold-constants
              lw-edvc-times-negative lw-edvc-negative-times lw-edvc-zero-times
              lw-edvc-minus-one lw-edvc-double-negative lw-edvc-add-cancel lw-edvc-double lw-edvc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
