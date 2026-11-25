(in-package "ACL2")

(include-book "euler-circle-uniform-clearance-budget")
(include-book "euler-circle-factor-anchor")

; Transfer the degree-independent factor floor to the native Euler
; value at a point on the generated rational circle.

(local (defthm lw-ecua-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ecua-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ecua-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ecua-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ecua-times-negative (a b) (b a)))
                 :in-theory (disable lw-ecua-times-negative)))))

(local (defthm lw-ecua-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ecua-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ecua-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ecua-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ecua-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ecua-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ecua-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ecua-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecua-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local
 (defthm lw-ecua-radius-order
   (implies (and (rationalp lower) (<= 0 lower) (rationalp upper) (< lower upper)
                 (rationalp scale) (< upper scale)
                 (rationalp cutoff-square) (< (* scale scale) cutoff-square) (< cutoff-square 1))
            (and (<= 0 cutoff-square) (< (* upper upper) cutoff-square) (< upper 1)))
   :hints (("Goal"
            :use ((:instance lw-ecua-multiply-order (a upper) (b scale) (factor upper))
                  (:instance lw-ecua-multiply-order (a upper) (b scale) (factor scale))
                  (:instance lw-ecua-multiply-order (a 1) (b scale) (factor scale))
                  (:instance lw-ecua-multiply-order (a 0) (b upper) (factor upper)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)

              lw-ecua-left-commutes lw-ecua-left-distributes lw-ecua-fold-constants
              lw-ecua-times-negative lw-ecua-negative-times lw-ecua-zero-times
              lw-ecua-minus-one lw-ecua-double-negative lw-ecua-add-cancel lw-ecua-double lw-ecua-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-ecua-factor-value-floor
   (implies (and (rationalp rate) (rationalp height) (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
                (natp target) (rationalp error) (< 0 error) (rationalp factor-error) (< 0 factor-error) (< 3 rate)
                (rationalp lower) (<= 0 lower) (rationalp upper) (< lower upper)
                (rationalp scale) (< upper scale)
                (rationalp cutoff-square) (< (* scale scale) cutoff-square) (< cutoff-square 1)
                (<= error (lw-euler-circle-uniform-approximation-limit rate height outer-radius lower upper scale cutoff-square)) (<= factor-error (lw-euler-circle-uniform-approximation-limit rate height outer-radius lower upper scale cutoff-square))
                (lw-complexp point) (equal (lw-complex-norm-square point) (* (car (lw-euler-circle-bounded-radius rate height outer-radius target error factor-error lower upper cutoff-square)) (car (lw-euler-circle-bounded-radius rate height outer-radius target error factor-error lower upper cutoff-square)))))
            (and (lw-complex-diskp point 1)
                 (rationalp (lw-euler-circle-uniform-distance rate height outer-radius lower upper scale cutoff-square)) (< 0 (lw-euler-circle-uniform-distance rate height outer-radius lower upper scale cutoff-square))
                 (<= (* (lw-euler-circle-uniform-distance rate height outer-radius lower upper scale cutoff-square) (lw-euler-circle-uniform-distance rate height outer-radius lower upper scale cutoff-square)) (lw-complex-norm-square (lw-complex-polynomial (lw-polynomial-disk-factor-polynomial (lw-euler-coefficient-polynomial rate height outer-radius target error) 1 factor-error) point 0)))))
   :hints (("Goal"
            :use (lw-ecua-radius-order lw-euler-circle-uniform-clearance-budget-data
                  lw-euler-zeta-clearance-check lw-euler-circle-bounded-radius-valid lw-euler-circle-jensen-count-budget-natural
                  (:instance lw-euler-circle-inner-factor-count
                    (radius outer-radius) (anchor-error (lw-euler-zeta-clearance-request rate height)))
                  (:instance lw-euler-circle-factor-model-data
                    (radius outer-radius) (anchor-error (lw-euler-zeta-clearance-request rate height)))
                  (:instance lw-circle-factor-uniform-clearance
                    (roots (lw-polynomial-normalized-factor-roots (lw-euler-coefficient-polynomial rate height outer-radius target error) 1 factor-error)) (leading (lw-polynomial-leading (lw-polynomial-trim (lw-euler-coefficient-polynomial rate height outer-radius target error)))) (center-lower (* (* 1/8 (lw-euler-value-clearance-size rate height (lw-euler-zeta-clearance-request rate height))) (* 1/8 (lw-euler-value-clearance-size rate height (lw-euler-zeta-clearance-request rate height))))) (cap (+ 1 (lw-euler-uniform-coefficient-cap rate height outer-radius))) (budget (lw-euler-circle-jensen-count-budget rate height outer-radius cutoff-square)))
                  (:instance lw-complex-disk-norm-square (radius (car (lw-euler-circle-bounded-radius rate height outer-radius target error factor-error lower upper cutoff-square))))
                  (:instance lw-complex-disk-enlarge (radius (car (lw-euler-circle-bounded-radius rate height outer-radius target error factor-error lower upper cutoff-square))) (cap 1)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-circle-bounded-radius lw-euler-circle-jensen-count-budget lw-polynomial-disk-factor-polynomial
              lw-ecua-left-commutes lw-ecua-left-distributes lw-ecua-fold-constants
              lw-ecua-times-negative lw-ecua-negative-times lw-ecua-zero-times
              lw-ecua-minus-one lw-ecua-double-negative lw-ecua-add-cancel lw-ecua-double lw-ecua-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-euler-disk-factor-native-comparison
  (implies (and (rationalp rate) (rationalp height) (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
               (natp target) (rationalp error) (< 0 error) (rationalp factor-error) (< 0 factor-error) (lw-complex-diskp point 1)
                (rationalp anchor-error) (< 0 anchor-error))
           (and (rationalp (+ rate (car (lw-complex-scale outer-radius point)))) (< 0 (+ rate (car (lw-complex-scale outer-radius point)))) (rationalp (+ height (cdr (lw-complex-scale outer-radius point))))
                (lw-complexp (lw-complex-polynomial (lw-polynomial-disk-factor-polynomial (lw-euler-coefficient-polynomial rate height outer-radius target error) 1 factor-error) point 0))
                (lw-complex-diskp (lw-complex-sub (lw-complex-polynomial (lw-polynomial-disk-factor-polynomial (lw-euler-coefficient-polynomial rate height outer-radius target error) 1 factor-error) point 0) (lw-complex-euler-continuation-value (+ rate (car (lw-complex-scale outer-radius point))) (+ height (cdr (lw-complex-scale outer-radius point))) anchor-error))
                   (+ factor-error error (* 1/4 anchor-error)))))
  :hints (("Goal"
           :use ((:instance lw-complex-disk-data (radius 1))
                 (:instance lw-complex-scale-disk (factor outer-radius) (radius 1))
                 (:instance lw-euler-polynomial-coefficient-rational (radius outer-radius) (index 0))
                 (:instance lw-euler-uniform-polynomial-valid (radius outer-radius))
                 (:instance lw-polynomial-rescale-evaluation
                   (coefficients (lw-euler-uniform-polynomial rate height outer-radius target error)) (factor outer-radius) (offset 0))
                 (:instance lw-euler-disk-point-data (radius outer-radius) (offset (lw-complex-scale outer-radius point)))
                 (:instance lw-complex-euler-uniform-polynomial-comparison
                   (radius outer-radius) (point (lw-complex-scale outer-radius point)) (value-error anchor-error))
                 (:instance lw-polynomial-disk-factor-data (coefficients (lw-euler-coefficient-polynomial rate height outer-radius target error)) (outer-radius 1) (epsilon factor-error))
                 (:instance lw-polynomial-disk-factor-value-error (coefficients (lw-euler-coefficient-polynomial rate height outer-radius target error)) (outer-radius 1) (epsilon factor-error))
                 (:instance lw-complex-polynomial-rational (coefficients (lw-euler-coefficient-polynomial rate height outer-radius target error)) (offset 0))
                 (:instance lw-complex-polynomial-rational (coefficients (lw-polynomial-disk-factor-polynomial (lw-euler-coefficient-polynomial rate height outer-radius target error) 1 factor-error)) (offset 0))
                 (:instance lw-complex-euler-continuation-value-rational
                   (rate (+ rate (car (lw-complex-scale outer-radius point)))) (height (+ height (cdr (lw-complex-scale outer-radius point)))) (error anchor-error))
                 (:instance lw-complex-difference-symmetric (left (lw-complex-polynomial (lw-euler-coefficient-polynomial rate height outer-radius target error) point 0)) (right (lw-complex-polynomial (lw-polynomial-disk-factor-polynomial (lw-euler-coefficient-polynomial rate height outer-radius target error) 1 factor-error) point 0)) (radius factor-error))
                 (:instance lw-complex-difference-triangle
                   (left (lw-complex-polynomial (lw-polynomial-disk-factor-polynomial (lw-euler-coefficient-polynomial rate height outer-radius target error) 1 factor-error) point 0)) (middle (lw-complex-polynomial (lw-euler-coefficient-polynomial rate height outer-radius target error) point 0)) (right (lw-complex-euler-continuation-value (+ rate (car (lw-complex-scale outer-radius point))) (+ height (cdr (lw-complex-scale outer-radius point))) anchor-error))
                   (radius factor-error) (other-radius (+ error (* 1/4 anchor-error)))))
           :in-theory (union-theories
           '(fold-consts-in-+ (:executable-counterpart lw-complexp)
             lw-euler-coefficient-polynomial abs
             lw-ecua-left-commutes lw-ecua-left-distributes lw-ecua-fold-constants
             lw-ecua-times-negative lw-ecua-negative-times lw-ecua-zero-times
             lw-ecua-minus-one lw-ecua-double-negative lw-ecua-add-cancel lw-ecua-double lw-ecua-add-double
             natp posp zp fix car-cons cdr-cons
             commutativity-of-* associativity-of-*
             commutativity-of-+ commutativity-2-of-+ associativity-of-+
             distributivity distributivity-of-minus-over-+
             inverse-of-+ unicity-of-0 unicity-of-1)
           (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(defthm lw-euler-circle-uniform-anchor
  (implies (and (rationalp rate) (rationalp height) (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
                (natp target) (rationalp error) (< 0 error) (rationalp factor-error) (< 0 factor-error) (< 3 rate)
                (rationalp lower) (<= 0 lower) (rationalp upper) (< lower upper)
                (rationalp scale) (< upper scale)
                (rationalp cutoff-square) (< (* scale scale) cutoff-square) (< cutoff-square 1)
                (<= error (lw-euler-circle-uniform-approximation-limit rate height outer-radius lower upper scale cutoff-square)) (<= factor-error (lw-euler-circle-uniform-approximation-limit rate height outer-radius lower upper scale cutoff-square))
                (lw-complexp point) (equal (lw-complex-norm-square point) (* (car (lw-euler-circle-bounded-radius rate height outer-radius target error factor-error lower upper cutoff-square)) (car (lw-euler-circle-bounded-radius rate height outer-radius target error factor-error lower upper cutoff-square))))
                (rationalp anchor-error) (< 0 anchor-error)
                (<= anchor-error (* 1/32 (lw-euler-circle-uniform-distance rate height outer-radius lower upper scale cutoff-square))))
           (and (lw-euler-value-clearance-check (+ rate (car (lw-complex-scale outer-radius point))) (+ height (cdr (lw-complex-scale outer-radius point))) anchor-error)
                (<= (* 1/2 (lw-euler-circle-uniform-distance rate height outer-radius lower upper scale cutoff-square)) (lw-euler-value-clearance-size (+ rate (car (lw-complex-scale outer-radius point))) (+ height (cdr (lw-complex-scale outer-radius point))) anchor-error))))
  :hints (("Goal"
           :use (lw-euler-circle-uniform-clearance-budget-data lw-ecua-factor-value-floor lw-euler-disk-factor-native-comparison
                 (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-polynomial (lw-polynomial-disk-factor-polynomial (lw-euler-coefficient-polynomial rate height outer-radius target error) 1 factor-error) point 0) (lw-complex-euler-continuation-value (+ rate (car (lw-complex-scale outer-radius point))) (+ height (cdr (lw-complex-scale outer-radius point))) anchor-error)))
                   (radius (+ factor-error error (* 1/4 anchor-error))) (cap (* 1/4 (lw-euler-circle-uniform-distance rate height outer-radius lower upper scale cutoff-square))))
                 (:instance lw-euler-value-clearance-from-approximation
                   (rate (+ rate (car (lw-complex-scale outer-radius point)))) (height (+ height (cdr (lw-complex-scale outer-radius point))))
                   (error anchor-error) (lower (lw-euler-circle-uniform-distance rate height outer-radius lower upper scale cutoff-square)) (model (lw-complex-polynomial (lw-polynomial-disk-factor-polynomial (lw-euler-coefficient-polynomial rate height outer-radius target error) 1 factor-error) point 0))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)

              lw-ecua-left-commutes lw-ecua-left-distributes lw-ecua-fold-constants
              lw-ecua-times-negative lw-ecua-negative-times lw-ecua-zero-times
              lw-ecua-minus-one lw-ecua-double-negative lw-ecua-add-cancel lw-ecua-double lw-ecua-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
