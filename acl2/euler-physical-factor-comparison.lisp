(in-package "ACL2")

(include-book "circle-normalized-factor-model")
(include-book "euler-coefficient-bounds")
(include-book "polynomial-disk-factorization")

; Normalize the factors chosen on the physical disk without choosing them again.

(local (defthm lw-epfc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-epfc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-epfc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-epfc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-epfc-times-negative (a b) (b a)))
                 :in-theory (disable lw-epfc-times-negative)))))

(local (defthm lw-epfc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-epfc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-epfc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-epfc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-epfc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-epfc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-epfc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-epfc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-epfc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-epfc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-epfc-left-commutes)))))

(local (deftheory lw-epfc-arithmetic (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              
              lw-epfc-left-commutes lw-epfc-left-distributes lw-epfc-fold-constants
              lw-epfc-times-negative lw-epfc-negative-times lw-epfc-zero-times
              lw-epfc-minus-one lw-epfc-double-negative lw-epfc-add-cancel lw-epfc-double lw-epfc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))

(defun lw-euler-physical-factor-polynomial (rate height radius target error factor-error)
  (let ((polynomial (lw-euler-uniform-polynomial rate height radius target error)))
    (lw-circle-normalized-factor-polynomial
      (lw-polynomial-normalized-factor-roots polynomial radius factor-error)
      (lw-polynomial-leading (lw-polynomial-trim polynomial))
      radius)))

(defthm lw-euler-physical-factor-polynomial-comparison
  (implies
   (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate)
       (natp target) (rationalp error) (< 0 error)
       (rationalp factor-error) (< 0 factor-error)
        (lw-complex-diskp point 1))
   (and (rationalp (+ rate (car (lw-complex-scale radius point)))) (< 0 (+ rate (car (lw-complex-scale radius point)))) (rationalp (+ height (cdr (lw-complex-scale radius point))))
        (lw-complex-diskp (lw-complex-scale radius point) radius)
        (lw-complexp (lw-complex-polynomial (lw-euler-physical-factor-polynomial rate height radius target error factor-error) point 0)) (lw-complexp (lw-complex-polynomial (lw-euler-uniform-polynomial rate height radius target error) (lw-complex-scale radius point) 0))
        (lw-complex-diskp (lw-complex-sub (lw-complex-polynomial (lw-euler-physical-factor-polynomial rate height radius target error factor-error) point 0) (lw-complex-polynomial (lw-euler-uniform-polynomial rate height radius target error) (lw-complex-scale radius point) 0)) factor-error)))
  :hints (("Goal"
           :use ((:instance lw-complex-disk-data (radius 1))
                 (:instance lw-complex-scale-disk (factor radius) (radius 1))
                 (:instance lw-complex-scale-rational (factor radius))
                 (:instance lw-euler-disk-point-data (offset (lw-complex-scale radius point)))
                 lw-euler-uniform-polynomial-valid
                 (:instance lw-polynomial-disk-factor-data
                   (coefficients (lw-euler-uniform-polynomial rate height radius target error)) (outer-radius radius) (epsilon factor-error))
                 (:instance lw-circle-normalized-factor-polynomial-evaluation (roots (lw-polynomial-normalized-factor-roots (lw-euler-uniform-polynomial rate height radius target error) radius factor-error)) (leading (lw-polynomial-leading (lw-polynomial-trim (lw-euler-uniform-polynomial rate height radius target error)))) (scale radius))
                 (:instance lw-polynomial-disk-factor-value-error
                   (coefficients (lw-euler-uniform-polynomial rate height radius target error)) (outer-radius radius) (epsilon factor-error) (point (lw-complex-scale radius point)))
                 (:instance lw-complex-polynomial-rational
                   (coefficients (lw-euler-uniform-polynomial rate height radius target error)) (offset 0) (point (lw-complex-scale radius point)))
                 (:instance lw-complex-polynomial-rational
                   (coefficients (lw-polynomial-disk-factor-polynomial (lw-euler-uniform-polynomial rate height radius target error) radius factor-error)) (offset 0) (point (lw-complex-scale radius point)))
                 (:instance lw-complex-difference-symmetric
                   (left (lw-complex-polynomial (lw-euler-uniform-polynomial rate height radius target error) (lw-complex-scale radius point) 0)) (right (lw-complex-polynomial (lw-polynomial-disk-factor-polynomial (lw-euler-uniform-polynomial rate height radius target error) radius factor-error) (lw-complex-scale radius point) 0)) (radius factor-error)))
           :in-theory (union-theories '(lw-euler-physical-factor-polynomial lw-polynomial-disk-factor-polynomial abs) (theory 'lw-epfc-arithmetic))
           :do-not-induct t))
  :rule-classes nil)

(defthm lw-euler-physical-factor-native-comparison
  (implies
   (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate)
       (natp target) (rationalp error) (< 0 error)
       (rationalp factor-error) (< 0 factor-error)
        (lw-complex-diskp point 1) (rationalp value-error) (< 0 value-error))
   (and (lw-complexp (lw-complex-polynomial (lw-euler-physical-factor-polynomial rate height radius target error factor-error) point 0)) (lw-complexp (lw-complex-euler-continuation-value (+ rate (car (lw-complex-scale radius point))) (+ height (cdr (lw-complex-scale radius point))) value-error))
        (lw-complex-diskp (lw-complex-sub (lw-complex-polynomial (lw-euler-physical-factor-polynomial rate height radius target error factor-error) point 0) (lw-complex-euler-continuation-value (+ rate (car (lw-complex-scale radius point))) (+ height (cdr (lw-complex-scale radius point))) value-error)) (+ factor-error error (* 1/4 value-error)))))
  :hints (("Goal"
           :use (lw-euler-physical-factor-polynomial-comparison
                 (:instance lw-complex-euler-continuation-value-rational (rate (+ rate (car (lw-complex-scale radius point)))) (height (+ height (cdr (lw-complex-scale radius point)))) (error value-error))
                 (:instance lw-complex-euler-uniform-polynomial-comparison (point (lw-complex-scale radius point)))
                 (:instance lw-complex-difference-triangle
                   (left (lw-complex-polynomial (lw-euler-physical-factor-polynomial rate height radius target error factor-error) point 0)) (middle (lw-complex-polynomial (lw-euler-uniform-polynomial rate height radius target error) (lw-complex-scale radius point) 0)) (right (lw-complex-euler-continuation-value (+ rate (car (lw-complex-scale radius point))) (+ height (cdr (lw-complex-scale radius point))) value-error))
                   (radius factor-error) (other-radius (+ error (* 1/4 value-error)))))
           :in-theory (theory 'lw-epfc-arithmetic)
           :do-not-induct t))
  :rule-classes nil)

(defthm lw-euler-physical-factor-unit-cap
  (implies
   (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate)
       (natp target) (rationalp error) (< 0 error)
       (rationalp factor-error) (< 0 factor-error)
        (<= error 1) (<= factor-error 1) (lw-complex-diskp point 1))
   (lw-complex-diskp (lw-complex-polynomial (lw-euler-physical-factor-polynomial rate height radius target error factor-error) point 0) (+ 1 (lw-euler-uniform-coefficient-cap rate height radius))))
  :hints (("Goal"
           :use (lw-euler-physical-factor-polynomial-comparison lw-euler-uniform-polynomial-valid
                 lw-euler-uniform-coefficient-cap-valid lw-complex-euler-polynomial-uniform-cap
                 (:instance lw-complex-disk-data (radius 1))
                 (:instance lw-polynomial-rescale-evaluation (coefficients (lw-euler-uniform-polynomial rate height radius target error)) (factor radius) (offset 0))
                 (:instance lw-complex-sub-zero (point (lw-complex-polynomial (lw-euler-physical-factor-polynomial rate height radius target error factor-error) point 0)))
                 (:instance lw-complex-sub-zero (point (lw-complex-polynomial (lw-euler-uniform-polynomial rate height radius target error) (lw-complex-scale radius point) 0)))
                 (:instance lw-complex-disk-enlarge (point (lw-complex-polynomial (lw-euler-uniform-polynomial rate height radius target error) (lw-complex-scale radius point) 0)) (radius (+ -1 error (lw-euler-uniform-coefficient-cap rate height radius))) (cap (lw-euler-uniform-coefficient-cap rate height radius)))
                 (:instance lw-complex-difference-triangle
                   (left (lw-complex-polynomial (lw-euler-physical-factor-polynomial rate height radius target error factor-error) point 0)) (middle (lw-complex-polynomial (lw-euler-uniform-polynomial rate height radius target error) (lw-complex-scale radius point) 0)) (right (cons 0 0))
                   (radius factor-error) (other-radius (lw-euler-uniform-coefficient-cap rate height radius)))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-complex-polynomial (lw-euler-physical-factor-polynomial rate height radius target error factor-error) point 0)) (radius (+ factor-error (lw-euler-uniform-coefficient-cap rate height radius))) (cap (+ 1 (lw-euler-uniform-coefficient-cap rate height radius)))))
           :in-theory (union-theories '(lw-euler-coefficient-polynomial) (theory 'lw-epfc-arithmetic))
           :do-not-induct t))
  :rule-classes nil)
