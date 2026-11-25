(in-package "ACL2")

(include-book "complex-laplace-basis")

; Compute the damped-exponential integral on a ray starting at an
; arbitrary nonnegative rational point. This is the endpoint needed
; when prime-power ramps start at a computed logarithm.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-reciprocal lw-complex-norm-square
                 lw-complex-l1 lw-rational-power lw-complex-exp-value
                 lw-exp-bounds lw-exp-neg-bounds lw-exp-index lw-exp-band lw-exp-sum lw-exp-term
                 lw-damped-phase-sample lw-phase-value
                 lw-complex-exp-integral-value lw-complex-exp-integral-grid
                 lw-complex-exp-primitive-value lw-complex-exp-grid
                 lw-complex-laplace-point lw-complex-laplace-cutoff lw-complex-quotient
                 lw-complex-disk-enlarge lw-disk-enlarge lw-precision-fuel)))

(local (defthm lw-cls-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-cls-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-cls-times-negative
         (implies (and (rationalp a) (rationalp b)) (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-cls-negative-times
         (implies (and (rationalp a) (rationalp b)) (equal (* (- a) b) (- (* a b))))))
(local (defthm lw-cls-zero-times (equal (* 0 a) 0)))
(local (defthm lw-cls-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))
(local (defthm lw-cls-double-negative (implies (rationalp a) (equal (- (- a)) a))))
(local (defthm lw-cls-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))
(local (defthm lw-cls-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))
(local (defthm lw-cls-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))
(local (defthm lw-cls-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))
(local (defthm lw-cls-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-cls-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-cls-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-cls-left-commutes)))))
(local (defthm lw-cls-fuel-natural
         (natp (lw-precision-fuel width error))
         :hints (("Goal" :in-theory (enable lw-precision-fuel)))
         :rule-classes (:rewrite :type-prescription)))
(local (defthm lw-cls-pair-complex
         (implies (and (rationalp a) (rationalp b)) (lw-complexp (cons a b)))
         :hints (("Goal" :in-theory (enable lw-complexp)))))

(local (defthm lw-cls-scale-laplace
         (implies (and (rationalp rate) (rationalp height) (rationalp cutoff))
                  (equal (lw-complex-scale cutoff (lw-complex-laplace-point rate height))
                         (cons (- (* rate cutoff)) (- (* height cutoff)))))
         :hints (("Goal" :in-theory (enable lw-complex-scale lw-complex-laplace-point)))))

(local (defthm lw-cls-scale-zero
         (equal (lw-complex-scale 0 point) (cons 0 0))
         :hints (("Goal" :in-theory (enable lw-complex-scale)))))

(local (defthm lw-cls-sub-negative
         (implies (and (lw-complexp a) (lw-complexp b))
                  (equal (lw-complex-sub (lw-complex-sub a b) (lw-complex-scale -1 b)) a))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-sub lw-complex-scale)))))

(local (defthm lw-cls-origin-shift
         (implies (and (lw-complexp a) (lw-complexp point))
                  (equal
                   (lw-complex-sub (lw-complex-quotient (lw-complex-sub a (cons 1 0)) point)
                                   (lw-complex-scale -1 (lw-complex-reciprocal point)))
                   (lw-complex-quotient a point)))
         :hints (("Goal"
                  :in-theory
                  (e/d (lw-complex-quotient lw-complex-mul-subtract
                        lw-complex-mul-commutative lw-complex-mul-left-commutes)
                       (lw-complex-sub-products-right))))))

(local (defthm lw-cls-quotient-disk
         (implies (and (lw-complex-diskp numerator radius) (lw-complexp denominator)
                       (rationalp clearance) (< 0 clearance)
                       (<= (* clearance clearance) (lw-complex-norm-square denominator)))
                  (lw-complex-diskp (lw-complex-quotient numerator denominator)
                                    (* radius (/ clearance))))
         :hints (("Goal"
                  :use ((:instance lw-complex-reciprocal-disk-bound
                          (point denominator) (lower clearance))
                        (:instance lw-complex-mul-disk
                          (left numerator) (right (lw-complex-reciprocal denominator))
                          (other-radius (/ clearance))))
                  :in-theory (e/d (lw-complex-quotient)
                                  (lw-complex-reciprocal-disk-bound lw-complex-mul-disk))))))


(defun lw-complex-laplace-shifted-value (rate height start error)
  (lw-complex-scale -1
    (lw-complex-quotient
      (lw-complex-exp-value (lw-complex-scale start (lw-complex-laplace-point rate height))
                            (* 1/64 rate error))
      (lw-complex-laplace-point rate height))))

(defun lw-complex-laplace-shifted-grid (rate height start error)
  (lw-complex-exp-integral-grid (lw-complex-laplace-point rate height) start
    (lw-complex-laplace-cutoff rate error) rate (* 1/4 error)))

(defthm lw-complex-laplace-shifted-value-rational
  (implies (and (rationalp rate) (< 0 rate) (rationalp height)
                (rationalp start) (<= 0 start) (rationalp error) (< 0 error))
           (lw-complexp (lw-complex-laplace-shifted-value rate height start error)))
  :hints (("Goal" :use (lw-complex-laplace-point-data) :nonlinearp t)))

(defthm lw-complex-laplace-shifted-value-identity
  (implies (and (rationalp rate) (< 0 rate) (rationalp height)
                (rationalp start) (<= 0 start) (rationalp error) (< 0 error))
           (equal
            (lw-complex-laplace-shifted-value rate height start error)
            (lw-complex-mul
              (lw-complex-exp-value (lw-complex-scale start (lw-complex-laplace-point rate height))
                                    (* 1/64 rate error))
              (lw-complex-reciprocal (cons rate height)))))
  :hints (("Goal" :use (lw-complex-laplace-point-data)
                   :in-theory (e/d (lw-complex-quotient)
                                   (lw-complex-laplace-point-data lw-complex-mul-commutative
                                    lw-complex-mul-left-commutes))
                   :nonlinearp t :do-not-induct t)))

(local (in-theory (disable lw-complex-laplace-shifted-value-identity)))

(local (defthm lw-cls-primitive-shift
         (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp point))
                  (equal
                   (lw-complex-sub
                     (lw-complex-quotient (lw-complex-sub a b) point)
                     (lw-complex-scale -1 (lw-complex-quotient b point)))
                   (lw-complex-quotient a point)))
         :hints (("Goal"
                  :use ((:instance lw-complex-reciprocal-rational))
                  :in-theory
                  (e/d (lw-complexp lw-complex-sub lw-complex-mul lw-complex-scale lw-complex-quotient)
                       (lw-complex-reciprocal-rational))))))

(defthm lw-complex-laplace-shifted-primitive-tail
  (implies (and (rationalp rate) (< 0 rate) (rationalp height)
                (rationalp start) (<= 0 start) (rationalp error) (< 0 error))
           (lw-complex-diskp
            (lw-complex-sub
              (lw-complex-exp-integral-value (lw-complex-laplace-point rate height) start
                (lw-complex-laplace-cutoff rate error) rate (* 1/4 error))
              (lw-complex-laplace-shifted-value rate height start error))
            (* 1/2 error)))
  :hints (("Goal"
           :use (lw-complex-laplace-cutoff-adequate lw-complex-laplace-point-data
                 (:instance lw-cls-positive-product (a rate) (b error))
                 (:instance lw-cls-multiply-order (a 0) (b start) (factor rate))
                 (:instance lw-reciprocal-antitone
                   (left (+ 1 (* rate (lw-complex-laplace-cutoff rate error))))
                   (right (+ 1 (* rate (+ start (lw-complex-laplace-cutoff rate error))))))
                 (:instance lw-complex-exp-damped-decay
                   (value (* rate (+ start (lw-complex-laplace-cutoff rate error))))
                   (angle (- (* height (+ start (lw-complex-laplace-cutoff rate error)))))
                   (error (* 1/64 rate error)))
                 (:instance lw-cls-primitive-shift
                   (a (lw-complex-exp-value
                     (lw-complex-scale (+ start (lw-complex-laplace-cutoff rate error))
                                       (lw-complex-laplace-point rate height)) (* 1/64 rate error)))
                   (b (lw-complex-exp-value
                     (lw-complex-scale start (lw-complex-laplace-point rate height)) (* 1/64 rate error)))
                   (point (lw-complex-laplace-point rate height)))
                 (:instance lw-cls-quotient-disk
                   (numerator (lw-complex-exp-value
                     (lw-complex-scale (+ start (lw-complex-laplace-cutoff rate error))
                                       (lw-complex-laplace-point rate height)) (* 1/64 rate error)))
                   (denominator (lw-complex-laplace-point rate height)) (clearance rate)
                   (radius (+ (/ (+ 1 (* rate (+ start (lw-complex-laplace-cutoff rate error)))))
                              (* 1/32 rate error))))
                 (:instance lw-cls-multiply-order
                   (a (/ (+ 1 (* rate (+ start (lw-complex-laplace-cutoff rate error))))))
                   (b (/ (+ 1 (* rate (lw-complex-laplace-cutoff rate error))))) (factor (/ rate)))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-complex-sub
                     (lw-complex-exp-integral-value (lw-complex-laplace-point rate height) start
                       (lw-complex-laplace-cutoff rate error) rate (* 1/4 error))
                     (lw-complex-laplace-shifted-value rate height start error)))
                   (radius (* (+ (/ (+ 1 (* rate (+ start (lw-complex-laplace-cutoff rate error)))))
                                  (* 1/32 rate error)) (/ rate)))
                   (cap (* 1/2 error))))
           :in-theory
           (e/d (lw-complex-laplace-shifted-value lw-complex-exp-integral-value
                 lw-complex-exp-primitive-value)
                (lw-complex-laplace-cutoff-adequate lw-complex-laplace-point-data lw-cls-primitive-shift
                 lw-cls-quotient-disk lw-complex-exp-damped-decay lw-complex-sub-add-first
                 lw-reciprocal-antitone))
           :nonlinearp nil :do-not-induct t)))

(local (defthm lw-cls-grid-rational
         (implies (and (lw-complexp point) (rationalp start) (<= 0 start)
                       (rationalp length) (< 0 length) (rationalp clearance) (< 0 clearance)
                       (rationalp error) (< 0 error))
                  (lw-complexp (lw-complex-exp-integral-grid point start length clearance error)))
         :hints (("Goal" :use (lw-complex-exp-integration-parameters)
                         :in-theory (e/d (lw-complex-exp-integral-grid)
                                         (lw-complex-exp-integration-parameters))
                         :do-not-induct t))))

(defthm lw-complex-laplace-shifted-grid-rational
  (implies (and (rationalp rate) (< 0 rate) (rationalp height)
                (rationalp start) (<= 0 start) (rationalp error) (< 0 error))
           (lw-complexp (lw-complex-laplace-shifted-grid rate height start error)))
  :hints (("Goal" :in-theory (enable lw-complex-laplace-shifted-grid))))

(defthm lw-complex-laplace-shifted-grid-endpoint
  (implies (and (rationalp rate) (< 0 rate) (rationalp height)
                (rationalp start) (<= 0 start) (rationalp error) (< 0 error))
           (lw-complex-diskp
            (lw-complex-sub (lw-complex-laplace-shifted-value rate height start error)
                            (lw-complex-laplace-shifted-grid rate height start error)) error))
  :hints (("Goal"
           :use (lw-complex-laplace-point-data lw-complex-laplace-shifted-primitive-tail
                 (:instance lw-complex-exp-computed-quadrature
                   (point (lw-complex-laplace-point rate height)) (start start)
                   (length (lw-complex-laplace-cutoff rate error)) (clearance rate) (error (* 1/4 error)))
                 (:instance lw-complex-difference-symmetric
                   (left (lw-complex-exp-integral-value (lw-complex-laplace-point rate height) start
                           (lw-complex-laplace-cutoff rate error) rate (* 1/4 error)))
                   (right (lw-complex-laplace-shifted-value rate height start error)) (radius (* 1/2 error)))
                 (:instance lw-complex-difference-triangle
                   (left (lw-complex-laplace-shifted-value rate height start error))
                   (middle (lw-complex-exp-integral-value (lw-complex-laplace-point rate height) start
                             (lw-complex-laplace-cutoff rate error) rate (* 1/4 error)))
                   (right (lw-complex-laplace-shifted-grid rate height start error))
                   (radius (* 1/2 error)) (other-radius (* 1/4 error)))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-complex-sub (lw-complex-laplace-shifted-value rate height start error)
                                          (lw-complex-laplace-shifted-grid rate height start error)))
                   (radius (+ (* 1/2 error) (* 1/4 error))) (cap error)))
           :in-theory
           (e/d (lw-complex-laplace-shifted-grid)
                (lw-complex-laplace-point-data lw-complex-laplace-shifted-primitive-tail
                 lw-complex-exp-computed-quadrature lw-complex-difference-triangle
                 lw-complex-exp-integral-value lw-complex-exp-integral-grid
                 lw-complex-laplace-shifted-value))
           :do-not-induct t)))
