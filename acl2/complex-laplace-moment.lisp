(in-package "ACL2")

(include-book "complex-exp-moment-integral")
(include-book "complex-laplace-basis")
(include-book "complex-kernel-agreement")
(include-book "kernel-mass")

; Effective Laplace normalization of the first-moment basis. First bound
; the damped endpoint, then combine a computed cutoff with the certified
; finite rectangle sum. No improper-integral identity is an assumption.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-reciprocal lw-complex-norm-square
                 lw-complex-l1 lw-rational-power lw-complex-exp-value
                 lw-exp-bounds lw-exp-neg-bounds lw-exp-index lw-exp-band lw-exp-sum lw-exp-term
                 lw-damped-phase-sample lw-phase-value
                 lw-complex-exp-integral-value lw-complex-exp-integral-grid
                 lw-complex-exp-moment-integral-value lw-complex-exp-moment-integral-grid
                 lw-complex-exp-moment-primitive lw-complex-exp-moment-grid
                 lw-complex-laplace-point
                 lw-complex-exp-primitive-value lw-complex-exp-grid
                 lw-complex-disk-enlarge lw-disk-enlarge lw-precision-fuel)))

(local (defthm lw-clm-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-clm-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-clm-times-negative
         (implies (and (rationalp a) (rationalp b)) (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-clm-negative-times
         (implies (and (rationalp a) (rationalp b)) (equal (* (- a) b) (- (* a b))))))
(local (defthm lw-clm-zero-times (equal (* 0 a) 0)))
(local (defthm lw-clm-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))
(local (defthm lw-clm-double-negative (implies (rationalp a) (equal (- (- a)) a))))
(local (defthm lw-clm-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))
(local (defthm lw-clm-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))
(local (defthm lw-clm-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))
(local (defthm lw-clm-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))
(local (defthm lw-clm-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-clm-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-clm-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-clm-left-commutes)))))
(local (defthm lw-clm-fuel-natural
         (natp (lw-precision-fuel width error))
         :hints (("Goal" :in-theory (enable lw-precision-fuel)))
         :rule-classes (:rewrite :type-prescription)))
(local (defthm lw-clm-pair-complex
         (implies (and (rationalp a) (rationalp b)) (lw-complexp (cons a b)))
         :hints (("Goal" :in-theory (enable lw-complexp)))))


(local (defthm lw-clm-power-two
         (implies (rationalp value) (equal (lw-rational-power value 2) (* value value)))
         :hints (("Goal" :expand ((lw-rational-power value 2)
                                  (lw-rational-power value 1) (lw-rational-power value 0))))))

(defthm lw-damped-phase-sample-quadratic-decay
  (implies (and (rationalp value) (<= 0 value) (rationalp angle)
                (rationalp negative-error) (< 0 negative-error)
                (rationalp phase-error) (< 0 phase-error))
           (lw-complex-diskp
            (lw-damped-phase-sample value angle negative-error phase-error) (/ (* (+ 1 (* 1/2 value)) (+ 1 (* 1/2 value))))))
  :hints (("Goal"
           :use ((:instance lw-exp-linear-power-le-upper (value (* 1/2 value)) (index 2) (error negative-error))
                 (:instance lw-exp-neg-bounds-valid (epsilon negative-error))
                 (:instance lw-reciprocal-antitone
                   (left (* (+ 1 (* 1/2 value)) (+ 1 (* 1/2 value)))) (right (cdr (lw-exp-bounds value negative-error))))
                 (:instance lw-phase-value-unit (error phase-error) (value angle))
                 (:instance lw-complex-scale-disk
                   (factor (car (lw-exp-neg-bounds value negative-error)))
                   (point (lw-phase-value angle phase-error)) (radius 1))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-damped-phase-sample value angle negative-error phase-error))
                   (radius (car (lw-exp-neg-bounds value negative-error))) (cap (/ (* (+ 1 (* 1/2 value)) (+ 1 (* 1/2 value)))))))
           :in-theory
           (e/d (lw-damped-phase-sample lw-exp-neg-bounds lw-intervalp)
                (lw-exp-linear-power-le-upper lw-exp-neg-bounds-valid
                 lw-reciprocal-antitone lw-phase-value-unit lw-complex-scale-disk))
           :do-not-induct t)))

(defthm lw-complex-exp-damped-quadratic-decay
  (implies (and (rationalp value) (<= 0 value) (rationalp angle)
                (rationalp error) (< 0 error))
           (lw-complex-diskp (lw-complex-exp-value (cons (- value) angle) error)
                             (+ (/ (* (+ 1 (* 1/2 value)) (+ 1 (* 1/2 value)))) (* 2 error))))
  :hints (("Goal"
           :use ((:instance lw-damped-phase-sample-quadratic-decay
                   (negative-error (* 1/2 error)) (phase-error (* 1/2 error)))
                 (:instance lw-complex-exp-kernel-agreement
                   (negative-error (* 1/2 error)) (phase-error (* 1/2 error)) (complex-error error))
                 (:instance lw-complex-subtract-cancel
                   (a (lw-damped-phase-sample value angle (* 1/2 error) (* 1/2 error)))
                   (b (lw-complex-exp-value (cons (- value) angle) error)))
                 (:instance lw-complex-sub-disk
                   (left (lw-damped-phase-sample value angle (* 1/2 error) (* 1/2 error)))
                   (radius (/ (* (+ 1 (* 1/2 value)) (+ 1 (* 1/2 value)))))
                   (right (lw-complex-sub
                     (lw-damped-phase-sample value angle (* 1/2 error) (* 1/2 error))
                     (lw-complex-exp-value (cons (- value) angle) error)))
                   (other-radius (* 2 error))))
           :in-theory (disable lw-damped-phase-sample-quadratic-decay lw-complex-exp-kernel-agreement
                               lw-complex-subtract-cancel lw-complex-sub-disk
                               lw-complex-sub-add-first)
           :do-not-induct t)))


(defun lw-complex-laplace-moment-cutoff (rate error)
  (+ 1 (lw-precision-fuel 1 rate)
     (lw-precision-fuel 32 (* rate rate rate error))))

(defun lw-complex-laplace-moment-grid (rate height error)
  (lw-complex-exp-moment-integral-grid (lw-complex-laplace-point rate height) 0
    (lw-complex-laplace-moment-cutoff rate error) rate (* 1/4 error)))

(defthm lw-complex-laplace-moment-cutoff-natural
  (posp (lw-complex-laplace-moment-cutoff rate error))
  :rule-classes (:rewrite :type-prescription))

(defthm lw-complex-laplace-moment-cutoff-growth
  (implies (and (rationalp rate) (< 0 rate) (rationalp error) (< 0 error))
           (and (<= 1 (* rate (lw-complex-laplace-moment-cutoff rate error)))
                (<= 32 (* rate rate rate error (lw-complex-laplace-moment-cutoff rate error)))))
  :hints (("Goal"
           :use ((:instance lw-clm-positive-product (a rate) (b rate))
                 (:instance lw-clm-positive-product (a rate) (b (* rate rate)))
                 (:instance lw-clm-positive-product (a (* rate rate rate)) (b error))
                 (:instance lw-precision-fuel-adequate (width 1) (epsilon rate))
                 (:instance lw-precision-fuel-adequate (width 32) (epsilon (* rate rate rate error)))
                 (:instance lw-clm-multiply-order
                   (a (lw-precision-fuel 1 rate))
                   (b (lw-complex-laplace-moment-cutoff rate error)) (factor rate))
                 (:instance lw-clm-multiply-order
                   (a (lw-precision-fuel 32 (* rate rate rate error)))
                   (b (lw-complex-laplace-moment-cutoff rate error)) (factor (* rate rate rate error))))
           :in-theory (disable lw-precision-fuel-adequate)
           :nonlinearp nil :do-not-induct t)))

(local (defthm lw-clm-cancel-equality
         (implies (and (rationalp a) (rationalp b) (rationalp factor) (< 0 factor)
                       (equal (* factor a) (* factor b))) (equal a b))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-clm-inverse-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b))
                  (equal (/ (* a b)) (* (/ a) (/ b))))
         :hints (("Goal"
                  :use ((:instance inverse-of-* (x a)) (:instance inverse-of-* (x b))
                        (:instance inverse-of-* (x (* a b)))
                        (:instance lw-clm-cancel-equality (factor (* a b))
                          (a (/ (* a b))) (b (* (/ a) (/ b)))))
                  :in-theory (disable inverse-of-*) :nonlinearp t))))

(local (defthm lw-clm-quadratic-decay-scalar
         (implies (and (rationalp value) (<= 1 value))
                  (<= (* (+ 1 value) (/ (* (+ 1 (* 1/2 value)) (+ 1 (* 1/2 value)))))
                      (* 8 (/ value))))
         :hints (("Goal"
                  :use ((:instance inverse-of-* (x value))
                        (:instance lw-positive-division-bound
                          (numerator (+ 1 value))
                          (divisor (* (+ 1 (* 1/2 value)) (+ 1 (* 1/2 value))))
                          (bound (* 8 (/ value)))))
                  :nonlinearp t)) :rule-classes nil))

(local (defthm lw-clm-tail-rounding-identity
         (implies (and (rationalp rate) (< 0 rate) (rationalp amplification) (< 0 amplification)
                       (rationalp error))
                  (equal (* 2 amplification (/ rate) (/ (* 1/4 rate error) (* 16 amplification)))
                         (* 1/32 error)))
         :hints (("Goal" :use ((:instance inverse-of-* (x rate))
                              (:instance inverse-of-* (x amplification)))
                         :in-theory (disable inverse-of-*) :nonlinearp nil))
         :rule-classes nil))

(local (defthm lw-clm-tail-scalar-budget
         (implies (and (rationalp rate) (< 0 rate) (rationalp cutoff) (< 0 cutoff)
                       (<= 1 (* rate cutoff)) (rationalp error) (< 0 error)
                       (<= 32 (* rate rate rate cutoff error)))
                  (<=
                   (* (+ cutoff (/ rate)) (/ rate)
                      (+ (/ (* (+ 1 (* 1/2 rate cutoff)) (+ 1 (* 1/2 rate cutoff))))
                         (* 2 (/ (* 1/4 rate error) (* 16 (+ cutoff (/ rate)))))))
                   (* 1/2 error)))
         :hints (("Goal"
                  :use ((:instance lw-clm-tail-rounding-identity
                          (amplification (+ cutoff (/ rate))))
                        (:instance lw-clm-quadratic-decay-scalar (value (* rate cutoff)))
                        (:instance lw-clm-multiply-order
                          (a (* (+ 1 (* rate cutoff))
                                (/ (* (+ 1 (* 1/2 rate cutoff)) (+ 1 (* 1/2 rate cutoff))))))
                          (b (* 8 (/ (* rate cutoff)))) (factor (* (/ rate) (/ rate))))
                        (:instance lw-positive-division-bound
                          (numerator 8) (divisor (* rate rate rate cutoff)) (bound (* 1/4 error)))
                        (:instance inverse-of-* (x rate))
                        (:instance inverse-of-* (x (+ cutoff (/ rate)))))
                  :in-theory (disable inverse-of-*) :nonlinearp nil :do-not-induct t))
         :rule-classes nil))

(local (in-theory (disable lw-complex-laplace-moment-cutoff lw-complex-quotient)))

(local (defthm lw-clm-scale-laplace
         (implies (and (rationalp rate) (rationalp height) (rationalp cutoff))
                  (equal (lw-complex-scale cutoff (lw-complex-laplace-point rate height))
                         (cons (- (* rate cutoff)) (- (* height cutoff)))))
         :hints (("Goal" :in-theory (enable lw-complex-scale lw-complex-laplace-point)))))

(local (defthm lw-clm-scale-zero
         (equal (lw-complex-scale 0 point) (cons 0 0))
         :hints (("Goal" :in-theory (enable lw-complex-scale)))))

(local (defthm lw-clm-sub-negative
         (implies (and (lw-complexp a) (lw-complexp b))
                  (equal (lw-complex-sub (lw-complex-sub a b) (lw-complex-scale -1 b)) a))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-sub lw-complex-scale)))))

(local (defthm lw-clm-origin-shift
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

(local (defthm lw-clm-quotient-disk
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


(local (defthm lw-clm-origin-moment-shift
         (implies (and (lw-complexp a) (lw-complexp point) (rationalp cutoff))
                  (equal
                   (lw-complex-sub
                    (lw-complex-quotient
                     (lw-complex-sub (lw-complex-scale cutoff a)
                                      (lw-complex-quotient (lw-complex-sub a (cons 1 0)) point))
                     point)
                    (lw-complex-mul (lw-complex-reciprocal point)
                                     (lw-complex-reciprocal point)))
                   (lw-complex-quotient
                    (lw-complex-sub (lw-complex-scale cutoff a) (lw-complex-quotient a point))
                    point)))
         :hints (("Goal" :use ((:instance lw-complex-reciprocal-rational))
                  :in-theory
                  (e/d (lw-complexp lw-complex-sub lw-complex-add lw-complex-scale
                        lw-complex-mul lw-complex-quotient)
                       (lw-complex-reciprocal-rational))))))

(local (defthm lw-clm-negative-square
         (implies (lw-complexp a)
                  (equal (lw-complex-mul (lw-complex-scale -1 a) (lw-complex-scale -1 a))
                         (lw-complex-mul a a)))
         :hints (("Goal" :in-theory
                  (enable lw-complexp lw-complex-scale lw-complex-mul)))))

(local (defthm lw-clm-reciprocal-square
         (implies (and (rationalp rate) (< 0 rate) (rationalp height))
                  (equal
                   (lw-complex-mul
                    (lw-complex-reciprocal (lw-complex-laplace-point rate height))
                    (lw-complex-reciprocal (lw-complex-laplace-point rate height)))
                   (lw-complex-mul (lw-complex-reciprocal (cons rate height))
                                    (lw-complex-reciprocal (cons rate height)))))
         :hints (("Goal"
                  :use (lw-complex-laplace-point-data
                        (:instance lw-clm-negative-square
                          (a (lw-complex-reciprocal (lw-complex-laplace-point rate height)))))
                  :in-theory (disable lw-complex-laplace-point-data lw-clm-negative-square)))))

(defthm lw-complex-laplace-moment-primitive-tail
  (implies (and (rationalp rate) (< 0 rate) (rationalp height)
                (rationalp error) (< 0 error))
           (lw-complex-diskp
            (lw-complex-sub
              (lw-complex-exp-moment-integral-value (lw-complex-laplace-point rate height) 0
                (lw-complex-laplace-moment-cutoff rate error) rate (* 1/4 error))
              (lw-complex-mul (lw-complex-reciprocal (cons rate height))
                               (lw-complex-reciprocal (cons rate height))))
            (* 1/2 error)))
  :hints (("Goal"
           :use (lw-complex-laplace-moment-cutoff-growth lw-complex-laplace-point-data
                 (:instance lw-clm-positive-product (a rate)
                   (b (lw-complex-laplace-moment-cutoff rate error)))
                 (:instance lw-clm-tail-scalar-budget
                   (cutoff (lw-complex-laplace-moment-cutoff rate error)))
                 (:instance lw-complex-exp-damped-quadratic-decay
                   (value (* rate (lw-complex-laplace-moment-cutoff rate error)))
                   (angle (- (* height (lw-complex-laplace-moment-cutoff rate error))))
                   (error (lw-complex-exp-moment-endpoint-error
                            0 (lw-complex-laplace-moment-cutoff rate error) rate (* 1/4 error))))
                 (:instance lw-clm-origin-moment-shift
                   (a (lw-complex-exp-value
                     (lw-complex-scale (lw-complex-laplace-moment-cutoff rate error)
                                       (lw-complex-laplace-point rate height))
                     (lw-complex-exp-moment-endpoint-error
                       0 (lw-complex-laplace-moment-cutoff rate error) rate (* 1/4 error))))
                   (point (lw-complex-laplace-point rate height))
                   (cutoff (lw-complex-laplace-moment-cutoff rate error)))
                 (:instance lw-complex-scale-disk
                   (factor (lw-complex-laplace-moment-cutoff rate error))
                   (point (lw-complex-exp-value
                     (lw-complex-scale (lw-complex-laplace-moment-cutoff rate error)
                                       (lw-complex-laplace-point rate height))
                     (lw-complex-exp-moment-endpoint-error
                       0 (lw-complex-laplace-moment-cutoff rate error) rate (* 1/4 error))))
                   (radius
                     (+ (/ (* (+ 1 (* 1/2 rate (lw-complex-laplace-moment-cutoff rate error)))
                              (+ 1 (* 1/2 rate (lw-complex-laplace-moment-cutoff rate error)))))
                        (* 2 (lw-complex-exp-moment-endpoint-error
                          0 (lw-complex-laplace-moment-cutoff rate error) rate (* 1/4 error))))))
                 (:instance lw-clm-quotient-disk
                   (numerator (lw-complex-exp-value
                     (lw-complex-scale (lw-complex-laplace-moment-cutoff rate error)
                                       (lw-complex-laplace-point rate height))
                     (lw-complex-exp-moment-endpoint-error
                       0 (lw-complex-laplace-moment-cutoff rate error) rate (* 1/4 error))))
                   (denominator (lw-complex-laplace-point rate height)) (clearance rate)
                   (radius
                     (+ (/ (* (+ 1 (* 1/2 rate (lw-complex-laplace-moment-cutoff rate error)))
                              (+ 1 (* 1/2 rate (lw-complex-laplace-moment-cutoff rate error)))))
                        (* 2 (lw-complex-exp-moment-endpoint-error
                          0 (lw-complex-laplace-moment-cutoff rate error) rate (* 1/4 error))))))
                 (:instance lw-complex-sub-disk
                   (left (lw-complex-scale (lw-complex-laplace-moment-cutoff rate error)
                     (lw-complex-exp-value
                       (lw-complex-scale (lw-complex-laplace-moment-cutoff rate error)
                                         (lw-complex-laplace-point rate height))
                       (lw-complex-exp-moment-endpoint-error
                         0 (lw-complex-laplace-moment-cutoff rate error) rate (* 1/4 error)))))
                   (radius
                    (* (lw-complex-laplace-moment-cutoff rate error)
                     (+ (/ (* (+ 1 (* 1/2 rate (lw-complex-laplace-moment-cutoff rate error)))
                              (+ 1 (* 1/2 rate (lw-complex-laplace-moment-cutoff rate error)))))
                        (* 2 (lw-complex-exp-moment-endpoint-error
                          0 (lw-complex-laplace-moment-cutoff rate error) rate (* 1/4 error))))))
                   (right (lw-complex-quotient
                     (lw-complex-exp-value
                       (lw-complex-scale (lw-complex-laplace-moment-cutoff rate error)
                                         (lw-complex-laplace-point rate height))
                       (lw-complex-exp-moment-endpoint-error
                         0 (lw-complex-laplace-moment-cutoff rate error) rate (* 1/4 error)))
                     (lw-complex-laplace-point rate height)))
                   (other-radius
                    (* (/ rate)
                     (+ (/ (* (+ 1 (* 1/2 rate (lw-complex-laplace-moment-cutoff rate error)))
                              (+ 1 (* 1/2 rate (lw-complex-laplace-moment-cutoff rate error)))))
                        (* 2 (lw-complex-exp-moment-endpoint-error
                          0 (lw-complex-laplace-moment-cutoff rate error) rate (* 1/4 error)))))))
                 (:instance lw-clm-quotient-disk
                   (numerator
                    (lw-complex-sub
                     (lw-complex-scale (lw-complex-laplace-moment-cutoff rate error)
                       (lw-complex-exp-value
                         (lw-complex-scale (lw-complex-laplace-moment-cutoff rate error)
                                           (lw-complex-laplace-point rate height))
                         (lw-complex-exp-moment-endpoint-error
                           0 (lw-complex-laplace-moment-cutoff rate error) rate (* 1/4 error))))
                     (lw-complex-quotient
                       (lw-complex-exp-value
                         (lw-complex-scale (lw-complex-laplace-moment-cutoff rate error)
                                           (lw-complex-laplace-point rate height))
                         (lw-complex-exp-moment-endpoint-error
                           0 (lw-complex-laplace-moment-cutoff rate error) rate (* 1/4 error)))
                       (lw-complex-laplace-point rate height))))
                   (denominator (lw-complex-laplace-point rate height)) (clearance rate)
                   (radius
                    (* (+ (lw-complex-laplace-moment-cutoff rate error) (/ rate))
                     (+ (/ (* (+ 1 (* 1/2 rate (lw-complex-laplace-moment-cutoff rate error)))
                              (+ 1 (* 1/2 rate (lw-complex-laplace-moment-cutoff rate error)))))
                        (* 2 (lw-complex-exp-moment-endpoint-error
                          0 (lw-complex-laplace-moment-cutoff rate error) rate (* 1/4 error)))))))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-complex-sub
                     (lw-complex-exp-moment-integral-value (lw-complex-laplace-point rate height) 0
                       (lw-complex-laplace-moment-cutoff rate error) rate (* 1/4 error))
                     (lw-complex-mul (lw-complex-reciprocal (cons rate height))
                                      (lw-complex-reciprocal (cons rate height)))))
                   (radius
                    (* (+ (lw-complex-laplace-moment-cutoff rate error) (/ rate)) (/ rate)
                     (+ (/ (* (+ 1 (* 1/2 rate (lw-complex-laplace-moment-cutoff rate error)))
                              (+ 1 (* 1/2 rate (lw-complex-laplace-moment-cutoff rate error)))))
                        (* 2 (lw-complex-exp-moment-endpoint-error
                          0 (lw-complex-laplace-moment-cutoff rate error) rate (* 1/4 error))))))
                   (cap (* 1/2 error))))
           :in-theory
           (e/d (lw-complex-exp-moment-integral-value lw-complex-exp-moment-primitive
                 lw-complex-exp-primitive-value)
                (lw-complex-laplace-moment-cutoff-growth lw-complex-laplace-point-data
                 lw-clm-origin-moment-shift lw-clm-quotient-disk
                 lw-complex-exp-damped-quadratic-decay lw-complex-scale-disk lw-complex-sub-disk
                 lw-complex-sub-add-first))
           :nonlinearp nil :do-not-induct t)))

(local (defthm lw-clm-grid-rational
         (implies (and (lw-complexp point) (rationalp start) (<= 0 start)
                       (rationalp length) (< 0 length) (rationalp clearance) (< 0 clearance)
                       (rationalp error) (< 0 error))
                  (lw-complexp (lw-complex-exp-moment-integral-grid point start length clearance error)))
         :hints (("Goal" :use (lw-complex-exp-moment-integration-parameters)
                         :in-theory (e/d (lw-complex-exp-moment-integral-grid)
                                         (lw-complex-exp-moment-integration-parameters))
                         :do-not-induct t))))

(defthm lw-complex-laplace-moment-grid-rational
  (implies (and (rationalp rate) (< 0 rate) (rationalp height)
                (rationalp error) (< 0 error))
           (lw-complexp (lw-complex-laplace-moment-grid rate height error)))
  :hints (("Goal" :in-theory (enable lw-complex-laplace-moment-grid))))

(defthm lw-complex-laplace-moment-grid-reciprocal-square
  (implies (and (rationalp rate) (< 0 rate) (rationalp height)
                (rationalp error) (< 0 error))
           (lw-complex-diskp
            (lw-complex-sub (lw-complex-mul (lw-complex-reciprocal (cons rate height))
                                  (lw-complex-reciprocal (cons rate height)))
                            (lw-complex-laplace-moment-grid rate height error)) error))
  :hints (("Goal"
           :use (lw-complex-laplace-point-data lw-complex-laplace-moment-primitive-tail
                 (:instance lw-complex-exp-moment-computed-quadrature
                   (point (lw-complex-laplace-point rate height)) (start 0)
                   (length (lw-complex-laplace-moment-cutoff rate error)) (clearance rate) (error (* 1/4 error)))
                 (:instance lw-complex-difference-symmetric
                   (left (lw-complex-exp-moment-integral-value (lw-complex-laplace-point rate height) 0
                           (lw-complex-laplace-moment-cutoff rate error) rate (* 1/4 error)))
                   (right (lw-complex-mul (lw-complex-reciprocal (cons rate height))
                                  (lw-complex-reciprocal (cons rate height)))) (radius (* 1/2 error)))
                 (:instance lw-complex-difference-triangle
                   (left (lw-complex-mul (lw-complex-reciprocal (cons rate height))
                                  (lw-complex-reciprocal (cons rate height))))
                   (middle (lw-complex-exp-moment-integral-value (lw-complex-laplace-point rate height) 0
                             (lw-complex-laplace-moment-cutoff rate error) rate (* 1/4 error)))
                   (right (lw-complex-laplace-moment-grid rate height error))
                   (radius (* 1/2 error)) (other-radius (* 1/4 error)))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-complex-sub (lw-complex-mul (lw-complex-reciprocal (cons rate height))
                                  (lw-complex-reciprocal (cons rate height)))
                                          (lw-complex-laplace-moment-grid rate height error)))
                   (radius (+ (* 1/2 error) (* 1/4 error))) (cap error)))
           :in-theory
           (e/d (lw-complex-laplace-moment-grid)
                (lw-complex-laplace-point-data lw-complex-laplace-moment-primitive-tail
                 lw-complex-exp-moment-computed-quadrature lw-complex-difference-triangle
                 lw-complex-exp-moment-integral-value lw-complex-exp-moment-integral-grid))
           :do-not-induct t)))
