(in-package "ACL2")

(include-book "complex-exp-integral")
(include-book "complex-kernel-agreement")
(include-book "kernel-mass")

; Effective Laplace normalization of the exponential basis. First bound
; the damped endpoint, then combine a computed cutoff with the certified
; finite rectangle sum. No improper-integral identity is an assumption.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-reciprocal lw-complex-norm-square
                 lw-complex-l1 lw-rational-power lw-complex-exp-value
                 lw-exp-bounds lw-exp-neg-bounds lw-exp-index lw-exp-band lw-exp-sum lw-exp-term
                 lw-damped-phase-sample lw-phase-value
                 lw-complex-exp-integral-value lw-complex-exp-integral-grid
                 lw-complex-exp-primitive-value lw-complex-exp-grid
                 lw-complex-disk-enlarge lw-disk-enlarge lw-precision-fuel)))

(local (defthm lw-clb-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-clb-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-clb-times-negative
         (implies (and (rationalp a) (rationalp b)) (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-clb-negative-times
         (implies (and (rationalp a) (rationalp b)) (equal (* (- a) b) (- (* a b))))))
(local (defthm lw-clb-zero-times (equal (* 0 a) 0)))
(local (defthm lw-clb-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))
(local (defthm lw-clb-double-negative (implies (rationalp a) (equal (- (- a)) a))))
(local (defthm lw-clb-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))
(local (defthm lw-clb-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))
(local (defthm lw-clb-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))
(local (defthm lw-clb-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))
(local (defthm lw-clb-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-clb-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-clb-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-clb-left-commutes)))))
(local (defthm lw-clb-fuel-natural
         (natp (lw-precision-fuel width error))
         :hints (("Goal" :in-theory (enable lw-precision-fuel)))
         :rule-classes (:rewrite :type-prescription)))
(local (defthm lw-clb-pair-complex
         (implies (and (rationalp a) (rationalp b)) (lw-complexp (cons a b)))
         :hints (("Goal" :in-theory (enable lw-complexp)))))

(defun lw-complex-laplace-point (rate height) (cons (- rate) (- height)))

(defun lw-complex-laplace-cutoff (rate error)
  (+ 1 (lw-precision-fuel 4 (* rate rate error))))

(defun lw-complex-laplace-grid (rate height error)
  (lw-complex-exp-integral-grid (lw-complex-laplace-point rate height) 0
    (lw-complex-laplace-cutoff rate error) rate (* 1/4 error)))

(defthm lw-complex-laplace-cutoff-natural
  (posp (lw-complex-laplace-cutoff rate error))
  :rule-classes (:rewrite :type-prescription))

(defthm lw-complex-laplace-cutoff-adequate
  (implies (and (rationalp rate) (< 0 rate) (rationalp error) (< 0 error))
           (and
            (<= 4 (* (lw-complex-laplace-cutoff rate error) rate rate error))
            (<= (* (/ rate) (/ (+ 1 (* rate (lw-complex-laplace-cutoff rate error)))))
                (* 1/4 error))))
  :hints (("Goal"
           :use ((:instance lw-clb-positive-product (a rate) (b rate))
                 (:instance lw-clb-positive-product (a (* rate rate)) (b error))
                 (:instance lw-precision-fuel-adequate (width 4) (epsilon (* rate rate error)))
                 (:instance lw-positive-division-bound
                   (numerator 1) (divisor (+ 1 (* rate (lw-complex-laplace-cutoff rate error))))
                   (bound (* 1/4 rate error)))
                 (:instance lw-clb-multiply-order
                   (a (/ (+ 1 (* rate (lw-complex-laplace-cutoff rate error)))))
                   (b (* 1/4 rate error)) (factor (/ rate))))
           :in-theory (disable lw-precision-fuel-adequate)
           :nonlinearp nil :do-not-induct t)))

(local (defthm lw-clb-power-one
         (implies (rationalp value) (equal (lw-rational-power value 1) value))
         :hints (("Goal" :expand ((lw-rational-power value 1) (lw-rational-power value 0))))))

(defthm lw-damped-phase-sample-decay
  (implies (and (rationalp value) (<= 0 value) (rationalp angle)
                (rationalp negative-error) (< 0 negative-error)
                (rationalp phase-error) (< 0 phase-error))
           (lw-complex-diskp
            (lw-damped-phase-sample value angle negative-error phase-error) (/ (+ 1 value))))
  :hints (("Goal"
           :use ((:instance lw-exp-linear-power-le-upper (index 1) (error negative-error))
                 (:instance lw-exp-neg-bounds-valid (epsilon negative-error))
                 (:instance lw-reciprocal-antitone
                   (left (+ 1 value)) (right (cdr (lw-exp-bounds value negative-error))))
                 (:instance lw-phase-value-unit (error phase-error) (value angle))
                 (:instance lw-complex-scale-disk
                   (factor (car (lw-exp-neg-bounds value negative-error)))
                   (point (lw-phase-value angle phase-error)) (radius 1))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-damped-phase-sample value angle negative-error phase-error))
                   (radius (car (lw-exp-neg-bounds value negative-error))) (cap (/ (+ 1 value)))))
           :in-theory
           (e/d (lw-damped-phase-sample lw-exp-neg-bounds lw-intervalp)
                (lw-exp-linear-power-le-upper lw-exp-neg-bounds-valid
                 lw-reciprocal-antitone lw-phase-value-unit lw-complex-scale-disk))
           :do-not-induct t)))

(defthm lw-complex-exp-damped-decay
  (implies (and (rationalp value) (<= 0 value) (rationalp angle)
                (rationalp error) (< 0 error))
           (lw-complex-diskp (lw-complex-exp-value (cons (- value) angle) error)
                             (+ (/ (+ 1 value)) (* 2 error))))
  :hints (("Goal"
           :use ((:instance lw-damped-phase-sample-decay
                   (negative-error (* 1/2 error)) (phase-error (* 1/2 error)))
                 (:instance lw-complex-exp-kernel-agreement
                   (negative-error (* 1/2 error)) (phase-error (* 1/2 error)) (complex-error error))
                 (:instance lw-complex-subtract-cancel
                   (a (lw-damped-phase-sample value angle (* 1/2 error) (* 1/2 error)))
                   (b (lw-complex-exp-value (cons (- value) angle) error)))
                 (:instance lw-complex-sub-disk
                   (left (lw-damped-phase-sample value angle (* 1/2 error) (* 1/2 error)))
                   (radius (/ (+ 1 value)))
                   (right (lw-complex-sub
                     (lw-damped-phase-sample value angle (* 1/2 error) (* 1/2 error))
                     (lw-complex-exp-value (cons (- value) angle) error)))
                   (other-radius (* 2 error))))
           :in-theory (disable lw-damped-phase-sample-decay lw-complex-exp-kernel-agreement
                               lw-complex-subtract-cancel lw-complex-sub-disk
                               lw-complex-sub-add-first)
           :do-not-induct t)))

(defthm lw-complex-laplace-point-data
  (implies (and (rationalp rate) (< 0 rate) (rationalp height))
           (and (lw-complexp (lw-complex-laplace-point rate height))
                (not (equal (lw-complex-laplace-point rate height) (cons 0 0)))
                (<= (* rate rate) (lw-complex-norm-square (lw-complex-laplace-point rate height)))
                (equal (lw-complex-scale -1
                         (lw-complex-reciprocal (lw-complex-laplace-point rate height)))
                       (lw-complex-reciprocal (cons rate height)))))
  :hints (("Goal" :in-theory (enable lw-complex-laplace-point lw-complexp lw-complex-scale
                                     lw-complex-reciprocal lw-complex-conjugate lw-complex-norm-square)
                  :nonlinearp t :do-not-induct t)))

(local (in-theory (disable lw-complex-laplace-point lw-complex-laplace-cutoff lw-complex-quotient)))

(local (defthm lw-clb-scale-laplace
         (implies (and (rationalp rate) (rationalp height) (rationalp cutoff))
                  (equal (lw-complex-scale cutoff (lw-complex-laplace-point rate height))
                         (cons (- (* rate cutoff)) (- (* height cutoff)))))
         :hints (("Goal" :in-theory (enable lw-complex-scale lw-complex-laplace-point)))))

(local (defthm lw-clb-scale-zero
         (equal (lw-complex-scale 0 point) (cons 0 0))
         :hints (("Goal" :in-theory (enable lw-complex-scale)))))

(local (defthm lw-clb-sub-negative
         (implies (and (lw-complexp a) (lw-complexp b))
                  (equal (lw-complex-sub (lw-complex-sub a b) (lw-complex-scale -1 b)) a))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-sub lw-complex-scale)))))

(local (defthm lw-clb-origin-shift
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

(local (defthm lw-clb-quotient-disk
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

(defthm lw-complex-laplace-primitive-tail
  (implies (and (rationalp rate) (< 0 rate) (rationalp height)
                (rationalp error) (< 0 error))
           (lw-complex-diskp
            (lw-complex-sub
              (lw-complex-exp-integral-value (lw-complex-laplace-point rate height) 0
                (lw-complex-laplace-cutoff rate error) rate (* 1/4 error))
              (lw-complex-reciprocal (cons rate height)))
            (* 1/2 error)))
  :hints (("Goal"
           :use (lw-complex-laplace-cutoff-adequate lw-complex-laplace-point-data
                 (:instance lw-clb-positive-product (a rate) (b error))
                 (:instance lw-complex-exp-damped-decay
                   (value (* rate (lw-complex-laplace-cutoff rate error)))
                   (angle (- (* height (lw-complex-laplace-cutoff rate error))))
                   (error (* 1/64 rate error)))
                 (:instance lw-clb-origin-shift
                   (a (lw-complex-exp-value
                     (lw-complex-scale (lw-complex-laplace-cutoff rate error)
                                       (lw-complex-laplace-point rate height)) (* 1/64 rate error)))
                   (point (lw-complex-laplace-point rate height)))
                 (:instance lw-clb-quotient-disk
                   (numerator (lw-complex-exp-value
                     (lw-complex-scale (lw-complex-laplace-cutoff rate error)
                                       (lw-complex-laplace-point rate height)) (* 1/64 rate error)))
                   (denominator (lw-complex-laplace-point rate height)) (clearance rate)
                   (radius (+ (/ (+ 1 (* rate (lw-complex-laplace-cutoff rate error))))
                              (* 1/32 rate error))))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-complex-sub
                     (lw-complex-exp-integral-value (lw-complex-laplace-point rate height) 0
                       (lw-complex-laplace-cutoff rate error) rate (* 1/4 error))
                     (lw-complex-reciprocal (cons rate height))))
                   (radius (* (+ (/ (+ 1 (* rate (lw-complex-laplace-cutoff rate error))))
                                  (* 1/32 rate error)) (/ rate)))
                   (cap (* 1/2 error))))
           :in-theory
           (e/d (lw-complex-exp-integral-value lw-complex-exp-primitive-value)
                (lw-complex-laplace-cutoff-adequate lw-clb-origin-shift
                 lw-clb-quotient-disk lw-complex-exp-damped-decay lw-complex-sub-add-first))
           :do-not-induct t)))

(local (defthm lw-clb-grid-rational
         (implies (and (lw-complexp point) (rationalp start) (<= 0 start)
                       (rationalp length) (< 0 length) (rationalp clearance) (< 0 clearance)
                       (rationalp error) (< 0 error))
                  (lw-complexp (lw-complex-exp-integral-grid point start length clearance error)))
         :hints (("Goal" :use (lw-complex-exp-integration-parameters)
                         :in-theory (e/d (lw-complex-exp-integral-grid)
                                         (lw-complex-exp-integration-parameters))
                         :do-not-induct t))))

(defthm lw-complex-laplace-grid-rational
  (implies (and (rationalp rate) (< 0 rate) (rationalp height)
                (rationalp error) (< 0 error))
           (lw-complexp (lw-complex-laplace-grid rate height error)))
  :hints (("Goal" :in-theory (enable lw-complex-laplace-grid))))

(defthm lw-complex-laplace-grid-reciprocal
  (implies (and (rationalp rate) (< 0 rate) (rationalp height)
                (rationalp error) (< 0 error))
           (lw-complex-diskp
            (lw-complex-sub (lw-complex-reciprocal (cons rate height))
                            (lw-complex-laplace-grid rate height error)) error))
  :hints (("Goal"
           :use (lw-complex-laplace-point-data lw-complex-laplace-primitive-tail
                 (:instance lw-complex-exp-computed-quadrature
                   (point (lw-complex-laplace-point rate height)) (start 0)
                   (length (lw-complex-laplace-cutoff rate error)) (clearance rate) (error (* 1/4 error)))
                 (:instance lw-complex-difference-symmetric
                   (left (lw-complex-exp-integral-value (lw-complex-laplace-point rate height) 0
                           (lw-complex-laplace-cutoff rate error) rate (* 1/4 error)))
                   (right (lw-complex-reciprocal (cons rate height))) (radius (* 1/2 error)))
                 (:instance lw-complex-difference-triangle
                   (left (lw-complex-reciprocal (cons rate height)))
                   (middle (lw-complex-exp-integral-value (lw-complex-laplace-point rate height) 0
                             (lw-complex-laplace-cutoff rate error) rate (* 1/4 error)))
                   (right (lw-complex-laplace-grid rate height error))
                   (radius (* 1/2 error)) (other-radius (* 1/4 error)))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-complex-sub (lw-complex-reciprocal (cons rate height))
                                          (lw-complex-laplace-grid rate height error)))
                   (radius (+ (* 1/2 error) (* 1/4 error))) (cap error)))
           :in-theory
           (e/d (lw-complex-laplace-grid)
                (lw-complex-laplace-point-data lw-complex-laplace-primitive-tail
                 lw-complex-exp-computed-quadrature lw-complex-difference-triangle
                 lw-complex-exp-integral-value lw-complex-exp-integral-grid))
           :do-not-induct t)))
