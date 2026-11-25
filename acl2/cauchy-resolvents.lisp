(in-package "ACL2")

(include-book "cauchy-extraction")
(include-book "mellin-tail-bounds")

; Finite Taylor polynomials of an actual rational resolvent. A computed
; truncation order controls the error throughout the unit disk.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-conjugate lw-complex-norm-square lw-complex-diskp lw-diskp
                 lw-complex-reciprocal lw-complex-power lw-rational-power
                 lw-complex-polynomial lw-complex-coefficient-at lw-complex-l1
                 lw-cauchy-orbit-rotation lw-cauchy-orbit-step lw-cauchy-orbit-gap
                 lw-phase-rotation lw-phase-denominator lw-cauchy-moment-count lw-cauchy-orbit-moment
                 lw-cauchy-moment-expansion lw-cauchy-correlation-expansion lw-cauchy-residual-expansion
                 lw-complex-correlation-sum lw-complex-signed-power lw-complex-geometric-average
                 lw-complex-geometric-sum lw-cauchy-evaluation-sum lw-cauchy-polynomial-average
                 lw-cauchy-evaluation-sum-expansion lw-cauchy-evaluation-sum-first
                 lw-complex-conjugate-power lw-complex-power-power lw-complex-power-add
                 lw-cauchy-polynomial-average-moments lw-cauchy-scaled-expansion
                 lw-cauchy-coefficient-count lw-cauchy-coefficient-precision
                 lw-geometric-index lw-geometric-threshold)))

(local (defthm lw-cr-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-cr-times-negative
         (implies (and (rationalp a) (rationalp b)) (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-cr-negative-times
         (implies (and (rationalp a) (rationalp b)) (equal (* (- a) b) (- (* a b))))))
(local (defthm lw-cr-double-negative (implies (rationalp a) (equal (- (- a)) a))))
(local (defthm lw-cr-zero-times (equal (* 0 a) 0)))
(local (defthm lw-cr-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))
(local (defthm lw-cr-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))
(local (defthm lw-cr-left-distribute
         (implies (and (rationalp a) (rationalp b) (rationalp c))
                  (equal (* (+ a b) c) (+ (* a c) (* b c))))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defun lw-cr-countdown (count)
         (declare (xargs :measure (nfix count)))
         (if (zp count) 0 (lw-cr-countdown (- count 1)))))

(defthm lw-complex-power-step
  (implies (and (lw-complexp point) (natp index))
           (equal (lw-complex-power point (+ 1 index))
                  (lw-complex-mul point (lw-complex-power point index))))
  :hints (("Goal" :expand ((lw-complex-power point (+ 1 index))))))

(local (defthm lw-cr-power-zero
         (implies (zp index) (equal (lw-complex-power point index) (cons 1 0)))
         :hints (("Goal" :in-theory (enable lw-complex-power)))))
(local (defthm lw-cr-geometric-zero
         (implies (zp count) (equal (lw-complex-geometric-sum point count) (cons 0 0)))
         :hints (("Goal" :in-theory (enable lw-complex-geometric-sum)))))

(defthm lw-complex-power-product
  (implies (and (lw-complexp left) (lw-complexp right) (natp index))
           (equal (lw-complex-power (lw-complex-mul left right) index)
                  (lw-complex-mul (lw-complex-power left index)
                                  (lw-complex-power right index))))
  :hints (("Goal" :induct (lw-cr-countdown index)
                  :expand ((lw-complex-power (lw-complex-mul left right) index)
                           (lw-complex-power left index) (lw-complex-power right index)))))

(defun lw-resolvent-coefficients (ratio offset count)
  (if (zp count) nil
    (cons (lw-complex-power ratio offset)
          (lw-resolvent-coefficients ratio (+ 1 offset) (- count 1)))))

(defthm lw-resolvent-coefficients-valid
  (implies (and (lw-complexp ratio) (natp offset) (natp count))
           (and (lw-complex-coefficientsp (lw-resolvent-coefficients ratio offset count))
                (equal (len (lw-resolvent-coefficients ratio offset count)) count)))
  :hints (("Goal" :induct (lw-resolvent-coefficients ratio offset count))))

(local (defun lw-cr-coefficient-induct (offset count index)
         (declare (xargs :measure (nfix count)))
         (if (or (zp count) (zp index)) (list offset index)
           (lw-cr-coefficient-induct (+ 1 offset) (- count 1) (- index 1)))))

(defthm lw-resolvent-coefficient-nth
  (implies (and (lw-complexp ratio) (natp offset) (natp count) (natp index) (< index count))
           (equal (nth index (lw-resolvent-coefficients ratio offset count))
                  (lw-complex-power ratio (+ offset index))))
  :hints (("Goal" :induct (lw-cr-coefficient-induct offset count index)
                  :expand ((lw-resolvent-coefficients ratio offset count))
                  :in-theory (enable nth))))

(defthm lw-resolvent-polynomial-evaluation
  (implies (and (lw-complexp ratio) (lw-complexp point) (natp offset) (natp count))
           (equal (lw-complex-polynomial (lw-resolvent-coefficients ratio offset count) point offset)
                  (lw-complex-mul
                   (lw-complex-power (lw-complex-mul ratio point) offset)
                   (lw-complex-geometric-sum (lw-complex-mul ratio point) count))))
  :hints (("Goal" :induct (lw-resolvent-coefficients ratio offset count)
                  :in-theory (enable lw-complex-polynomial lw-complex-geometric-sum))))

(defun lw-resolvent-value (ratio point)
  (lw-complex-reciprocal (lw-complex-sub (cons 1 0) (lw-complex-mul ratio point))))

(defthm lw-resolvent-value-rational
  (implies (and (lw-complexp ratio) (lw-complexp point))
           (lw-complexp (lw-resolvent-value ratio point))))

(defthm lw-resolvent-polynomial-error
  (implies (and (lw-complex-diskp ratio radius) (< radius 1)
                (lw-complex-diskp point 1) (natp count))
           (lw-complex-diskp
            (lw-complex-sub
             (lw-resolvent-value ratio point)
             (lw-complex-polynomial (lw-resolvent-coefficients ratio 0 count) point 0))
            (/ (lw-rational-power radius count) (- 1 radius))))
  :hints (("Goal" :use ((:instance lw-complex-mul-disk
                          (left ratio) (right point) (other-radius 1))
                        (:instance lw-complex-geometric-remainder-bound
                          (point (lw-complex-mul ratio point))))
                  :in-theory (disable lw-complex-geometric-remainder-bound lw-complex-mul-disk
                                      lw-resolvent-coefficients))))

(local (defthm lw-cr-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* (/ divisor) (* divisor coefficient)) coefficient))
         :hints (("Goal" :use ((:instance associativity-of-* (x (/ divisor)) (y divisor) (z coefficient))
                              (:instance commutativity-of-* (x (/ divisor)) (y divisor))
                              (:instance inverse-of-* (x divisor)))
                         :in-theory (disable associativity-of-* commutativity-of-* lw-cr-left-commutes)))))

(local (defthm lw-cr-inverse-unique
         (implies (and (rationalp a) (rationalp b) (< 0 b)
                       (equal (* a b) 1))
                  (equal a (/ b)))
         :hints (("Goal" :use ((:instance lw-cr-inverse-factor (divisor b) (coefficient a)))
                         :in-theory (disable lw-cr-inverse-factor)))
         :rule-classes nil))

(local (defthm lw-cr-double-inverse
         (implies (and (rationalp a) (< 0 a)) (equal (/ (/ a)) a))
         :hints (("Goal" :use ((:instance inverse-of-* (x a))
                              (:instance lw-cr-inverse-unique (b (/ a))))
                         :in-theory (disable inverse-of-*)))))

(local (defthm lw-cr-tail-algebra
         (implies (and (rationalp value) (<= 0 value)
                       (rationalp reciprocal) (< 0 reciprocal)
                       (rationalp scale) (< 0 scale)
                       (rationalp error) (< 0 error)
                       (equal (* value reciprocal) 1)
                       (<= (/ (* error scale)) reciprocal))
                  (<= (/ value scale) error))
         :hints (("Goal" :use ((:instance lw-cr-inverse-unique (a value) (b reciprocal))
                              (:instance lw-reciprocal-antitone
                                (left (/ (* error scale))) (right reciprocal))
                              (:instance lw-positive-division-bound
                                (numerator value) (divisor scale) (bound error)))
                         :in-theory (disable lw-reciprocal-antitone) :nonlinearp nil))
         :rule-classes nil))

(defun lw-resolvent-truncation-count (radius error)
  (if (equal radius 0) 1
    (+ 1 (lw-geometric-index (/ radius) (/ (* error (- 1 radius)))))))

(defthm lw-resolvent-truncation-count-natural
  (and (natp (lw-resolvent-truncation-count radius error))
       (< 0 (lw-resolvent-truncation-count radius error)))
  :hints (("Goal" :use ((:instance lw-geometric-index-natural
                          (base (/ radius)) (target (/ (* error (- 1 radius))))))))
  :rule-classes (:rewrite :type-prescription))

(local (defthm lw-cr-reciprocal-greater-one
         (implies (and (rationalp radius) (< 0 radius) (< radius 1))
                  (< 1 (/ radius)))
         :hints (("Goal" :use ((:instance inverse-of-* (x radius)))
                         :in-theory (disable inverse-of-*) :nonlinearp t))
         :rule-classes nil))

(local (defthm lw-cr-zero-power
         (implies (posp count) (equal (lw-rational-power 0 count) 0))
         :hints (("Goal" :in-theory (enable lw-rational-power)))))

(defthm lw-resolvent-truncation-count-adequate
  (implies (and (rationalp radius) (<= 0 radius) (< radius 1)
                (rationalp error) (< 0 error) (natp count)
                (<= (lw-resolvent-truncation-count radius error) count))
           (<= (/ (lw-rational-power radius count) (- 1 radius)) error))
  :hints (("Goal" :cases ((equal radius 0))
                  :use ((:instance lw-geometric-threshold
                            (base (/ radius)) (target (/ (* error (- 1 radius)))) (exponent count))
                        (:instance lw-rational-power-reciprocal-pair (value radius) (index count))
                        (:instance lw-rational-power-nonnegative (base radius) (exponent count))
                        (:instance lw-rational-power-positive (base (/ radius)) (exponent count))
                        lw-cr-reciprocal-greater-one
                        (:instance lw-cr-tail-algebra
                          (value (lw-rational-power radius count))
                          (reciprocal (lw-rational-power (/ radius) count)) (scale (- 1 radius))))
                  :in-theory (disable lw-rational-power-reciprocal-pair
                                      lw-rational-power-nonnegative lw-rational-power-positive))))

(defthm lw-resolvent-computed-polynomial-error
  (implies (and (lw-complex-diskp ratio radius) (< radius 1)
                (lw-complex-diskp point 1) (rationalp error) (< 0 error) (natp count)
                (<= (lw-resolvent-truncation-count radius error) count))
           (lw-complex-diskp
            (lw-complex-sub
             (lw-resolvent-value ratio point)
             (lw-complex-polynomial (lw-resolvent-coefficients ratio 0 count) point 0))
            error))
  :hints (("Goal" :use (lw-resolvent-polynomial-error lw-resolvent-truncation-count-adequate
                        (:instance lw-complex-disk-enlarge
                          (point (lw-complex-sub
                                  (lw-resolvent-value ratio point)
                                  (lw-complex-polynomial (lw-resolvent-coefficients ratio 0 count) point 0)))
                          (radius (/ (lw-rational-power radius count) (- 1 radius))) (cap error)))
                  :in-theory (disable lw-resolvent-value lw-resolvent-coefficients
                                      lw-resolvent-polynomial-error lw-resolvent-truncation-count
                                      lw-resolvent-truncation-count-adequate))))
