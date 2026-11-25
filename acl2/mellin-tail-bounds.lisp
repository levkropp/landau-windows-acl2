(in-package "ACL2")

(include-book "kernel-continuity")
(include-book "rpow-continuity")

(local (in-theory
        (disable lw-exp-term lw-exp-sum lw-exp-bounds lw-exp-neg-bounds
                 lw-exp-bounds-overlap lw-exp-bounds-monotone-overlap
                 lw-kernel-weight-bounds lw-kernel-weight-scale lw-kernel-weight-precision
                 lw-rational-power lw-rational-power-add-exponents)))
(local (defthm lw-mt-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-mt-times-negative
         (implies (and (rationalp a) (rationalp b))
                  (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-mt-left-distribute
         (implies (and (rationalp a) (rationalp b) (rationalp c))
                  (equal (* (+ a b) c) (+ (* a c) (* b c))))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-mt-times-zero (equal (* 0 a) 0)))
(local (defthm lw-mt-times-minus-one
         (implies (rationalp a) (equal (* -1 a) (- a)))))
(local (defthm lw-mt-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))
(local (defthm lw-mt-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal" :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient)))
                         :in-theory (disable associativity-of-* commutativity-of-* lw-mt-left-commutes)))))
(local (defthm lw-mt-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b) (rationalp c) (<= 0 c))
                  (<= (* a c) (* b c)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defun lw-mt-countdown (index)
         (declare (xargs :measure (nfix index)))
         (if (zp index) nil (lw-mt-countdown (- index 1)))))
(local (defthm lw-mt-term-zero
         (implies (zp index) (equal (lw-exp-term value index) 1))
         :hints (("Goal" :in-theory (enable lw-exp-term)))))
(local (defthm lw-mt-power-zero
         (implies (zp index) (equal (lw-rational-power value index) 1))
         :hints (("Goal" :in-theory (enable lw-rational-power)))))
(local (defthm lw-mt-power-one
         (equal (lw-rational-power 1 index) 1)
         :hints (("Goal" :induct (lw-mt-countdown index) :in-theory (enable lw-rational-power)))))

(defthm lw-exp-term-scale-argument
  (implies (and (rationalp value) (rationalp factor) (natp index))
           (equal (lw-exp-term (* factor value) index)
                  (* (lw-rational-power factor index) (lw-exp-term value index))))
  :hints (("Goal" :induct (lw-mt-countdown index))
          (and stable-under-simplificationp
               '(:expand ((lw-exp-term (* factor value) index) (lw-exp-term value index)
                          (lw-rational-power factor index))))))

(defthm lw-exp-term-two-shifts
  (implies (and (rationalp value) (natp index))
           (equal (* (+ 1 index) (+ 2 index) (lw-exp-term value (+ 2 index)))
                  (* value value (lw-exp-term value index))))
  :hints (("Goal" :use ((:instance lw-exp-term-multiplied (index (+ 2 index)))
                        (:instance lw-exp-term-multiplied (index (+ 1 index))))
                  :in-theory (disable lw-exp-term-multiplied)
                  :nonlinearp t)))

(defthm lw-rational-power-reciprocal-pair
  (implies (and (rationalp value) (< 0 value) (natp index))
           (equal (* (lw-rational-power value index) (lw-rational-power (/ value) index)) 1))
  :hints (("Goal" :use ((:instance lw-rational-power-product (left value) (right (/ value)) (exponent index))
                        (:instance inverse-of-* (x value)))
                  :in-theory (disable lw-rational-power-product inverse-of-*))))

(defthm lw-exp-bounds-lower-term
  (implies (and (rationalp value) (<= 0 value) (natp index) (<= index (lw-exp-index value error)))
           (<= (lw-exp-term value index) (car (lw-exp-bounds value error))))
  :hints (("Goal" :use (lw-exp-term-le-sum
                        (:instance lw-exp-index-adequate (epsilon error))
                        (:instance lw-exp-sum-monotone-index (small index) (large (lw-exp-index value error))))
                  :in-theory (e/d (lw-exp-bounds lw-exp-band)
                                  (lw-exp-index lw-exp-index-adequate lw-exp-term-le-sum)))))

(local
 (defthm lw-mt-scaled-term-identity
   (implies (and (rationalp value) (rationalp rate) (natp index))
            (equal (* (lw-rational-power rate (+ 2 index)) value value (lw-exp-term value index))
                   (* (+ 1 index) (+ 2 index) (lw-exp-term (* rate value) (+ 2 index)))))
   :hints (("Goal" :use ((:instance lw-exp-term-two-shifts (value (* rate value)))
                         (:instance lw-exp-term-scale-argument (factor rate)))
                   :expand ((lw-rational-power rate 2) (lw-rational-power rate 1))
                   :in-theory (e/d (lw-rational-power-add-exponents)
                                   (lw-exp-term-scale-argument lw-exp-term-two-shifts))
                   :nonlinearp t))
   :rule-classes nil))

; Once rate*u >= j+2, the computed exponential's starting index already
; includes the (j+2)-th Taylor term, regardless of the requested precision.
; Its reciprocal therefore gives a uniform inverse-square upper bound.
(defthm lw-kernel-upper-inverse-square
  (implies (and (rationalp value) (< 0 value) (rationalp rate) (< 0 rate)
                (natp index) (<= (+ 2 index) (* rate value))
                (rationalp step) (<= 0 step))
           (<= (* value value (cdr (lw-kernel-weight-bounds value rate index step error)))
               (* step (+ 1 index) (+ 2 index) (lw-rational-power (/ rate) (+ 2 index)))))
  :hints (("Goal"
           :use ((:instance lw-exp-index-adequate (value (* rate value))
                   (epsilon (lw-kernel-weight-precision value index step error)))
                 (:instance lw-exp-bounds-valid (value (* rate value))
                   (epsilon (lw-kernel-weight-precision value index step error)))
                 (:instance lw-exp-bounds-lower-term (value (* rate value)) (index (+ 2 index))
                   (error (lw-kernel-weight-precision value index step error)))
                 (:instance lw-mt-scaled-term-identity)
                 (:instance lw-rational-power-reciprocal-pair (value rate) (index (+ 2 index)))
                 (:instance lw-rational-power-positive (base rate) (exponent (+ 2 index)))
                 (:instance lw-rational-power-positive (base (/ rate)) (exponent (+ 2 index)))
                 (:instance lw-mt-multiply-order
                   (a (lw-exp-term (* rate value) (+ 2 index)))
                   (b (car (lw-exp-bounds (* rate value) (lw-kernel-weight-precision value index step error))))
                   (c (* (+ 1 index) (+ 2 index) (lw-rational-power (/ rate) (+ 2 index)))))
                 (:instance lw-positive-division-bound
                   (numerator (* value value (lw-exp-term value index)))
                   (divisor (car (lw-exp-bounds (* rate value) (lw-kernel-weight-precision value index step error))))
                   (bound (* (+ 1 index) (+ 2 index) (lw-rational-power (/ rate) (+ 2 index)))))
                 (:instance lw-mt-multiply-order
                   (a (/ (* value value (lw-exp-term value index))
                         (car (lw-exp-bounds (* rate value) (lw-kernel-weight-precision value index step error)))))
                   (b (* (+ 1 index) (+ 2 index) (lw-rational-power (/ rate) (+ 2 index)))) (c step)))
           :in-theory (e/d (lw-kernel-weight-bounds lw-kernel-weight-scale lw-exp-neg-bounds)
                           (lw-kernel-weight-precision lw-exp-index lw-exp-index-adequate lw-exp-bounds-valid
                            lw-exp-bounds-lower-term lw-rational-power-reciprocal-pair lw-rational-power-positive))
           :nonlinearp t)))

(defun lw-mellin-tail-coefficient (rate index mass)
  (* mass (+ 1 (nfix index)) (+ 2 (nfix index)) (lw-rational-power (/ rate) (+ 2 (nfix index)))))
(defun lw-mellin-tail-cutoff (rate index mass error)
  (+ 1 (/ (+ 2 (nfix index)) rate)
     (lw-ceiling-rational (/ (* 2 (lw-mellin-tail-coefficient rate index mass)) error))))
(defun lw-mellin-tail-radius (rate index mass cutoff)
  (/ (lw-mellin-tail-coefficient rate index mass) cutoff))

(defthm lw-mellin-tail-coefficient-nonnegative
  (implies (and (rationalp rate) (< 0 rate) (rationalp mass) (<= 0 mass))
           (and (rationalp (lw-mellin-tail-coefficient rate index mass))
                (<= 0 (lw-mellin-tail-coefficient rate index mass))))
  :hints (("Goal" :use ((:instance lw-rational-power-positive (base (/ rate)) (exponent (+ 2 (nfix index)))))
                  :in-theory (disable lw-rational-power-positive) :nonlinearp t)))

(defthm lw-mellin-tail-cutoff-adequate
  (implies (and (rationalp rate) (< 0 rate) (rationalp mass) (<= 0 mass)
                (rationalp error) (< 0 error))
           (and (rationalp (lw-mellin-tail-cutoff rate index mass error))
                (< 0 (lw-mellin-tail-cutoff rate index mass error))
                (<= (+ 2 (nfix index)) (* rate (lw-mellin-tail-cutoff rate index mass error)))
                (<= (* 2 (lw-mellin-tail-coefficient rate index mass))
                    (* error (lw-mellin-tail-cutoff rate index mass error)))))
  :hints (("Goal" :use (lw-mellin-tail-coefficient-nonnegative
                        (:instance lw-ceiling-rational-bracket
                          (value (/ (* 2 (lw-mellin-tail-coefficient rate index mass)) error)))
                        (:instance inverse-of-* (x rate)) (:instance inverse-of-* (x error)))
                  :in-theory (disable lw-ceiling-rational lw-ceiling-rational-bracket
                                      lw-mellin-tail-coefficient lw-mellin-tail-coefficient-nonnegative inverse-of-*)
                  :nonlinearp t)))

(defthm lw-mellin-tail-radius-budget
  (implies (and (rationalp rate) (< 0 rate) (rationalp mass) (<= 0 mass)
                (rationalp error) (< 0 error))
           (<= (lw-mellin-tail-radius rate index mass (lw-mellin-tail-cutoff rate index mass error)) (/ error 2)))
  :hints (("Goal" :use (lw-mellin-tail-cutoff-adequate lw-mellin-tail-coefficient-nonnegative
                        (:instance lw-positive-division-bound
                          (numerator (lw-mellin-tail-coefficient rate index mass))
                          (divisor (lw-mellin-tail-cutoff rate index mass error)) (bound (/ error 2))))
                  :in-theory (disable lw-mellin-tail-cutoff lw-mellin-tail-cutoff-adequate
                                      lw-mellin-tail-coefficient lw-mellin-tail-coefficient-nonnegative)
                  :nonlinearp t)))

(local
 (defthm lw-mt-reciprocal-difference
   (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b) (rationalp coefficient))
            (equal (* a b coefficient (- (/ a) (/ b))) (* coefficient (- b a))))
   :hints (("Goal" :use ((:instance lw-mt-inverse-factor (divisor a) (coefficient (* b coefficient)))
                         (:instance lw-mt-inverse-factor (divisor b) (coefficient (* a coefficient))))))
   :rule-classes nil))
(local (defthm lw-mt-cancel-positive
         (implies (and (rationalp a) (rationalp b) (rationalp factor) (< 0 factor)
                       (<= (* factor a) (* factor b)))
                  (<= a b))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local
 (defthm lw-mt-rectangle-potential
   (implies (and (rationalp start) (< 0 start) (rationalp step) (< 0 step) (<= step start)
                 (rationalp coefficient) (<= 0 coefficient) (rationalp term) (<= 0 term)
                 (<= (* start start term) (* step coefficient)))
            (<= term (* 2 coefficient (- (/ start) (/ (+ start step))))))
   :hints (("Goal" :use ((:instance lw-mt-reciprocal-difference (a start) (b (+ start step)) (coefficient (* 2 coefficient)))
                         (:instance lw-mt-multiply-order (a (+ start step)) (b (* 2 start)) (c (* start term)))
                         (:instance lw-mt-multiply-order
                           (a (* start start term)) (b (* step coefficient)) (c 2))
                         (:instance lw-mt-cancel-positive (a term)
                           (b (* 2 coefficient (- (/ start) (/ (+ start step))))) (factor (* start (+ start step)))))
                   :nonlinearp t))
   :rule-classes nil))

(defthm lw-kernel-upper-tail-potential
  (implies (and (rationalp value) (< 0 value) (rationalp rate) (< 0 rate)
                (natp index) (<= (+ 2 index) (* rate value))
                (rationalp step) (< 0 step) (<= step value))
           (<= (cdr (lw-kernel-weight-bounds value rate index step error))
               (* 2 (lw-mellin-tail-coefficient rate index 1) (- (/ value) (/ (+ value step))))))
  :hints (("Goal" :use (lw-kernel-upper-inverse-square
                        (:instance lw-kernel-weight-bounds-valid (sigma rate))
                        (:instance lw-mellin-tail-coefficient-nonnegative (mass 1))
                        (:instance lw-mt-rectangle-potential
                          (start value) (coefficient (lw-mellin-tail-coefficient rate index 1))
                          (term (cdr (lw-kernel-weight-bounds value rate index step error)))))
                  :in-theory (disable lw-kernel-weight-bounds lw-kernel-weight-bounds-valid
                                      lw-kernel-weight-bounds-overlap lw-kernel-upper-inverse-square
                                      lw-mellin-tail-coefficient-nonnegative))))

(defun lw-kernel-tail-rectangles (start step count rate index error)
  (declare (xargs :measure (nfix count)))
  (if (zp count) 0
    (+ (cdr (lw-kernel-weight-bounds start rate index step error))
       (lw-kernel-tail-rectangles (+ start step) step (- count 1) rate index error))))

(defthm lw-kernel-tail-rectangles-rational
  (implies (and (rationalp start) (< 0 start) (rationalp step) (< 0 step) (rationalp rate) (< 0 rate))
           (rationalp (lw-kernel-tail-rectangles start step count rate index error)))
  :hints (("Goal" :induct (lw-kernel-tail-rectangles start step count rate index error)
                  :in-theory (disable lw-kernel-weight-bounds lw-kernel-weight-bounds-valid))
          (and stable-under-simplificationp
               '(:use ((:instance lw-kernel-weight-bounds-valid (value start) (sigma rate))))))
  :rule-classes (:rewrite :type-prescription))

(defthm lw-kernel-tail-rectangles-potential
  (implies (and (rationalp start) (< 0 start) (rationalp rate) (< 0 rate)
                (natp index) (<= (+ 2 index) (* rate start)) (natp count)
                (rationalp step) (< 0 step) (<= step start))
           (<= (+ (lw-kernel-tail-rectangles start step count rate index error)
                  (* 2 (lw-mellin-tail-coefficient rate index 1) (/ (+ start (* count step)))))
               (* 2 (lw-mellin-tail-coefficient rate index 1) (/ start))))
  :hints (("Goal" :induct (lw-kernel-tail-rectangles start step count rate index error)
                  :in-theory (disable lw-kernel-weight-bounds lw-mellin-tail-coefficient
                                      lw-kernel-upper-tail-potential))
          (and stable-under-simplificationp
               '(:use ((:instance lw-kernel-upper-tail-potential (value start))
                       (:instance lw-mellin-tail-coefficient-nonnegative (mass 1)))
                 :in-theory (disable lw-kernel-weight-bounds lw-kernel-tail-rectangles
                                     lw-mellin-tail-coefficient lw-kernel-upper-tail-potential
                                     lw-mellin-tail-coefficient-nonnegative)
                 :nonlinearp t))))

(defthm lw-kernel-tail-rectangles-bound
  (implies (and (rationalp start) (< 0 start) (rationalp rate) (< 0 rate)
                (natp index) (<= (+ 2 index) (* rate start)) (natp count)
                (rationalp step) (< 0 step) (<= step start))
           (<= (lw-kernel-tail-rectangles start step count rate index error)
               (/ (* 2 (lw-mellin-tail-coefficient rate index 1)) start)))
  :hints (("Goal" :use (lw-kernel-tail-rectangles-potential
                        (:instance lw-mellin-tail-coefficient-nonnegative (mass 1)))
                  :in-theory (disable lw-kernel-tail-rectangles lw-kernel-tail-rectangles-potential
                                      lw-mellin-tail-coefficient lw-mellin-tail-coefficient-nonnegative)
                  :nonlinearp t)))

(defthm lw-kernel-tail-rectangles-at-cutoff
  (implies (and (rationalp rate) (< 0 rate) (rationalp mass) (<= 0 mass)
                (rationalp target-error) (< 0 target-error) (natp index) (natp count)
                (rationalp step) (< 0 step) (<= step (lw-mellin-tail-cutoff rate index mass target-error)))
           (<= (* mass (lw-kernel-tail-rectangles (lw-mellin-tail-cutoff rate index mass target-error)
                                                 step count rate index error)) target-error))
  :hints (("Goal"
           :use ((:instance lw-mellin-tail-cutoff-adequate (error target-error))
                 (:instance lw-kernel-tail-rectangles-bound (start (lw-mellin-tail-cutoff rate index mass target-error)))
                 (:instance lw-mt-multiply-order
                   (a (lw-kernel-tail-rectangles (lw-mellin-tail-cutoff rate index mass target-error) step count rate index error))
                   (b (/ (* 2 (lw-mellin-tail-coefficient rate index 1))
                         (lw-mellin-tail-cutoff rate index mass target-error))) (c mass))
                 (:instance lw-positive-division-bound
                   (numerator (* 2 (lw-mellin-tail-coefficient rate index mass)))
                   (divisor (lw-mellin-tail-cutoff rate index mass target-error)) (bound target-error)))
           :in-theory (e/d (lw-mellin-tail-coefficient)
                           (lw-mellin-tail-cutoff lw-mellin-tail-cutoff-adequate lw-kernel-tail-rectangles
                            lw-kernel-tail-rectangles-bound))
           :nonlinearp t)))

(assert-event
 (and (< 0 (lw-mellin-tail-cutoff 2 3 4 1/10))
      (<= (* 2 (lw-mellin-tail-coefficient 2 3 4)) (* 1/10 (lw-mellin-tail-cutoff 2 3 4 1/10)))
      (<= (lw-mellin-tail-radius 2 3 4 (lw-mellin-tail-cutoff 2 3 4 1/10)) 1/20)))
