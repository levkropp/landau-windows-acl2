(in-package "ACL2")

(include-book "exp-addition")
(include-book "rpow-continuity")

; Rising binomial coefficients and a finite geometric-tail potential.
; They majorize factorial-normalized grid moments without an integral
; or an assumed infinite-series sum.
(local (in-theory (disable lw-exp-term lw-exp-sum lw-rational-power lw-exp-term-multiplied)))
(local (defthm lw-nb-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-nb-times-negative
         (implies (and (rationalp a) (rationalp b)) (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-nb-negative-times
         (implies (and (rationalp a) (rationalp b)) (equal (* (- a) b) (- (* a b))))))
(local (defthm lw-nb-zero-times (equal (* 0 a) 0)))
(local (defthm lw-nb-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))
(local (defthm lw-nb-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))
(local (defthm lw-nb-left-distribute
         (implies (and (rationalp a) (rationalp b) (rationalp c))
                  (equal (* (+ a b) c) (+ (* a c) (* b c))))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-nb-equal-times
         (implies (equal a b) (equal (* a factor) (* b factor))) :rule-classes nil))
(local (defthm lw-nb-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b) (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-nb-nonnegative-product
         (implies (and (rationalp a) (<= 0 a) (rationalp b) (<= 0 b)) (<= 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-nb-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal" :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient)))
                         :in-theory (disable associativity-of-* commutativity-of-* lw-nb-left-commutes)))))
(local (defun lw-nb-countdown (index)
         (declare (xargs :measure (nfix index)))
         (if (zp index) nil (lw-nb-countdown (- index 1)))))

(defun lw-rising-binomial (value index)
  (declare (xargs :measure (nfix index)))
  (if (zp index) 1
    (/ (* (+ value index) (lw-rising-binomial value (- index 1))) index)))

(defthm lw-rising-binomial-rational
  (implies (rationalp value) (rationalp (lw-rising-binomial value index)))
  :rule-classes (:rewrite :type-prescription))

(defthm lw-rising-binomial-nonnegative
  (implies (and (rationalp value) (<= -1 value)) (<= 0 (lw-rising-binomial value index)))
  :hints (("Goal" :induct (lw-rising-binomial value index)
                  :in-theory (disable distributivity lw-nb-left-distribute) :nonlinearp t)
          (and stable-under-simplificationp
               '(:use ((:instance lw-nb-multiply-order (a 0) (b (lw-rising-binomial value (- index 1)))
                         (factor (/ (+ value index) index)))
                       (:instance lw-nb-nonnegative-product (a (/ index)) (b (+ value index)))) :nonlinearp t)))
  :rule-classes (:rewrite :linear))

(local (defthm lw-nb-rising-zero
         (implies (zp index) (equal (lw-rising-binomial value index) 1))))

(defthm lw-rising-binomial-multiplied
  (implies (and (rationalp value) (posp index))
           (equal (* index (lw-rising-binomial value index))
                  (* (+ value index) (lw-rising-binomial value (- index 1)))))
  :hints (("Goal" :use ((:instance lw-nb-inverse-factor
                          (divisor index) (coefficient (* (+ value index) (lw-rising-binomial value (- index 1))))))
                  :expand ((lw-rising-binomial value index))
                  :in-theory (disable lw-rising-binomial distributivity lw-nb-left-distribute)))
  :rule-classes nil)

(local (in-theory (disable (:definition lw-rising-binomial))))

(defthm lw-rising-binomial-translate
  (implies (and (rationalp value) (natp index))
           (equal (* (+ 1 value) (lw-rising-binomial (+ 1 value) index))
                  (* (+ 1 value index) (lw-rising-binomial value index))))
  :hints (("Goal" :induct (lw-nb-countdown index))
          (and stable-under-simplificationp
               '(:use (lw-rising-binomial-multiplied
                       (:instance lw-rising-binomial-multiplied (value (+ 1 value)))
                       (:instance lw-nb-equal-times
                         (a (* index (lw-rising-binomial (+ 1 value) index)))
                         (b (* (+ 1 value index) (lw-rising-binomial (+ 1 value) (- index 1)))) (factor (+ 1 value)))
                       (:instance lw-nb-equal-times
                         (a (* index (lw-rising-binomial value index)))
                         (b (* (+ value index) (lw-rising-binomial value (- index 1)))) (factor (+ 1 value index)))
                       (:instance lw-nb-equal-times
                         (a (* (+ 1 value) (lw-rising-binomial (+ 1 value) (- index 1))))
                         (b (* (+ value index) (lw-rising-binomial value (- index 1)))) (factor (+ 1 value index))))
                 :nonlinearp t))))

(defthm lw-rising-binomial-pascal
  (implies (and (rationalp value) (posp index))
           (equal (lw-rising-binomial (+ 1 value) index)
                  (+ (lw-rising-binomial value index) (lw-rising-binomial (+ 1 value) (- index 1)))))
  :hints (("Goal" :use (lw-rising-binomial-multiplied
                        (:instance lw-rising-binomial-multiplied (value (+ 1 value)))
                        (:instance lw-rising-binomial-translate (index (- index 1))))
                  :in-theory (disable lw-rising-binomial-translate) :nonlinearp t)))

(defthm lw-rising-binomial-majorizes-taylor-term
  (implies (and (rationalp value) (<= 0 value) (natp index))
           (<= (lw-exp-term value index) (lw-rising-binomial value index)))
  :hints (("Goal" :induct (lw-nb-countdown index))
          (and stable-under-simplificationp
               '(:use (lw-rising-binomial-multiplied lw-exp-term-multiplied
                       (:instance lw-exp-term-nonnegative)
                       (:instance lw-rising-binomial-nonnegative (index (- index 1)))
                       (:instance lw-nb-multiply-order (a (lw-exp-term value (- index 1)))
                         (b (lw-rising-binomial value (- index 1))) (factor value)))
                 :expand ((lw-exp-term value 0)) :nonlinearp t))))

(defthm lw-rising-binomial-minus-one
  (implies (posp index) (equal (lw-rising-binomial -1 index) 0))
  :hints (("Goal" :induct (lw-nb-countdown index) :in-theory (enable lw-rising-binomial))))

(defun lw-negative-binomial-potential (start index ratio)
  (declare (xargs :measure (nfix index)))
  (if (zp index)
      (/ (lw-rational-power ratio start) (- 1 ratio))
    (/ (+ (lw-negative-binomial-potential start (- index 1) ratio)
          (* (lw-rational-power ratio start) (lw-rising-binomial (- start 1) index))) (- 1 ratio))))

(defthm lw-negative-binomial-potential-rational
  (implies (and (rationalp start) (rationalp ratio))
           (rationalp (lw-negative-binomial-potential start index ratio)))
  :rule-classes (:rewrite :type-prescription))

(local (defthm lw-nb-quotient-nonnegative
         (implies (and (rationalp numerator) (<= 0 numerator) (rationalp divisor) (< 0 divisor))
                  (<= 0 (/ numerator divisor)))
         :hints (("Goal" :use ((:instance lw-nb-nonnegative-product (a numerator) (b (/ divisor))))))
         :rule-classes nil))

(defthm lw-negative-binomial-potential-nonnegative
  (implies (and (natp start) (rationalp ratio) (<= 0 ratio) (< ratio 1))
           (<= 0 (lw-negative-binomial-potential start index ratio)))
  :hints (("Goal" :induct (lw-negative-binomial-potential start index ratio)
                  :in-theory (disable distributivity lw-nb-left-distribute) :nonlinearp t)
          (and stable-under-simplificationp
               '(:use ((:instance lw-rising-binomial-nonnegative (value (- start 1)))
                       (:instance lw-rational-power-nonnegative (base ratio) (exponent start))
                       (:instance lw-nb-nonnegative-product (a (lw-rational-power ratio start)) (b (lw-rising-binomial (- start 1) index)))
                       (:instance lw-nb-quotient-nonnegative (divisor (- 1 ratio))
                         (numerator (if (zp index) (lw-rational-power ratio start)
                                      (+ (lw-negative-binomial-potential start (- index 1) ratio)
                                         (* (lw-rational-power ratio start) (lw-rising-binomial (- start 1) index)))))))
                 :in-theory (disable distributivity lw-nb-left-distribute lw-rising-binomial-nonnegative lw-rational-power-nonnegative)
                 :nonlinearp t))))

(local (defthm lw-nb-power-zero
         (implies (zp exponent) (equal (lw-rational-power base exponent) 1))
         :hints (("Goal" :in-theory (enable lw-rational-power)))))
(local (defthm lw-nb-power-first
         (implies (rationalp base) (equal (lw-rational-power base 1) base))
         :hints (("Goal" :in-theory (enable lw-rational-power)))))
(local (defthm lw-nb-power-successor
         (implies (natp exponent)
                  (equal (lw-rational-power base (+ 1 exponent)) (* base (lw-rational-power base exponent))))
         :hints (("Goal" :expand ((lw-rational-power base (+ 1 exponent)))))
         :rule-classes nil))

(local (in-theory (disable lw-negative-binomial-potential lw-rising-binomial-translate lw-rising-binomial-pascal)))

(local (defthm lw-nb-potential-zero-index
         (implies (zp index)
                  (equal (lw-negative-binomial-potential start index ratio) (/ (lw-rational-power ratio start) (- 1 ratio))))
         :hints (("Goal" :in-theory (enable lw-negative-binomial-potential)))))

(defthm lw-negative-binomial-potential-zero
  (implies (and (natp index) (rationalp ratio) (<= 0 ratio) (< ratio 1))
           (equal (lw-negative-binomial-potential 0 index ratio) (lw-rational-power (/ (- 1 ratio)) (+ 1 index))))
  :hints (("Goal" :induct (lw-nb-countdown index))
          (and stable-under-simplificationp
               '(:use ((:instance lw-nb-power-successor (base (/ (- 1 ratio))) (exponent index)))
                 :expand ((lw-negative-binomial-potential 0 index ratio))
                 :nonlinearp t))))

(defthm lw-negative-binomial-potential-multiplied
  (implies (and (natp start) (rationalp ratio) (<= 0 ratio) (< ratio 1))
           (equal (* (- 1 ratio) (lw-negative-binomial-potential start index ratio))
                  (if (zp index) (lw-rational-power ratio start)
                    (+ (lw-negative-binomial-potential start (- index 1) ratio)
                       (* (lw-rational-power ratio start) (lw-rising-binomial (- start 1) index))))))
  :hints (("Goal" :use ((:instance lw-nb-inverse-factor (divisor (- 1 ratio))
                          (coefficient (if (zp index) (lw-rational-power ratio start)
                                         (+ (lw-negative-binomial-potential start (- index 1) ratio)
                                            (* (lw-rational-power ratio start) (lw-rising-binomial (- start 1) index)))))))
                  :expand ((lw-negative-binomial-potential start index ratio))
                  :in-theory (disable distributivity lw-nb-left-distribute)))
  :rule-classes nil)

(local (defthm lw-nb-cancel-positive-equality
         (implies (and (rationalp a) (rationalp b) (rationalp factor) (< 0 factor)
                       (equal (* factor a) (* factor b))) (equal a b))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defthm lw-negative-binomial-potential-step
  (implies (and (natp start) (natp index) (rationalp ratio) (<= 0 ratio) (< ratio 1))
           (equal (- (lw-negative-binomial-potential start index ratio)
                     (lw-negative-binomial-potential (+ start 1) index ratio))
                  (* (lw-rational-power ratio start) (lw-rising-binomial start index))))
  :hints (("Goal" :induct (lw-nb-countdown index))
          (and stable-under-simplificationp
               '(:use (lw-negative-binomial-potential-multiplied
                       (:instance lw-nb-inverse-factor (divisor (- 1 ratio)) (coefficient (lw-rational-power ratio start)))
                       (:instance lw-negative-binomial-potential-multiplied (start (+ start 1)))
                       (:instance lw-rising-binomial-pascal (value (- start 1)))
                       (:instance lw-nb-power-successor (base ratio) (exponent start))
                       (:instance lw-nb-equal-times (factor (lw-rational-power ratio start))
                         (a (lw-rising-binomial start index))
                         (b (+ (lw-rising-binomial (- start 1) index) (lw-rising-binomial start (- index 1)))))
                       (:instance lw-nb-cancel-positive-equality
                         (a (- (lw-negative-binomial-potential start index ratio)
                               (lw-negative-binomial-potential (+ start 1) index ratio)))
                         (b (* (lw-rational-power ratio start) (lw-rising-binomial start index))) (factor (- 1 ratio))))
                 :in-theory (disable lw-nb-inverse-factor)
                 :do-not-induct t :nonlinearp t))))

(defun lw-negative-binomial-sum (start count index ratio)
  (declare (xargs :measure (nfix count)))
  (if (zp count) 0
    (+ (* (lw-rational-power ratio start) (lw-rising-binomial start index))
       (lw-negative-binomial-sum (+ start 1) (- count 1) index ratio))))

(defthm lw-negative-binomial-sum-rational
  (implies (and (rationalp start) (rationalp ratio)) (rationalp (lw-negative-binomial-sum start count index ratio)))
  :rule-classes (:rewrite :type-prescription))

(defthm lw-negative-binomial-sum-telescope
  (implies (and (natp start) (natp count) (natp index) (rationalp ratio) (<= 0 ratio) (< ratio 1))
           (equal (+ (lw-negative-binomial-sum start count index ratio)
                     (lw-negative-binomial-potential (+ start count) index ratio))
                  (lw-negative-binomial-potential start index ratio)))
  :hints (("Goal" :induct (lw-negative-binomial-sum start count index ratio)
                  :in-theory (disable lw-negative-binomial-potential-step))
          (and stable-under-simplificationp
               '(:use (lw-negative-binomial-potential-step) :do-not-induct t))))

(defthm lw-negative-binomial-sum-bound
  (implies (and (natp start) (natp count) (natp index) (rationalp ratio) (<= 0 ratio) (< ratio 1))
           (<= (lw-negative-binomial-sum start count index ratio) (lw-negative-binomial-potential start index ratio)))
  :hints (("Goal" :use (lw-negative-binomial-sum-telescope
                        (:instance lw-negative-binomial-potential-nonnegative (start (+ start count))))
                  :in-theory (disable lw-negative-binomial-sum lw-negative-binomial-sum-telescope lw-negative-binomial-potential-nonnegative))))

(defthm lw-negative-binomial-mass-bound
  (implies (and (natp count) (natp index) (rationalp ratio) (<= 0 ratio) (< ratio 1))
           (<= (lw-negative-binomial-sum 0 count index ratio) (lw-rational-power (/ (- 1 ratio)) (+ 1 index))))
  :hints (("Goal" :use ((:instance lw-negative-binomial-sum-bound (start 0))
                        lw-negative-binomial-potential-zero)
                  :in-theory (disable lw-negative-binomial-sum lw-negative-binomial-sum-bound lw-negative-binomial-potential-zero))))

(defthm lw-negative-binomial-sum-nonnegative
  (implies (and (natp start) (natp index) (rationalp ratio) (<= 0 ratio))
           (<= 0 (lw-negative-binomial-sum start count index ratio)))
  :hints (("Goal" :induct (lw-negative-binomial-sum start count index ratio))
          (and stable-under-simplificationp
               '(:use ((:instance lw-rising-binomial-nonnegative (value start))
                       (:instance lw-rational-power-nonnegative (base ratio) (exponent start))
                       (:instance lw-nb-nonnegative-product (a (lw-rational-power ratio start)) (b (lw-rising-binomial start index))))
                 :in-theory (disable lw-rising-binomial-nonnegative lw-rational-power-nonnegative)
                 :do-not-induct t))))

(defthm lw-negative-binomial-interval-mass-bound
  (implies (and (natp start) (natp count) (natp index) (rationalp ratio) (<= 0 ratio) (< ratio 1))
           (<= (lw-negative-binomial-sum start count index ratio) (lw-rational-power (/ (- 1 ratio)) (+ 1 index))))
  :hints (("Goal" :use (lw-negative-binomial-sum-bound
                        (:instance lw-negative-binomial-sum-telescope (start 0) (count start))
                        (:instance lw-negative-binomial-sum-nonnegative (start 0) (count start))
                        lw-negative-binomial-potential-zero)
                  :in-theory (disable lw-negative-binomial-sum lw-negative-binomial-sum-bound
                                      lw-negative-binomial-sum-telescope lw-negative-binomial-sum-nonnegative
                                      lw-negative-binomial-potential-zero))))

(defthm lw-rising-binomial-at-zero
  (implies (natp index) (equal (lw-rising-binomial 0 index) 1))
  :hints (("Goal" :induct (lw-nb-countdown index))
          (and stable-under-simplificationp
               '(:use ((:instance lw-rising-binomial-multiplied (value 0))
                       (:instance lw-nb-cancel-positive-equality (a (lw-rising-binomial 0 index)) (b 1) (factor index)))
                 :do-not-induct t :nonlinearp t))))

(local
 (defun lw-nb-symmetry-induction (value index)
   (declare (xargs :measure (+ (nfix value) (nfix index))))
   (if (or (zp value) (zp index)) nil
     (list (lw-nb-symmetry-induction (- value 1) index)
           (lw-nb-symmetry-induction value (- index 1))))))

(defthm lw-rising-binomial-symmetric
  (implies (and (natp value) (natp index))
           (equal (lw-rising-binomial value index) (lw-rising-binomial index value)))
  :hints (("Goal" :induct (lw-nb-symmetry-induction value index)
                  :in-theory (disable lw-rising-binomial-pascal))
          (and stable-under-simplificationp
               '(:use ((:instance lw-rising-binomial-pascal (value (- value 1)))
                       (:instance lw-rising-binomial-pascal (value (- index 1)) (index value))) :do-not-induct t))))

(defthm lw-negative-binomial-sum-last
  (implies (and (natp start) (natp count) (rationalp ratio))
           (equal (lw-negative-binomial-sum start (+ 1 count) index ratio)
                  (+ (lw-negative-binomial-sum start count index ratio)
                     (* (lw-rational-power ratio (+ start count)) (lw-rising-binomial (+ start count) index)))))
  :hints (("Goal" :induct (lw-negative-binomial-sum start count index ratio))
          (and stable-under-simplificationp
               '(:expand ((lw-negative-binomial-sum start (+ 1 count) index ratio)
                          (lw-negative-binomial-sum start count index ratio)
                          (lw-negative-binomial-sum start 1 index ratio)) :do-not-induct t))))
