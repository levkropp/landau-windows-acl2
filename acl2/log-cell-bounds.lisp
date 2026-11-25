(in-package "ACL2")

(include-book "log-multiplication")
(include-book "log-exp")

; Native logarithm cells used by the Euler-corrected zeta series.
; Coarse one-cell rectangles are compared with the actual native grid.

(local (in-theory (disable lw-log-bounds lw-log-count lw-log-rectangles
 lw-uniform-log-partition lw-positive-partitionp lw-partition-end
 lw-log-partition-lower lw-log-partition-upper)))

(local (defthm lw-lcb-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-lcb-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-lcb-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-lcb-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-lcb-times-negative (a b) (b a)))
                 :in-theory (disable lw-lcb-times-negative)))))

(local (defthm lw-lcb-zero-times (equal (* 0 a) 0)))

(local (defthm lw-lcb-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-lcb-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-lcb-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-lcb-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-lcb-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-lcb-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-lcb-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-lcb-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-lcb-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-lcb-left-commutes)))))

(local (defthm lw-lcb-grid-data
 (implies (and (rationalp value) (< 1 value) (rationalp error) (< 0 error))
  (and (lw-positive-partitionp 1 (lw-uniform-log-partition 1 (/ (- value 1) (lw-log-count value error)) (lw-log-count value error)))
       (true-listp (lw-uniform-log-partition 1 (/ (- value 1) (lw-log-count value error)) (lw-log-count value error)))
       (equal (lw-partition-end 1 (lw-uniform-log-partition 1 (/ (- value 1) (lw-log-count value error)) (lw-log-count value error))) value)
       (equal (lw-log-partition-lower 1 (lw-uniform-log-partition 1 (/ (- value 1) (lw-log-count value error)) (lw-log-count value error))) (car (lw-log-bounds value error)))
       (equal (lw-log-partition-upper 1 (lw-uniform-log-partition 1 (/ (- value 1) (lw-log-count value error)) (lw-log-count value error))) (cdr (lw-log-bounds value error)))))
 :hints (("Goal"
  :use ((:instance lw-log-count-positive (epsilon error))
        (:instance lw-log-step-positive (epsilon error))
        (:instance lw-log-grid-endpoint (epsilon error))
        (:instance lw-uniform-log-partition-valid
         (start 1) (step (/ (- value 1) (lw-log-count value error))) (count (lw-log-count value error)))
        (:instance lw-uniform-log-partition-end
         (start 1) (step (/ (- value 1) (lw-log-count value error))) (count (lw-log-count value error)))
        (:instance lw-uniform-log-partition-sums
         (start 1) (step (/ (- value 1) (lw-log-count value error))) (count (lw-log-count value error))))
  :in-theory (e/d (lw-log-bounds)
    (lw-log-count-positive lw-log-step-positive lw-log-grid-endpoint
     lw-uniform-log-partition-valid lw-uniform-log-partition-end lw-uniform-log-partition-sums))
  :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-lcb-single-partition
 (implies (and (rationalp value) (< 1 value))
  (and (lw-positive-partitionp 1 (list value))
       (equal (lw-partition-end 1 (list value)) value)
       (equal (lw-log-partition-lower 1 (list value)) (* (- value 1) (/ value)))
       (equal (lw-log-partition-upper 1 (list value)) (- value 1))))
 :hints (("Goal" :in-theory (enable lw-positive-partitionp lw-partition-end
                                    lw-log-partition-lower lw-log-partition-upper)))
 :rule-classes nil))

(defthm lw-log-bounds-unit-envelopes
 (implies (and (rationalp value) (< 1 value) (rationalp error) (< 0 error))
  (and (<= (* (- value 1) (/ value)) (cdr (lw-log-bounds value error)))
       (<= (car (lw-log-bounds value error)) (- value 1))))
 :hints (("Goal"
  :use (lw-lcb-grid-data lw-lcb-single-partition
        (:instance lw-log-partitions-compare (start 1) (left (list value)) (right (lw-uniform-log-partition 1 (/ (- value 1) (lw-log-count value error)) (lw-log-count value error))))
        (:instance lw-log-partitions-compare (start 1) (left (lw-uniform-log-partition 1 (/ (- value 1) (lw-log-count value error)) (lw-log-count value error))) (right (list value))))
  :in-theory (disable lw-log-partitions-compare)
  :do-not-induct t)))

(local (defthm lw-lcb-cell-normalization
 (implies (posp index)
  (equal (* (+ 1 index) (/ index) (/ (+ 1 (/ index)))) 1))
 :hints (("Goal"
  :use ((:instance lw-lcb-inverse-factor (divisor index) (coefficient (/ (+ 1 (/ index)))))
        (:instance inverse-of-* (x (+ 1 (/ index)))))
  :in-theory (disable lw-lcb-inverse-factor inverse-of-*)
  :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(defthm lw-log-successor-cell-normalization
 (implies (and (posp index) (rationalp error) (< 0 error))
  (and (rationalp (car (lw-log-bounds (+ 1 (/ index)) error))) (<= 0 (car (lw-log-bounds (+ 1 (/ index)) error))) (<= (car (lw-log-bounds (+ 1 (/ index)) error)) (/ index))
       (<= (- 1 (* (+ 1 index) error)) (* (+ 1 index) (car (lw-log-bounds (+ 1 (/ index)) error))))
       (<= (* (+ 1 index) (car (lw-log-bounds (+ 1 (/ index)) error))) (+ 1 (/ index)))))
 :hints (("Goal"
  :use ((:instance lw-log-bounds-unit-envelopes (value (+ 1 (/ index))))
        (:instance lw-log-bounds-interval (value (+ 1 (/ index))) (epsilon error))
        (:instance lw-log-bounds-width (value (+ 1 (/ index))) (epsilon error))
        (:instance lw-log-bounds-nonnegative (point (+ 1 (/ index))) (log-error error))
        lw-lcb-cell-normalization
        (:instance lw-lcb-inverse-factor (divisor index) (coefficient 1))
        (:instance lw-lcb-multiply-order (a (* (/ index) (/ (+ 1 (/ index))))) (b (cdr (lw-log-bounds (+ 1 (/ index)) error))) (factor (+ 1 index)))
        (:instance lw-lcb-multiply-order (a (- (cdr (lw-log-bounds (+ 1 (/ index)) error)) (car (lw-log-bounds (+ 1 (/ index)) error)))) (b error) (factor (+ 1 index)))
        (:instance lw-lcb-multiply-order (a (car (lw-log-bounds (+ 1 (/ index)) error))) (b (/ index)) (factor (+ 1 index))))
  :in-theory (e/d (lw-intervalp)
   (lw-log-bounds-unit-envelopes lw-log-bounds-interval lw-log-bounds-width lw-log-bounds-nonnegative
    lw-lcb-inverse-factor))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-log-successor-cell-error
 (implies (and (posp index) (rationalp error) (< 0 error))
  (<= (abs (- 1 (* (+ 1 index) (car (lw-log-bounds (+ 1 (/ index)) error)))))
      (+ (/ index) (* (+ 1 index) error))))
 :hints (("Goal"
  :use (lw-log-successor-cell-normalization
        (:instance lw-lcb-positive-product (a (+ 1 index)) (b error)))
  :in-theory (disable lw-log-successor-cell-normalization)
  :nonlinearp nil :do-not-induct t)))

