(in-package "ACL2")

(include-book "prime-powers")
(include-book "euler-bounds")

(local (defthm lw-signal-multiply-left-commutes
         (equal (* left (* middle right)) (* middle (* left right)))
         :hints (("Goal" :use ((:instance associativity-of-* (x left) (y middle) (z right))
                              (:instance associativity-of-* (x middle) (y left) (z right))
                              (:instance commutativity-of-* (x left) (y middle)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-signal-times-negation
         (implies (and (rationalp left) (rationalp right))
                  (equal (* left (- right)) (- (* left right))))
         :hints (("Goal" :use ((:instance distributivity
                                (x left) (y right) (z (- right))))
                         :in-theory (disable distributivity)))))

(defun lw-interval-width (bounds) (- (cdr bounds) (car bounds)))

(defthm lw-interval-add-valid
  (implies (and (lw-intervalp left) (lw-intervalp right))
           (lw-intervalp (lw-interval-add left right))))

(defthm lw-interval-sub-valid
  (implies (and (lw-intervalp left) (lw-intervalp right))
           (lw-intervalp (lw-interval-sub left right))))

(defthm lw-interval-scale-valid
  (implies (and (rationalp coefficient) (lw-intervalp bounds))
           (lw-intervalp (lw-interval-scale coefficient bounds)))
  :hints (("Goal" :nonlinearp t)))

(defthm lw-interval-add-width
  (implies (and (lw-intervalp left) (lw-intervalp right))
           (equal (lw-interval-width (lw-interval-add left right))
                  (+ (lw-interval-width left) (lw-interval-width right)))))

(defthm lw-interval-sub-width
  (implies (and (lw-intervalp left) (lw-intervalp right))
           (equal (lw-interval-width (lw-interval-sub left right))
                  (+ (lw-interval-width left) (lw-interval-width right)))))

(defthm lw-interval-scale-width
  (implies (and (rationalp coefficient) (<= 0 coefficient) (lw-intervalp bounds))
           (equal (lw-interval-width (lw-interval-scale coefficient bounds))
                  (* coefficient (lw-interval-width bounds)))))

; Padding above x contributes zero. This lets the executable bound be the
; integer numerator of x, so no floor or real oracle enters the summation.
(defun lw-ramp (value index) (max 0 (- (/ value index) 1)))

(defthm lw-ramp-rational
  (implies (and (rationalp value) (posp index)) (rationalp (lw-ramp value index)))
  :rule-classes (:rewrite :type-prescription))

(defthm lw-ramp-nonnegative (<= 0 (lw-ramp value index)))

(local (defthm lw-signal-multiply-at-most-one
         (implies (and (rationalp coefficient) (<= coefficient 1)
                       (rationalp value) (<= 0 value))
                  (<= (* coefficient value) value))
         :hints (("Goal" :nonlinearp t))))

(defthm lw-ramp-upper-bound
  (implies (and (rationalp value) (<= 1 value) (posp index))
           (<= (lw-ramp value index) value))
  :hints (("Goal" :use ((:instance lw-reciprocal-antitone (left 1) (right index))
                        (:instance lw-signal-multiply-at-most-one (coefficient (/ index))))
                  :in-theory (disable lw-reciprocal-antitone lw-signal-multiply-at-most-one)
                  :nonlinearp t)))

(defun lw-smoothed-sum-bounds (value count epsilon)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (cons 0 0)
    (lw-interval-add
     (lw-interval-scale (lw-ramp value count) (lw-mangoldt-bounds count epsilon))
     (lw-smoothed-sum-bounds value (- count 1) epsilon))))

(defthm lw-smoothed-sum-bounds-valid
  (implies (and (rationalp value) (rationalp epsilon) (< 0 epsilon))
           (lw-intervalp (lw-smoothed-sum-bounds value count epsilon)))
  :hints (("Goal" :induct (lw-smoothed-sum-bounds value count epsilon)
                  :in-theory (disable lw-interval-add lw-interval-scale lw-ramp
                                      lw-mangoldt-bounds lw-intervalp))))

(local
 (defthm lw-signal-product-bound
   (implies (and (rationalp coefficient) (<= 0 coefficient)
                 (rationalp value) (<= coefficient value)
                 (rationalp width) (<= 0 width)
                 (rationalp epsilon) (<= width epsilon))
            (<= (* coefficient width) (* value epsilon)))
   :hints (("Goal" :nonlinearp t))))

(defthm lw-smoothed-sum-bounds-width
  (implies (and (rationalp value) (<= 1 value) (natp count)
                (rationalp epsilon) (< 0 epsilon))
           (<= (lw-interval-width (lw-smoothed-sum-bounds value count epsilon))
               (* count value epsilon)))
  :hints (("Goal" :induct (lw-smoothed-sum-bounds value count epsilon)
                  :in-theory (disable lw-interval-add lw-interval-scale lw-ramp
                                      lw-mangoldt-bounds lw-interval-width lw-intervalp)
                  :nonlinearp t)
          (and stable-under-simplificationp
               '(:use ((:instance lw-mangoldt-bounds-width (value count))
                        (:instance lw-mangoldt-bounds-interval (value count))
                        (:instance lw-ramp-upper-bound (index count))
                        (:instance lw-ramp-nonnegative (index count))
                        (:instance lw-signal-product-bound
                          (coefficient (lw-ramp value count))
                          (width (lw-interval-width (lw-mangoldt-bounds count epsilon)))))
                 :in-theory (e/d (lw-interval-width lw-intervalp)
                                 (lw-smoothed-sum-bounds lw-interval-add lw-interval-scale
                                  lw-ramp lw-mangoldt-bounds lw-mangoldt-bounds-width
                                  lw-mangoldt-bounds-interval lw-ramp-upper-bound
                                  lw-ramp-nonnegative lw-signal-product-bound))
                 :nonlinearp t))))

(defun lw-gz-bounds-raw (value count epsilon)
  (lw-interval-add
   (lw-interval-sub (lw-smoothed-sum-bounds value count epsilon)
                    (lw-interval-scale value (lw-log-bounds value epsilon)))
   (lw-interval-scale value (lw-interval-add (cons 1 1) (lw-euler-bounds epsilon)))))

(defthm lw-gz-bounds-raw-valid
  (implies (and (rationalp value) (<= 1 value)
                (rationalp epsilon) (< 0 epsilon))
           (lw-intervalp (lw-gz-bounds-raw value count epsilon)))
  :hints (("Goal" :in-theory (disable lw-smoothed-sum-bounds lw-log-bounds lw-euler-bounds
                                      lw-interval-add lw-interval-sub lw-interval-scale))))

(defthm lw-gz-bounds-raw-width
  (implies (and (rationalp value) (<= 1 value) (natp count)
                (rationalp epsilon) (< 0 epsilon))
           (<= (lw-interval-width (lw-gz-bounds-raw value count epsilon))
               (* (+ count 2) value epsilon)))
  :hints (("Goal" :use (lw-smoothed-sum-bounds-width lw-log-bounds-width
                        lw-euler-bounds-width lw-log-bounds-interval lw-euler-bounds-interval)
                  :in-theory (disable lw-smoothed-sum-bounds lw-log-bounds lw-euler-bounds
                                      lw-interval-add lw-interval-sub lw-interval-scale
                                      lw-smoothed-sum-bounds-width lw-log-bounds-width
                                      lw-euler-bounds-width lw-log-bounds-interval
                                      lw-euler-bounds-interval)
                  :nonlinearp t)))

(defun lw-signal-count (value) (nfix (abs (numerator value))))

(defthm lw-signal-count-natural
  (natp (lw-signal-count value))
  :rule-classes (:rewrite :type-prescription))

(defthm lw-signal-count-covers
  (implies (and (rationalp value) (<= 1 value))
           (<= value (lw-signal-count value)))
  :hints (("Goal" :use ((:instance lw-numerator-upper-bound (width value))
                        (:instance rational-implies1 (x value)))
                  :in-theory (disable lw-numerator-upper-bound))))

(defun lw-signal-error-factor (value ceiling)
  (+ (* (+ (lw-signal-count value) 2) value) ceiling))

(defun lw-signal-precision (value ceiling error)
  (/ error (+ 1 (lw-signal-error-factor value ceiling))))

(defthm lw-signal-precision-positive
  (implies (and (rationalp value) (<= 1 value)
                (rationalp ceiling) (<= 0 ceiling)
                (rationalp error) (< 0 error))
           (and (rationalp (lw-signal-precision value ceiling error))
                (< 0 (lw-signal-precision value ceiling error))))
  :hints (("Goal" :in-theory (disable lw-signal-count) :nonlinearp t)))

(defun lw-signal-bounds-raw (value count ceiling numerator denominator epsilon)
  (lw-interval-sub
   (lw-gz-bounds-raw value count epsilon)
   (lw-interval-scale ceiling (lw-rpow-bounds value numerator denominator epsilon))))

(defthm lw-signal-bounds-raw-valid
  (implies (and (rationalp value) (<= 1 value) (rationalp ceiling)
                (natp numerator) (posp denominator) (<= numerator denominator)
                (rationalp epsilon) (< 0 epsilon))
           (lw-intervalp (lw-signal-bounds-raw value count ceiling numerator denominator epsilon)))
  :hints (("Goal" :in-theory (disable lw-gz-bounds-raw lw-rpow-bounds
                                      lw-interval-sub lw-interval-scale))))

(defthm lw-signal-bounds-raw-width
  (implies (and (rationalp value) (<= 1 value) (natp count)
                (rationalp ceiling) (<= 0 ceiling)
                (natp numerator) (posp denominator) (<= numerator denominator)
                (rationalp epsilon) (< 0 epsilon))
           (<= (lw-interval-width
                (lw-signal-bounds-raw value count ceiling numerator denominator epsilon))
               (* (+ (* (+ count 2) value) ceiling) epsilon)))
  :hints (("Goal" :use (lw-gz-bounds-raw-width lw-rpow-bounds-width
                        lw-gz-bounds-raw-valid lw-rpow-bounds-sound)
                  :in-theory (disable lw-gz-bounds-raw lw-rpow-bounds lw-interval-sub
                                      lw-interval-scale lw-gz-bounds-raw-valid lw-rpow-bounds-sound
                                      lw-gz-bounds-raw-width lw-rpow-bounds-width)
                  :nonlinearp t)))

(defun lw-signal-bounds (value ceiling numerator denominator error)
  (lw-signal-bounds-raw value (lw-signal-count value) ceiling numerator denominator
                        (lw-signal-precision value ceiling error)))

(defthm lw-signal-bounds-valid
  (implies (and (rationalp value) (<= 1 value)
                (rationalp ceiling) (<= 0 ceiling)
                (natp numerator) (posp denominator) (<= numerator denominator)
                (rationalp error) (< 0 error))
           (lw-intervalp (lw-signal-bounds value ceiling numerator denominator error)))
  :hints (("Goal" :in-theory (disable lw-signal-bounds-raw lw-signal-precision))))

(local
 (defthm lw-signal-budget
   (implies (and (rationalp factor) (<= 0 factor)
                 (rationalp error) (<= 0 error))
            (<= (* factor (/ error (+ 1 factor))) error))
   :hints (("Goal" :use ((:instance lw-positive-division-bound
                          (numerator factor) (divisor (+ 1 factor)) (bound 1))
                        (:instance lw-signal-multiply-at-most-one
                          (coefficient (/ factor (+ 1 factor))) (value error)))
                   :in-theory (disable lw-signal-multiply-at-most-one)
                   :nonlinearp t))))

(defthm lw-signal-bounds-width
  (implies (and (rationalp value) (<= 1 value)
                (rationalp ceiling) (<= 0 ceiling)
                (natp numerator) (posp denominator) (<= numerator denominator)
                (rationalp error) (< 0 error))
           (<= (lw-interval-width (lw-signal-bounds value ceiling numerator denominator error))
               error))
  :hints (("Goal" :use ((:instance lw-signal-budget
                          (factor (lw-signal-error-factor value ceiling)))
                        (:instance lw-signal-bounds-raw-width
                          (count (lw-signal-count value))
                          (epsilon (lw-signal-precision value ceiling error))))
                  :in-theory (disable lw-signal-bounds-raw lw-signal-bounds-raw-width
                                      lw-signal-count lw-interval-width)
                  :nonlinearp t)))

(assert-event (let ((bounds (lw-signal-bounds 1 1 1 2 1)))
                (and (lw-intervalp bounds) (< 0 (car bounds))
                     (<= (lw-interval-width bounds) 1))))
(assert-event (let ((bounds (lw-signal-bounds 3/2 1 1 2 1)))
                (and (lw-intervalp bounds) (< 0 (car bounds))
                     (<= (lw-interval-width bounds) 1))))
