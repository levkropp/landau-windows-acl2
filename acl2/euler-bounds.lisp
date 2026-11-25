(in-package "ACL2")

(include-book "log-bounds")

(local (defthm lw-euler-multiply-left-commutes
         (equal (* left (* middle right)) (* middle (* left right)))
         :hints (("Goal" :use ((:instance associativity-of-* (x left) (y middle) (z right))
                              (:instance associativity-of-* (x middle) (y left) (z right))
                              (:instance commutativity-of-* (x left) (y middle)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(defun lw-harmonic (count)
  (declare (xargs :measure (nfix count)))
  (if (zp count) 0 (+ (/ count) (lw-harmonic (- count 1)))))

(defthm lw-harmonic-rational
  (rationalp (lw-harmonic count))
  :rule-classes (:rewrite :type-prescription))

(defun lw-euler-count (epsilon)
  (+ 1 (lw-precision-fuel 2 epsilon)))

(defthm lw-euler-count-positive
  (and (natp (lw-euler-count epsilon)) (< 0 (lw-euler-count epsilon)))
  :rule-classes (:rewrite :type-prescription))

(defthm lw-euler-reciprocal-bound
  (implies (and (rationalp epsilon) (< 0 epsilon))
           (<= (/ (lw-euler-count epsilon)) (/ epsilon 2)))
  :hints (("Goal" :use ((:instance lw-precision-fuel-adequate (width 2))
                        (:instance lw-positive-division-bound
                          (numerator 1) (divisor (lw-euler-count epsilon))
                          (bound (/ epsilon 2))))
                  :in-theory (disable lw-precision-fuel lw-precision-fuel-adequate)
                  :nonlinearp t)))

(defun lw-euler-from-log (count logarithm)
  (cons (- (- (lw-harmonic count) (cdr logarithm)) (/ count))
        (- (lw-harmonic count) (car logarithm))))

(defthm lw-euler-from-log-interval
  (implies (and (posp count) (lw-intervalp logarithm))
           (lw-intervalp (lw-euler-from-log count logarithm))))

(defthm lw-euler-from-log-width
  (implies (and (posp count) (lw-intervalp logarithm))
           (equal (- (cdr (lw-euler-from-log count logarithm))
                     (car (lw-euler-from-log count logarithm)))
                  (+ (- (cdr logarithm) (car logarithm)) (/ count)))))

; Finite propagation theorem; the real bounds used here are established
; for the actual Euler constant in Soft/EulerBounds.lean, not axiomatized.
(defthm lw-euler-from-log-sound
  (implies (and (posp count) (lw-contains logarithm log-value)
                (rationalp constant)
                (<= (- (- (lw-harmonic count) log-value) (/ count)) constant)
                (<= constant (- (lw-harmonic count) log-value)))
           (lw-contains (lw-euler-from-log count logarithm) constant)))

(defun lw-euler-bounds (epsilon)
  (let ((count (lw-euler-count epsilon)))
    (lw-euler-from-log count (lw-log-bounds count (/ epsilon 2)))))

(defthm lw-euler-bounds-interval
  (implies (and (rationalp epsilon) (< 0 epsilon))
           (lw-intervalp (lw-euler-bounds epsilon)))
  :hints (("Goal" :in-theory (disable lw-euler-from-log lw-log-bounds lw-euler-count))))

(defthm lw-euler-bounds-width
  (implies (and (rationalp epsilon) (< 0 epsilon))
           (<= (- (cdr (lw-euler-bounds epsilon))
                  (car (lw-euler-bounds epsilon))) epsilon))
  :hints (("Goal" :use (lw-euler-reciprocal-bound
                        (:instance lw-log-bounds-width
                          (value (lw-euler-count epsilon)) (epsilon (/ epsilon 2)))
                        (:instance lw-log-bounds-interval
                          (value (lw-euler-count epsilon)) (epsilon (/ epsilon 2))))
                  :in-theory (disable lw-log-bounds lw-euler-count lw-euler-from-log
                                      lw-euler-reciprocal-bound lw-log-bounds-width
                                      lw-log-bounds-interval))))

(assert-event (equal (lw-harmonic 6) 49/20))
(assert-event (let ((bounds (lw-euler-bounds 1/2)))
                (and (< (car bounds) 3/5) (< 1/2 (cdr bounds))
                     (<= (- (cdr bounds) (car bounds)) 1/2))))
