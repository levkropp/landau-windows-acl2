(in-package "ACL2")

(include-book "rational-window")

(local (defthm lw-log-multiply-left-commutes
         (equal (* left (* middle right)) (* middle (* left right)))
         :hints (("Goal" :use ((:instance associativity-of-* (x left) (y middle) (z right))
                              (:instance associativity-of-* (x middle) (y left) (z right))
                              (:instance commutativity-of-* (x left) (y middle)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-log-zero-product
         (equal (* 0 value) 0)))

(local (defthm lw-log-times-negation
         (implies (and (rationalp left) (rationalp right))
                  (equal (* left (- right)) (- (* left right))))
         :hints (("Goal" :use ((:instance distributivity
                                (x left) (y right) (z (- right))))
                         :in-theory (disable distributivity)))))

(local (defthm lw-log-additive-cancellation
         (implies (and (rationalp left) (rationalp right) (rationalp tail))
                  (equal (+ left right (- right) tail) (+ left tail)))))

; Rational left/right rectangle sums for integral_a^(a+n*h) dt/t.
; Their analytic interpretation is proved separately in Lean.  No real-valued
; logarithm or unverified oracle is introduced into the ACL2 logic.
(defun lw-log-rectangles (start step count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (cons 0 0)
    (lw-interval-add
     (cons (/ step (+ start step)) (/ step start))
     (lw-log-rectangles (+ start step) step (- count 1)))))

(defthm lw-reciprocal-positive
  (implies (and (rationalp value) (< 0 value)) (< 0 (/ value)))
  :rule-classes (:rewrite :type-prescription))

(defthm lw-reciprocal-antitone
  (implies (and (rationalp left) (rationalp right)
                (< 0 left) (<= left right))
           (<= (/ right) (/ left)))
  :hints (("Goal" :use ((:instance inverse-of-* (x left))
                        (:instance inverse-of-* (x right)))
                  :in-theory (disable inverse-of-*)
                  :nonlinearp t)))

(defthm lw-log-rectangles-interval
  (implies (and (rationalp start) (< 0 start)
                (rationalp step) (<= 0 step))
           (lw-intervalp (lw-log-rectangles start step count)))
  :hints (("Goal" :induct (lw-log-rectangles start step count)
                  :nonlinearp t)
          (and stable-under-simplificationp
               '(:use ((:instance lw-reciprocal-antitone
                         (left start) (right (+ start step))))
                 :in-theory (disable lw-reciprocal-antitone)
                 :nonlinearp t))))

(defthm lw-log-rectangles-nonnegative
  (implies (and (rationalp start) (< 0 start)
                (rationalp step) (<= 0 step))
           (<= 0 (car (lw-log-rectangles start step count))))
  :hints (("Goal" :induct (lw-log-rectangles start step count)
                  :nonlinearp t)))

(defthm lw-log-rectangles-width
  (implies (and (rationalp start) (< 0 start)
                (rationalp step) (<= 0 step) (natp count))
           (equal (- (cdr (lw-log-rectangles start step count))
                     (car (lw-log-rectangles start step count)))
                  (* step (- (/ start) (/ (+ start (* count step)))))))
  :hints (("Goal" :induct (lw-log-rectangles start step count)
                  :nonlinearp t)))

(local
 (defthm lw-log-scalar-width
   (implies (and (rationalp coefficient) (<= coefficient 1)
                 (rationalp tail) (<= 0 tail)
                 (rationalp step) (<= 0 step))
            (<= (- (* coefficient step) (* tail step)) step))
   :hints (("Goal" :nonlinearp t))))

(defthm lw-log-rectangles-width-bound
  (implies (and (rationalp start) (<= 1 start)
                (rationalp step) (<= 0 step) (natp count))
           (<= (- (cdr (lw-log-rectangles start step count))
                  (car (lw-log-rectangles start step count))) step))
  :hints (("Goal" :use (lw-log-rectangles-width
                        lw-log-rectangles-interval
                        (:instance lw-reciprocal-positive
                          (value (+ start (* count step))))
                        (:instance lw-reciprocal-antitone (left 1) (right start))
                        (:instance lw-log-scalar-width (coefficient (/ start))
                          (tail (/ (+ start (* count step))))))
                  :in-theory (disable lw-log-rectangles lw-log-rectangles-width
                                      lw-log-rectangles-interval lw-reciprocal-antitone
                                      lw-reciprocal-positive lw-log-scalar-width)
                  :nonlinearp t)))

(defun lw-log-count (value epsilon)
  (+ 1 (lw-precision-fuel (- value 1) epsilon)))

(defun lw-log-bounds (value epsilon)
  (let* ((count (lw-log-count value epsilon))
         (step (/ (- value 1) count)))
    (lw-log-rectangles 1 step count)))

(defthm lw-log-count-positive
  (and (natp (lw-log-count value epsilon)) (< 0 (lw-log-count value epsilon)))
  :rule-classes (:rewrite :type-prescription))

(local (defthm lw-log-multiply-inequality
         (implies (and (rationalp left) (rationalp right) (<= left right)
                       (rationalp factor) (<= 0 factor))
                  (<= (* left factor) (* right factor)))
         :hints (("Goal" :nonlinearp t))
         :rule-classes nil))

(defthm lw-positive-division-bound
  (implies (and (rationalp numerator) (<= 0 numerator)
                (rationalp divisor) (< 0 divisor)
                (rationalp bound) (<= numerator (* bound divisor)))
           (and (<= 0 (/ numerator divisor))
                (<= (/ numerator divisor) bound)))
  :hints (("Goal" :use ((:instance inverse-of-* (x divisor))
                        (:instance lw-log-multiply-inequality
                          (left numerator) (right (* bound divisor))
                          (factor (/ divisor))))
                  :in-theory (disable inverse-of-*) :nonlinearp t))
  :rule-classes nil)

(defthm lw-log-step-adequate
  (implies (and (rationalp value) (<= 1 value)
                (rationalp epsilon) (< 0 epsilon))
           (and (<= 0 (/ (- value 1) (lw-log-count value epsilon)))
                (<= (/ (- value 1) (lw-log-count value epsilon)) epsilon)))
  :hints (("Goal" :use ((:instance lw-precision-fuel-adequate (width (- value 1)))
                        (:instance lw-positive-division-bound
                          (numerator (- value 1)) (divisor (lw-log-count value epsilon))
                          (bound epsilon)))
                  :in-theory (disable lw-precision-fuel lw-precision-fuel-adequate)
                  :nonlinearp t)))

(defthm lw-log-bounds-interval
  (implies (and (rationalp value) (<= 1 value)
                (rationalp epsilon) (< 0 epsilon))
           (lw-intervalp (lw-log-bounds value epsilon)))
  :hints (("Goal" :in-theory (disable lw-log-rectangles lw-log-count))))

(defthm lw-log-bounds-width
  (implies (and (rationalp value) (<= 1 value)
                (rationalp epsilon) (< 0 epsilon))
           (<= (- (cdr (lw-log-bounds value epsilon))
                  (car (lw-log-bounds value epsilon))) epsilon))
  :hints (("Goal" :use (lw-log-step-adequate
                        (:instance lw-log-rectangles-interval
                          (start 1)
                          (step (/ (- value 1) (lw-log-count value epsilon)))
                          (count (lw-log-count value epsilon)))
                        (:instance lw-log-rectangles-width-bound
                          (start 1)
                          (step (/ (- value 1) (lw-log-count value epsilon)))
                          (count (lw-log-count value epsilon))))
                  :in-theory (disable lw-log-rectangles lw-log-count
                                      lw-log-rectangles-width lw-log-step-adequate
                                      lw-log-rectangles-interval lw-log-rectangles-width-bound)
                  :nonlinearp t)))

(assert-event (equal (lw-log-bounds 1 1/10) '(0 . 0)))
(assert-event (let ((bounds (lw-log-bounds 2 1/100)))
                (and (< (car bounds) 7/10) (< 69/100 (cdr bounds))
                     (<= (- (cdr bounds) (car bounds)) 1/100))))
