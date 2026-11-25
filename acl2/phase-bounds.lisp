(in-package "ACL2")

(include-book "complex-bounds")

(local (defthm lw-pb-multiply-left-commutes
         (equal (* left (* middle right)) (* middle (* left right)))
         :hints (("Goal" :use ((:instance associativity-of-* (x left) (y middle) (z right))
                              (:instance associativity-of-* (x middle) (y left) (z right))
                              (:instance commutativity-of-* (x left) (y middle)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-pb-times-negation
         (implies (and (rationalp left) (rationalp right))
                  (equal (* left (- right)) (- (* left right))))
         :hints (("Goal" :use ((:instance distributivity (x left) (y right) (z (- right))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-pb-zero-product (equal (* 0 value) 0)))
(local (defthm lw-pb-minus-one-product
         (implies (rationalp value) (equal (* -1 value) (- value)))))
(local (defthm lw-pb-add-cancel
         (implies (and (rationalp value) (rationalp rest))
                  (equal (+ value (- value) rest) rest))))
(local (defthm lw-pb-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal" :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient)))
                         :in-theory (disable associativity-of-* commutativity-of-*
                                             lw-pb-multiply-left-commutes)))))
(local (defthm lw-pb-sum-left-distribute
         (implies (and (rationalp left) (rationalp right) (rationalp factor))
                  (equal (* (+ left right) factor) (+ (* left factor) (* right factor))))
         :hints (("Goal" :use ((:instance distributivity (x factor) (y left) (z right)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-pb-square-nonnegative
         (implies (rationalp value) (<= 0 (* value value)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-pb-double
         (implies (rationalp value) (equal (+ value value) (* 2 value)))))
(local (defthm lw-pb-two-halves
         (implies (rationalp value) (equal (* 2 1/2 value) value))
         :hints (("Goal" :use ((:instance associativity-of-* (x 2) (y 1/2) (z value)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(defun lw-phase-denominator (value) (+ 4 (* value value)))
(defun lw-phase-rotation (value)
  (lw-complex-scale (/ (lw-phase-denominator value))
                    (cons (- 4 (* value value)) (* 4 value))))

(defthm lw-phase-denominator-positive
  (implies (rationalp value)
           (and (rationalp (lw-phase-denominator value)) (< 0 (lw-phase-denominator value))))
  :hints (("Goal" :nonlinearp t))
  :rule-classes (:rewrite :type-prescription))

(defthm lw-phase-rotation-rational
  (implies (rationalp value) (lw-complexp (lw-phase-rotation value))))

(local
 (defthm lw-pb-normalize-disk
   (implies (and (rationalp denominator) (< 0 denominator)
                 (lw-complex-diskp point (* denominator radius)) (rationalp radius))
            (lw-complex-diskp (lw-complex-scale (/ denominator) point) radius))
   :hints (("Goal" :use ((:instance lw-complex-scale-disk
                          (factor (/ denominator)) (radius (* denominator radius)))
                         (:instance inverse-of-* (x denominator)))
                   :in-theory (disable lw-complex-scale lw-complex-diskp lw-complex-scale-disk
                                       lw-complex-disk-enlarge lw-disk-enlarge inverse-of-*)
                   :nonlinearp t))
   :rule-classes nil))

(defthm lw-phase-rotation-unit
  (implies (rationalp value) (lw-complex-diskp (lw-phase-rotation value) 1))
  :hints (("Goal" :use ((:instance lw-pb-normalize-disk
                          (point (cons (- 4 (* value value)) (* 4 value)))
                          (denominator (lw-phase-denominator value)) (radius 1)))
                  :in-theory (disable lw-complex-scale lw-complex-scale-disk lw-complex-disk-enlarge lw-disk-enlarge)
                  :nonlinearp t)))

(local
 (defthm lw-pb-rotation-sub-one
   (implies (rationalp value)
            (equal (lw-complex-sub (lw-phase-rotation value) (cons 1 0))
                   (lw-complex-scale (/ (lw-phase-denominator value))
                                     (cons (- (* 2 value value)) (* 4 value)))))
   :hints (("Goal" :use ((:instance inverse-of-* (x (lw-phase-denominator value))))
                   :in-theory (disable inverse-of-*) :nonlinearp t))))

(defthm lw-phase-rotation-chord
  (implies (rationalp value)
           (lw-complex-diskp (lw-complex-sub (lw-phase-rotation value) (cons 1 0)) (abs value)))
  :hints (("Goal" :use ((:instance lw-pb-normalize-disk
                          (point (cons (- (* 2 value value)) (* 4 value)))
                          (denominator (lw-phase-denominator value)) (radius (abs value))))
                  :in-theory (disable lw-phase-rotation lw-complex-sub lw-complex-scale lw-complex-scale-disk
                                      lw-complex-disk-enlarge lw-disk-enlarge)
                  :cases ((<= 0 value)) :nonlinearp t)))

(local
 (defthm lw-pb-rotation-linear-defect
   (implies (rationalp value)
            (equal (lw-complex-sub (lw-phase-rotation value) (cons 1 value))
                   (lw-complex-scale (/ (lw-phase-denominator value))
                                     (cons (- (* 2 value value)) (- (* value value value))))))
   :hints (("Goal" :use ((:instance inverse-of-* (x (lw-phase-denominator value)))
                         (:instance lw-pb-inverse-factor (divisor (lw-phase-denominator value)) (coefficient value)))
                   :in-theory (disable inverse-of-* lw-pb-inverse-factor) :nonlinearp t))))

(local
 (defthm lw-pb-raw-linear-disk
   (implies (rationalp value)
            (lw-complex-diskp (cons (- (* 2 value value)) (- (* value value value)))
                              (* (lw-phase-denominator value) 1/2 value value)))
   :hints (("Goal" :use ((:instance lw-pb-square-nonnegative)
                         (:instance lw-pb-square-nonnegative (value (* value value)))
                         (:instance lw-pb-square-nonnegative (value (* value value value)))
                         (:instance lw-pb-square-nonnegative (value (* value value value value))))
                   :nonlinearp t))
   :rule-classes nil))

(defthm lw-phase-rotation-linear-bound
  (implies (rationalp value)
           (lw-complex-diskp (lw-complex-sub (lw-phase-rotation value) (cons 1 value)) (* 1/2 value value)))
  :hints (("Goal" :use (lw-pb-raw-linear-disk (:instance lw-pb-normalize-disk
                          (point (cons (- (* 2 value value)) (- (* value value value))))
                          (denominator (lw-phase-denominator value)) (radius (* 1/2 value value))))
                  :in-theory (disable lw-phase-rotation lw-complex-sub lw-complex-scale lw-complex-scale-disk lw-complex-diskp
                                      lw-complex-disk-enlarge lw-disk-enlarge)
                  :nonlinearp t)))

(defun lw-phase-linear-radius (value index)
  (* 1/2 (nfix index) (nfix index) value value))

(local
 (defthm lw-pb-power-linear-identity
   (implies (and (lw-complexp point) (rationalp value) (natp index))
            (equal (lw-complex-sub (lw-complex-power point index) (cons 1 (* index value)))
                   (lw-complex-add (lw-complex-power-remainder point index)
                                   (lw-complex-scale index (lw-complex-sub point (cons 1 value))))))
   :hints (("Goal" :use (lw-complex-power-remainder-identity lw-complex-power-rational)
                   :in-theory (disable lw-complex-power lw-complex-power-remainder
                                       lw-complex-power-remainder-identity lw-complex-power-rational)))
   :rule-classes nil))

(local
 (defthm lw-pb-power-linear-radius
   (implies (and (rationalp value) (natp index))
            (equal (+ (lw-quadratic-radius index (abs value)) (* index 1/2 value value))
                   (lw-phase-linear-radius value index)))
   :hints (("Goal" :cases ((<= 0 value))))
   :rule-classes nil))

(defthm lw-phase-power-linear-bound
  (implies (and (rationalp value) (natp index))
           (lw-complex-diskp
            (lw-complex-sub (lw-complex-power (lw-phase-rotation value) index) (cons 1 (* index value)))
            (lw-phase-linear-radius value index)))
  :hints (("Goal"
           :use (lw-pb-power-linear-radius lw-phase-rotation-chord lw-phase-rotation-linear-bound
                 (:instance lw-pb-power-linear-identity (point (lw-phase-rotation value)))
                 (:instance lw-complex-power-quadratic-bound (point (lw-phase-rotation value)) (error (abs value)))
                 (:instance lw-complex-scale-disk (factor index)
                   (point (lw-complex-sub (lw-phase-rotation value) (cons 1 value))) (radius (* 1/2 value value)))
                 (:instance lw-complex-add-disk
                   (left (lw-complex-power-remainder (lw-phase-rotation value) index))
                   (radius (lw-quadratic-radius index (abs value)))
                   (right (lw-complex-scale index (lw-complex-sub (lw-phase-rotation value) (cons 1 value))))
                   (other-radius (* index 1/2 value value))))
           :in-theory (disable lw-phase-rotation lw-phase-linear-radius lw-quadratic-radius lw-complex-power
                               lw-complex-power-remainder lw-complex-power-remainder-identity
                               lw-complex-power-quadratic-bound lw-complex-add lw-complex-sub lw-complex-scale
                               lw-complex-diskp lw-complex-scale-disk lw-complex-add-disk
                               lw-pb-rotation-sub-one lw-pb-rotation-linear-defect
                               lw-phase-rotation-chord lw-phase-rotation-linear-bound
                               lw-complex-disk-enlarge lw-disk-enlarge))))

(local
 (defthm lw-pb-linear-radius-scale
   (implies (and (rationalp value) (natp index))
            (equal (* 1/2 (* index value) (* index value)) (lw-phase-linear-radius value index)))
   :rule-classes nil))

(defthm lw-phase-block-bound
  (implies (and (rationalp value) (natp index))
           (lw-complex-diskp
            (lw-complex-sub (lw-complex-power (lw-phase-rotation value) index)
                            (lw-phase-rotation (* index value)))
            (* 2 (lw-phase-linear-radius value index))))
  :hints (("Goal"
           :use (lw-pb-linear-radius-scale lw-phase-power-linear-bound
                 (:instance lw-phase-rotation-linear-bound (value (* index value)))
                 (:instance lw-complex-difference-symmetric
                   (left (lw-phase-rotation (* index value))) (right (cons 1 (* index value)))
                   (radius (* 1/2 (* index value) (* index value))))
                 (:instance lw-complex-difference-triangle
                   (left (lw-complex-power (lw-phase-rotation value) index)) (middle (cons 1 (* index value)))
                   (right (lw-phase-rotation (* index value)))
                   (radius (lw-phase-linear-radius value index)) (other-radius (lw-phase-linear-radius value index))))
           :in-theory (disable lw-phase-rotation lw-phase-linear-radius lw-complex-diskp lw-complex-power
                               lw-complex-sub lw-complex-add lw-complex-scale lw-complex-difference-triangle
                               lw-phase-power-linear-bound lw-phase-rotation-linear-bound lw-pb-rotation-linear-defect
                               lw-complex-disk-enlarge lw-disk-enlarge))))

(defun lw-phase-grid (value steps)
  (lw-complex-power (lw-phase-rotation (/ value steps)) steps))

(defthm lw-phase-grid-rational
  (implies (and (rationalp value) (natp steps)) (lw-complexp (lw-phase-grid value steps)))
  :hints (("Goal" :in-theory (disable lw-complex-power lw-phase-rotation lw-complexp))))

(defthm lw-phase-grid-unit
  (implies (and (rationalp value) (natp steps)) (lw-complex-diskp (lw-phase-grid value steps) 1))
  :hints (("Goal" :in-theory (disable lw-complex-power lw-phase-rotation lw-complex-diskp))))

(local
 (defthm lw-pb-cancel-product
   (implies (and (rationalp left) (rationalp right) (rationalp factor) (< 0 factor)
                 (equal (* factor left) (* factor right)))
            (equal left right))
   :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local
 (defthm lw-pb-divide-refinement
   (implies (and (rationalp value) (posp steps) (posp factor))
            (equal (* factor (/ value (* steps factor))) (/ value steps)))
   :hints (("Goal"
            :use ((:instance lw-pb-inverse-factor (divisor steps) (coefficient value))
                  (:instance lw-pb-inverse-factor (divisor (* steps factor)) (coefficient value))
                  (:instance lw-pb-cancel-product (factor steps)
                    (left (* factor (/ value (* steps factor)))) (right (/ value steps))))
            :in-theory (disable lw-pb-inverse-factor) :nonlinearp t))
   :rule-classes nil))

(local
 (defthm lw-pb-square-quotient
   (implies (and (rationalp value) (posp steps))
            (equal (* steps (/ value steps) (/ value steps)) (/ (* value value) steps)))
   :hints (("Goal" :use ((:instance lw-pb-inverse-factor
                          (divisor steps) (coefficient (* value value (/ steps)))))
                   :in-theory (disable lw-pb-inverse-factor)))
   :rule-classes nil))

(local
 (defthm lw-pb-reciprocal-product
   (implies (and (rationalp left) (rationalp right) (< 0 left) (< 0 right))
            (equal (/ (* left right)) (* (/ left) (/ right))))
   :hints (("Goal" :use ((:instance inverse-of-* (x left))
                         (:instance inverse-of-* (x right))
                         (:instance inverse-of-* (x (* left right)))
                         (:instance lw-pb-cancel-product (factor (* left right))
                           (left (/ (* left right))) (right (* (/ left) (/ right)))))
                   :in-theory (disable inverse-of-*) :nonlinearp t))))

(local
 (defthm lw-pb-refinement-radius
   (implies (and (rationalp value) (posp steps) (posp factor))
            (equal (* steps 2 (lw-phase-linear-radius (/ value (* steps factor)) factor))
                   (/ (* value value) steps)))
   :hints (("Goal" :use (lw-pb-square-quotient)
                   :in-theory (enable lw-pb-reciprocal-product)))
   :rule-classes nil))

(defthm lw-phase-grid-refinement
  (implies (and (rationalp value) (posp steps) (posp factor))
           (lw-complex-diskp (lw-complex-sub (lw-phase-grid value steps) (lw-phase-grid value (* steps factor)))
                             (/ (* value value) steps)))
  :hints (("Goal"
           :use (lw-pb-divide-refinement lw-pb-refinement-radius
                 (:instance lw-phase-block-bound (value (/ value (* steps factor))) (index factor))
                 (:instance lw-complex-difference-symmetric
                   (left (lw-complex-power (lw-phase-rotation (/ value (* steps factor))) factor))
                   (right (lw-phase-rotation (/ value steps)))
                   (radius (* 2 (lw-phase-linear-radius (/ value (* steps factor)) factor))))
                 (:instance lw-complex-power-difference
                   (left (lw-phase-rotation (/ value steps)))
                   (right (lw-complex-power (lw-phase-rotation (/ value (* steps factor))) factor))
                   (index steps) (error (* 2 (lw-phase-linear-radius (/ value (* steps factor)) factor))))
                 (:instance lw-complex-power-power
                   (point (lw-phase-rotation (/ value (* steps factor)))) (inner factor) (outer steps)))
           :in-theory (disable lw-phase-rotation lw-complex-power lw-complex-sub lw-complex-diskp
                               lw-phase-linear-radius lw-phase-block-bound lw-complex-power-difference
                               lw-complex-power-power lw-complex-disk-enlarge lw-disk-enlarge)
           :nonlinearp t)))

(defthm lw-phase-grid-cauchy
  (implies (and (rationalp value) (posp left-steps) (posp right-steps))
           (lw-complex-diskp (lw-complex-sub (lw-phase-grid value left-steps) (lw-phase-grid value right-steps))
                             (+ (/ (* value value) left-steps) (/ (* value value) right-steps))))
  :hints (("Goal"
           :use ((:instance lw-phase-grid-refinement (steps left-steps) (factor right-steps))
                 (:instance lw-phase-grid-refinement (steps right-steps) (factor left-steps))
                 (:instance lw-complex-difference-symmetric
                   (left (lw-phase-grid value right-steps)) (right (lw-phase-grid value (* left-steps right-steps)))
                   (radius (/ (* value value) right-steps)))
                 (:instance lw-complex-difference-triangle
                   (left (lw-phase-grid value left-steps)) (middle (lw-phase-grid value (* left-steps right-steps)))
                   (right (lw-phase-grid value right-steps))
                   (radius (/ (* value value) left-steps)) (other-radius (/ (* value value) right-steps))))
           :in-theory (disable lw-phase-grid lw-complex-sub lw-complex-diskp lw-complexp
                               lw-phase-grid-refinement lw-complex-difference-triangle
                               lw-complex-disk-enlarge lw-disk-enlarge)
           :nonlinearp t)))

(defun lw-phase-steps (value error)
  (+ 1 (max (lw-precision-fuel (abs value) 1) (lw-precision-fuel (* 2 value value) error))))

(defun lw-phase-value (value error) (lw-phase-grid value (lw-phase-steps value error)))

(defthm lw-phase-steps-positive
  (posp (lw-phase-steps value error))
  :rule-classes (:rewrite :type-prescription))

(defthm lw-phase-steps-adequate
  (implies (and (rationalp value) (rationalp error) (< 0 error))
           (and (<= (abs value) (lw-phase-steps value error))
                (<= (* 2 value value) (* (lw-phase-steps value error) error))))
  :hints (("Goal" :use ((:instance lw-precision-fuel-adequate (width (abs value)) (epsilon 1))
                        (:instance lw-precision-fuel-adequate (width (* 2 value value)) (epsilon error)))
                  :in-theory (disable lw-precision-fuel lw-precision-fuel-adequate)
                  :nonlinearp t)))

(defthm lw-phase-value-unit
  (implies (rationalp value) (lw-complex-diskp (lw-phase-value value error) 1))
  :hints (("Goal" :in-theory (disable lw-phase-grid lw-phase-steps lw-complex-diskp))))

(defthm lw-phase-value-rational
  (implies (rationalp value) (lw-complexp (lw-phase-value value error)))
  :hints (("Goal" :in-theory (disable lw-phase-grid lw-phase-steps lw-complexp))))

(defthm lw-phase-value-cauchy
  (implies (and (rationalp value) (rationalp left-error) (< 0 left-error)
                (rationalp right-error) (< 0 right-error))
           (lw-complex-diskp (lw-complex-sub (lw-phase-value value left-error) (lw-phase-value value right-error))
                             (+ left-error right-error)))
  :hints (("Goal"
           :use ((:instance lw-phase-grid-cauchy
                   (left-steps (lw-phase-steps value left-error)) (right-steps (lw-phase-steps value right-error)))
                 (:instance lw-phase-steps-adequate (error left-error))
                 (:instance lw-phase-steps-adequate (error right-error))
                 (:instance lw-positive-division-bound (numerator (* value value))
                   (divisor (lw-phase-steps value left-error)) (bound (/ left-error 2)))
                 (:instance lw-positive-division-bound (numerator (* value value))
                   (divisor (lw-phase-steps value right-error)) (bound (/ right-error 2)))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-complex-sub (lw-phase-value value left-error) (lw-phase-value value right-error)))
                   (radius (+ (/ (* value value) (lw-phase-steps value left-error))
                              (/ (* value value) (lw-phase-steps value right-error))))
                   (cap (+ left-error right-error))))
           :in-theory (disable lw-phase-grid lw-phase-steps lw-complex-sub lw-complex-diskp
                               lw-phase-grid-cauchy lw-phase-steps-adequate lw-complex-disk-enlarge lw-disk-enlarge)
           :nonlinearp t)))

(assert-event
 (and (equal (lw-phase-rotation 0) (cons 1 0))
      (equal (lw-phase-rotation 2) (cons 0 1))
      (lw-complex-diskp (lw-phase-rotation -3/2) 1)))

(assert-event
 (and (equal (lw-phase-value 0 1/10) (cons 1 0))
      (lw-complex-diskp (lw-phase-value 1/2 1/4) 1)
      (lw-complex-diskp (lw-complex-sub (lw-phase-grid 1/2 3) (lw-phase-grid 1/2 5)) 2/15)))
