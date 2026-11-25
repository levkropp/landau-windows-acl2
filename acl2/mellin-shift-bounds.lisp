(in-package "ACL2")

(include-book "mellin-exponential-sample")

; Magnitude caps depend on a whole checked shift disk, so a single base
; precision can be frozen for every point and every polynomial coefficient.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-l1 lw-complex-exp-cap lw-complex-exp-value
                 lw-exp-bounds lw-exp-sum lw-exp-term lw-exp-index lw-exp-band
                 lw-kernel-weight-scale lw-mellin-signal-cap lw-mellin-exponential-error-factor
                 lw-log-signal-bounds lw-mellin-sample lw-mellin-signal lw-mellin-phase lw-mellin-weight
                 lw-complex-disk-enlarge lw-disk-enlarge)))

(local (defthm lw-msb-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-msb-left-distribute
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-msb-times-negative
         (implies (and (rationalp a) (rationalp b)) (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-msb-negative-times
         (implies (and (rationalp a) (rationalp b)) (equal (* (- a) b) (- (* a b))))))
(local (defthm lw-msb-double-negative
         (implies (rationalp value) (equal (- (- value)) value))))
(local (defthm lw-msb-zero-times (equal (* 0 a) 0)))
(local (defthm lw-msb-abs-product
         (implies (and (rationalp a) (rationalp b)) (equal (abs (* a b)) (* (abs a) (abs b))))
         :hints (("Goal" :cases ((<= 0 a) (<= 0 b)) :nonlinearp t))))
(local (defthm lw-msb-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b) (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defun lw-complex-exp-radius-cap (radius)
  (+ 1 (cdr (lw-exp-bounds radius 1))))

(defthm lw-complex-exp-radius-cap-valid
  (implies (and (rationalp radius) (<= 0 radius))
           (and (rationalp (lw-complex-exp-radius-cap radius))
                (<= 2 (lw-complex-exp-radius-cap radius))))
  :hints (("Goal" :use ((:instance lw-exp-bounds-valid (value radius) (epsilon 1)))
                  :in-theory (e/d (lw-intervalp)
                                  (lw-exp-bounds-valid lw-exp-bounds-overlap lw-exp-bounds-monotone-overlap)))))

(defthm lw-complex-exp-radius-cap-bound
  (implies (and (lw-complexp point) (rationalp radius) (<= (lw-complex-l1 point) radius))
           (<= (lw-complex-exp-cap point) (lw-complex-exp-radius-cap radius)))
  :hints (("Goal" :use (lw-complex-l1-bound
                        (:instance lw-exp-bounds-monotone-overlap
                          (left (lw-complex-l1 point)) (right radius) (left-error 1) (right-error 1))
                        (:instance lw-exp-bounds-width (value (lw-complex-l1 point)) (epsilon 1)))
                  :in-theory (e/d (lw-complex-exp-cap)
                                  (lw-complex-l1-bound lw-exp-bounds-monotone-overlap lw-exp-bounds-width)))))

(local (in-theory (disable lw-complex-exp-radius-cap)))

(local (defthm lw-msb-disk-l1
         (implies (lw-complex-diskp point radius) (<= (lw-complex-l1 point) (* 2 radius)))
         :hints (("Goal" :use (lw-complex-disk-coordinates)
                         :in-theory (e/d (lw-complex-l1) (lw-complex-disk-coordinates))))
         :rule-classes nil))
(local (defthm lw-msb-l1-scale
         (implies (and (rationalp factor) (lw-complexp point))
                  (equal (lw-complex-l1 (lw-complex-scale factor point))
                         (* (abs factor) (lw-complex-l1 point))))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-scale lw-complex-l1)))))

(defthm lw-complex-exp-scaled-disk-cap
  (implies (and (rationalp factor) (<= 0 factor) (lw-complex-diskp point radius))
           (<= (lw-complex-exp-cap (lw-complex-scale factor point))
               (lw-complex-exp-radius-cap (* 2 factor radius))))
  :hints (("Goal" :use (lw-msb-disk-l1
                        (:instance lw-msb-multiply-order
                          (a (lw-complex-l1 point)) (b (* 2 radius)))
                        (:instance lw-complex-exp-radius-cap-bound
                          (point (lw-complex-scale factor point)) (radius (* 2 factor radius))))
                  :in-theory (disable lw-complex-exp-radius-cap-bound)
                  :nonlinearp t)))

(defun lw-mellin-exponent (value sigma height)
  (cons (- (* sigma value)) (- (* height value))))

(defthm lw-mellin-exponent-rational
  (implies (and (rationalp value) (rationalp sigma) (rationalp height))
           (lw-complexp (lw-mellin-exponent value sigma height)))
  :hints (("Goal" :in-theory (enable lw-complexp))))

(defthm lw-mellin-exponent-shift
  (implies (and (rationalp value) (rationalp sigma) (rationalp height) (lw-complexp shift))
           (equal (lw-complex-add (lw-mellin-exponent value sigma height) (lw-complex-scale value shift))
                  (lw-mellin-exponent value (- sigma (car shift)) (- height (cdr shift)))))
  :hints (("Goal" :in-theory (enable lw-complexp lw-complex-add lw-complex-scale))))

(assert-event
 (equal (lw-complex-add (lw-mellin-exponent 2 3 5) (lw-complex-scale 2 (cons 1 -1)))
        (lw-mellin-exponent 2 2 6)))


(local (in-theory (disable lw-mellin-exponent)))

(defthm lw-mellin-exponential-value-cap
  (implies (and (rationalp value) (<= 0 value) (rationalp sigma) (<= 0 sigma)
                (rationalp height) (rationalp error) (< 0 error))
           (lw-complex-diskp
            (lw-complex-exp-value (lw-mellin-exponent value sigma height) error) (+ 1 error)))
  :hints (("Goal" :use ((:instance lw-complex-exp-damped-cap
                          (value (* sigma value)) (angle (- (* height value)))))
                  :in-theory (e/d (lw-mellin-exponent) (lw-complex-exp-damped-cap))
                  :nonlinearp t)))

(defun lw-mellin-shift-error-factor (value sigma height index step radius)
  (let ((mass (lw-kernel-weight-scale value index step))
        (signal-cap (lw-mellin-signal-cap value))
        (factor (lw-mellin-exponential-error-factor value index step))
        (shift-cap (lw-complex-exp-radius-cap (* 2 value radius)))
        (base-cap (lw-complex-exp-cap (lw-mellin-exponent value sigma height))))
    (+ 1 (* 2 factor (+ 1 shift-cap))
       (* signal-cap mass (+ shift-cap base-cap 2)) (* 4 mass))))

(local (defthm lw-msb-product-nonnegative
         (implies (and (rationalp a) (<= 0 a) (rationalp b) (<= 0 b)) (<= 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defthm lw-mellin-shift-error-factor-valid
  (implies (and (rationalp value) (<= 0 value) (rationalp sigma) (rationalp height)
                (rationalp step) (<= 0 step) (rationalp radius) (<= 0 radius))
           (and (rationalp (lw-mellin-shift-error-factor value sigma height index step radius))
                (<= 1 (lw-mellin-shift-error-factor value sigma height index step radius))))
  :hints (("Goal" :use (lw-kernel-weight-scale-nonnegative lw-mellin-signal-cap-valid
                        lw-mellin-exponential-error-factor-valid
                        (:instance lw-msb-product-nonnegative (a value) (b radius))
                        (:instance lw-complex-exp-radius-cap-valid (radius (* 2 value radius)))
                        (:instance lw-complex-exp-cap-valid (point (lw-mellin-exponent value sigma height)))
                        (:instance lw-msb-product-nonnegative
                          (a (lw-mellin-signal-cap value)) (b (lw-kernel-weight-scale value index step)))
                        (:instance lw-msb-product-nonnegative
                          (a (* (lw-mellin-signal-cap value) (lw-kernel-weight-scale value index step)))
                          (b (+ (lw-complex-exp-radius-cap (* 2 value radius))
                                (lw-complex-exp-cap (lw-mellin-exponent value sigma height)) 2)))
                        (:instance lw-msb-product-nonnegative
                          (a (lw-mellin-exponential-error-factor value index step))
                          (b (+ 1 (lw-complex-exp-radius-cap (* 2 value radius))))))
                  :in-theory (disable lw-kernel-weight-scale-nonnegative lw-mellin-signal-cap-valid
                                      lw-mellin-exponential-error-factor-valid lw-complex-exp-radius-cap-valid
                                      lw-complex-exp-cap-valid)
                  :nonlinearp t)))

(local (in-theory (disable lw-mellin-shift-error-factor)))

(defun lw-mellin-shift-precision (value sigma height index step radius error)
  (min 1 (/ error (+ 1 (lw-mellin-shift-error-factor value sigma height index step radius)))))

(defthm lw-mellin-shift-precision-adequate
  (implies (and (rationalp value) (<= 0 value) (rationalp sigma) (rationalp height)
                (rationalp step) (<= 0 step) (rationalp radius) (<= 0 radius)
                (rationalp error) (< 0 error))
           (and (rationalp (lw-mellin-shift-precision value sigma height index step radius error))
                (< 0 (lw-mellin-shift-precision value sigma height index step radius error))
                (<= (lw-mellin-shift-precision value sigma height index step radius error) 1)
                (<= (* (lw-mellin-shift-error-factor value sigma height index step radius)
                       (lw-mellin-shift-precision value sigma height index step radius error)) error)))
  :hints (("Goal" :use (lw-mellin-shift-error-factor-valid
                        (:instance lw-positive-division-bound
                          (numerator (* (lw-mellin-shift-error-factor value sigma height index step radius) error))
                          (divisor (+ 1 (lw-mellin-shift-error-factor value sigma height index step radius))) (bound error)))
                  :in-theory (disable lw-mellin-shift-error-factor-valid) :nonlinearp t)))


(defun lw-mellin-sample-cap (value index step)
  (* (lw-mellin-signal-cap value) (lw-kernel-weight-scale value index step)))

(defthm lw-mellin-sample-cap-valid
  (implies (and (rationalp value) (<= 0 value) (rationalp step) (<= 0 step))
           (and (rationalp (lw-mellin-sample-cap value index step))
                (<= 0 (lw-mellin-sample-cap value index step))))
  :hints (("Goal" :use (lw-mellin-signal-cap-valid lw-kernel-weight-scale-nonnegative
                        (:instance lw-msb-product-nonnegative
                          (a (lw-mellin-signal-cap value)) (b (lw-kernel-weight-scale value index step))))
                  :in-theory (disable lw-mellin-signal-cap-valid lw-kernel-weight-scale-nonnegative))))

(local (in-theory (disable lw-mellin-sample-cap lw-mellin-sample-kernel-form
                           lw-mellin-negative-error lw-mellin-phase-error lw-damped-phase-sample)))

(defthm lw-mellin-sample-uniform-cap
  (implies (and (rationalp value) (<= 0 value) (rationalp sigma) (<= 0 sigma)
                (rationalp height) (rationalp step) (<= 0 step) (rationalp error) (< 0 error))
           (lw-complex-diskp (lw-mellin-sample value sigma height index step error)
                             (lw-mellin-sample-cap value index step)))
  :hints (("Goal" :use (
    lw-mellin-signal-bounded lw-kernel-weight-scale-nonnegative lw-mellin-sample-kernel-form
    (:instance lw-msb-product-nonnegative (a sigma) (b value))
    (:instance lw-damped-phase-sample-unit (value (* sigma value)) (angle (- (* height value)))
      (negative-error (lw-mellin-negative-error value index step error))
      (phase-error (lw-mellin-phase-error value sigma index step error)))
    (:instance lw-complex-scale-disk
      (factor (* (lw-mellin-signal value sigma index step error) (lw-kernel-weight-scale value index step)))
      (point (lw-damped-phase-sample
              (* sigma value) (- (* height value))
              (lw-mellin-negative-error value index step error)
              (lw-mellin-phase-error value sigma index step error))) (radius 1))
    (:instance lw-msb-abs-product (a (lw-mellin-signal value sigma index step error))
      (b (lw-kernel-weight-scale value index step)))
    (:instance lw-msb-multiply-order
      (a (abs (lw-mellin-signal value sigma index step error))) (b (lw-mellin-signal-cap value))
      (factor (lw-kernel-weight-scale value index step)))
    (:instance lw-complex-disk-enlarge
      (point (lw-mellin-sample value sigma height index step error))
      (radius (* (abs (lw-mellin-signal value sigma index step error)) (lw-kernel-weight-scale value index step)))
      (cap (lw-mellin-sample-cap value index step))))
    :in-theory (e/d (lw-mellin-sample-cap)
                    (lw-mellin-signal-bounded lw-kernel-weight-scale-nonnegative lw-complex-scale-disk
                     lw-msb-abs-product))
    :nonlinearp t)))

(defthm lw-mellin-sample-l1-cap
  (implies (and (rationalp value) (<= 0 value) (rationalp sigma) (<= 0 sigma)
                (rationalp height) (rationalp step) (<= 0 step) (rationalp error) (< 0 error))
           (<= (lw-complex-l1 (lw-mellin-sample value sigma height index step error))
               (* 2 (lw-mellin-sample-cap value index step))))
  :hints (("Goal" :use (lw-mellin-sample-uniform-cap
                        (:instance lw-msb-disk-l1
                          (point (lw-mellin-sample value sigma height index step error))
                          (radius (lw-mellin-sample-cap value index step))))
                  :in-theory (disable lw-mellin-sample-uniform-cap))))

