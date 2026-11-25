(in-package "ACL2")

(include-book "complex-exp-negative")
(include-book "phase-bounds")

; Compare the rational Cayley rotation sampler with complex Taylor sums.
; The exact unit bound of each rotation prevents exponential error growth.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-scale-add lw-complex-scale-product
                 lw-complex-exp-term lw-complex-exp-sum lw-complex-exp-value lw-complex-exp-cap
                 lw-complex-power lw-complex-l1 lw-exp-term lw-exp-sum lw-exp-index lw-exp-band
                 lw-exp-bounds lw-exp-neg-bounds lw-exp-start-index lw-exp-depth lw-exp-initial-width
                 lw-phase-rotation lw-phase-grid lw-phase-value lw-phase-steps
                 lw-complex-disk-enlarge lw-disk-enlarge)))

(local (defthm lw-cep-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-cep-left-distribute
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-cep-times-negative
         (implies (and (rationalp a) (rationalp b)) (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-cep-negative-times
         (implies (and (rationalp a) (rationalp b)) (equal (* (- a) b) (- (* a b))))))
(local (defthm lw-cep-zero-times (equal (* 0 a) 0)))
(local (defthm lw-cep-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))
(local (defthm lw-cep-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))
(local (defthm lw-cep-square-nonnegative
         (implies (rationalp value) (<= 0 (* value value)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-cep-product-nonnegative
         (implies (and (rationalp a) (<= 0 a) (rationalp b) (<= 0 b))
                  (<= 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-cep-imaginary-complex
         (implies (rationalp value) (lw-complexp (cons 0 value)))
         :hints (("Goal" :in-theory (enable lw-complexp)))))
(local (defthm lw-cep-linear-complex
         (implies (rationalp value) (lw-complexp (cons 1 value)))
         :hints (("Goal" :in-theory (enable lw-complexp)))))
(local (defthm lw-cep-imaginary-add
         (implies (and (rationalp a) (rationalp b))
                  (equal (lw-complex-add (cons 0 a) (cons 0 b)) (cons 0 (+ a b))))
         :hints (("Goal" :in-theory (enable lw-complex-add)))))

(defun lw-complex-phase-cap (value)
  (+ 1 (cdr (lw-exp-bounds (abs value) 1))))

(defthm lw-complex-phase-cap-valid
  (implies (rationalp value)
           (and (rationalp (lw-complex-phase-cap value)) (<= 2 (lw-complex-phase-cap value))))
  :hints (("Goal" :use ((:instance lw-exp-bounds-valid (value (abs value)) (epsilon 1)))
                  :in-theory (e/d (lw-intervalp)
                                  (lw-exp-bounds-valid lw-exp-bounds-overlap lw-exp-bounds-monotone-overlap)))))

(defthm lw-complex-exp-imaginary-cap
  (implies (and (rationalp value) (rationalp bound) (<= (abs value) (abs bound)))
           (<= (lw-complex-exp-cap (cons 0 value)) (lw-complex-phase-cap bound)))
  :hints (("Goal" :use ((:instance lw-exp-bounds-monotone-overlap
                          (left (abs value)) (right (abs bound)) (left-error 1) (right-error 1))
                        (:instance lw-exp-bounds-width (value (abs value)) (epsilon 1)))
                  :in-theory (e/d (lw-complex-exp-cap lw-complex-l1)
                                  (lw-exp-bounds-monotone-overlap lw-exp-bounds-width)))))

(local (in-theory (disable lw-complex-phase-cap)))

(local (defthm lw-cep-imaginary-disk
         (implies (rationalp value) (lw-complex-diskp (cons 0 value) (abs value)))
         :hints (("Goal" :in-theory (enable lw-complex-diskp lw-complexp lw-diskp)
                         :cases ((<= 0 value)) :nonlinearp t))))
(local (defthm lw-cep-first-prefix
         (implies (rationalp value)
                  (equal (lw-complex-exp-sum (cons 0 value) 1) (cons 1 value)))
         :hints (("Goal" :in-theory (enable lw-complex-exp-sum lw-complex-exp-term
                                           lw-complex-add lw-complex-mul lw-complex-scale)))))
(local (defthm lw-cep-second-real-term
         (implies (rationalp value) (equal (* 2 (lw-exp-term (abs value) 2)) (* value value)))
         :hints (("Goal" :in-theory (enable lw-exp-term) :cases ((<= 0 value))))))

(defthm lw-complex-exp-rotation-error
  (implies (and (rationalp value) (<= (abs value) 1) (rationalp error) (< 0 error))
           (lw-complex-diskp
            (lw-complex-sub (lw-phase-rotation value) (lw-complex-exp-value (cons 0 value) error))
            (+ (* 3/2 value value) error)))
  :hints (("Goal" :use (lw-phase-rotation-linear-bound lw-cep-imaginary-disk lw-cep-second-real-term
                        (:instance lw-complex-exp-prefix-error (point (cons 0 value)) (radius (abs value)) (small 1))
                        (:instance lw-complex-difference-triangle
                          (left (lw-phase-rotation value)) (middle (cons 1 value))
                          (right (lw-complex-exp-value (cons 0 value) error))
                          (radius (* 1/2 value value)) (other-radius (+ (* value value) error)))
                        (:instance lw-complex-disk-enlarge
                          (point (lw-complex-sub (lw-phase-rotation value) (lw-complex-exp-value (cons 0 value) error)))
                          (radius (+ (* 1/2 value value) (* value value) error))
                          (cap (+ (* 3/2 value value) error))))
                  :in-theory (disable lw-phase-rotation-linear-bound lw-complex-exp-prefix-error
                                      lw-complex-difference-triangle)
                  :nonlinearp t)))


(defthm lw-complex-exp-phase-step
  (implies (and (rationalp step) (<= (abs step) 1) (rationalp value) (rationalp bound)
                (<= (abs step) (abs bound)) (<= (abs value) (abs bound))
                (rationalp error) (< 0 error))
           (lw-complex-diskp
             (lw-complex-sub
               (lw-complex-mul (lw-phase-rotation step) (lw-complex-exp-value (cons 0 value) error))
               (lw-complex-exp-value (cons 0 (+ step value)) error))
             (+
               (* 3/2 (lw-complex-phase-cap bound) step step)
               (* (+ (* 3 (lw-complex-phase-cap bound)) 2) error))))
  :hints (("Goal" :use (
    (:instance lw-complex-phase-cap-valid (value bound))
    (:instance lw-complex-exp-imaginary-cap (value step))
    lw-complex-exp-imaginary-cap
    (:instance lw-complex-exp-rotation-error (value step))
    (:instance lw-complex-disk-enlarge
      (point (lw-complex-exp-value (cons 0 value) error))
      (radius (lw-complex-exp-cap (cons 0 value)))
      (cap (lw-complex-phase-cap bound)))
    (:instance lw-complex-mul-difference-bound
      (a (lw-phase-rotation step))
      (b (lw-complex-exp-value (cons 0 value) error))
      (c (lw-complex-exp-value (cons 0 step) error))
      (d (lw-complex-exp-value (cons 0 value) error))
      (left-cap (lw-complex-exp-cap (cons 0 step)))
      (right-cap (lw-complex-phase-cap bound))
      (left-error (+ (* 3/2 step step) error))
      (right-error 0))
    (:instance lw-complex-exp-value-multiplication
      (left (cons 0 step))
      (right (cons 0 value))
      (left-error error)
      (right-error error)
      (sum-error error))
    (:instance lw-complex-difference-triangle
      (left (lw-complex-mul (lw-phase-rotation step) (lw-complex-exp-value (cons 0 value) error)))
      (middle
        (lw-complex-mul
          (lw-complex-exp-value (cons 0 step) error)
          (lw-complex-exp-value (cons 0 value) error)))
      (right (lw-complex-exp-value (cons 0 (+ step value)) error))
      (radius (* (lw-complex-phase-cap bound) (+ (* 3/2 step step) error)))
      (other-radius
        (+
          (* (lw-complex-exp-cap (cons 0 value)) error)
          (* (lw-complex-exp-cap (cons 0 step)) error)
          (* 2 error))))
    (:instance lw-complex-disk-enlarge
      (point
        (lw-complex-sub
          (lw-complex-mul (lw-phase-rotation step) (lw-complex-exp-value (cons 0 value) error))
          (lw-complex-exp-value (cons 0 (+ step value)) error)))
      (radius
        (+
          (* (lw-complex-phase-cap bound) (+ (* 3/2 step step) error))
          (+
            (* (lw-complex-exp-cap (cons 0 value)) error)
            (* (lw-complex-exp-cap (cons 0 step)) error)
            (* 2 error))))
      (cap
        (+ (* 3/2 (lw-complex-phase-cap bound) step step) (* (+ (* 3 (lw-complex-phase-cap bound)) 2) error)))))
    :in-theory (disable lw-complex-exp-imaginary-cap lw-complex-exp-rotation-error
                        lw-complex-mul-difference-bound lw-complex-exp-value-multiplication
                        lw-complex-difference-triangle lw-complex-phase-cap-valid)
    :nonlinearp t)))


(defthm lw-complex-unit-evolution-step
  (implies (and (lw-complex-diskp rotation 1) (lw-complexp previous)
                (lw-complexp reference) (lw-complexp next)
                (lw-complex-diskp (lw-complex-sub previous reference) previous-error)
                (lw-complex-diskp (lw-complex-sub (lw-complex-mul rotation reference) next) step-error))
           (lw-complex-diskp (lw-complex-sub (lw-complex-mul rotation previous) next)
                             (+ previous-error step-error)))
  :hints (("Goal" :use (
    (:instance lw-complex-mul-disk (left rotation) (right (lw-complex-sub previous reference))
      (radius 1) (other-radius previous-error))
    (:instance lw-complex-mul-subtract (a rotation) (b previous) (c reference))
    (:instance lw-complex-difference-triangle
      (left (lw-complex-mul rotation previous)) (middle (lw-complex-mul rotation reference))
      (right next) (radius previous-error) (other-radius step-error)))
    :in-theory (disable lw-complex-mul-disk lw-complex-mul-subtract lw-complex-difference-triangle
                        lw-complex-mul-commutative lw-complex-mul-left-commutes))))

(defun lw-complex-phase-step-error (step bound error)
  (+ (* 3/2 (lw-complex-phase-cap bound) step step)
     (* (+ (* 3 (lw-complex-phase-cap bound)) 2) error)))

(defthm lw-complex-phase-step-error-valid
  (implies (and (rationalp step) (rationalp bound) (rationalp error) (< 0 error))
           (and (rationalp (lw-complex-phase-step-error step bound error))
                (< 0 (lw-complex-phase-step-error step bound error))))
  :hints (("Goal" :use ((:instance lw-complex-phase-cap-valid (value bound))
                        (:instance lw-cep-square-nonnegative (value step))
                        (:instance lw-cep-product-nonnegative
                          (a (* step step)) (b (lw-complex-phase-cap bound)))
                        (:instance lw-cep-product-nonnegative
                          (a error) (b (lw-complex-phase-cap bound))))
                  :in-theory (disable lw-complex-phase-cap-valid) :nonlinearp t)))

(local (in-theory (disable lw-complex-phase-step-error)))

(local (defthm lw-cep-absolute-multiple
         (implies (and (rationalp value) (rationalp factor) (<= 0 factor))
                  (equal (abs (* factor value)) (* factor (abs value))))
         :hints (("Goal" :cases ((<= 0 value)) :nonlinearp t))))
(local (defthm lw-cep-range-data
         (implies (and (rationalp step) (rationalp bound) (posp index)
                       (<= (* index (abs step)) (abs bound)))
                  (and (<= (* (- index 1) (abs step)) (abs bound))
                       (<= (abs (* (- index 1) step)) (abs bound))))
         :hints (("Goal" :use ((:instance lw-cep-absolute-multiple (value step) (factor (- index 1))))
                         :nonlinearp t))
         :rule-classes nil))
(local (defthm lw-cep-power-step
         (implies (posp index)
                  (equal (lw-complex-power point index)
                         (lw-complex-mul point (lw-complex-power point (- index 1)))))
         :hints (("Goal" :in-theory (enable lw-complex-power)))
         :rule-classes nil))


(local (defthm lw-cep-power-zero
         (implies (zp index) (equal (lw-complex-power point index) (cons 1 0)))
         :hints (("Goal" :in-theory (enable lw-complex-power)))))
(local (defthm lw-cep-step-error-bound
         (implies (and (rationalp step) (<= (abs step) 1) (rationalp value) (rationalp bound)
                       (<= (abs step) (abs bound)) (<= (abs value) (abs bound))
                       (rationalp error) (< 0 error))
                  (lw-complex-diskp
                   (lw-complex-sub (lw-complex-mul (lw-phase-rotation step)
                                                  (lw-complex-exp-value (cons 0 value) error))
                                   (lw-complex-exp-value (cons 0 (+ step value)) error))
                   (lw-complex-phase-step-error step bound error)))
         :hints (("Goal" :use (lw-complex-exp-phase-step)
                         :in-theory (e/d (lw-complex-phase-step-error)
                                         (lw-complex-exp-phase-step))))
         :rule-classes nil))

(local (in-theory (disable abs)))

(local (defthm lw-cep-evolution-step
         (implies (and (rationalp step) (<= (abs step) 1) (rationalp bound)
                       (<= (abs step) (abs bound)) (posp index)
                       (<= (* index (abs step)) (abs bound)) (rationalp error) (< 0 error)
                       (lw-complex-diskp
                        (lw-complex-sub (lw-complex-power (lw-phase-rotation step) (- index 1))
                                        (lw-complex-exp-value (cons 0 (* (- index 1) step)) error))
                        (* (- index 1) (lw-complex-phase-step-error step bound error))))
                  (lw-complex-diskp
                   (lw-complex-sub (lw-complex-power (lw-phase-rotation step) index)
                                   (lw-complex-exp-value (cons 0 (* index step)) error))
                   (* index (lw-complex-phase-step-error step bound error))))
         :hints (("Goal" :use (lw-cep-range-data
                               (:instance lw-cep-power-step (point (lw-phase-rotation step)))
                               (:instance lw-cep-step-error-bound (value (* (- index 1) step)))
                               (:instance lw-complex-unit-evolution-step
                                 (rotation (lw-phase-rotation step))
                                 (previous (lw-complex-power (lw-phase-rotation step) (- index 1)))
                                 (reference (lw-complex-exp-value (cons 0 (* (- index 1) step)) error))
                                 (next (lw-complex-exp-value (cons 0 (* index step)) error))
                                 (previous-error (* (- index 1) (lw-complex-phase-step-error step bound error)))
                                 (step-error (lw-complex-phase-step-error step bound error)))
                               (:instance lw-complex-disk-enlarge
                                 (point (lw-complex-sub (lw-complex-power (lw-phase-rotation step) index)
                                                       (lw-complex-exp-value (cons 0 (* index step)) error)))
                                 (radius (+ (* (- index 1) (lw-complex-phase-step-error step bound error))
                                            (lw-complex-phase-step-error step bound error)))
                                 (cap (* index (lw-complex-phase-step-error step bound error)))))
                         :in-theory (disable lw-complex-unit-evolution-step lw-cep-power-zero)
                         :nonlinearp t))
         :rule-classes nil))

(defthm lw-complex-exp-phase-evolution
  (implies (and (rationalp step) (<= (abs step) 1) (rationalp bound)
                (<= (abs step) (abs bound)) (natp index)
                (<= (* index (abs step)) (abs bound)) (rationalp error) (< 0 error))
           (lw-complex-diskp
            (lw-complex-sub (lw-complex-power (lw-phase-rotation step) index)
                            (lw-complex-exp-value (cons 0 (* index step)) error))
            (* index (lw-complex-phase-step-error step bound error))))
  :hints (("Goal" :induct (lw-complex-power (lw-phase-rotation step) index)
                  :in-theory (enable (:induction lw-complex-power)))
          ("Subgoal *1/2" :use (lw-cep-range-data lw-cep-evolution-step))))


(local (defthm lw-cep-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal" :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                              (:instance inverse-of-* (x divisor)))
                         :in-theory (disable associativity-of-* commutativity-of-* lw-cep-left-commutes)))))
(local (defthm lw-cep-grid-range
         (implies (and (rationalp value) (posp steps) (<= (abs value) steps))
                  (and (<= (abs (/ value steps)) 1)
                       (<= (abs (/ value steps)) (abs value))
                       (equal (* steps (abs (/ value steps))) (abs value))))
         :hints (("Goal" :use ((:instance lw-cep-absolute-multiple (factor (/ steps)))
                               (:instance lw-reciprocal-positive (value steps))
                               (:instance lw-positive-division-bound
                                 (numerator (abs value)) (divisor steps) (bound 1))
                               (:instance lw-positive-division-bound
                                 (numerator (abs value)) (divisor steps) (bound (abs value))))
                         :in-theory (enable abs) :nonlinearp t))
         :rule-classes nil))

(defthm lw-complex-exp-phase-grid-error
  (implies (and (rationalp value) (posp steps) (<= (abs value) steps)
                (rationalp error) (< 0 error))
           (lw-complex-diskp
            (lw-complex-sub (lw-phase-grid value steps)
                            (lw-complex-exp-value (cons 0 value) error))
            (+ (* 3/2 (lw-complex-phase-cap value) (/ (* value value) steps))
               (* steps (+ (* 3 (lw-complex-phase-cap value)) 2) error))))
  :hints (("Goal" :use (lw-cep-grid-range
                        (:instance lw-complex-exp-phase-evolution
                          (step (/ value steps)) (bound value) (index steps)))
                  :in-theory (e/d (lw-phase-grid lw-complex-phase-step-error)
                                  (lw-complex-exp-phase-evolution))
                  :nonlinearp t)))

(defthm lw-phase-grid-value-error
  (implies (and (rationalp value) (posp steps) (rationalp error) (< 0 error))
           (lw-complex-diskp (lw-complex-sub (lw-phase-grid value steps) (lw-phase-value value error))
                             (+ (/ (* value value) steps) (* 1/2 error))))
  :hints (("Goal" :use (lw-phase-steps-adequate
                        (:instance lw-phase-grid-cauchy (left-steps steps) (right-steps (lw-phase-steps value error)))
                        (:instance lw-positive-division-bound
                          (numerator (* value value)) (divisor (lw-phase-steps value error)) (bound (* 1/2 error)))
                        (:instance lw-complex-disk-enlarge
                          (point (lw-complex-sub (lw-phase-grid value steps) (lw-phase-value value error)))
                          (radius (+ (/ (* value value) steps) (/ (* value value) (lw-phase-steps value error))))
                          (cap (+ (/ (* value value) steps) (* 1/2 error)))))
                  :in-theory (e/d (lw-phase-value)
                                  (lw-phase-steps-adequate lw-phase-grid-cauchy))
                  :nonlinearp t)))

