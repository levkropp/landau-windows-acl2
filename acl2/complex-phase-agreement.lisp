(in-package "ACL2")

(include-book "complex-exp-phase")

; A computed common precision identifies the existing phase sampler with
; the imaginary restriction of the complex Taylor evaluator.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-scale-add lw-complex-scale-product
                 lw-complex-exp-term lw-complex-exp-sum lw-complex-exp-value lw-complex-exp-cap
                 lw-complex-power lw-complex-l1 lw-exp-term lw-exp-sum lw-exp-index lw-exp-band
                 lw-exp-bounds lw-exp-neg-bounds lw-exp-start-index lw-exp-depth lw-exp-initial-width
                 lw-phase-rotation lw-phase-grid lw-phase-value lw-phase-steps
                 lw-complex-phase-cap lw-complex-phase-step-error lw-precision-fuel
                 lw-complex-disk-enlarge lw-disk-enlarge)))

(local (defthm lw-cpa-imaginary-complex
         (implies (rationalp value) (lw-complexp (cons 0 value)))
         :hints (("Goal" :in-theory (enable lw-complexp)))))
(local (defthm lw-cpa-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-cpa-left-distribute
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-cpa-square-nonnegative
         (implies (rationalp value) (<= 0 (* value value)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-cpa-product-nonnegative
         (implies (and (rationalp a) (<= 0 a) (rationalp b) (<= 0 b)) (<= 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defthm lw-complex-exp-phase-agreement
  (implies (and (rationalp value) (posp steps) (<= (abs value) steps)
                (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
           (lw-complex-diskp
             (lw-complex-sub
               (lw-complex-exp-value (cons 0 value) left-error)
               (lw-phase-value value right-error))
             (+
               (* (+ 1 (* 3/2 (lw-complex-phase-cap value))) (/ (* value value) steps))
               (* steps (+ (* 3 (lw-complex-phase-cap value)) 2) left-error)
               (* 1/2 right-error))))
  :hints (("Goal" :use (
    (:instance lw-complex-exp-phase-grid-error (error left-error))
    (:instance lw-phase-grid-value-error (error right-error))
    (:instance lw-complex-difference-symmetric
      (left (lw-phase-grid value steps))
      (right (lw-complex-exp-value (cons 0 value) left-error))
      (radius
        (+
          (* 3/2 (lw-complex-phase-cap value) (/ (* value value) steps))
          (* steps (+ (* 3 (lw-complex-phase-cap value)) 2) left-error))))
    (:instance lw-complex-difference-triangle
      (left (lw-complex-exp-value (cons 0 value) left-error))
      (middle (lw-phase-grid value steps))
      (right (lw-phase-value value right-error))
      (radius
        (+
          (* 3/2 (lw-complex-phase-cap value) (/ (* value value) steps))
          (* steps (+ (* 3 (lw-complex-phase-cap value)) 2) left-error)))
      (other-radius (+ (/ (* value value) steps) (* 1/2 right-error))))
    (:instance lw-complex-disk-enlarge
      (point
        (lw-complex-sub (lw-complex-exp-value (cons 0 value) left-error) (lw-phase-value value right-error)))
      (radius
        (+
          (+
            (* 3/2 (lw-complex-phase-cap value) (/ (* value value) steps))
            (* steps (+ (* 3 (lw-complex-phase-cap value)) 2) left-error))
          (+ (/ (* value value) steps) (* 1/2 right-error))))
      (cap
        (+
          (* (+ 1 (* 3/2 (lw-complex-phase-cap value))) (/ (* value value) steps))
          (* steps (+ (* 3 (lw-complex-phase-cap value)) 2) left-error)
          (* 1/2 right-error)))))
    :in-theory (disable lw-complex-exp-phase-grid-error lw-phase-grid-value-error lw-complex-difference-triangle)
    :nonlinearp t)))

(defun lw-complex-phase-comparison-steps (value error)
  (+ 1 (max (lw-precision-fuel (abs value) 1)
            (lw-precision-fuel (* 8 (+ 1 (lw-complex-phase-cap value)) value value) error))))

(defthm lw-complex-phase-comparison-steps-positive
  (posp (lw-complex-phase-comparison-steps value error))
  :hints (("Goal" :in-theory (enable lw-precision-fuel)))
  :rule-classes (:rewrite :type-prescription))

(defthm lw-complex-phase-comparison-steps-adequate
  (implies (and (rationalp value) (rationalp error) (< 0 error))
           (and (<= (abs value) (lw-complex-phase-comparison-steps value error))
                (<= (* 8 (+ 1 (lw-complex-phase-cap value)) value value)
                    (* (lw-complex-phase-comparison-steps value error) error))))
  :hints (("Goal" :use (lw-complex-phase-cap-valid
                        lw-cpa-square-nonnegative
                        (:instance lw-cpa-product-nonnegative
                          (a (+ 1 (lw-complex-phase-cap value))) (b (* value value)))
                        (:instance lw-precision-fuel-adequate (width (abs value)) (epsilon 1))
                        (:instance lw-precision-fuel-adequate
                          (width (* 8 (+ 1 (lw-complex-phase-cap value)) value value)) (epsilon error)))
                  :in-theory (disable lw-complex-phase-cap-valid lw-precision-fuel-adequate)
                  :nonlinearp t)))

(local (in-theory (disable lw-complex-phase-comparison-steps)))

(defun lw-complex-phase-comparison-amplifier (value error)
  (+ 1 (* (lw-complex-phase-comparison-steps value error)
          (+ 2 (* 3 (lw-complex-phase-cap value))))))

(defthm lw-complex-phase-comparison-amplifier-valid
  (implies (and (rationalp value) (rationalp error) (< 0 error))
           (and (rationalp (lw-complex-phase-comparison-amplifier value error))
                (<= 1 (lw-complex-phase-comparison-amplifier value error))))
  :hints (("Goal" :use (lw-complex-phase-cap-valid
                        (:instance lw-cpa-product-nonnegative
                          (a (lw-complex-phase-comparison-steps value error))
                          (b (+ 2 (* 3 (lw-complex-phase-cap value))))))
                  :in-theory (disable lw-complex-phase-cap-valid) :nonlinearp t)))

(local (in-theory (disable lw-complex-phase-comparison-amplifier)))

(defun lw-complex-phase-comparison-precision (value error)
  (/ error (* 4 (lw-complex-phase-comparison-amplifier value error))))

(defthm lw-complex-phase-comparison-precision-adequate
  (implies (and (rationalp value) (rationalp error) (< 0 error))
           (and (rationalp (lw-complex-phase-comparison-precision value error))
                (< 0 (lw-complex-phase-comparison-precision value error))
                (<= (* (lw-complex-phase-comparison-amplifier value error)
                       (lw-complex-phase-comparison-precision value error)) (* 1/4 error))))
  :hints (("Goal" :use (lw-complex-phase-comparison-amplifier-valid
                        (:instance lw-positive-division-bound
                          (numerator (* (lw-complex-phase-comparison-amplifier value error) error))
                          (divisor (* 4 (lw-complex-phase-comparison-amplifier value error))) (bound (* 1/4 error))))
                  :in-theory (disable lw-complex-phase-comparison-amplifier-valid)
                  :nonlinearp t)))

(local (in-theory (disable lw-complex-phase-comparison-precision)))


(defthm lw-complex-phase-comparison-radius-adequate
  (implies (and (rationalp value) (rationalp error) (< 0 error))
           (<= (+ (* (+ 1 (* 3/2 (lw-complex-phase-cap value)))
                     (/ (* value value) (lw-complex-phase-comparison-steps value error)))
                  (* (lw-complex-phase-comparison-steps value error)
                     (+ (* 3 (lw-complex-phase-cap value)) 2)
                     (lw-complex-phase-comparison-precision value error))
                  (* 1/2 (lw-complex-phase-comparison-precision value error)))
               error))
  :hints (("Goal" :use (lw-complex-phase-cap-valid
                        lw-complex-phase-comparison-steps-adequate
                        lw-complex-phase-comparison-precision-adequate
                        lw-cpa-square-nonnegative
                        (:instance lw-cpa-product-nonnegative
                          (a (+ 1 (* 1/2 (lw-complex-phase-cap value)))) (b (* value value)))
                        (:instance lw-positive-division-bound
                          (numerator (* (+ 1 (* 3/2 (lw-complex-phase-cap value))) value value))
                          (divisor (lw-complex-phase-comparison-steps value error)) (bound (* 1/4 error))))
                  :in-theory (e/d (lw-complex-phase-comparison-amplifier)
                                  (lw-complex-phase-cap-valid lw-complex-phase-comparison-steps-adequate
                                   lw-complex-phase-comparison-precision-adequate))
                  :nonlinearp t)))

(defthm lw-complex-exp-computed-phase-agreement
  (implies (and (rationalp value) (rationalp error) (< 0 error))
           (lw-complex-diskp
            (lw-complex-sub (lw-complex-exp-value (cons 0 value) (lw-complex-phase-comparison-precision value error))
                            (lw-phase-value value (lw-complex-phase-comparison-precision value error))) error))
  :hints (("Goal" :use (lw-complex-phase-comparison-steps-adequate
                        lw-complex-phase-comparison-precision-adequate
                        lw-complex-phase-comparison-radius-adequate
                        (:instance lw-complex-exp-phase-agreement
                          (steps (lw-complex-phase-comparison-steps value error))
                          (left-error (lw-complex-phase-comparison-precision value error))
                          (right-error (lw-complex-phase-comparison-precision value error)))
                        (:instance lw-complex-disk-enlarge
                          (point (lw-complex-sub
                                  (lw-complex-exp-value
                                   (cons 0 value) (lw-complex-phase-comparison-precision value error))
                                  (lw-phase-value value (lw-complex-phase-comparison-precision value error))))
                          (radius (+ (* (+ 1 (* 3/2 (lw-complex-phase-cap value)))
                                        (/ (* value value) (lw-complex-phase-comparison-steps value error)))
                                     (* (lw-complex-phase-comparison-steps value error)
                                        (+ (* 3 (lw-complex-phase-cap value)) 2)
                                        (lw-complex-phase-comparison-precision value error))
                                     (* 1/2 (lw-complex-phase-comparison-precision value error))))
                          (cap error)))
                  :in-theory (disable lw-complex-phase-comparison-steps-adequate
                                      lw-complex-phase-comparison-precision-adequate
                                      lw-complex-phase-comparison-radius-adequate lw-complex-exp-phase-agreement))))

; Independent exact checks: E_4(i/2) and two Cayley steps at t=1/2.
; Exercise both argument signs as well as the phase orientation.
(assert-event
 (and (equal (lw-complex-exp-sum (cons 0 1/2) 4) (cons 337/384 23/48))
      (equal (lw-phase-grid 1/2 2) (cons 3713/4225 2016/4225))
      (equal (lw-phase-grid -1/2 2) (cons 3713/4225 -2016/4225))))

