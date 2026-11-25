(in-package "ACL2")

(include-book "complex-kernel-agreement")
(include-book "exp-quadratic-decay")

; Keep the size of the actual damping factor when comparing the native
; complex exponential with its rational reciprocal-times-phase sample.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-scale-add lw-complex-scale-product
                 lw-complex-exp-term lw-complex-exp-sum lw-complex-exp-value lw-complex-exp-cap
                 lw-complex-power lw-complex-l1 lw-exp-term lw-exp-sum lw-exp-index lw-exp-band
                 lw-exp-bounds lw-exp-neg-bounds lw-exp-neg-bounds-overlap
                 lw-exp-start-index lw-exp-depth lw-exp-initial-width
                 lw-phase-rotation lw-phase-grid lw-phase-value lw-phase-steps
                 lw-complex-phase-cap lw-complex-phase-comparison-steps
                 lw-complex-phase-comparison-amplifier lw-complex-phase-comparison-precision
                 lw-complex-exp-negative-precision lw-complex-damped-phase-budget
                 lw-complex-norm-square lw-disk-gap-error
                 lw-complex-damped-phase-value lw-complex-disk-enlarge lw-disk-enlarge)))

(local (defthm lw-dcap-triple
 (implies (rationalp value) (equal (+ value value value) (* 3 value)))))

(local (defthm lw-dcap-reconstruct
 (implies (and (lw-complexp point) (lw-complexp sample))
  (equal (lw-complex-add (lw-complex-sub point sample) sample) point))
 :hints (("Goal" :in-theory (enable lw-complexp lw-complex-add lw-complex-sub)))))

(defthm lw-damped-phase-sample-damping-cap
 (implies (and (rationalp value) (<= 0 value) (rationalp angle))
  (lw-complex-diskp (lw-damped-phase-sample value angle negative-error phase-error)
                   (car (lw-exp-neg-bounds value negative-error))))
 :hints (("Goal"
  :use ((:instance lw-exp-neg-bounds-valid (epsilon negative-error))
        (:instance lw-phase-value-unit (value angle) (error phase-error))
        (:instance lw-complex-scale-disk
         (point (lw-phase-value angle phase-error)) (radius 1)
         (factor (car (lw-exp-neg-bounds value negative-error)))))
  :in-theory (e/d (lw-damped-phase-sample lw-intervalp)
                  (lw-exp-neg-bounds-valid lw-complex-scale-disk))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-exp-damping-cap
 (implies (and (rationalp value) (<= 0 value) (rationalp angle)
               (rationalp negative-error) (< 0 negative-error)
               (rationalp phase-error) (< 0 phase-error)
               (rationalp complex-error) (< 0 complex-error))
  (lw-complex-diskp (lw-complex-exp-value (cons (- value) angle) complex-error)
   (+ (car (lw-exp-neg-bounds value negative-error))
      negative-error phase-error complex-error)))
 :hints (("Goal"
  :use (lw-complex-exp-kernel-agreement lw-damped-phase-sample-damping-cap
        (:instance lw-complex-difference-symmetric
         (left (lw-damped-phase-sample value angle negative-error phase-error))
         (right (lw-complex-exp-value (cons (- value) angle) complex-error))
         (radius (+ negative-error phase-error complex-error)))
        (:instance lw-complex-add-disk
         (left (lw-complex-sub
          (lw-complex-exp-value (cons (- value) angle) complex-error)
          (lw-damped-phase-sample value angle negative-error phase-error)))
         (right (lw-damped-phase-sample value angle negative-error phase-error))
         (radius (+ negative-error phase-error complex-error))
         (other-radius (car (lw-exp-neg-bounds value negative-error)))))
  :in-theory (e/d (lw-complexp)
   (lw-complex-exp-kernel-agreement lw-damped-phase-sample-damping-cap lw-complex-add-disk))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-exp-quadratic-damping-cap
 (implies (and (rationalp value) (< 0 value) (rationalp angle)
               (rationalp error) (< 0 error))
  (lw-complex-diskp (lw-complex-exp-value (cons (- value) angle) error)
   (+ (* 2 (/ value) (/ value)) (* 3 error))))
 :hints (("Goal"
  :use ((:instance lw-complex-exp-damping-cap
         (negative-error error) (phase-error error) (complex-error error))
        (:instance lw-exp-neg-bounds-quadratic-decay (epsilon error))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-exp-value (cons (- value) angle) error))
         (radius (+ (car (lw-exp-neg-bounds value error)) (* 3 error)))
         (cap (+ (* 2 (/ value) (/ value)) (* 3 error)))))
  :in-theory (disable lw-complex-exp-damping-cap lw-exp-neg-bounds-quadratic-decay)
  :nonlinearp nil :do-not-induct t)))

