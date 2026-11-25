(in-package "ACL2")

(include-book "mellin-endpoint-budgets")
(include-book "mellin-cutoffs")

; A computed endpoint family for the actual improper Mellin evaluator.
; The endpoint family inherits the evaluator's proved arithmetic Cauchy
; convergence in sigma>2. Its Dirichlet normalization is still separate.

(local (in-theory
 (disable lw-log-bounds lw-exp-bounds lw-euler-bounds lw-mangoldt-bounds
          lw-smoothed-ramp-log-error lw-smoothed-ramp-unit-error
          lw-log-signal-ramp-count lw-log-signal-spatial-cap lw-signal-count
          lw-signal-exponential-precision lw-signal-exponential-cost
          lw-mellin-prime-endpoint lw-mellin-ramp-endpoint lw-mellin-common-endpoint
          lw-mellin-frozen-endpoint lw-mellin-endpoint-request lw-mellin-computed-bounded-endpoint
          lw-mellin-integral lw-mellin-integral-cutoff lw-mellin-bounded-integral
          lw-mellin-integral-depth lw-mellin-integral-precision
          lw-complexp lw-complex-add lw-complex-sub lw-complex-scale lw-complex-diskp lw-diskp
          lw-complex-disk-enlarge lw-disk-enlarge lw-complex-sub-add-first
          lw-complex-add-commutative lw-complex-add-left-commutes)))

(defthm lw-mellin-prime-endpoint-rational
 (implies
  (and (rationalp cap) (<= 0 cap) (rationalp start) (<= 0 start) (rationalp length) (<= 0 length)
       (rationalp sigma) (< 1 sigma) (rationalp height) (natp count) (natp total)
       (rationalp model-error) (< 0 model-error) (rationalp primitive-error) (< 0 primitive-error)
       (rationalp error) (< 0 error))
  (lw-complexp (lw-mellin-prime-endpoint cap start length sigma height count total model-error primitive-error error)))
 :hints (("Goal"
   :induct (lw-mellin-prime-endpoint cap start length sigma height count total model-error primitive-error error)
   :in-theory (enable (:induction lw-mellin-prime-endpoint) (:definition lw-mellin-prime-endpoint)
                      lw-complexp lw-complex-add lw-complex-sub lw-complex-scale))
  (and stable-under-simplificationp
   '(:use ((:instance lw-smoothed-ramp-log-error-adequate (index count) (error model-error))
           (:instance lw-log-bounds-interval (value count) (epsilon (lw-smoothed-ramp-log-error count total model-error)))
           (:instance lw-mangoldt-lower-coarse (index count) (epsilon primitive-error))
           (:instance lw-mellin-common-endpoint-rational (kind 0)
             (cutpoint (car (lw-log-bounds count (lw-smoothed-ramp-log-error count total model-error)))))
           (:instance lw-mellin-common-endpoint-rational (kind 3)
             (cutpoint (car (lw-log-bounds count (lw-smoothed-ramp-log-error count total model-error))))))
     :expand ((lw-mellin-prime-endpoint cap start length sigma height count total model-error primitive-error error))
     :in-theory (e/d (lw-mellin-ramp-endpoint lw-intervalp lw-complexp lw-complex-add lw-complex-sub lw-complex-scale)
       (lw-smoothed-ramp-log-error-adequate lw-log-bounds-interval lw-mangoldt-lower-coarse
        lw-mellin-common-endpoint-rational))
     :do-not-induct t))))

(defthm lw-mellin-frozen-endpoint-rational
 (implies
  (and (rationalp cap) (<= 0 cap) (rationalp start) (<= 0 start) (rationalp length) (<= 0 length)
       (rationalp sigma) (< 1 sigma) (rationalp height) (rationalp model-error) (< 0 model-error)
       (rationalp error) (< 0 error))
  (lw-complexp (lw-mellin-frozen-endpoint cap start length sigma height model-error error)))
 :hints (("Goal"
   :use ((:instance lw-signal-exponential-parameters (error model-error))
         (:instance lw-signal-count-natural (value (lw-log-signal-spatial-cap cap)))
         (:instance lw-euler-bounds-interval (epsilon (lw-signal-exponential-precision cap model-error)))
         (:instance lw-mellin-prime-endpoint-rational
          (count (lw-log-signal-ramp-count cap)) (total (lw-log-signal-ramp-count cap))
          (primitive-error (lw-signal-exponential-precision cap model-error)))
         (:instance lw-mellin-common-endpoint-rational (kind 1) (cutpoint 0))
         (:instance lw-mellin-common-endpoint-rational (kind 0) (cutpoint 0)))
   :in-theory (e/d (lw-mellin-frozen-endpoint lw-log-signal-ramp-count lw-intervalp
                   lw-complexp lw-complex-add lw-complex-sub lw-complex-scale)
     (lw-signal-exponential-parameters lw-euler-bounds-interval lw-mellin-prime-endpoint-rational
      lw-mellin-common-endpoint-rational))
   :nonlinearp nil :do-not-induct t)))

(defthm lw-mellin-computed-bounded-endpoint-rational
 (implies
  (and (rationalp cap) (<= 0 cap) (rationalp sigma) (< 1 sigma) (rationalp height)
       (rationalp error) (< 0 error))
  (lw-complexp (lw-mellin-computed-bounded-endpoint cap sigma height error)))
 :hints (("Goal"
   :use (lw-mellin-endpoint-request-valid
         (:instance lw-mellin-frozen-endpoint-rational (start 0) (length cap)
          (model-error (lw-mellin-endpoint-request cap error)) (error (lw-mellin-endpoint-request cap error))))
   :in-theory (e/d (lw-mellin-computed-bounded-endpoint)
     (lw-mellin-endpoint-request-valid lw-mellin-frozen-endpoint-rational))
   :do-not-induct t)))

(defun lw-mellin-computed-improper-endpoint (sigma height error)
 (lw-mellin-computed-bounded-endpoint (lw-mellin-integral-cutoff sigma 0 error) sigma height error))

(local (in-theory (disable lw-mellin-computed-improper-endpoint)))

(defthm lw-mellin-computed-improper-endpoint-rational
 (implies (and (rationalp sigma) (< 2 sigma) (rationalp height) (rationalp error) (< 0 error))
          (lw-complexp (lw-mellin-computed-improper-endpoint sigma height error)))
 :hints (("Goal"
   :use ((:instance lw-mellin-integral-cutoff-valid (index 0))
         (:instance lw-mellin-computed-bounded-endpoint-rational (cap (lw-mellin-integral-cutoff sigma 0 error))))
   :in-theory (e/d (lw-mellin-computed-improper-endpoint)
     (lw-mellin-integral-cutoff-valid lw-mellin-computed-bounded-endpoint-rational))
   :do-not-induct t)))

(defthm lw-mellin-computed-improper-endpoint-comparison
 (implies (and (rationalp sigma) (< 2 sigma) (rationalp height) (rationalp error) (< 0 error))
  (lw-complex-diskp (lw-complex-sub (lw-mellin-integral sigma height 0 error) (lw-mellin-computed-improper-endpoint sigma height error)) error))
 :hints (("Goal"
   :use ((:instance lw-mellin-integral-cutoff-valid (index 0))
         (:instance lw-mellin-endpoint-request-valid (cap (lw-mellin-integral-cutoff sigma 0 error)))
         (:instance lw-mellin-bounded-integral-cauchy
          (cap (lw-mellin-integral-cutoff sigma 0 error)) (index 0) (left-error (* 1/2 error)) (right-error (lw-mellin-endpoint-request (lw-mellin-integral-cutoff sigma 0 error) error)))
         (:instance lw-mellin-computed-bounded-endpoint-comparison (cap (lw-mellin-integral-cutoff sigma 0 error)))
         (:instance lw-mellin-integral-rational (index 0))
         (:instance lw-mellin-bounded-integral-rational (cap (lw-mellin-integral-cutoff sigma 0 error)) (index 0) (error (lw-mellin-endpoint-request (lw-mellin-integral-cutoff sigma 0 error) error)))
         lw-mellin-computed-improper-endpoint-rational
         (:instance lw-complex-difference-triangle
          (left (lw-mellin-integral sigma height 0 error)) (middle (lw-mellin-bounded-integral (lw-mellin-integral-cutoff sigma 0 error) sigma height 0 (lw-mellin-endpoint-request (lw-mellin-integral-cutoff sigma 0 error) error))) (right (lw-mellin-computed-improper-endpoint sigma height error))
          (radius (+ (* 1/2 error) (lw-mellin-endpoint-request (lw-mellin-integral-cutoff sigma 0 error) error))) (other-radius (* 1/16 error)))
         (:instance lw-complex-disk-enlarge
          (point (lw-complex-sub (lw-mellin-integral sigma height 0 error) (lw-mellin-computed-improper-endpoint sigma height error)))
          (radius (+ (* 1/2 error) (lw-mellin-endpoint-request (lw-mellin-integral-cutoff sigma 0 error) error) (* 1/16 error))) (cap error)))
   :in-theory
   (e/d (lw-mellin-integral lw-mellin-computed-improper-endpoint)
     (lw-mellin-integral-cutoff-valid lw-mellin-endpoint-request-valid lw-mellin-bounded-integral-cauchy
      lw-mellin-computed-bounded-endpoint-comparison lw-mellin-integral-rational
      lw-mellin-bounded-integral-rational lw-mellin-computed-improper-endpoint-rational
      lw-complex-difference-triangle))
   :nonlinearp nil :do-not-induct t)))

(defthm lw-mellin-computed-improper-endpoint-cauchy
 (implies
  (and (rationalp sigma) (< 2 sigma) (rationalp height)
       (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
  (lw-complex-diskp (lw-complex-sub (lw-mellin-computed-improper-endpoint sigma height left-error) (lw-mellin-computed-improper-endpoint sigma height right-error)) (* 6 (+ left-error right-error))))
 :hints (("Goal"
   :use ((:instance lw-mellin-computed-improper-endpoint-comparison (error left-error))
         (:instance lw-mellin-computed-improper-endpoint-comparison (error right-error))
         (:instance lw-mellin-computed-improper-endpoint-rational (error left-error))
         (:instance lw-mellin-computed-improper-endpoint-rational (error right-error))
         (:instance lw-mellin-integral-rational (index 0) (error left-error))
         (:instance lw-mellin-integral-rational (index 0) (error right-error))
         (:instance lw-mellin-integral-cauchy (index 0))
         (:instance lw-complex-difference-symmetric (left (lw-mellin-integral sigma height 0 left-error)) (right (lw-mellin-computed-improper-endpoint sigma height left-error)) (radius left-error))
         (:instance lw-complex-difference-triangle
          (left (lw-mellin-integral sigma height 0 left-error)) (middle (lw-mellin-integral sigma height 0 right-error)) (right (lw-mellin-computed-improper-endpoint sigma height right-error))
          (radius (* 5 (+ left-error right-error))) (other-radius right-error))
         (:instance lw-complex-difference-triangle
          (left (lw-mellin-computed-improper-endpoint sigma height left-error)) (middle (lw-mellin-integral sigma height 0 left-error)) (right (lw-mellin-computed-improper-endpoint sigma height right-error))
          (radius left-error) (other-radius (+ (* 5 (+ left-error right-error)) right-error)))
         (:instance lw-complex-disk-enlarge
          (point (lw-complex-sub
           (lw-mellin-computed-improper-endpoint sigma height left-error)
           (lw-mellin-computed-improper-endpoint sigma height right-error)))
          (radius (+ left-error (* 5 (+ left-error right-error)) right-error))
          (cap (* 6 (+ left-error right-error)))))
   :in-theory (disable lw-mellin-computed-improper-endpoint-comparison
                       lw-mellin-computed-improper-endpoint-rational lw-mellin-integral-rational
                       lw-mellin-integral-cauchy lw-complex-difference-triangle)
   :nonlinearp nil :do-not-induct t)))


