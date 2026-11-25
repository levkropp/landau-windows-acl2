(in-package "ACL2")

(include-book "complex-boundary-decay")

(include-book "mellin-endpoint-precision")

; The fixed finite family decays beyond all its logarithmic cutpoints.
; Compute the far endpoint and a node threshold for any requested error.

(local (in-theory
 (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
          lw-complex-reciprocal lw-complex-quotient lw-complex-diskp lw-diskp
          lw-log-bounds lw-exp-bounds lw-euler-bounds lw-mangoldt-bounds
          lw-exp-lipschitz-cap lw-complex-exp-value lw-complex-laplace-point
          lw-complex-exp-boundary lw-complex-exp-moment-boundary
          lw-complex-exp-clipped-primitive lw-complex-exp-clipped-moment-primitive
          lw-complex-exp-clipped-primitive-endpoint lw-complex-exp-clipped-moment-primitive-endpoint
          lw-complex-exp-laplace-boundary lw-complex-exp-laplace-moment-boundary
          lw-complex-exp-boundaries-at-zero lw-complex-exp-laplace-boundaries-at-zero
          lw-complex-log-ramp-independent-exp lw-complex-log-ramp-independent-endpoint
          lw-complex-log-ramp-independent-model lw-complex-log-ramp-independent-model-identity
          lw-complex-log-ramp-family lw-complex-dirichlet-prime-sum lw-complex-log-ramp-family-precision
          lw-complex-log-ramp-family-factorization
          lw-smoothed-ramp-log-error lw-smoothed-ramp-unit-error
          lw-log-signal-ramp-count lw-log-signal-spatial-cap lw-signal-count
          lw-signal-exponential-precision lw-signal-exponential-cost
          lw-complex-mul-commutative lw-complex-mul-left-commutes lw-complex-mul-subtract
          lw-complex-sub-add-first lw-complex-add-commutative lw-complex-add-left-commutes)))

(local (defthm lw-mfb-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-mfb-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-mfb-zero-times (equal (* 0 a) 0)))

(local (defthm lw-mfb-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-mfb-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-mfb-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-mfb-times-negative (a b) (b a)))
                 :in-theory (disable lw-mfb-times-negative)))))

(local (in-theory (disable lw-mellin-prime-endpoint-mass lw-mellin-endpoint-precision-factor
 lw-complex-boundary-decay-radius lw-complex-exp-boundaries-rational
 lw-complex-exp-laplace-boundary lw-complex-exp-laplace-moment-boundary)))

(local (defthm lw-mfb-zero-disk
 (lw-complex-diskp (cons 0 0) 0)
 :hints (("Goal" :in-theory (enable lw-complex-diskp lw-complexp lw-diskp)))))

(local (defthm lw-mfb-ramp-far-bound
 (implies
  (and (rationalp end) (<= 1 end) (rationalp rate) (< 2 rate) (rationalp height)
       (rationalp index) (< 1 index) (<= index end)
       (rationalp log-error) (< 0 log-error) (rationalp delta) (< 0 delta))
  (lw-complex-diskp (lw-mellin-ramp-boundary end rate height index log-error delta) (* (+ 1 (/ index)) (lw-complex-boundary-decay-radius end delta))))
 :hints (("Goal"
  :use ((:instance lw-log-bounds-lower-coarse (value index) (epsilon log-error))
        (:instance lw-log-bounds-interval (value index) (epsilon log-error))
        (:instance lw-complex-exp-laplace-boundaries-decay (rate (- rate 1)) (value end) (error delta))
        (:instance lw-complex-exp-laplace-boundaries-decay (value end) (error delta))
        (:instance lw-complex-scale-disk (point (lw-complex-exp-boundary (lw-complex-laplace-point (- rate 1) height) end delta)) (radius (lw-complex-boundary-decay-radius end delta)) (factor (/ index)))
        (:instance lw-complex-sub-disk
         (left (lw-complex-scale (/ index) (lw-complex-exp-boundary (lw-complex-laplace-point (- rate 1) height) end delta)))
         (right (lw-complex-exp-boundary (lw-complex-laplace-point rate height) end delta)) (radius (* (/ index) (lw-complex-boundary-decay-radius end delta))) (other-radius (lw-complex-boundary-decay-radius end delta))))
  :in-theory (e/d (lw-mellin-ramp-boundary lw-intervalp)
    (lw-log-bounds-lower-coarse lw-log-bounds-interval
     lw-complex-exp-laplace-boundaries-decay lw-complex-scale-disk lw-complex-sub-disk))
  :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-mfb-weighted-ramp-far-bound
 (implies
  (and (rationalp end) (<= 1 end) (rationalp rate) (< 2 rate) (rationalp height)
       (natp count) (< 1 count) (<= count end) (natp total)
       (rationalp model-error) (< 0 model-error) (rationalp primitive-error) (< 0 primitive-error)
       (rationalp delta) (< 0 delta))
  (lw-complex-diskp (lw-complex-scale (car (lw-mangoldt-bounds count primitive-error)) (lw-mellin-ramp-boundary end rate height count (lw-smoothed-ramp-log-error count total model-error) delta)) (* (car (lw-mangoldt-bounds count primitive-error)) (+ 1 (/ count)) (lw-complex-boundary-decay-radius end delta))))
 :hints (("Goal"
  :use ((:instance lw-smoothed-ramp-log-error-adequate (index count) (error model-error))
        (:instance lw-mangoldt-lower-coarse (index count) (epsilon primitive-error))
        (:instance lw-mfb-ramp-far-bound (index count) (log-error (lw-smoothed-ramp-log-error count total model-error)))
        (:instance lw-complex-scale-disk (point (lw-mellin-ramp-boundary end rate height count (lw-smoothed-ramp-log-error count total model-error) delta)) (factor (car (lw-mangoldt-bounds count primitive-error))) (radius (* (+ 1 (/ count)) (lw-complex-boundary-decay-radius end delta)))))
  :in-theory (disable lw-smoothed-ramp-log-error-adequate lw-mangoldt-lower-coarse lw-complex-scale-disk)
  :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(defthm lw-mellin-prime-boundary-far-bound
 (implies
  (and (rationalp end) (<= 1 end) (rationalp rate) (< 2 rate) (rationalp height)
       (natp count) (<= count end) (natp total)
       (rationalp model-error) (< 0 model-error) (rationalp primitive-error) (< 0 primitive-error)
       (rationalp delta) (< 0 delta))
  (lw-complex-diskp (lw-mellin-prime-boundary end rate height count total model-error primitive-error delta) (* (lw-mellin-prime-endpoint-mass count primitive-error) (lw-complex-boundary-decay-radius end delta))))
 :hints (("Goal"
  :induct (lw-mellin-prime-boundary end rate height count total model-error primitive-error delta)
  :in-theory (enable (:induction lw-mellin-prime-boundary) (:definition lw-mellin-prime-boundary)
                     (:definition lw-mellin-prime-endpoint-mass)))
  (and stable-under-simplificationp
   '(:use (lw-mfb-weighted-ramp-far-bound
           (:instance lw-complex-add-disk
            (left (lw-complex-scale (car (lw-mangoldt-bounds count primitive-error)) (lw-mellin-ramp-boundary end rate height count (lw-smoothed-ramp-log-error count total model-error) delta))) (right (lw-mellin-prime-boundary end rate height (- count 1) total model-error primitive-error delta))
            (radius (* (car (lw-mangoldt-bounds count primitive-error)) (+ 1 (/ count)) (lw-complex-boundary-decay-radius end delta)))
            (other-radius (* (lw-mellin-prime-endpoint-mass (- count 1) primitive-error) (lw-complex-boundary-decay-radius end delta)))))
     :in-theory (disable lw-mellin-prime-boundary lw-mellin-prime-endpoint-mass lw-complex-add-disk)
     :nonlinearp nil :do-not-induct t))))

(local (defthm lw-mfb-frozen-data
 (implies (and (rationalp cap) (<= 0 cap) (rationalp model-error) (< 0 model-error))
  (and (natp (lw-log-signal-ramp-count cap)) (rationalp (lw-signal-exponential-precision cap model-error)) (< 0 (lw-signal-exponential-precision cap model-error))
       (rationalp (car (lw-euler-bounds (lw-signal-exponential-precision cap model-error))))))
 :hints (("Goal"
  :use ((:instance lw-signal-count-natural (value (lw-log-signal-spatial-cap cap)))
        (:instance lw-signal-exponential-parameters (error model-error))
        (:instance lw-euler-bounds-interval (epsilon (lw-signal-exponential-precision cap model-error))))
  :in-theory (e/d (lw-log-signal-ramp-count lw-intervalp)
                 (lw-signal-exponential-parameters lw-euler-bounds-interval))
  :do-not-induct t))
 :rule-classes nil))

(defthm lw-mellin-finite-boundary-far-bound
 (implies
  (and (rationalp cap) (<= 0 cap) (rationalp end) (<= 1 end) (<= (lw-log-signal-ramp-count cap) end)
       (rationalp rate) (< 2 rate) (rationalp height)
       (rationalp model-error) (< 0 model-error) (rationalp delta) (< 0 delta))
  (lw-complex-diskp (lw-mellin-finite-boundary cap end rate height model-error delta) (* (lw-mellin-endpoint-precision-factor cap model-error) (lw-complex-boundary-decay-radius end delta))))
 :hints (("Goal"
  :use (lw-mfb-frozen-data lw-mellin-endpoint-precision-factor-valid
        (:instance lw-mellin-prime-boundary-far-bound (count (lw-log-signal-ramp-count cap)) (total (lw-log-signal-ramp-count cap)) (primitive-error (lw-signal-exponential-precision cap model-error)))
        (:instance lw-complex-exp-laplace-boundaries-decay (rate (- rate 1)) (value end) (error delta))
        (:instance lw-complex-sub-disk (left (lw-mellin-prime-boundary end rate height (lw-log-signal-ramp-count cap) (lw-log-signal-ramp-count cap) model-error (lw-signal-exponential-precision cap model-error) delta)) (right (lw-complex-exp-moment-boundary (lw-complex-laplace-point (- rate 1) height) end delta)) (radius (* (lw-mellin-prime-endpoint-mass (lw-log-signal-ramp-count cap) (lw-signal-exponential-precision cap model-error)) (lw-complex-boundary-decay-radius end delta))) (other-radius (lw-complex-boundary-decay-radius end delta)))
        (:instance lw-complex-scale-disk (point (lw-complex-exp-boundary (lw-complex-laplace-point (- rate 1) height) end delta)) (radius (lw-complex-boundary-decay-radius end delta)) (factor (+ 1 (car (lw-euler-bounds (lw-signal-exponential-precision cap model-error))))))
        (:instance lw-complex-add-disk
         (left (lw-complex-sub (lw-mellin-prime-boundary end rate height (lw-log-signal-ramp-count cap) (lw-log-signal-ramp-count cap) model-error (lw-signal-exponential-precision cap model-error) delta) (lw-complex-exp-moment-boundary (lw-complex-laplace-point (- rate 1) height) end delta))) (right (lw-complex-scale (+ 1 (car (lw-euler-bounds (lw-signal-exponential-precision cap model-error)))) (lw-complex-exp-boundary (lw-complex-laplace-point (- rate 1) height) end delta)))
         (radius (+ (* (lw-mellin-prime-endpoint-mass (lw-log-signal-ramp-count cap) (lw-signal-exponential-precision cap model-error)) (lw-complex-boundary-decay-radius end delta)) (lw-complex-boundary-decay-radius end delta))) (other-radius (* (abs (+ 1 (car (lw-euler-bounds (lw-signal-exponential-precision cap model-error))))) (lw-complex-boundary-decay-radius end delta))))
        (:instance lw-complex-disk-enlarge (point (lw-mellin-finite-boundary cap end rate height model-error delta))
         (radius (+ (* (lw-mellin-prime-endpoint-mass (lw-log-signal-ramp-count cap) (lw-signal-exponential-precision cap model-error)) (lw-complex-boundary-decay-radius end delta)) (lw-complex-boundary-decay-radius end delta) (* (abs (+ 1 (car (lw-euler-bounds (lw-signal-exponential-precision cap model-error))))) (lw-complex-boundary-decay-radius end delta))))
         (cap (* (lw-mellin-endpoint-precision-factor cap model-error) (lw-complex-boundary-decay-radius end delta)))))
  :in-theory (e/d (lw-mellin-finite-boundary lw-mellin-endpoint-precision-factor)
    (lw-mellin-endpoint-precision-factor-valid lw-mellin-prime-boundary-far-bound
     lw-complex-exp-laplace-boundaries-decay lw-complex-sub-disk lw-complex-scale-disk lw-complex-add-disk
     lw-complex-disk-enlarge))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-mellin-prime-boundary-rational
 (implies
  (and (rationalp end) (<= 0 end) (rationalp rate) (< 1 rate) (rationalp height)
       (natp count) (natp total) (rationalp model-error) (< 0 model-error)
       (rationalp primitive-error) (< 0 primitive-error) (rationalp delta) (< 0 delta))
  (lw-complexp (lw-mellin-prime-boundary end rate height count total model-error primitive-error delta)))
 :hints (("Goal"
  :induct (lw-mellin-prime-boundary end rate height count total model-error primitive-error delta)
  :in-theory (enable (:induction lw-mellin-prime-boundary) (:definition lw-mellin-prime-boundary)
                     lw-complexp lw-complex-add lw-complex-scale))
  (and stable-under-simplificationp
   '(:use ((:instance lw-smoothed-ramp-log-error-adequate (index count) (error model-error))
           (:instance lw-log-bounds-interval (value count)
            (epsilon (lw-smoothed-ramp-log-error count total model-error)))
           (:instance lw-mangoldt-lower-coarse (index count) (epsilon primitive-error))
           (:instance lw-complex-exp-boundaries-rational
            (point (lw-complex-laplace-point (- rate 1) height))
            (value (max end (car (lw-log-bounds count (lw-smoothed-ramp-log-error count total model-error))))) (error delta))
           (:instance lw-complex-exp-boundaries-rational
            (point (lw-complex-laplace-point rate height))
            (value (max end (car (lw-log-bounds count (lw-smoothed-ramp-log-error count total model-error))))) (error delta)))
     :expand ((lw-mellin-prime-boundary end rate height count total model-error primitive-error delta))
     :in-theory (e/d (lw-mellin-ramp-boundary lw-complex-laplace-point lw-intervalp
                      lw-complexp lw-complex-add lw-complex-sub lw-complex-scale)
       (lw-smoothed-ramp-log-error-adequate lw-log-bounds-interval lw-mangoldt-lower-coarse
        lw-complex-exp-boundaries-rational))
     :do-not-induct t))))

(defthm lw-mellin-finite-boundary-rational
 (implies
  (and (rationalp cap) (<= 0 cap) (rationalp end) (<= 0 end)
       (rationalp rate) (< 1 rate) (rationalp height)
       (rationalp model-error) (< 0 model-error) (rationalp delta) (< 0 delta))
  (lw-complexp (lw-mellin-finite-boundary cap end rate height model-error delta)))
 :hints (("Goal"
  :use (lw-mfb-frozen-data
        (:instance lw-mellin-prime-boundary-rational (count (lw-log-signal-ramp-count cap)) (total (lw-log-signal-ramp-count cap)) (primitive-error (lw-signal-exponential-precision cap model-error)))
        (:instance lw-complex-exp-boundaries-rational
         (point (lw-complex-laplace-point (- rate 1) height)) (value end) (error delta)))
  :in-theory (e/d (lw-mellin-finite-boundary lw-complex-laplace-point
                   lw-complexp lw-complex-add lw-complex-sub lw-complex-scale)
    (lw-mellin-prime-boundary-rational lw-complex-exp-boundaries-rational))
  :do-not-induct t)))

(local (in-theory (disable lw-precision-fuel)))

(local (defthm lw-mfb-fuel-natural
 (natp (lw-precision-fuel width error))
 :hints (("Goal" :in-theory (enable lw-precision-fuel)))))

(local (defthm lw-mfb-multiply-order
 (implies (and (rationalp a) (rationalp b) (<= a b) (rationalp factor) (<= 0 factor))
  (<= (* a factor) (* b factor)))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-mfb-nonnegative-product
 (implies (and (rationalp a) (<= 0 a) (rationalp b) (<= 0 b)) (<= 0 (* a b)))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defun lw-mellin-far-boundary-end (cap start model-error error)
 (+ 1 start (lw-log-signal-ramp-count cap) (lw-precision-fuel (* 16 (lw-mellin-endpoint-precision-factor cap model-error)) error)))

(local (in-theory (disable lw-mellin-far-boundary-end)))

(local (defthm lw-mfb-end-scalar
 (implies
  (and (natp count) (natp fuel) (rationalp start) (<= 0 start)
       (rationalp mass) (<= 1 mass) (rationalp error) (< 0 error)
       (<= (* 16 mass) (* (+ 1 fuel) error)))
  (let ((end (+ 1 start count fuel)))
   (and (rationalp end) (<= 1 end) (<= start end) (<= count end)
        (<= (* 8 mass (/ end)) (* 1/2 error)))))
 :hints (("Goal"
  :use ((:instance lw-mfb-multiply-order
         (a (+ 1 fuel)) (b (+ 1 start count fuel)) (factor error))
        (:instance lw-positive-division-bound
         (numerator (* 8 mass)) (divisor (+ 1 start count fuel)) (bound (* 1/2 error))))
  :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(defthm lw-mellin-far-boundary-end-valid
 (implies
  (and (rationalp cap) (<= 0 cap) (rationalp start) (<= 0 start)
       (rationalp model-error) (< 0 model-error) (rationalp error) (< 0 error))
  (and (rationalp (lw-mellin-far-boundary-end cap start model-error error)) (<= 1 (lw-mellin-far-boundary-end cap start model-error error)) (<= start (lw-mellin-far-boundary-end cap start model-error error)) (<= (lw-log-signal-ramp-count cap) (lw-mellin-far-boundary-end cap start model-error error))
       (<= (* 8 (lw-mellin-endpoint-precision-factor cap model-error) (/ (lw-mellin-far-boundary-end cap start model-error error))) (* 1/2 error))))
 :hints (("Goal"
  :use (lw-mfb-frozen-data lw-mellin-endpoint-precision-factor-valid
        (:instance lw-precision-fuel-adequate (width (* 16 (lw-mellin-endpoint-precision-factor cap model-error))) (epsilon error))
        (:instance lw-mfb-end-scalar
         (count (lw-log-signal-ramp-count cap)) (mass (lw-mellin-endpoint-precision-factor cap model-error)) (fuel (lw-precision-fuel (* 16 (lw-mellin-endpoint-precision-factor cap model-error)) error))))
  :in-theory (e/d (lw-mellin-far-boundary-end)
    (lw-mellin-endpoint-precision-factor-valid lw-precision-fuel-adequate))
  :nonlinearp nil :do-not-induct t)))

(defun lw-mellin-far-boundary-precision (cap end model-error error)
 (/ error (* 4 (lw-mellin-endpoint-precision-factor cap model-error) (+ 1 end))))

(local (in-theory (disable lw-mellin-far-boundary-precision)))

(local (defthm lw-mfb-precision-scalar
 (implies
  (and (rationalp mass) (<= 1 mass) (rationalp end) (<= 1 end) (rationalp error) (< 0 error))
  (let ((delta (/ error (* 4 mass (+ 1 end)))))
   (and (rationalp delta) (< 0 delta)
        (<= (* 2 mass (+ 1 end) delta) (* 1/2 error)))))
 :hints (("Goal"
  :use ((:instance lw-positive-division-bound
         (numerator (* 2 mass (+ 1 end) error)) (divisor (* 4 mass (+ 1 end))) (bound (* 1/2 error))))
  :nonlinearp t :do-not-induct t))
 :rule-classes nil))

(defthm lw-mellin-far-boundary-precision-valid
 (implies
  (and (rationalp cap) (<= 0 cap) (rationalp end) (<= 1 end)
       (rationalp model-error) (< 0 model-error) (rationalp error) (< 0 error))
  (and (rationalp (lw-mellin-far-boundary-precision cap end model-error error)) (< 0 (lw-mellin-far-boundary-precision cap end model-error error)) (<= (* 2 (lw-mellin-endpoint-precision-factor cap model-error) (+ 1 end) (lw-mellin-far-boundary-precision cap end model-error error)) (* 1/2 error))))
 :hints (("Goal"
  :use (lw-mellin-endpoint-precision-factor-valid
        (:instance lw-mfb-precision-scalar (mass (lw-mellin-endpoint-precision-factor cap model-error))))
  :in-theory (e/d (lw-mellin-far-boundary-precision) (lw-mellin-endpoint-precision-factor-valid))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-mellin-computed-far-boundary-small
 (implies
  (and (rationalp cap) (<= 0 cap) (rationalp start) (<= 0 start)
       (rationalp rate) (< 2 rate) (rationalp height)
       (rationalp model-error) (< 0 model-error) (rationalp error) (< 0 error)
       (rationalp delta) (< 0 delta) (<= delta (lw-mellin-far-boundary-precision cap (lw-mellin-far-boundary-end cap start model-error error) model-error error)))
  (lw-complex-diskp (lw-mellin-finite-boundary cap (lw-mellin-far-boundary-end cap start model-error error) rate height model-error delta) error))
 :hints (("Goal"
  :use (lw-mellin-far-boundary-end-valid lw-mellin-endpoint-precision-factor-valid
        (:instance lw-mellin-far-boundary-precision-valid (end (lw-mellin-far-boundary-end cap start model-error error)))
        (:instance lw-mellin-finite-boundary-far-bound (end (lw-mellin-far-boundary-end cap start model-error error)))
        (:instance lw-mfb-nonnegative-product (a (lw-mellin-endpoint-precision-factor cap model-error)) (b (+ 1 (lw-mellin-far-boundary-end cap start model-error error))))
        (:instance lw-mfb-multiply-order (a delta) (b (lw-mellin-far-boundary-precision cap (lw-mellin-far-boundary-end cap start model-error error) model-error error)) (factor (* 2 (lw-mellin-endpoint-precision-factor cap model-error) (+ 1 (lw-mellin-far-boundary-end cap start model-error error)))))
        (:instance lw-complex-disk-enlarge (point (lw-mellin-finite-boundary cap (lw-mellin-far-boundary-end cap start model-error error) rate height model-error delta))
         (radius (* (lw-mellin-endpoint-precision-factor cap model-error) (lw-complex-boundary-decay-radius (lw-mellin-far-boundary-end cap start model-error error) delta))) (cap error)))
  :in-theory (e/d (lw-complex-boundary-decay-radius)
    (lw-mellin-far-boundary-end-valid lw-mellin-endpoint-precision-factor-valid
     lw-mellin-far-boundary-precision-valid lw-mellin-finite-boundary-far-bound
     lw-complex-disk-enlarge))
  :nonlinearp nil :do-not-induct t)))
