(in-package "ACL2")

(include-book "complex-exp-boundaries")

(include-book "complex-log-ramp-family")

(include-book "signal-exponential-decomposition")

; Retain the finite upper boundary explicitly when relating the clipped
; Mellin primitives to the normalized Dirichlet family. The construction
; cap controls frozen coefficients; the interval endpoint is independent.

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

(local (defthm lw-mdb-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-mdb-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-mdb-zero-times (equal (* 0 a) 0)))

(local (defthm lw-mdb-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-mdb-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))
(local (defthm lw-mdb-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-mdb-times-negative (a b) (b a)))
                 :in-theory (disable lw-mdb-times-negative)))))

(local (defthm lw-mdb-log-data
 (implies (and (rationalp index) (< 1 index) (rationalp log-error) (< 0 log-error))
  (and (rationalp (car (lw-log-bounds index log-error)))
       (<= 0 (car (lw-log-bounds index log-error)))))
 :hints (("Goal"
   :use ((:instance lw-log-bounds-interval (value index) (epsilon log-error))
         (:instance lw-log-bounds-lower-coarse (value index) (epsilon log-error)))
   :in-theory (e/d (lw-intervalp) (lw-log-bounds-interval lw-log-bounds-lower-coarse))))
 :rule-classes nil))

(defun lw-mellin-ramp-primitive (end rate height index log-error delta)
 (let ((cutpoint (car (lw-log-bounds index log-error))))
  (lw-complex-sub
   (lw-complex-scale (/ index)
    (lw-complex-exp-clipped-primitive (lw-complex-laplace-point (- rate 1) height) 0 end cutpoint delta))
   (lw-complex-exp-clipped-primitive (lw-complex-laplace-point rate height) 0 end cutpoint delta))))

(defun lw-mellin-ramp-boundary (end rate height index log-error delta)
 (let ((node (max end (car (lw-log-bounds index log-error)))))
  (lw-complex-sub
   (lw-complex-scale (/ index) (lw-complex-exp-boundary (lw-complex-laplace-point (- rate 1) height) node delta))
   (lw-complex-exp-boundary (lw-complex-laplace-point rate height) node delta))))

(local (in-theory (disable lw-mellin-ramp-primitive lw-mellin-ramp-boundary)))

(local (defthm lw-mdb-ramp-boundary-add
 (equal
  (lw-complex-add
   (lw-complex-sub (lw-complex-scale factor (lw-complex-sub a u)) (lw-complex-sub b v))
   (lw-complex-sub (lw-complex-scale factor u) v))
  (lw-complex-sub (lw-complex-scale factor a) b))
 :hints (("Goal" :in-theory (enable lw-complex-add lw-complex-sub lw-complex-scale)))))

(defthm lw-mellin-ramp-primitive-boundary
 (implies
  (and (rationalp end) (<= 0 end) (rationalp rate) (< 1 rate) (rationalp height)
       (rationalp index) (< 1 index) (rationalp log-error) (< 0 log-error)
       (rationalp delta) (< 0 delta))
  (equal
   (lw-complex-add (lw-mellin-ramp-primitive end rate height index log-error delta)
                   (lw-mellin-ramp-boundary end rate height index log-error delta))
   (lw-complex-log-ramp-independent-endpoint rate height index log-error delta)))
 :hints (("Goal"
   :use (lw-mdb-log-data
         (:instance lw-complex-exp-laplace-boundary
          (rate (- rate 1)) (value (car (lw-log-bounds index log-error))) (error delta))
         (:instance lw-complex-exp-laplace-boundary
          (value (car (lw-log-bounds index log-error))) (error delta)))
   :in-theory
   (e/d (lw-mellin-ramp-primitive lw-mellin-ramp-boundary lw-complex-log-ramp-independent-endpoint
         lw-complex-log-ramp-independent-exp lw-complex-log-ramp-start)
     (lw-complex-exp-laplace-boundary lw-log-bounds-nonnegative lw-log-bounds-monotone-overlap))
   :nonlinearp nil :do-not-induct t)))

(defun lw-mellin-prime-primitive (end rate height count total model-error primitive-error delta)
 (declare (xargs :measure (nfix count)))
 (if (or (zp count) (equal count 1)) (cons 0 0)
  (lw-complex-add
   (lw-complex-scale (car (lw-mangoldt-bounds count primitive-error))
    (lw-mellin-ramp-primitive end rate height count (lw-smoothed-ramp-log-error count total model-error) delta))
   (lw-mellin-prime-primitive end rate height (- count 1) total model-error primitive-error delta))))

(defun lw-mellin-prime-boundary (end rate height count total model-error primitive-error delta)
 (declare (xargs :measure (nfix count)))
 (if (or (zp count) (equal count 1)) (cons 0 0)
  (lw-complex-add
   (lw-complex-scale (car (lw-mangoldt-bounds count primitive-error))
    (lw-mellin-ramp-boundary end rate height count (lw-smoothed-ramp-log-error count total model-error) delta))
   (lw-mellin-prime-boundary end rate height (- count 1) total model-error primitive-error delta))))

(local (defthm lw-mdb-merge-sums
 (equal
  (lw-complex-add (lw-complex-add (lw-complex-scale weight a) x)
                   (lw-complex-add (lw-complex-scale weight b) y))
  (lw-complex-add (lw-complex-scale weight (lw-complex-add a b)) (lw-complex-add x y)))
 :hints (("Goal" :in-theory (enable lw-complex-add lw-complex-scale)))))

(defthm lw-mellin-prime-primitive-boundary
 (implies
  (and (rationalp end) (<= 0 end) (rationalp rate) (< 1 rate) (rationalp height)
       (natp count) (natp total) (rationalp model-error) (< 0 model-error)
       (rationalp primitive-error) (< 0 primitive-error) (rationalp delta) (< 0 delta))
  (equal
   (lw-complex-add
    (lw-mellin-prime-primitive end rate height count total model-error primitive-error delta)
    (lw-mellin-prime-boundary end rate height count total model-error primitive-error delta))
   (lw-complex-log-ramp-family nil rate height count total model-error primitive-error delta)))
 :hints (("Goal"
   :induct (lw-mellin-prime-primitive end rate height count total model-error primitive-error delta)
   :in-theory (enable lw-mellin-prime-primitive lw-mellin-prime-boundary lw-complex-log-ramp-family))
  (and stable-under-simplificationp
   '(:use ((:instance lw-smoothed-ramp-log-error-adequate (index count) (error model-error))
           (:instance lw-mellin-ramp-primitive-boundary
            (index count) (log-error (lw-smoothed-ramp-log-error count total model-error))))
     :in-theory (disable lw-smoothed-ramp-log-error-adequate lw-mellin-ramp-primitive-boundary)
     :do-not-induct t))))

(local (in-theory (disable lw-mellin-prime-primitive lw-mellin-prime-boundary)))

(defun lw-mellin-finite-primitive (cap end rate height model-error delta)
 (lw-complex-add
  (lw-complex-sub
   (lw-mellin-prime-primitive end rate height (lw-log-signal-ramp-count cap) (lw-log-signal-ramp-count cap) model-error (lw-signal-exponential-precision cap model-error) delta)
   (lw-complex-exp-clipped-moment-primitive (lw-complex-laplace-point (- rate 1) height) 0 end 0 delta))
  (lw-complex-scale (+ 1 (car (lw-euler-bounds (lw-signal-exponential-precision cap model-error)))) (lw-complex-exp-clipped-primitive (lw-complex-laplace-point (- rate 1) height) 0 end 0 delta))))

(defun lw-mellin-finite-boundary (cap end rate height model-error delta)
 (lw-complex-add
  (lw-complex-sub
   (lw-mellin-prime-boundary end rate height (lw-log-signal-ramp-count cap) (lw-log-signal-ramp-count cap) model-error (lw-signal-exponential-precision cap model-error) delta)
   (lw-complex-exp-moment-boundary (lw-complex-laplace-point (- rate 1) height) end delta))
  (lw-complex-scale (+ 1 (car (lw-euler-bounds (lw-signal-exponential-precision cap model-error)))) (lw-complex-exp-boundary (lw-complex-laplace-point (- rate 1) height) end delta))))

(defun lw-mellin-finite-ray-endpoint (cap rate height model-error delta)
 (lw-complex-add
  (lw-complex-sub
   (lw-complex-log-ramp-family nil rate height (lw-log-signal-ramp-count cap) (lw-log-signal-ramp-count cap) model-error (lw-signal-exponential-precision cap model-error) delta)
   (lw-complex-mul (lw-complex-reciprocal (cons (- rate 1) height)) (lw-complex-reciprocal (cons (- rate 1) height))))
  (lw-complex-scale (+ 1 (car (lw-euler-bounds (lw-signal-exponential-precision cap model-error)))) (lw-complex-reciprocal (cons (- rate 1) height)))))

(defun lw-mellin-finite-dirichlet-model (cap rate height model-error delta)
 (lw-complex-add
  (lw-complex-sub
   (lw-complex-mul
    (lw-complex-dirichlet-prime-sum rate height (lw-log-signal-ramp-count cap) (lw-log-signal-ramp-count cap) model-error (lw-signal-exponential-precision cap model-error) delta)
    (lw-complex-reciprocal (lw-complex-mul (cons (- rate 1) height) (cons rate height))))
   (lw-complex-mul (lw-complex-reciprocal (cons (- rate 1) height)) (lw-complex-reciprocal (cons (- rate 1) height))))
  (lw-complex-scale (+ 1 (car (lw-euler-bounds (lw-signal-exponential-precision cap model-error)))) (lw-complex-reciprocal (cons (- rate 1) height)))))

(local (in-theory (disable lw-mellin-finite-primitive lw-mellin-finite-boundary
                          lw-mellin-finite-ray-endpoint lw-mellin-finite-dirichlet-model)))

(local (defthm lw-mdb-frozen-data
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

(local (defthm lw-mdb-complete-boundary
 (equal
  (lw-complex-add
   (lw-complex-add (lw-complex-sub p (lw-complex-sub moment upper-moment))
                   (lw-complex-scale factor (lw-complex-sub exponential upper-exponential)))
   (lw-complex-add (lw-complex-sub b upper-moment) (lw-complex-scale factor upper-exponential)))
  (lw-complex-add (lw-complex-sub (lw-complex-add p b) moment) (lw-complex-scale factor exponential)))
 :hints (("Goal" :in-theory (enable lw-complex-add lw-complex-sub lw-complex-scale)))))

(defthm lw-mellin-finite-primitive-boundary
 (implies
  (and (rationalp cap) (<= 0 cap) (rationalp end) (<= 0 end)
       (rationalp rate) (< 1 rate) (rationalp height)
       (rationalp model-error) (< 0 model-error) (rationalp delta) (< 0 delta))
  (equal
   (lw-complex-add (lw-mellin-finite-primitive cap end rate height model-error delta)
                   (lw-mellin-finite-boundary cap end rate height model-error delta))
   (lw-mellin-finite-ray-endpoint cap rate height model-error delta)))
 :hints (("Goal"
  :use (lw-mdb-frozen-data
        (:instance lw-mellin-prime-primitive-boundary (count (lw-log-signal-ramp-count cap)) (total (lw-log-signal-ramp-count cap)) (primitive-error (lw-signal-exponential-precision cap model-error)))
        (:instance lw-complex-exp-laplace-boundaries-at-zero (rate (- rate 1)) (error delta)))
  :in-theory (e/d (lw-mellin-finite-primitive lw-mellin-finite-boundary lw-mellin-finite-ray-endpoint)
     (lw-mellin-prime-primitive-boundary lw-complex-exp-laplace-boundaries-at-zero))
  :nonlinearp nil :do-not-induct t)))

(local (defthm lw-mdb-corrections-cancel
 (equal
  (lw-complex-sub
   (lw-complex-add (lw-complex-sub a correction) rest)
   (lw-complex-add (lw-complex-sub b correction) rest))
  (lw-complex-sub a b))
 :hints (("Goal" :in-theory (enable lw-complex-add lw-complex-sub)))))

(defthm lw-mellin-finite-boundary-normalization
 (implies
  (and (rationalp cap) (<= 0 cap) (rationalp end) (<= 0 end)
       (rationalp rate) (< 1 rate) (rationalp height)
       (rationalp model-error) (< 0 model-error) (rationalp error) (< 0 error))
  (let ((delta (lw-complex-log-ramp-family-precision rate height (lw-log-signal-ramp-count cap) error)))
   (lw-complex-diskp
    (lw-complex-sub
     (lw-complex-add (lw-mellin-finite-primitive cap end rate height model-error delta)
                     (lw-mellin-finite-boundary cap end rate height model-error delta))
     (lw-mellin-finite-dirichlet-model cap rate height model-error delta))
    (+ (* 1/16 error) (* 1/8 model-error (/ (- rate 1)))))))
 :hints (("Goal"
  :use (lw-mdb-frozen-data
        (:instance lw-complex-log-ramp-family-precision-valid (count (lw-log-signal-ramp-count cap)))
        (:instance lw-mellin-finite-primitive-boundary
          (delta (lw-complex-log-ramp-family-precision rate height (lw-log-signal-ramp-count cap) error)))
        (:instance lw-complex-log-ramp-family-computed-normalization
          (count (lw-log-signal-ramp-count cap)) (total (lw-log-signal-ramp-count cap)) (primitive-error (lw-signal-exponential-precision cap model-error))))
  :in-theory
   (e/d (lw-mellin-finite-ray-endpoint lw-mellin-finite-dirichlet-model)
     (lw-mellin-finite-primitive-boundary lw-complex-log-ramp-family-precision-valid
      lw-complex-log-ramp-family-computed-normalization))
  :nonlinearp nil :do-not-induct t)))


