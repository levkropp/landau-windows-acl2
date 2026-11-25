(in-package "ACL2")

(include-book "mellin-far-boundary")

(include-book "mellin-boundary-tail")

(include-book "mellin-boundary-precision")

; Remove the upper boundary from the actual improper Mellin comparison.
; A finite auxiliary endpoint and one common finer precision suffice.

(local (in-theory
 (disable lw-log-bounds lw-exp-bounds lw-euler-bounds lw-mangoldt-bounds
          lw-log-signal-ramp-count lw-log-signal-spatial-cap lw-signal-count
          lw-signal-exponential-precision lw-signal-exponential-cost
          lw-mellin-common-depth lw-mellin-component-minimum-depth
          lw-mellin-prime-endpoint-mass lw-mellin-common-base-radius
          lw-mellin-refined-endpoint lw-mellin-refined-endpoint-radius
          lw-kernel-spatial-cap lw-kernel-spatial-slope lw-complex-exp-uniform-cap
          lw-halved-width lw-halving-depth lw-precision-fuel
          lw-mellin-integral-cutoff lw-mellin-tail-coefficient
          lw-complexp lw-complex-add lw-complex-sub lw-complex-scale lw-complex-diskp lw-diskp
          lw-complex-disk-enlarge lw-disk-enlarge
          lw-complex-sub-add-first lw-complex-add-commutative lw-complex-add-left-commutes)))

(local (in-theory (disable lw-mellin-finite-interval-primitive lw-mellin-finite-interval-boundary
 lw-mellin-finite-boundary lw-mellin-refined-comparison-cost
 lw-mellin-refined-endpoint-request lw-mellin-endpoint-precision-factor
 lw-mellin-computed-refined-endpoint lw-mellin-refined-endpoint)))

(local (in-theory (disable lw-mellin-endpoint-request lw-mellin-dirichlet-precision
 lw-mellin-dirichlet-node-precision lw-mellin-computed-dirichlet-boundary
 lw-mellin-computed-dirichlet-model lw-mellin-far-boundary-end lw-mellin-far-boundary-precision
 lw-mellin-computed-tail-node-precision lw-mellin-integral lw-mellin-integral-cutoff
 lw-mellin-finite-boundary)))

(local (defthm lw-mdd-left-commutes
 (equal (* a (* b c)) (* b (* a c)))
 :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                       (:instance associativity-of-* (x b) (y a) (z c))
                       (:instance commutativity-of-* (x a) (y b)))
                 :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-mdd-left-distributes
 (equal (* (+ a b) c) (+ (* a c) (* b c)))
 :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                 :in-theory (disable distributivity)))))

(local (defthm lw-mdd-zero-times (equal (* 0 a) 0)))

(local (defthm lw-mdd-times-negative
         (equal (* a (- b)) (- (* a b)))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))

(local (defthm lw-mdd-negative-times
         (equal (* (- a) b) (- (* a b)))
         :hints (("Goal" :use ((:instance lw-mdd-times-negative (a b) (b a)))
                         :in-theory (disable lw-mdd-times-negative)))))

(local (defthm lw-mdd-multiply-order
 (implies (and (rationalp a) (rationalp b) (<= a b) (rationalp factor) (<= 0 factor))
  (<= (* a factor) (* b factor)))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defun lw-mellin-boundary-decay-end (cap error)
 (lw-mellin-far-boundary-end cap cap (lw-mellin-endpoint-request cap error) (* 1/4 error)))

(local (in-theory (disable lw-mellin-boundary-decay-end)))

(local (defthm lw-mdd-end-data
 (implies (and (rationalp cap) (<= 0 cap) (rationalp error) (< 0 error))
  (and (rationalp (lw-mellin-boundary-decay-end cap error)) (<= 1 (lw-mellin-boundary-decay-end cap error)) (<= cap (lw-mellin-boundary-decay-end cap error))
       (<= (lw-log-signal-ramp-count cap) (lw-mellin-boundary-decay-end cap error))))
 :hints (("Goal"
  :use (lw-mellin-endpoint-request-valid
        (:instance lw-mellin-far-boundary-end-valid (start cap) (model-error (lw-mellin-endpoint-request cap error)) (error (* 1/4 error))))
  :in-theory (e/d (lw-mellin-boundary-decay-end)
    (lw-mellin-endpoint-request-valid lw-mellin-far-boundary-end-valid))
  :do-not-induct t))
 :rule-classes nil))



(defun lw-mellin-boundary-decay-node-precision (cap rate height error)
 (min (lw-mellin-dirichlet-node-precision cap rate height error) (min (lw-mellin-computed-tail-node-precision cap (lw-mellin-boundary-decay-end cap error) cap (- (lw-mellin-boundary-decay-end cap error) cap) rate (lw-mellin-endpoint-request cap error) (* 1/4 error)) (lw-mellin-far-boundary-precision cap (lw-mellin-boundary-decay-end cap error) (lw-mellin-endpoint-request cap error) (* 1/4 error)))))

(local (in-theory (disable lw-mellin-boundary-decay-node-precision)))

(defthm lw-mellin-boundary-decay-node-precision-valid
 (implies
  (and (rationalp cap) (<= 0 cap) (rationalp rate) (< 2 rate) (rationalp height)
       (rationalp error) (< 0 error))
  (and (rationalp (lw-mellin-boundary-decay-node-precision cap rate height error)) (< 0 (lw-mellin-boundary-decay-node-precision cap rate height error)) (<= (lw-mellin-boundary-decay-node-precision cap rate height error) 1)
       (<= (lw-mellin-boundary-decay-node-precision cap rate height error) (lw-mellin-dirichlet-node-precision cap rate height error)) (<= (lw-mellin-boundary-decay-node-precision cap rate height error) (lw-mellin-computed-tail-node-precision cap (lw-mellin-boundary-decay-end cap error) cap (- (lw-mellin-boundary-decay-end cap error) cap) rate (lw-mellin-endpoint-request cap error) (* 1/4 error))) (<= (lw-mellin-boundary-decay-node-precision cap rate height error) (lw-mellin-far-boundary-precision cap (lw-mellin-boundary-decay-end cap error) (lw-mellin-endpoint-request cap error) (* 1/4 error)))))
 :hints (("Goal"
  :use (lw-mdd-end-data lw-mellin-endpoint-request-valid
        (:instance lw-mellin-dirichlet-precision-valid (end cap) (component-error (lw-mellin-endpoint-request cap error)))
        (:instance lw-mellin-computed-tail-node-precision-valid
         (model-cap cap) (cap (lw-mellin-boundary-decay-end cap error)) (start cap) (length (- (lw-mellin-boundary-decay-end cap error) cap))
         (model-error (lw-mellin-endpoint-request cap error)) (error (* 1/4 error)))
        (:instance lw-mellin-far-boundary-precision-valid (end (lw-mellin-boundary-decay-end cap error)) (model-error (lw-mellin-endpoint-request cap error)) (error (* 1/4 error))))
  :in-theory (e/d (lw-mellin-boundary-decay-node-precision lw-mellin-dirichlet-node-precision)
    (lw-mellin-endpoint-request-valid lw-mellin-dirichlet-precision-valid
     lw-mellin-computed-tail-node-precision-valid lw-mellin-far-boundary-precision-valid))
  :do-not-induct t)))

(local (defthm lw-mdd-computed-boundary-rational
 (implies
  (and (rationalp cap) (<= 0 cap) (rationalp rate) (< 1 rate) (rationalp height)
       (rationalp error) (< 0 error))
  (lw-complexp (lw-mellin-computed-dirichlet-boundary cap rate height error)))
 :hints (("Goal"
  :use (lw-mellin-endpoint-request-valid
        (:instance lw-mellin-dirichlet-precision-valid (end cap) (component-error (lw-mellin-endpoint-request cap error)))
        (:instance lw-mellin-finite-boundary-rational (end cap) (model-error (lw-mellin-endpoint-request cap error)) (delta (lw-mellin-dirichlet-node-precision cap rate height error))))
  :in-theory (e/d (lw-mellin-computed-dirichlet-boundary lw-mellin-dirichlet-node-precision)
    (lw-mellin-endpoint-request-valid lw-mellin-dirichlet-precision-valid lw-mellin-finite-boundary-rational))
  :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-mdd-three-term-recover
 (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c))
  (equal a (lw-complex-add (lw-complex-sub a b)
             (lw-complex-add (lw-complex-sub b c) c))))
 :hints (("Goal" :in-theory (enable lw-complexp lw-complex-add lw-complex-sub)))
 :rule-classes nil))

(local (defthm lw-mdd-three-term-bound
 (implies
  (and (lw-complexp a) (lw-complexp b) (lw-complexp c)
       (lw-complex-diskp (lw-complex-sub a b) near-radius)
       (lw-complex-diskp (lw-complex-sub b c) tail-radius)
       (lw-complex-diskp c far-radius))
  (lw-complex-diskp a (+ near-radius tail-radius far-radius)))
 :hints (("Goal"
  :use (lw-mdd-three-term-recover
        (:instance lw-complex-add-disk (left (lw-complex-sub b c)) (right c)
         (radius tail-radius) (other-radius far-radius))
        (:instance lw-complex-add-disk (left (lw-complex-sub a b))
         (right (lw-complex-add (lw-complex-sub b c) c))
         (radius near-radius) (other-radius (+ tail-radius far-radius))))
  :in-theory (disable lw-complex-add-disk)
  :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-mdd-fold-constants
 (implies (syntaxp (and (quotep a) (quotep b)))
  (equal (* a (* b c)) (* (* a b) c)))
 :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                 :in-theory (disable associativity-of-*)))))

(defthm lw-mellin-computed-dirichlet-boundary-decay
 (implies
  (and (rationalp rate) (< 2 rate) (rationalp height) (rationalp error) (< 0 error))
  (lw-complex-diskp (lw-mellin-computed-dirichlet-boundary (lw-mellin-integral-cutoff rate 0 error) rate height error) (* 2 error)))
 :hints (("Goal"
  :use ((:instance lw-mellin-integral-cutoff-valid (sigma rate) (index 0))
        (:instance lw-mdd-end-data (cap (lw-mellin-integral-cutoff rate 0 error)))
        (:instance lw-mellin-endpoint-request-valid (cap (lw-mellin-integral-cutoff rate 0 error)))
        (:instance lw-mellin-boundary-decay-node-precision-valid (cap (lw-mellin-integral-cutoff rate 0 error)))
        (:instance lw-mdd-computed-boundary-rational (cap (lw-mellin-integral-cutoff rate 0 error)))
        (:instance lw-mellin-finite-boundary-rational (cap (lw-mellin-integral-cutoff rate 0 error)) (end (lw-mellin-integral-cutoff rate 0 error)) (model-error (lw-mellin-endpoint-request (lw-mellin-integral-cutoff rate 0 error) error)) (delta (lw-mellin-boundary-decay-node-precision (lw-mellin-integral-cutoff rate 0 error) rate height error)))
        (:instance lw-mellin-finite-boundary-rational (cap (lw-mellin-integral-cutoff rate 0 error)) (end (lw-mellin-boundary-decay-end (lw-mellin-integral-cutoff rate 0 error) error)) (model-error (lw-mellin-endpoint-request (lw-mellin-integral-cutoff rate 0 error) error)) (delta (lw-mellin-boundary-decay-node-precision (lw-mellin-integral-cutoff rate 0 error) rate height error)))
        (:instance lw-mellin-computed-boundary-precision-stable (cap (lw-mellin-integral-cutoff rate 0 error)) (delta (lw-mellin-boundary-decay-node-precision (lw-mellin-integral-cutoff rate 0 error) rate height error)))
        (:instance lw-mellin-common-node-boundary-at-integral-cutoff
         (model-cap (lw-mellin-integral-cutoff rate 0 error)) (end (lw-mellin-boundary-decay-end (lw-mellin-integral-cutoff rate 0 error) error)) (model-error (lw-mellin-endpoint-request (lw-mellin-integral-cutoff rate 0 error) error)) (cutoff-error error) (error (* 1/4 error)) (delta (lw-mellin-boundary-decay-node-precision (lw-mellin-integral-cutoff rate 0 error) rate height error)))
        (:instance lw-mellin-computed-far-boundary-small
         (cap (lw-mellin-integral-cutoff rate 0 error)) (start (lw-mellin-integral-cutoff rate 0 error)) (model-error (lw-mellin-endpoint-request (lw-mellin-integral-cutoff rate 0 error) error)) (error (* 1/4 error)) (delta (lw-mellin-boundary-decay-node-precision (lw-mellin-integral-cutoff rate 0 error) rate height error)))
        (:instance lw-mdd-three-term-bound
         (a (lw-mellin-computed-dirichlet-boundary (lw-mellin-integral-cutoff rate 0 error) rate height error)) (b (lw-mellin-finite-boundary (lw-mellin-integral-cutoff rate 0 error) (lw-mellin-integral-cutoff rate 0 error) rate height (lw-mellin-endpoint-request (lw-mellin-integral-cutoff rate 0 error) error) (lw-mellin-boundary-decay-node-precision (lw-mellin-integral-cutoff rate 0 error) rate height error))) (c (lw-mellin-finite-boundary (lw-mellin-integral-cutoff rate 0 error) (lw-mellin-boundary-decay-end (lw-mellin-integral-cutoff rate 0 error) error) rate height (lw-mellin-endpoint-request (lw-mellin-integral-cutoff rate 0 error) error) (lw-mellin-boundary-decay-node-precision (lw-mellin-integral-cutoff rate 0 error) rate height error)))
         (near-radius (* 1/256 error)) (tail-radius (+ (* 5/4 error) (* 1/32 error))) (far-radius (* 1/4 error)))
        (:instance lw-complex-disk-enlarge (point (lw-mellin-computed-dirichlet-boundary (lw-mellin-integral-cutoff rate 0 error) rate height error))
         (radius (+ (* 1/256 error) (+ (* 5/4 error) (* 1/32 error)) (* 1/4 error)))
         (cap (* 2 error))))
  :in-theory (e/d (lw-mellin-boundary-decay-end)
    (lw-mellin-integral-cutoff-valid lw-mellin-endpoint-request-valid
     lw-mellin-boundary-decay-node-precision-valid lw-mellin-finite-boundary-rational
     lw-mellin-computed-boundary-precision-stable lw-mellin-common-node-boundary-at-integral-cutoff
     lw-mellin-computed-far-boundary-small lw-complex-disk-enlarge))
  :nonlinearp nil :do-not-induct t)))

(local (defthm lw-mdd-remove-boundary
 (equal (lw-complex-sub (lw-complex-sub (lw-complex-add a b) c) b)
        (lw-complex-sub a c))
 :hints (("Goal" :in-theory (enable lw-complex-add lw-complex-sub)))))

(defthm lw-mellin-improper-dirichlet-without-boundary
 (implies
  (and (rationalp rate) (< 2 rate) (rationalp height) (rationalp error) (< 0 error))
  (lw-complex-diskp (lw-complex-sub (lw-mellin-integral rate height 0 error) (lw-mellin-computed-dirichlet-model (lw-mellin-integral-cutoff rate 0 error) rate height error)) (* 3 error)))
 :hints (("Goal"
  :use (lw-mellin-improper-dirichlet-comparison lw-mellin-computed-dirichlet-boundary-decay
        (:instance lw-complex-sub-disk
         (left (lw-complex-sub (lw-complex-add (lw-mellin-integral rate height 0 error) (lw-mellin-computed-dirichlet-boundary (lw-mellin-integral-cutoff rate 0 error) rate height error)) (lw-mellin-computed-dirichlet-model (lw-mellin-integral-cutoff rate 0 error) rate height error)))
         (right (lw-mellin-computed-dirichlet-boundary (lw-mellin-integral-cutoff rate 0 error) rate height error)) (radius error) (other-radius (* 2 error)))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub (lw-mellin-integral rate height 0 error) (lw-mellin-computed-dirichlet-model (lw-mellin-integral-cutoff rate 0 error) rate height error)))
         (radius (+ error (* 2 error))) (cap (* 3 error))))
  :in-theory (disable lw-mellin-improper-dirichlet-comparison
                      lw-mellin-computed-dirichlet-boundary-decay lw-complex-sub-disk)
  :do-not-induct t)))
