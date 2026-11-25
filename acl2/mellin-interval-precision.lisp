(in-package "ACL2")

(include-book "mellin-endpoint-precision")

; Change all component endpoints on [start,start+length] to one finer
; node precision. The first-moment budget retains the nonzero start.

(local (in-theory
 (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
          lw-complex-diskp lw-diskp lw-complex-norm-square lw-complex-reciprocal lw-complex-quotient
          lw-complex-exp-value lw-complex-exp-cap lw-complex-exp-uniform-cap lw-exp-bounds lw-exp-lipschitz-cap
          lw-log-bounds lw-euler-bounds lw-mangoldt-bounds
          lw-mellin-basis-clearance lw-mellin-basis-exponential-point lw-complex-laplace-point
          lw-mellin-component-endpoint-target lw-mellin-component-endpoint-value
          lw-mellin-moment-endpoint-target lw-mellin-moment-endpoint-value
          lw-complex-exp-dyadic-integral-value lw-complex-exp-dyadic-moment-integral-value
          lw-complex-exp-dyadic-moment-endpoint-error lw-complex-exp-moment-amplification
          lw-complex-exp-dyadic-moment-depth lw-complex-exp-dyadic-moment-error
          lw-complex-exp-dyadic-moment-slope lw-complex-exp-dyadic-depth lw-complex-exp-dyadic-error
          lw-complex-exp-clipped-primitive lw-complex-exp-clipped-moment-primitive
          lw-complex-exp-clipped-primitive-endpoint lw-complex-exp-clipped-moment-primitive-endpoint
          lw-complex-exp-primitive-boundaries lw-complex-exp-moment-primitive-boundaries
          lw-complex-exp-clipped-primitive-boundaries lw-complex-exp-clipped-moment-primitive-boundaries
          lw-complex-exp-boundary lw-complex-exp-moment-boundary
          lw-complex-exp-laplace-boundary lw-complex-exp-laplace-moment-boundary
          lw-mellin-prime-endpoint lw-mellin-ramp-endpoint lw-mellin-frozen-endpoint
          lw-mellin-prime-primitive lw-mellin-ramp-primitive lw-mellin-finite-primitive
          lw-mellin-finite-boundary lw-mellin-finite-dirichlet-model lw-mellin-finite-ray-endpoint
          lw-mellin-prime-endpoint-mass lw-smoothed-ramp-log-error lw-smoothed-ramp-unit-error
          lw-log-signal-ramp-count lw-log-signal-spatial-cap lw-signal-count
          lw-signal-exponential-precision lw-signal-exponential-cost
          lw-complex-log-ramp-family-precision lw-complex-log-ramp-family-cost
          lw-halving-depth lw-precision-fuel lw-complex-disk-enlarge lw-disk-enlarge
          lw-complex-sub-add-first lw-complex-add-commutative lw-complex-add-left-commutes)))

(local (defthm lw-mip-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-mip-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-mip-zero-times (equal (* 0 a) 0)))

(local (defthm lw-mip-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-mip-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-mip-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-mip-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-mip-left-commutes)))))

(local (defthm lw-mip-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-mip-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-mip-times-negative (a b) (b a)))
                 :in-theory (disable lw-mip-times-negative)))))

(local (defthm lw-mip-point-form
 (implies (and (rationalp rate) (rationalp height))
  (equal (lw-mellin-basis-exponential-point kind rate height)
         (lw-complex-laplace-point (lw-mellin-basis-clearance kind rate) height)))
 :hints (("Goal" :in-theory (enable lw-mellin-basis-exponential-point lw-mellin-basis-clearance lw-complex-laplace-point)))))

(defun lw-mellin-interval-moment-precision (cap start length rate error)
 (lw-complex-exp-dyadic-moment-endpoint-error
  start length (lw-mellin-basis-clearance 1 rate) (lw-mellin-moment-endpoint-target cap rate length error)))

(local (in-theory (disable lw-mellin-interval-moment-precision)))

(local (defthm lw-mip-fraction-budget
 (implies
  (and (rationalp mass) (<= 0 mass) (rationalp tau)
       (rationalp clearance) (< 0 clearance) (rationalp target) (rationalp error)
       (<= target (* 1/4 error)) (<= (* mass tau) (* 1/16 clearance target)))
  (<= (* 4 mass tau (/ clearance)) (* 1/16 error)))
 :hints (("Goal"
   :use ((:instance inverse-of-* (x clearance))
         (:instance lw-mip-multiply-order (a (* mass tau)) (b (* 1/16 clearance target)) (factor (* 4 (/ clearance)))))
   :in-theory (disable inverse-of-*) :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(defthm lw-mellin-interval-moment-precision-valid
 (implies (and (rationalp cap) (<= 0 cap) (rationalp start) (<= 0 start) (rationalp length) (<= 0 length)
               (rationalp rate) (< 1 rate) (rationalp error) (< 0 error))
  (let ((tau (lw-mellin-interval-moment-precision cap start length rate error))
        (clearance (lw-mellin-basis-clearance 1 rate)))
   (and (rationalp tau) (< 0 tau)
        (<= (* 4 (+ start length (/ clearance)) tau (/ clearance)) (* 1/16 error)))))
 :hints (("Goal"
   :use ((:instance lw-mellin-basis-clearance-valid (kind 1) (sigma rate) (height 0))
         (:instance lw-mellin-moment-endpoint-target-valid (sigma rate) (length length))
         (:instance lw-complex-exp-dyadic-moment-error-valid
          (point (lw-mellin-basis-exponential-point 1 rate 0)) (start start) (length length)
          (clearance (lw-mellin-basis-clearance 1 rate))
          (error (lw-mellin-moment-endpoint-target cap rate length error)))
         (:instance lw-mip-fraction-budget
          (mass (+ start length (/ (lw-mellin-basis-clearance 1 rate))))
          (tau (lw-mellin-interval-moment-precision cap start length rate error))
          (clearance (lw-mellin-basis-clearance 1 rate)) (target (lw-mellin-moment-endpoint-target cap rate length error))))
   :in-theory (e/d (lw-mellin-interval-moment-precision lw-complex-exp-moment-amplification)
     (lw-mellin-basis-clearance-valid lw-mellin-moment-endpoint-target-valid lw-complex-exp-dyadic-moment-error-valid))
   :nonlinearp nil :do-not-induct t)))

(local (defthm lw-mip-nonnegative-product
 (implies (and (rationalp a) (<= 0 a) (rationalp b) (<= 0 b)) (<= 0 (* a b)))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-mip-cauchy-budget
 (implies
  (and (rationalp mass) (<= 0 mass) (rationalp tau) (rationalp delta) (<= delta tau)
       (rationalp clearance) (< 0 clearance) (rationalp error)
       (<= (* 4 mass tau (/ clearance)) (* 1/16 error)))
  (<= (* 2 mass (+ tau delta) (/ clearance)) (* 1/16 error)))
 :hints (("Goal"
   :use ((:instance lw-mip-nonnegative-product (a mass) (b (/ clearance)))
         (:instance lw-mip-multiply-order (a delta) (b tau) (factor (* 2 mass (/ clearance)))))
   :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(defthm lw-mellin-interval-component-precision-comparison
 (implies
  (and (rationalp start) (<= 0 start) (rationalp length) (<= 0 length) (rationalp cutpoint) (rationalp rate) (< 1 rate) (rationalp height)
       (rationalp error) (< 0 error) (rationalp delta) (< 0 delta)
       (<= delta (lw-mellin-component-endpoint-precision kind length rate error)))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-mellin-component-endpoint-value kind start length cutpoint rate height error)
    (lw-complex-exp-clipped-primitive
     (lw-complex-laplace-point (lw-mellin-basis-clearance kind rate) height) start (+ start length) cutpoint delta))
   (* 1/16 error)))
 :hints (("Goal"
   :use ((:instance lw-mellin-component-endpoint-precision-valid (end length))
         (:instance lw-mellin-basis-clearance-valid (sigma rate))
         (:instance lw-mip-cauchy-budget
          (mass 1) (tau (lw-mellin-component-endpoint-precision kind length rate error))
          (clearance (lw-mellin-basis-clearance kind rate)))
         (:instance lw-complex-exp-clipped-primitive-cauchy
          (point (lw-mellin-basis-exponential-point kind rate height)) (start start) (end (+ start length))
          (clearance (lw-mellin-basis-clearance kind rate))
          (left-error (lw-mellin-component-endpoint-precision kind length rate error)) (right-error delta))
         (:instance lw-complex-disk-enlarge
          (point (lw-complex-sub
           (lw-mellin-component-endpoint-value kind start length cutpoint rate height error)
           (lw-complex-exp-clipped-primitive
            (lw-complex-laplace-point (lw-mellin-basis-clearance kind rate) height) start (+ start length) cutpoint delta)))
          (radius (* 2 (+ (lw-mellin-component-endpoint-precision kind length rate error) delta)
                     (/ (lw-mellin-basis-clearance kind rate))))
          (cap (* 1/16 error))))
   :in-theory (e/d (lw-mellin-component-endpoint-value lw-complex-exp-dyadic-integral-value
                   lw-mellin-component-endpoint-precision)
     (lw-mellin-component-endpoint-precision-valid lw-mellin-basis-clearance-valid
      lw-complex-exp-clipped-primitive-cauchy))
   :nonlinearp nil :do-not-induct t)))

(defthm lw-mellin-interval-moment-precision-comparison
 (implies
  (and (rationalp cap) (<= 0 cap) (rationalp start) (<= 0 start) (rationalp length) (<= 0 length)
       (rationalp cutpoint) (<= 0 cutpoint) (rationalp rate) (< 1 rate) (rationalp height)
       (rationalp error) (< 0 error) (rationalp delta) (< 0 delta)
       (<= delta (lw-mellin-interval-moment-precision cap start length rate error)))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-mellin-moment-endpoint-value cap start length cutpoint rate height error)
    (lw-complex-exp-clipped-moment-primitive
     (lw-complex-laplace-point (lw-mellin-basis-clearance 1 rate) height) start (+ start length) cutpoint delta))
   (* 1/16 error)))
 :hints (("Goal"
   :use (lw-mellin-interval-moment-precision-valid
         (:instance lw-mellin-basis-clearance-valid (kind 1) (sigma rate))
         (:instance lw-mip-cauchy-budget
          (mass (+ start length (/ (lw-mellin-basis-clearance 1 rate))))
          (tau (lw-mellin-interval-moment-precision cap start length rate error))
          (clearance (lw-mellin-basis-clearance 1 rate)))
         (:instance lw-complex-exp-clipped-moment-primitive-cauchy
          (point (lw-mellin-basis-exponential-point 1 rate height)) (start start) (end (+ start length)) (bound (+ start length))
          (clearance (lw-mellin-basis-clearance 1 rate))
          (left-error (lw-mellin-interval-moment-precision cap start length rate error)) (right-error delta))
         (:instance lw-complex-disk-enlarge
          (point (lw-complex-sub
           (lw-mellin-moment-endpoint-value cap start length cutpoint rate height error)
           (lw-complex-exp-clipped-moment-primitive
            (lw-complex-laplace-point (lw-mellin-basis-clearance 1 rate) height) start (+ start length) cutpoint delta)))
          (radius (* 2 (+ start length (/ (lw-mellin-basis-clearance 1 rate)))
                     (+ (lw-mellin-interval-moment-precision cap start length rate error) delta)
                     (/ (lw-mellin-basis-clearance 1 rate))))
          (cap (* 1/16 error))))
   :in-theory (e/d (lw-mellin-moment-endpoint-value lw-complex-exp-dyadic-moment-integral-value
                   lw-mellin-interval-moment-precision)
     (lw-mellin-interval-moment-precision-valid lw-mellin-basis-clearance-valid
      lw-complex-exp-clipped-moment-primitive-cauchy lw-complex-exp-dyadic-moment-error-valid))
   :nonlinearp nil :do-not-induct t)))

(defun lw-mellin-interval-node-precision (cap start length rate error)
 (min 1 (min (lw-mellin-component-endpoint-precision 0 length rate error) (min (lw-mellin-component-endpoint-precision 3 length rate error) (lw-mellin-interval-moment-precision cap start length rate error)))))

(local (in-theory (disable lw-mellin-interval-node-precision)))

(defthm lw-mellin-interval-node-precision-valid
 (implies
  (and (rationalp cap) (<= 0 cap) (rationalp start) (<= 0 start)
       (rationalp length) (<= 0 length) (rationalp rate) (< 1 rate)
       (rationalp error) (< 0 error))
  (and (rationalp (lw-mellin-interval-node-precision cap start length rate error)) (< 0 (lw-mellin-interval-node-precision cap start length rate error)) (<= (lw-mellin-interval-node-precision cap start length rate error) 1)
       (<= (lw-mellin-interval-node-precision cap start length rate error) (lw-mellin-component-endpoint-precision 0 length rate error)) (<= (lw-mellin-interval-node-precision cap start length rate error) (lw-mellin-component-endpoint-precision 3 length rate error)) (<= (lw-mellin-interval-node-precision cap start length rate error) (lw-mellin-interval-moment-precision cap start length rate error))))
 :hints (("Goal"
  :use ((:instance lw-mellin-component-endpoint-precision-valid (kind 0) (end length))
        (:instance lw-mellin-component-endpoint-precision-valid (kind 3) (end length))
        lw-mellin-interval-moment-precision-valid)
  :in-theory (e/d (lw-mellin-interval-node-precision)
   (lw-mellin-component-endpoint-precision-valid lw-mellin-interval-moment-precision-valid))
  :do-not-induct t)))
