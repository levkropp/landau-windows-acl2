(in-package "ACL2")

(include-book "mellin-improper-endpoints")

(include-book "mellin-dirichlet-boundaries")

; Change the existing component endpoint precisions to one common node
; precision, retaining the frozen logarithms and primitive coefficients.

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

(local (defthm lw-mepc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-mepc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-mepc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-mepc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-mepc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-mepc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-mepc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-mepc-left-commutes)))))

(local (defthm lw-mepc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))
(local (defthm lw-mepc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-mepc-times-negative (a b) (b a)))
                 :in-theory (disable lw-mepc-times-negative)))))

(local (defthm lw-mepc-point-form
 (implies (and (rationalp rate) (rationalp height))
  (equal (lw-mellin-basis-exponential-point kind rate height)
         (lw-complex-laplace-point (lw-mellin-basis-clearance kind rate) height)))
 :hints (("Goal" :in-theory (enable lw-mellin-basis-exponential-point lw-mellin-basis-clearance lw-complex-laplace-point)))))

(defun lw-mellin-component-endpoint-precision (kind end rate error)
 (* 1/16 (lw-mellin-basis-clearance kind rate) (lw-mellin-component-endpoint-target kind rate end error)))

(defun lw-mellin-moment-endpoint-precision (cap end rate error)
 (lw-complex-exp-dyadic-moment-endpoint-error
  0 end (lw-mellin-basis-clearance 1 rate) (lw-mellin-moment-endpoint-target cap rate end error)))

(local (in-theory (disable lw-mellin-component-endpoint-precision lw-mellin-moment-endpoint-precision)))

(local (defthm lw-mepc-fraction-budget
 (implies
  (and (rationalp mass) (<= 0 mass) (rationalp tau)
       (rationalp clearance) (< 0 clearance) (rationalp target) (rationalp error)
       (<= target (* 1/4 error)) (<= (* mass tau) (* 1/16 clearance target)))
  (<= (* 4 mass tau (/ clearance)) (* 1/16 error)))
 :hints (("Goal"
   :use ((:instance inverse-of-* (x clearance))
         (:instance lw-mepc-multiply-order (a (* mass tau)) (b (* 1/16 clearance target)) (factor (* 4 (/ clearance)))))
   :in-theory (disable inverse-of-*) :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(defthm lw-mellin-component-endpoint-precision-valid
 (implies (and (rationalp end) (<= 0 end) (rationalp rate) (< 1 rate) (rationalp error) (< 0 error))
  (let ((tau (lw-mellin-component-endpoint-precision kind end rate error))
        (clearance (lw-mellin-basis-clearance kind rate)))
   (and (rationalp tau) (< 0 tau) (<= (* 4 tau (/ clearance)) (* 1/16 error)))))
 :hints (("Goal"
   :use ((:instance lw-mellin-basis-clearance-valid (sigma rate) (height 0))
         (:instance lw-mellin-component-endpoint-target-valid (sigma rate) (length end))
         (:instance lw-mepc-positive-product (a (lw-mellin-basis-clearance kind rate))
          (b (lw-mellin-component-endpoint-target kind rate end error)))
         (:instance lw-mepc-fraction-budget
          (mass 1) (tau (lw-mellin-component-endpoint-precision kind end rate error))
          (clearance (lw-mellin-basis-clearance kind rate)) (target (lw-mellin-component-endpoint-target kind rate end error))))
   :in-theory (e/d (lw-mellin-component-endpoint-precision)
                   (lw-mellin-basis-clearance-valid lw-mellin-component-endpoint-target-valid))
   :nonlinearp nil :do-not-induct t)))

(defthm lw-mellin-moment-endpoint-precision-valid
 (implies (and (rationalp cap) (<= 0 cap) (rationalp end) (<= 0 end)
               (rationalp rate) (< 1 rate) (rationalp error) (< 0 error))
  (let ((tau (lw-mellin-moment-endpoint-precision cap end rate error))
        (clearance (lw-mellin-basis-clearance 1 rate)))
   (and (rationalp tau) (< 0 tau)
        (<= (* 4 (+ end (/ clearance)) tau (/ clearance)) (* 1/16 error)))))
 :hints (("Goal"
   :use ((:instance lw-mellin-basis-clearance-valid (kind 1) (sigma rate) (height 0))
         (:instance lw-mellin-moment-endpoint-target-valid (sigma rate) (length end))
         (:instance lw-complex-exp-dyadic-moment-error-valid
          (point (lw-mellin-basis-exponential-point 1 rate 0)) (start 0) (length end)
          (clearance (lw-mellin-basis-clearance 1 rate))
          (error (lw-mellin-moment-endpoint-target cap rate end error)))
         (:instance lw-mepc-fraction-budget
          (mass (+ end (/ (lw-mellin-basis-clearance 1 rate))))
          (tau (lw-mellin-moment-endpoint-precision cap end rate error))
          (clearance (lw-mellin-basis-clearance 1 rate)) (target (lw-mellin-moment-endpoint-target cap rate end error))))
   :in-theory (e/d (lw-mellin-moment-endpoint-precision lw-complex-exp-moment-amplification)
     (lw-mellin-basis-clearance-valid lw-mellin-moment-endpoint-target-valid lw-complex-exp-dyadic-moment-error-valid))
   :nonlinearp nil :do-not-induct t)))

(local (defthm lw-mepc-nonnegative-product
 (implies (and (rationalp a) (<= 0 a) (rationalp b) (<= 0 b)) (<= 0 (* a b)))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-mepc-cauchy-budget
 (implies
  (and (rationalp mass) (<= 0 mass) (rationalp tau) (rationalp delta) (<= delta tau)
       (rationalp clearance) (< 0 clearance) (rationalp error)
       (<= (* 4 mass tau (/ clearance)) (* 1/16 error)))
  (<= (* 2 mass (+ tau delta) (/ clearance)) (* 1/16 error)))
 :hints (("Goal"
   :use ((:instance lw-mepc-nonnegative-product (a mass) (b (/ clearance)))
         (:instance lw-mepc-multiply-order (a delta) (b tau) (factor (* 2 mass (/ clearance)))))
   :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(defthm lw-mellin-component-endpoint-precision-comparison
 (implies
  (and (rationalp end) (<= 0 end) (rationalp cutpoint) (rationalp rate) (< 1 rate) (rationalp height)
       (rationalp error) (< 0 error) (rationalp delta) (< 0 delta)
       (<= delta (lw-mellin-component-endpoint-precision kind end rate error)))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-mellin-component-endpoint-value kind 0 end cutpoint rate height error)
    (lw-complex-exp-clipped-primitive
     (lw-complex-laplace-point (lw-mellin-basis-clearance kind rate) height) 0 end cutpoint delta))
   (* 1/16 error)))
 :hints (("Goal"
   :use (lw-mellin-component-endpoint-precision-valid
         (:instance lw-mellin-basis-clearance-valid (sigma rate))
         (:instance lw-mepc-cauchy-budget
          (mass 1) (tau (lw-mellin-component-endpoint-precision kind end rate error))
          (clearance (lw-mellin-basis-clearance kind rate)))
         (:instance lw-complex-exp-clipped-primitive-cauchy
          (point (lw-mellin-basis-exponential-point kind rate height)) (start 0)
          (clearance (lw-mellin-basis-clearance kind rate))
          (left-error (lw-mellin-component-endpoint-precision kind end rate error)) (right-error delta))
         (:instance lw-complex-disk-enlarge
          (point (lw-complex-sub
           (lw-mellin-component-endpoint-value kind 0 end cutpoint rate height error)
           (lw-complex-exp-clipped-primitive
            (lw-complex-laplace-point (lw-mellin-basis-clearance kind rate) height) 0 end cutpoint delta)))
          (radius (* 2 (+ (lw-mellin-component-endpoint-precision kind end rate error) delta)
                     (/ (lw-mellin-basis-clearance kind rate))))
          (cap (* 1/16 error))))
   :in-theory (e/d (lw-mellin-component-endpoint-value lw-complex-exp-dyadic-integral-value
                   lw-mellin-component-endpoint-precision)
     (lw-mellin-component-endpoint-precision-valid lw-mellin-basis-clearance-valid
      lw-complex-exp-clipped-primitive-cauchy))
   :nonlinearp nil :do-not-induct t)))

(defthm lw-mellin-moment-endpoint-precision-comparison
 (implies
  (and (rationalp cap) (<= 0 cap) (rationalp end) (<= 0 end)
       (rationalp cutpoint) (<= 0 cutpoint) (rationalp rate) (< 1 rate) (rationalp height)
       (rationalp error) (< 0 error) (rationalp delta) (< 0 delta)
       (<= delta (lw-mellin-moment-endpoint-precision cap end rate error)))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-mellin-moment-endpoint-value cap 0 end cutpoint rate height error)
    (lw-complex-exp-clipped-moment-primitive
     (lw-complex-laplace-point (lw-mellin-basis-clearance 1 rate) height) 0 end cutpoint delta))
   (* 1/16 error)))
 :hints (("Goal"
   :use (lw-mellin-moment-endpoint-precision-valid
         (:instance lw-mellin-basis-clearance-valid (kind 1) (sigma rate))
         (:instance lw-mepc-cauchy-budget
          (mass (+ end (/ (lw-mellin-basis-clearance 1 rate))))
          (tau (lw-mellin-moment-endpoint-precision cap end rate error))
          (clearance (lw-mellin-basis-clearance 1 rate)))
         (:instance lw-complex-exp-clipped-moment-primitive-cauchy
          (point (lw-mellin-basis-exponential-point 1 rate height)) (start 0) (bound end)
          (clearance (lw-mellin-basis-clearance 1 rate))
          (left-error (lw-mellin-moment-endpoint-precision cap end rate error)) (right-error delta))
         (:instance lw-complex-disk-enlarge
          (point (lw-complex-sub
           (lw-mellin-moment-endpoint-value cap 0 end cutpoint rate height error)
           (lw-complex-exp-clipped-moment-primitive
            (lw-complex-laplace-point (lw-mellin-basis-clearance 1 rate) height) 0 end cutpoint delta)))
          (radius (* 2 (+ end (/ (lw-mellin-basis-clearance 1 rate)))
                     (+ (lw-mellin-moment-endpoint-precision cap end rate error) delta)
                     (/ (lw-mellin-basis-clearance 1 rate))))
          (cap (* 1/16 error))))
   :in-theory (e/d (lw-mellin-moment-endpoint-value lw-complex-exp-dyadic-moment-integral-value
                   lw-mellin-moment-endpoint-precision)
     (lw-mellin-moment-endpoint-precision-valid lw-mellin-basis-clearance-valid
      lw-complex-exp-clipped-moment-primitive-cauchy lw-complex-exp-dyadic-moment-error-valid))
   :nonlinearp nil :do-not-induct t)))

(local (defthm lw-mepc-scale-difference
 (equal (lw-complex-sub (lw-complex-scale factor left) (lw-complex-scale factor right))
        (lw-complex-scale factor (lw-complex-sub left right)))
 :hints (("Goal" :in-theory (enable lw-complex-sub lw-complex-scale)))))

(local (defthm lw-mepc-add-differences
 (equal (lw-complex-sub (lw-complex-add left rest) (lw-complex-add right other))
        (lw-complex-add (lw-complex-sub left right) (lw-complex-sub rest other)))
 :hints (("Goal" :in-theory (enable lw-complex-sub lw-complex-add)))))

(local (defthm lw-mepc-subtract-differences
 (equal (lw-complex-sub
         (lw-complex-sub (lw-complex-scale factor left) rest)
         (lw-complex-sub (lw-complex-scale factor right) other))
        (lw-complex-add
         (lw-complex-scale factor (lw-complex-sub left right))
         (lw-complex-scale -1 (lw-complex-sub rest other))))
 :hints (("Goal" :in-theory (enable lw-complex-sub lw-complex-add lw-complex-scale)))
 :rule-classes nil))

(local (defthm lw-mepc-subtract-comparisons
 (implies (and (lw-complex-diskp (lw-complex-sub left right) radius)
               (lw-complex-diskp (lw-complex-sub rest other) other-radius)
               (rationalp factor))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-complex-sub (lw-complex-scale factor left) rest)
    (lw-complex-sub (lw-complex-scale factor right) other))
   (+ (* (abs factor) radius) other-radius)))
 :hints (("Goal"
   :use (lw-mepc-subtract-differences
         (:instance lw-complex-scale-disk (point (lw-complex-sub left right)))
         (:instance lw-complex-scale-disk (point (lw-complex-sub rest other)) (factor -1) (radius other-radius))
         (:instance lw-complex-add-disk
          (left (lw-complex-scale factor (lw-complex-sub left right)))
          (right (lw-complex-scale -1 (lw-complex-sub rest other)))
          (radius (* (abs factor) radius))))
   :in-theory (disable lw-complex-scale-disk lw-complex-add-disk)
   :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-mepc-log-data
 (implies (and (rationalp prime) (< 1 prime) (rationalp log-error) (< 0 log-error))
  (and (rationalp (car (lw-log-bounds prime log-error))) (<= 0 (car (lw-log-bounds prime log-error)))))
 :hints (("Goal"
   :use ((:instance lw-log-bounds-interval (value prime) (epsilon log-error))
         (:instance lw-log-bounds-lower-coarse (value prime) (epsilon log-error)))
   :in-theory (e/d (lw-intervalp) (lw-log-bounds-interval lw-log-bounds-lower-coarse))))
 :rule-classes nil))

(local (defthm lw-mepc-sub-self (equal (lw-complex-sub point point) (cons 0 0))
 :hints (("Goal" :in-theory (enable lw-complex-sub)))))

(local (defthm lw-mepc-zero-disk (lw-complex-diskp (cons 0 0) 0)
 :hints (("Goal" :in-theory (enable lw-complex-diskp lw-complexp lw-diskp)))))

(local (defthm lw-mepc-ramp-comparison
 (implies
  (and (rationalp cap) (<= 0 cap) (rationalp end) (<= 0 end) (rationalp rate) (< 1 rate) (rationalp height)
       (rationalp index) (< 1 index) (rationalp log-error) (< 0 log-error)
       (rationalp error) (< 0 error) (rationalp delta) (< 0 delta)
       (<= delta (lw-mellin-component-endpoint-precision 0 end rate error))
       (<= delta (lw-mellin-component-endpoint-precision 3 end rate error)))
  (lw-complex-diskp (lw-complex-sub (lw-mellin-ramp-endpoint cap 0 end (car (lw-log-bounds index log-error)) rate height index error) (lw-mellin-ramp-primitive end rate height index log-error delta)) (* (+ 1 (/ index)) 1/16 error)))
 :hints (("Goal"
  :use ((:instance lw-mepc-log-data (prime index))
        (:instance lw-mellin-component-endpoint-precision-comparison (kind 0) (cutpoint (car (lw-log-bounds index log-error))))
        (:instance lw-mellin-component-endpoint-precision-comparison (kind 3) (cutpoint (car (lw-log-bounds index log-error))))
        (:instance lw-mepc-subtract-comparisons
         (left (lw-mellin-component-endpoint-value 0 0 end (car (lw-log-bounds index log-error)) rate height error)) (right (lw-complex-exp-clipped-primitive (lw-complex-laplace-point (- rate 1) height) 0 end (car (lw-log-bounds index log-error)) delta))
         (rest (lw-mellin-component-endpoint-value 3 0 end (car (lw-log-bounds index log-error)) rate height error)) (other (lw-complex-exp-clipped-primitive (lw-complex-laplace-point rate height) 0 end (car (lw-log-bounds index log-error)) delta))
         (factor (/ index)) (radius (* 1/16 error)) (other-radius (* 1/16 error))))
  :in-theory (e/d (lw-mellin-ramp-endpoint lw-mellin-common-endpoint lw-mellin-ramp-primitive lw-mellin-basis-clearance)
                  (lw-mellin-component-endpoint-precision-comparison))
  :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-mepc-weighted-ramp-comparison
 (implies
  (and (rationalp cap) (<= 0 cap) (rationalp end) (<= 0 end) (rationalp rate) (< 1 rate) (rationalp height)
       (natp count) (< 1 count) (natp total) (rationalp model-error) (< 0 model-error)
       (rationalp primitive-error) (< 0 primitive-error) (rationalp error) (< 0 error)
       (rationalp delta) (< 0 delta)
       (<= delta (lw-mellin-component-endpoint-precision 0 end rate error))
       (<= delta (lw-mellin-component-endpoint-precision 3 end rate error)))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-scale (car (lw-mangoldt-bounds count primitive-error)) (lw-mellin-ramp-endpoint cap 0 end (car (lw-log-bounds count (lw-smoothed-ramp-log-error count total model-error))) rate height count error)) (lw-complex-scale (car (lw-mangoldt-bounds count primitive-error)) (lw-mellin-ramp-primitive end rate height count (lw-smoothed-ramp-log-error count total model-error) delta)))
   (* (car (lw-mangoldt-bounds count primitive-error)) (+ 1 (/ count)) 1/16 error)))
 :hints (("Goal"
  :use ((:instance lw-smoothed-ramp-log-error-adequate (index count) (error model-error))
        (:instance lw-mangoldt-lower-coarse (index count) (epsilon primitive-error))
        (:instance lw-mepc-ramp-comparison (index count) (log-error (lw-smoothed-ramp-log-error count total model-error)))
        (:instance lw-complex-scale-disk
         (factor (car (lw-mangoldt-bounds count primitive-error))) (point (lw-complex-sub (lw-mellin-ramp-endpoint cap 0 end (car (lw-log-bounds count (lw-smoothed-ramp-log-error count total model-error))) rate height count error) (lw-mellin-ramp-primitive end rate height count (lw-smoothed-ramp-log-error count total model-error) delta))) (radius (* (+ 1 (/ count)) 1/16 error))))
  :in-theory (disable lw-smoothed-ramp-log-error-adequate lw-mangoldt-lower-coarse lw-complex-scale-disk)
  :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(defthm lw-mellin-prime-endpoint-precision-comparison
 (implies
  (and (rationalp cap) (<= 0 cap) (rationalp end) (<= 0 end) (rationalp rate) (< 1 rate) (rationalp height)
       (natp count) (natp total) (rationalp model-error) (< 0 model-error)
       (rationalp primitive-error) (< 0 primitive-error) (rationalp error) (< 0 error)
       (rationalp delta) (< 0 delta)
       (<= delta (lw-mellin-component-endpoint-precision 0 end rate error))
       (<= delta (lw-mellin-component-endpoint-precision 3 end rate error)))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-mellin-prime-endpoint cap 0 end rate height count total model-error primitive-error error)
    (lw-mellin-prime-primitive end rate height count total model-error primitive-error delta))
   (* (lw-mellin-prime-endpoint-mass count primitive-error) 1/16 error)))
 :hints (("Goal"
   :induct (lw-mellin-prime-endpoint cap 0 end rate height count total model-error primitive-error error)
   :in-theory (enable (:induction lw-mellin-prime-endpoint) (:definition lw-mellin-prime-endpoint)
                      (:definition lw-mellin-prime-primitive) (:definition lw-mellin-prime-endpoint-mass)))
  (and stable-under-simplificationp
   '(:use (lw-mepc-weighted-ramp-comparison
           (:instance lw-complex-add-disk
            (left (lw-complex-sub (lw-complex-scale (car (lw-mangoldt-bounds count primitive-error)) (lw-mellin-ramp-endpoint cap 0 end (car (lw-log-bounds count (lw-smoothed-ramp-log-error count total model-error))) rate height count error)) (lw-complex-scale (car (lw-mangoldt-bounds count primitive-error)) (lw-mellin-ramp-primitive end rate height count (lw-smoothed-ramp-log-error count total model-error) delta))))
            (right (lw-complex-sub
             (lw-mellin-prime-endpoint cap 0 end rate height (- count 1) total model-error primitive-error error)
             (lw-mellin-prime-primitive end rate height (- count 1) total model-error primitive-error delta)))
            (radius (* (car (lw-mangoldt-bounds count primitive-error)) (+ 1 (/ count)) 1/16 error))
            (other-radius (* (lw-mellin-prime-endpoint-mass (- count 1) primitive-error) 1/16 error))))
     :in-theory (disable lw-mellin-prime-endpoint lw-mellin-prime-primitive
                         lw-mellin-prime-endpoint-mass lw-complex-add-disk)
     :nonlinearp nil :do-not-induct t))))

(local (defthm lw-mepc-family-difference
 (equal
  (lw-complex-sub
   (lw-complex-add (lw-complex-sub a b) (lw-complex-scale factor c))
   (lw-complex-add (lw-complex-sub x y) (lw-complex-scale factor z)))
  (lw-complex-add
   (lw-complex-add (lw-complex-sub a x) (lw-complex-scale -1 (lw-complex-sub b y)))
   (lw-complex-scale factor (lw-complex-sub c z))))
 :hints (("Goal" :in-theory (enable lw-complex-sub lw-complex-add lw-complex-scale)))
 :rule-classes nil))

(local (defthm lw-mepc-family-disk
 (implies (and (lw-complex-diskp (lw-complex-sub a x) radius)
               (lw-complex-diskp (lw-complex-sub b y) moment-radius)
               (lw-complex-diskp (lw-complex-sub c z) correction-radius) (rationalp factor))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-complex-add (lw-complex-sub a b) (lw-complex-scale factor c))
    (lw-complex-add (lw-complex-sub x y) (lw-complex-scale factor z)))
   (+ radius moment-radius (* (abs factor) correction-radius))))
 :hints (("Goal"
   :use (lw-mepc-family-difference
         (:instance lw-complex-scale-disk (point (lw-complex-sub b y)) (radius moment-radius) (factor -1))
         (:instance lw-complex-scale-disk (point (lw-complex-sub c z)) (radius correction-radius))
         (:instance lw-complex-add-disk
          (left (lw-complex-sub a x)) (right (lw-complex-scale -1 (lw-complex-sub b y)))
          (other-radius moment-radius))
         (:instance lw-complex-add-disk
          (left (lw-complex-add (lw-complex-sub a x) (lw-complex-scale -1 (lw-complex-sub b y))))
          (right (lw-complex-scale factor (lw-complex-sub c z)))
          (radius (+ radius moment-radius)) (other-radius (* (abs factor) correction-radius))))
   :in-theory (disable lw-complex-scale-disk lw-complex-add-disk) :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-mepc-parameters
 (implies (and (rationalp cap) (<= 0 cap) (rationalp model-error) (< 0 model-error))
  (and (natp (lw-log-signal-ramp-count cap))
       (rationalp (lw-signal-exponential-precision cap model-error))
       (< 0 (lw-signal-exponential-precision cap model-error))
       (rationalp (car (lw-euler-bounds (lw-signal-exponential-precision cap model-error))))))
 :hints (("Goal"
   :use (lw-log-signal-spatial-cap-valid
         (:instance lw-signal-count-natural (value (lw-log-signal-spatial-cap cap)))
         (:instance lw-signal-exponential-parameters (error model-error))
         (:instance lw-euler-bounds-interval (epsilon (lw-signal-exponential-precision cap model-error))))
   :in-theory (e/d (lw-log-signal-ramp-count lw-intervalp)
     (lw-log-signal-spatial-cap-valid lw-signal-exponential-parameters lw-euler-bounds-interval))
   :do-not-induct t))
 :rule-classes nil))

(defun lw-mellin-endpoint-precision-factor (cap model-error)
 (+ (lw-mellin-prime-endpoint-mass (lw-log-signal-ramp-count cap) (lw-signal-exponential-precision cap model-error))
    1 (abs (+ 1 (car (lw-euler-bounds (lw-signal-exponential-precision cap model-error)))))))

(local (in-theory (disable lw-mellin-endpoint-precision-factor)))

(defthm lw-mellin-endpoint-precision-factor-valid
 (implies (and (rationalp cap) (<= 0 cap) (rationalp model-error) (< 0 model-error))
  (and (rationalp (lw-mellin-endpoint-precision-factor cap model-error))
       (<= 1 (lw-mellin-endpoint-precision-factor cap model-error))
       (<= (lw-mellin-endpoint-precision-factor cap model-error) (lw-mellin-endpoint-family-factor cap))))
 :hints (("Goal"
  :use (lw-mepc-parameters
        (:instance lw-signal-exponential-parameters (error model-error))
        (:instance lw-mellin-prime-endpoint-mass-valid (count (lw-log-signal-ramp-count cap)) (primitive-error (lw-signal-exponential-precision cap model-error)))
        (:instance lw-mellin-prime-endpoint-mass-bound (count (lw-log-signal-ramp-count cap)) (primitive-error (lw-signal-exponential-precision cap model-error)))
        (:instance lw-euler-bounds-interval (epsilon (lw-signal-exponential-precision cap model-error)))
        (:instance lw-euler-bounds-coarse (epsilon (lw-signal-exponential-precision cap model-error))))
  :in-theory (e/d (lw-mellin-endpoint-precision-factor lw-mellin-endpoint-family-factor lw-intervalp)
    (lw-signal-exponential-parameters lw-mellin-prime-endpoint-mass-valid lw-mellin-prime-endpoint-mass-bound
     lw-euler-bounds-interval lw-euler-bounds-coarse lw-euler-bounds-overlap))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-mellin-frozen-endpoint-precision-comparison
 (implies
  (and (rationalp cap) (<= 0 cap) (rationalp end) (<= 0 end) (rationalp rate) (< 1 rate) (rationalp height)
       (rationalp model-error) (< 0 model-error) (rationalp error) (< 0 error)
       (rationalp delta) (< 0 delta)
       (<= delta (lw-mellin-component-endpoint-precision 0 end rate error))
       (<= delta (lw-mellin-component-endpoint-precision 3 end rate error))
       (<= delta (lw-mellin-moment-endpoint-precision cap end rate error)))
  (lw-complex-diskp (lw-complex-sub (lw-mellin-frozen-endpoint cap 0 end rate height model-error error) (lw-mellin-finite-primitive cap end rate height model-error delta))
                   (* (lw-mellin-endpoint-precision-factor cap model-error) 1/16 error)))
 :hints (("Goal"
  :use (lw-mepc-parameters lw-mellin-endpoint-precision-factor-valid
        (:instance lw-mellin-prime-endpoint-precision-comparison (count (lw-log-signal-ramp-count cap)) (total (lw-log-signal-ramp-count cap)) (primitive-error (lw-signal-exponential-precision cap model-error)))
        (:instance lw-mellin-moment-endpoint-precision-comparison (cutpoint 0))
        (:instance lw-mellin-component-endpoint-precision-comparison (kind 0) (cutpoint 0))
        (:instance lw-mepc-family-disk
         (a (lw-mellin-prime-endpoint cap 0 end rate height (lw-log-signal-ramp-count cap) (lw-log-signal-ramp-count cap) model-error (lw-signal-exponential-precision cap model-error) error))
         (x (lw-mellin-prime-primitive end rate height (lw-log-signal-ramp-count cap) (lw-log-signal-ramp-count cap) model-error (lw-signal-exponential-precision cap model-error) delta))
         (b (lw-mellin-moment-endpoint-value cap 0 end 0 rate height error))
         (y (lw-complex-exp-clipped-moment-primitive (lw-complex-laplace-point (- rate 1) height) 0 end 0 delta))
         (c (lw-mellin-component-endpoint-value 0 0 end 0 rate height error))
         (z (lw-complex-exp-clipped-primitive (lw-complex-laplace-point (- rate 1) height) 0 end 0 delta))
         (factor (+ 1 (car (lw-euler-bounds (lw-signal-exponential-precision cap model-error))))) (radius (* (lw-mellin-prime-endpoint-mass (lw-log-signal-ramp-count cap) (lw-signal-exponential-precision cap model-error)) 1/16 error))
         (moment-radius (* 1/16 error)) (correction-radius (* 1/16 error)))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub (lw-mellin-frozen-endpoint cap 0 end rate height model-error error) (lw-mellin-finite-primitive cap end rate height model-error delta)))
         (radius (+ (* (lw-mellin-prime-endpoint-mass (lw-log-signal-ramp-count cap) (lw-signal-exponential-precision cap model-error)) 1/16 error) (* 1/16 error) (* (abs (+ 1 (car (lw-euler-bounds (lw-signal-exponential-precision cap model-error))))) 1/16 error)))
         (cap (* (lw-mellin-endpoint-precision-factor cap model-error) 1/16 error))))
  :in-theory
   (e/d (lw-mellin-frozen-endpoint lw-mellin-finite-primitive lw-mellin-common-endpoint
         lw-mellin-basis-clearance lw-mellin-endpoint-precision-factor)
     (lw-mellin-prime-endpoint-precision-comparison lw-mellin-moment-endpoint-precision-comparison
      lw-mellin-component-endpoint-precision-comparison lw-mellin-endpoint-precision-factor-valid))
  :nonlinearp nil :do-not-induct t)))

(defun lw-mellin-dirichlet-precision (cap end rate height component-error error)
 (min (lw-mellin-component-endpoint-precision 0 end rate component-error)
  (min (lw-mellin-component-endpoint-precision 3 end rate component-error)
   (min (lw-mellin-moment-endpoint-precision cap end rate component-error)
        (lw-complex-log-ramp-family-precision rate height (lw-log-signal-ramp-count cap) error)))))

(local (in-theory (disable lw-mellin-dirichlet-precision)))

(defthm lw-mellin-dirichlet-precision-valid
 (implies
  (and (rationalp cap) (<= 0 cap) (rationalp end) (<= 0 end) (rationalp rate) (< 1 rate) (rationalp height)
       (rationalp component-error) (< 0 component-error) (rationalp error) (< 0 error))
  (let ((delta (lw-mellin-dirichlet-precision cap end rate height component-error error)))
   (and (rationalp delta) (< 0 delta) (<= delta 1)
        (<= delta (lw-mellin-component-endpoint-precision 0 end rate component-error))
        (<= delta (lw-mellin-component-endpoint-precision 3 end rate component-error))
        (<= delta (lw-mellin-moment-endpoint-precision cap end rate component-error))
        (<= delta (lw-complex-log-ramp-family-precision rate height (lw-log-signal-ramp-count cap) error)))))
 :hints (("Goal"
  :use ((:instance lw-signal-count-natural (value (lw-log-signal-spatial-cap cap)))
        (:instance lw-mellin-component-endpoint-precision-valid (kind 0) (error component-error))
        (:instance lw-mellin-component-endpoint-precision-valid (kind 3) (error component-error))
        (:instance lw-mellin-moment-endpoint-precision-valid (error component-error))
        (:instance lw-complex-log-ramp-family-precision-valid (count (lw-log-signal-ramp-count cap))))
  :in-theory (e/d (lw-mellin-dirichlet-precision lw-log-signal-ramp-count)
    (lw-mellin-component-endpoint-precision-valid lw-mellin-moment-endpoint-precision-valid
     lw-complex-log-ramp-family-precision-valid))
  :nonlinearp nil :do-not-induct t)))




