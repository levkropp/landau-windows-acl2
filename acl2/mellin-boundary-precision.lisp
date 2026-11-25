(in-package "ACL2")

(include-book "mellin-dirichlet-comparison")

; Precision stability of the retained upper boundary. Primitive Cauchy
; bounds apply because the lower boundary at zero is precision-independent.

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

(local (defthm lw-mbp-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-mbp-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-mbp-zero-times (equal (* 0 a) 0)))

(local (defthm lw-mbp-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-mbp-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-mbp-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-mbp-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-mbp-left-commutes)))))

(local (defthm lw-mbp-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-mbp-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-mbp-times-negative (a b) (b a)))
                 :in-theory (disable lw-mbp-times-negative)))))

(local (defthm lw-mbp-point-form
 (implies (and (rationalp rate) (rationalp height))
  (equal (lw-mellin-basis-exponential-point kind rate height)
         (lw-complex-laplace-point (lw-mellin-basis-clearance kind rate) height)))
 :hints (("Goal" :in-theory (enable lw-mellin-basis-exponential-point lw-mellin-basis-clearance lw-complex-laplace-point)))))

(local (defthm lw-mbp-cancel-lower
 (equal (lw-complex-sub (lw-complex-sub a b) (lw-complex-sub a c))
        (lw-complex-sub c b))
 :hints (("Goal" :in-theory (enable lw-complex-sub)))))

(defthm lw-complex-exp-boundary-cauchy
 (implies
  (and (lw-complexp point) (rationalp value)
       (rationalp clearance) (< 0 clearance)
       (<= (* clearance clearance) (lw-complex-norm-square point))
       (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-exp-boundary point value left-error)
                   (lw-complex-exp-boundary point value right-error))
   (* 2 (+ left-error right-error) (/ clearance))))
 :hints (("Goal"
  :use ((:instance lw-complex-exp-boundaries-at-zero (error left-error))
        (:instance lw-complex-exp-boundaries-at-zero (error right-error))
        (:instance lw-complex-exp-boundaries-rational (error left-error))
        (:instance lw-complex-exp-boundaries-rational (error right-error))
        (:instance lw-complex-exp-primitive-cauchy (start 0) (end value))
        (:instance lw-complex-difference-symmetric
         (left (lw-complex-exp-boundary point value right-error))
         (right (lw-complex-exp-boundary point value left-error))
         (radius (* 2 (+ left-error right-error) (/ clearance)))))
  :in-theory (e/d (lw-complex-exp-primitive-boundaries)
    (lw-complex-exp-boundaries-at-zero lw-complex-exp-boundaries-rational lw-complex-exp-primitive-cauchy))
  :do-not-induct t)))

(defthm lw-complex-exp-moment-boundary-cauchy
 (implies
  (and (lw-complexp point) (rationalp value) (<= 0 value)
       (rationalp clearance) (< 0 clearance)
       (<= (* clearance clearance) (lw-complex-norm-square point))
       (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-exp-moment-boundary point value left-error)
                   (lw-complex-exp-moment-boundary point value right-error))
   (* 2 (+ value (/ clearance)) (+ left-error right-error) (/ clearance))))
 :hints (("Goal"
  :use ((:instance lw-complex-exp-boundaries-at-zero (error left-error))
        (:instance lw-complex-exp-boundaries-at-zero (error right-error))
        (:instance lw-complex-exp-boundaries-rational (error left-error))
        (:instance lw-complex-exp-boundaries-rational (error right-error))
        (:instance lw-complex-exp-moment-primitive-cauchy (start 0) (end value) (bound value))
        (:instance lw-complex-difference-symmetric
         (left (lw-complex-exp-moment-boundary point value right-error))
         (right (lw-complex-exp-moment-boundary point value left-error))
         (radius (* 2 (+ value (/ clearance)) (+ left-error right-error) (/ clearance)))))
  :in-theory (e/d (lw-complex-exp-moment-primitive-boundaries)
    (lw-complex-exp-boundaries-at-zero lw-complex-exp-boundaries-rational lw-complex-exp-moment-primitive-cauchy))
  :do-not-induct t)))

(local (defthm lw-mbp-nonnegative-product
 (implies (and (rationalp a) (<= 0 a) (rationalp b) (<= 0 b)) (<= 0 (* a b)))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-mbp-two-precision-budget
 (implies
  (and (rationalp mass) (<= 0 mass) (rationalp tau)
       (rationalp left-error) (<= left-error tau) (rationalp right-error) (<= right-error tau)
       (rationalp clearance) (< 0 clearance) (rationalp error)
       (<= (* 4 mass tau (/ clearance)) (* 1/16 error)))
  (<= (* 2 mass (+ left-error right-error) (/ clearance)) (* 1/16 error)))
 :hints (("Goal"
  :use ((:instance lw-mbp-nonnegative-product (a mass) (b (/ clearance)))
        (:instance lw-mbp-multiply-order
         (a (+ left-error right-error)) (b (* 2 tau)) (factor (* 2 mass (/ clearance)))))
  :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(defthm lw-mellin-component-boundary-precision-comparison
 (implies
  (and (rationalp end) (<= 0 end) (rationalp cutpoint) (rationalp rate) (< 1 rate) (rationalp height)
       (rationalp error) (< 0 error)
       (rationalp left-error) (< 0 left-error) (<= left-error (lw-mellin-component-endpoint-precision kind end rate error))
       (rationalp right-error) (< 0 right-error) (<= right-error (lw-mellin-component-endpoint-precision kind end rate error)))
  (lw-complex-diskp (lw-complex-sub (lw-complex-exp-boundary (lw-complex-laplace-point (lw-mellin-basis-clearance kind rate) height) (max end cutpoint) left-error)
                   (lw-complex-exp-boundary (lw-complex-laplace-point (lw-mellin-basis-clearance kind rate) height) (max end cutpoint) right-error)) (* 1/16 error)))
 :hints (("Goal"
  :use (lw-mellin-component-endpoint-precision-valid
        (:instance lw-mellin-basis-clearance-valid (sigma rate))
        (:instance lw-mbp-two-precision-budget (mass 1) (clearance (lw-mellin-basis-clearance kind rate)) (tau (lw-mellin-component-endpoint-precision kind end rate error)))
        (:instance lw-complex-exp-boundary-cauchy
         (point (lw-mellin-basis-exponential-point kind rate height)) (value (max end cutpoint)) (clearance (lw-mellin-basis-clearance kind rate)))
        (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-exp-boundary (lw-complex-laplace-point (lw-mellin-basis-clearance kind rate) height) (max end cutpoint) left-error)
                   (lw-complex-exp-boundary (lw-complex-laplace-point (lw-mellin-basis-clearance kind rate) height) (max end cutpoint) right-error)))
         (radius (* 2 (+ left-error right-error) (/ (lw-mellin-basis-clearance kind rate)))) (cap (* 1/16 error))))
  :in-theory (disable lw-mellin-component-endpoint-precision-valid lw-mellin-basis-clearance-valid
                      lw-complex-exp-boundary-cauchy)
  :nonlinearp nil :do-not-induct t)))

(defthm lw-mellin-moment-boundary-precision-comparison
 (implies
  (and (rationalp cap) (<= 0 cap) (rationalp end) (<= 0 end)
       (rationalp rate) (< 1 rate) (rationalp height) (rationalp error) (< 0 error)
       (rationalp left-error) (< 0 left-error) (<= left-error (lw-mellin-moment-endpoint-precision cap end rate error))
       (rationalp right-error) (< 0 right-error) (<= right-error (lw-mellin-moment-endpoint-precision cap end rate error)))
  (lw-complex-diskp (lw-complex-sub (lw-complex-exp-moment-boundary (lw-complex-laplace-point (lw-mellin-basis-clearance 1 rate) height) end left-error)
                   (lw-complex-exp-moment-boundary (lw-complex-laplace-point (lw-mellin-basis-clearance 1 rate) height) end right-error)) (* 1/16 error)))
 :hints (("Goal"
  :use (lw-mellin-moment-endpoint-precision-valid
        (:instance lw-mellin-basis-clearance-valid (kind 1) (sigma rate))
        (:instance lw-mbp-two-precision-budget
         (mass (+ end (/ (lw-mellin-basis-clearance 1 rate)))) (clearance (lw-mellin-basis-clearance 1 rate)) (tau (lw-mellin-moment-endpoint-precision cap end rate error)))
        (:instance lw-complex-exp-moment-boundary-cauchy
         (point (lw-mellin-basis-exponential-point 1 rate height)) (value end) (clearance (lw-mellin-basis-clearance 1 rate)))
        (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-exp-moment-boundary (lw-complex-laplace-point (lw-mellin-basis-clearance 1 rate) height) end left-error)
                   (lw-complex-exp-moment-boundary (lw-complex-laplace-point (lw-mellin-basis-clearance 1 rate) height) end right-error)))
         (radius (* 2 (+ end (/ (lw-mellin-basis-clearance 1 rate))) (+ left-error right-error) (/ (lw-mellin-basis-clearance 1 rate)))) (cap (* 1/16 error))))
  :in-theory (disable lw-mellin-moment-endpoint-precision-valid lw-mellin-basis-clearance-valid
                      lw-complex-exp-moment-boundary-cauchy)
  :nonlinearp nil :do-not-induct t)))

(local (in-theory (disable lw-mellin-ramp-boundary lw-mellin-prime-boundary)))

(local (defthm lw-mbp-scale-difference
 (equal (lw-complex-sub (lw-complex-scale factor left) (lw-complex-scale factor right))
        (lw-complex-scale factor (lw-complex-sub left right)))
 :hints (("Goal" :in-theory (enable lw-complex-sub lw-complex-scale)))))

(local (defthm lw-mbp-add-differences
 (equal (lw-complex-sub (lw-complex-add left rest) (lw-complex-add right other))
        (lw-complex-add (lw-complex-sub left right) (lw-complex-sub rest other)))
 :hints (("Goal" :in-theory (enable lw-complex-sub lw-complex-add)))))

(local (defthm lw-mbp-subtract-differences
 (equal (lw-complex-sub
         (lw-complex-sub (lw-complex-scale factor left) rest)
         (lw-complex-sub (lw-complex-scale factor right) other))
        (lw-complex-add
         (lw-complex-scale factor (lw-complex-sub left right))
         (lw-complex-scale -1 (lw-complex-sub rest other))))
 :hints (("Goal" :in-theory (enable lw-complex-sub lw-complex-add lw-complex-scale)))
 :rule-classes nil))

(local (defthm lw-mbp-subtract-comparisons
 (implies (and (lw-complex-diskp (lw-complex-sub left right) radius)
               (lw-complex-diskp (lw-complex-sub rest other) other-radius)
               (rationalp factor))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-complex-sub (lw-complex-scale factor left) rest)
    (lw-complex-sub (lw-complex-scale factor right) other))
   (+ (* (abs factor) radius) other-radius)))
 :hints (("Goal"
   :use (lw-mbp-subtract-differences
         (:instance lw-complex-scale-disk (point (lw-complex-sub left right)))
         (:instance lw-complex-scale-disk (point (lw-complex-sub rest other)) (factor -1) (radius other-radius))
         (:instance lw-complex-add-disk
          (left (lw-complex-scale factor (lw-complex-sub left right)))
          (right (lw-complex-scale -1 (lw-complex-sub rest other)))
          (radius (* (abs factor) radius))))
   :in-theory (disable lw-complex-scale-disk lw-complex-add-disk)
   :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-mbp-log-data
 (implies (and (rationalp prime) (< 1 prime) (rationalp log-error) (< 0 log-error))
  (and (rationalp (car (lw-log-bounds prime log-error))) (<= 0 (car (lw-log-bounds prime log-error)))))
 :hints (("Goal"
   :use ((:instance lw-log-bounds-interval (value prime) (epsilon log-error))
         (:instance lw-log-bounds-lower-coarse (value prime) (epsilon log-error)))
   :in-theory (e/d (lw-intervalp) (lw-log-bounds-interval lw-log-bounds-lower-coarse))))
 :rule-classes nil))

(local (defthm lw-mbp-sub-self (equal (lw-complex-sub point point) (cons 0 0))
 :hints (("Goal" :in-theory (enable lw-complex-sub)))))

(local (defthm lw-mbp-zero-disk (lw-complex-diskp (cons 0 0) 0)
 :hints (("Goal" :in-theory (enable lw-complex-diskp lw-complexp lw-diskp)))))

(local (defthm lw-mbp-ramp-boundary-comparison
 (implies
  (and (rationalp end) (<= 0 end) (rationalp rate) (< 1 rate) (rationalp height)
       (rationalp error) (< 0 error)
       (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error)
       (<= left-error (lw-mellin-component-endpoint-precision 0 end rate error))
       (<= right-error (lw-mellin-component-endpoint-precision 0 end rate error))
       (<= left-error (lw-mellin-component-endpoint-precision 3 end rate error))
       (<= right-error (lw-mellin-component-endpoint-precision 3 end rate error)) (rationalp index) (< 1 index) (rationalp log-error) (< 0 log-error))
  (lw-complex-diskp (lw-complex-sub (lw-mellin-ramp-boundary end rate height index log-error left-error) (lw-mellin-ramp-boundary end rate height index log-error right-error)) (* (+ 1 (/ index)) 1/16 error)))
 :hints (("Goal"
  :use ((:instance lw-mbp-log-data (prime index))
        (:instance lw-mellin-component-boundary-precision-comparison (kind 0) (cutpoint (car (lw-log-bounds index log-error))))
        (:instance lw-mellin-component-boundary-precision-comparison (kind 3) (cutpoint (car (lw-log-bounds index log-error))))
        (:instance lw-mbp-subtract-comparisons
         (left (lw-complex-exp-boundary (lw-complex-laplace-point (- rate 1) height) (max end (car (lw-log-bounds index log-error))) left-error)) (right (lw-complex-exp-boundary (lw-complex-laplace-point (- rate 1) height) (max end (car (lw-log-bounds index log-error))) right-error))
         (rest (lw-complex-exp-boundary (lw-complex-laplace-point rate height) (max end (car (lw-log-bounds index log-error))) left-error)) (other (lw-complex-exp-boundary (lw-complex-laplace-point rate height) (max end (car (lw-log-bounds index log-error))) right-error))
         (factor (/ index)) (radius (* 1/16 error)) (other-radius (* 1/16 error))))
  :in-theory (e/d (lw-mellin-ramp-boundary lw-mellin-basis-clearance)
    (lw-mellin-component-boundary-precision-comparison))
  :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-mbp-weighted-boundary-comparison
 (implies
  (and (rationalp end) (<= 0 end) (rationalp rate) (< 1 rate) (rationalp height)
       (rationalp error) (< 0 error)
       (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error)
       (<= left-error (lw-mellin-component-endpoint-precision 0 end rate error))
       (<= right-error (lw-mellin-component-endpoint-precision 0 end rate error))
       (<= left-error (lw-mellin-component-endpoint-precision 3 end rate error))
       (<= right-error (lw-mellin-component-endpoint-precision 3 end rate error))
       (natp count) (< 1 count) (natp total) (rationalp model-error) (< 0 model-error)
       (rationalp primitive-error) (< 0 primitive-error))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-scale (car (lw-mangoldt-bounds count primitive-error)) (lw-mellin-ramp-boundary end rate height count (lw-smoothed-ramp-log-error count total model-error) left-error))
                   (lw-complex-scale (car (lw-mangoldt-bounds count primitive-error)) (lw-mellin-ramp-boundary end rate height count (lw-smoothed-ramp-log-error count total model-error) right-error)))
   (* (car (lw-mangoldt-bounds count primitive-error)) (+ 1 (/ count)) 1/16 error)))
 :hints (("Goal"
  :use ((:instance lw-smoothed-ramp-log-error-adequate (index count) (error model-error))
        (:instance lw-mangoldt-lower-coarse (index count) (epsilon primitive-error))
        (:instance lw-mbp-ramp-boundary-comparison (index count) (log-error (lw-smoothed-ramp-log-error count total model-error)))
        (:instance lw-complex-scale-disk (factor (car (lw-mangoldt-bounds count primitive-error)))
         (point (lw-complex-sub (lw-mellin-ramp-boundary end rate height count (lw-smoothed-ramp-log-error count total model-error) left-error) (lw-mellin-ramp-boundary end rate height count (lw-smoothed-ramp-log-error count total model-error) right-error)))
         (radius (* (+ 1 (/ count)) 1/16 error))))
  :in-theory (disable lw-smoothed-ramp-log-error-adequate lw-mangoldt-lower-coarse lw-complex-scale-disk)
  :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(defthm lw-mellin-prime-boundary-precision-comparison
 (implies
  (and (rationalp end) (<= 0 end) (rationalp rate) (< 1 rate) (rationalp height)
       (rationalp error) (< 0 error)
       (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error)
       (<= left-error (lw-mellin-component-endpoint-precision 0 end rate error))
       (<= right-error (lw-mellin-component-endpoint-precision 0 end rate error))
       (<= left-error (lw-mellin-component-endpoint-precision 3 end rate error))
       (<= right-error (lw-mellin-component-endpoint-precision 3 end rate error)) (natp count) (natp total)
       (rationalp model-error) (< 0 model-error) (rationalp primitive-error) (< 0 primitive-error))
  (lw-complex-diskp (lw-complex-sub (lw-mellin-prime-boundary end rate height count total model-error primitive-error left-error) (lw-mellin-prime-boundary end rate height count total model-error primitive-error right-error))
                   (* (lw-mellin-prime-endpoint-mass count primitive-error) 1/16 error)))
 :hints (("Goal"
  :induct (lw-mellin-prime-boundary end rate height count total model-error primitive-error left-error)
  :in-theory (enable (:induction lw-mellin-prime-boundary) (:definition lw-mellin-prime-boundary)
                     (:definition lw-mellin-prime-endpoint-mass)))
  (and stable-under-simplificationp
   '(:use (lw-mbp-weighted-boundary-comparison
           (:instance lw-complex-add-disk
            (left (lw-complex-sub (lw-complex-scale (car (lw-mangoldt-bounds count primitive-error)) (lw-mellin-ramp-boundary end rate height count (lw-smoothed-ramp-log-error count total model-error) left-error))
                                  (lw-complex-scale (car (lw-mangoldt-bounds count primitive-error)) (lw-mellin-ramp-boundary end rate height count (lw-smoothed-ramp-log-error count total model-error) right-error))))
            (right (lw-complex-sub (lw-mellin-prime-boundary end rate height (- count 1) total model-error primitive-error left-error) (lw-mellin-prime-boundary end rate height (- count 1) total model-error primitive-error right-error)))
            (radius (* (car (lw-mangoldt-bounds count primitive-error)) (+ 1 (/ count)) 1/16 error))
            (other-radius (* (lw-mellin-prime-endpoint-mass (- count 1) primitive-error) 1/16 error))))
     :in-theory (disable lw-mellin-prime-boundary lw-mellin-prime-endpoint-mass lw-complex-add-disk)
     :nonlinearp nil :do-not-induct t))))


(local (defthm lw-mbp-family-difference
 (equal
  (lw-complex-sub
   (lw-complex-add (lw-complex-sub a b) (lw-complex-scale factor c))
   (lw-complex-add (lw-complex-sub x y) (lw-complex-scale factor z)))
  (lw-complex-add
   (lw-complex-add (lw-complex-sub a x) (lw-complex-scale -1 (lw-complex-sub b y)))
   (lw-complex-scale factor (lw-complex-sub c z))))
 :hints (("Goal" :in-theory (enable lw-complex-sub lw-complex-add lw-complex-scale)))
 :rule-classes nil))

(local (defthm lw-mbp-family-disk
 (implies (and (lw-complex-diskp (lw-complex-sub a x) radius)
               (lw-complex-diskp (lw-complex-sub b y) moment-radius)
               (lw-complex-diskp (lw-complex-sub c z) correction-radius) (rationalp factor))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-complex-add (lw-complex-sub a b) (lw-complex-scale factor c))
    (lw-complex-add (lw-complex-sub x y) (lw-complex-scale factor z)))
   (+ radius moment-radius (* (abs factor) correction-radius))))
 :hints (("Goal"
   :use (lw-mbp-family-difference
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

(local (defthm lw-mbp-parameters
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

(defthm lw-mellin-finite-boundary-precision-comparison
 (implies
  (and (rationalp cap) (<= 0 cap) (rationalp end) (<= 0 end) (rationalp rate) (< 1 rate) (rationalp height)
       (rationalp error) (< 0 error)
       (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error)
       (<= left-error (lw-mellin-component-endpoint-precision 0 end rate error))
       (<= right-error (lw-mellin-component-endpoint-precision 0 end rate error))
       (<= left-error (lw-mellin-component-endpoint-precision 3 end rate error))
       (<= right-error (lw-mellin-component-endpoint-precision 3 end rate error))
       (rationalp model-error) (< 0 model-error)
       (<= left-error (lw-mellin-moment-endpoint-precision cap end rate error))
       (<= right-error (lw-mellin-moment-endpoint-precision cap end rate error)))
  (lw-complex-diskp (lw-complex-sub (lw-mellin-finite-boundary cap end rate height model-error left-error) (lw-mellin-finite-boundary cap end rate height model-error right-error))
                   (* (lw-mellin-endpoint-precision-factor cap model-error) 1/16 error)))
 :hints (("Goal"
  :use (lw-mbp-parameters lw-mellin-endpoint-precision-factor-valid
        (:instance lw-mellin-prime-boundary-precision-comparison
         (count (lw-log-signal-ramp-count cap)) (total (lw-log-signal-ramp-count cap)) (primitive-error (lw-signal-exponential-precision cap model-error)))
        lw-mellin-moment-boundary-precision-comparison
        (:instance lw-mellin-component-boundary-precision-comparison (kind 0) (cutpoint 0))
        (:instance lw-mbp-family-disk
         (a (lw-mellin-prime-boundary end rate height (lw-log-signal-ramp-count cap) (lw-log-signal-ramp-count cap) model-error (lw-signal-exponential-precision cap model-error) left-error)) (x (lw-mellin-prime-boundary end rate height (lw-log-signal-ramp-count cap) (lw-log-signal-ramp-count cap) model-error (lw-signal-exponential-precision cap model-error) right-error))
         (b (lw-complex-exp-moment-boundary (lw-complex-laplace-point (- rate 1) height) end left-error)) (y (lw-complex-exp-moment-boundary (lw-complex-laplace-point (- rate 1) height) end right-error))
         (c (lw-complex-exp-boundary (lw-complex-laplace-point (- rate 1) height) end left-error)) (z (lw-complex-exp-boundary (lw-complex-laplace-point (- rate 1) height) end right-error)) (factor (+ 1 (car (lw-euler-bounds (lw-signal-exponential-precision cap model-error)))))
         (radius (* (lw-mellin-prime-endpoint-mass (lw-log-signal-ramp-count cap) (lw-signal-exponential-precision cap model-error)) 1/16 error)) (moment-radius (* 1/16 error)) (correction-radius (* 1/16 error)))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub (lw-mellin-finite-boundary cap end rate height model-error left-error)
                                (lw-mellin-finite-boundary cap end rate height model-error right-error)))
         (radius (+ (* (lw-mellin-prime-endpoint-mass (lw-log-signal-ramp-count cap) (lw-signal-exponential-precision cap model-error)) 1/16 error)
                    (* 1/16 error)
                    (* (abs (+ 1 (car (lw-euler-bounds (lw-signal-exponential-precision cap model-error))))) 1/16 error)))
         (cap (* (lw-mellin-endpoint-precision-factor cap model-error) 1/16 error))))
  :in-theory (e/d (lw-mellin-finite-boundary lw-mellin-basis-clearance lw-mellin-endpoint-precision-factor)
    (lw-mellin-prime-boundary-precision-comparison lw-mellin-moment-boundary-precision-comparison
     lw-mellin-component-boundary-precision-comparison lw-mellin-endpoint-precision-factor-valid))
  :nonlinearp nil :do-not-induct t)))

(local (in-theory (disable lw-mellin-endpoint-request lw-mellin-endpoint-cost
 lw-mellin-endpoint-family-factor lw-mellin-endpoint-precision-factor
 lw-mellin-dirichlet-precision lw-mellin-dirichlet-node-precision
 lw-mellin-computed-dirichlet-boundary)))

(local (defthm lw-mbp-cost-dominates
 (implies (and (rationalp cap) (<= 0 cap))
          (<= (lw-mellin-endpoint-family-factor cap) (lw-mellin-endpoint-cost cap)))
 :hints (("Goal"
  :use (lw-mellin-endpoint-cost-valid
        (:instance lw-kernel-spatial-parameters (sigma 0) (step 1))
        (:instance lw-complex-exp-uniform-cap-data (argument-cap cap))
        (:instance lw-mbp-nonnegative-product (a cap) (b (lw-kernel-spatial-cap cap 1)))
        (:instance lw-mbp-nonnegative-product
         (a (lw-mellin-endpoint-family-factor cap)) (b (+ 1 (* 2 (lw-complex-exp-uniform-cap cap)))))
        (:instance lw-mbp-nonnegative-product
         (a cap) (b (* (lw-mellin-endpoint-family-factor cap) (+ 1 (* 2 (lw-complex-exp-uniform-cap cap)))))))
  :in-theory (e/d (lw-mellin-endpoint-cost)
    (lw-mellin-endpoint-cost-valid lw-kernel-spatial-parameters lw-complex-exp-uniform-cap-data))
  :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-mbp-precision-budget
 (implies (and (rationalp cap) (<= 0 cap) (rationalp error) (< 0 error))
  (<= (* (lw-mellin-endpoint-precision-factor cap (lw-mellin-endpoint-request cap error)) 1/16 (lw-mellin-endpoint-request cap error)) (* 1/256 error)))
 :hints (("Goal"
  :use (lw-mellin-endpoint-request-valid lw-mellin-endpoint-cost-valid lw-mbp-cost-dominates
        (:instance lw-mellin-endpoint-precision-factor-valid (model-error (lw-mellin-endpoint-request cap error)))
        (:instance lw-mbp-multiply-order
         (a (lw-mellin-endpoint-precision-factor cap (lw-mellin-endpoint-request cap error))) (b (lw-mellin-endpoint-cost cap))
         (factor (* 1/16 (lw-mellin-endpoint-request cap error)))))
  :in-theory (disable lw-mellin-endpoint-request-valid lw-mellin-endpoint-cost-valid
                      lw-mellin-endpoint-precision-factor-valid)
  :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(defthm lw-mellin-computed-boundary-precision-stable
 (implies
  (and (rationalp cap) (<= 0 cap) (rationalp rate) (< 1 rate) (rationalp height)
       (rationalp error) (< 0 error) (rationalp delta) (< 0 delta) (<= delta (lw-mellin-dirichlet-node-precision cap rate height error)))
  (lw-complex-diskp (lw-complex-sub (lw-mellin-computed-dirichlet-boundary cap rate height error)
                   (lw-mellin-finite-boundary cap cap rate height (lw-mellin-endpoint-request cap error) delta)) (* 1/256 error)))
 :hints (("Goal"
  :use (lw-mellin-endpoint-request-valid lw-mbp-precision-budget
        (:instance lw-mellin-dirichlet-precision-valid
         (end cap) (component-error (lw-mellin-endpoint-request cap error)))
        (:instance lw-mellin-finite-boundary-precision-comparison
         (end cap) (model-error (lw-mellin-endpoint-request cap error)) (error (lw-mellin-endpoint-request cap error)) (left-error (lw-mellin-dirichlet-node-precision cap rate height error)) (right-error delta))
        (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-mellin-computed-dirichlet-boundary cap rate height error)
                   (lw-mellin-finite-boundary cap cap rate height (lw-mellin-endpoint-request cap error) delta)))
         (radius (* (lw-mellin-endpoint-precision-factor cap (lw-mellin-endpoint-request cap error)) 1/16 (lw-mellin-endpoint-request cap error)))
         (cap (* 1/256 error))))
  :in-theory (e/d (lw-mellin-computed-dirichlet-boundary lw-mellin-dirichlet-node-precision)
    (lw-mellin-endpoint-request-valid lw-mellin-dirichlet-precision-valid
     lw-mellin-finite-boundary-precision-comparison))
  :nonlinearp nil :do-not-induct t)))
