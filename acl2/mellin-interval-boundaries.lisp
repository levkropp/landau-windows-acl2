(in-package "ACL2")

(include-book "mellin-interval-precision")

(include-book "mellin-refined-endpoints")

; A common-node primitive on a general interval. Fixed coefficients and
; cutpoints give exactly the difference of the existing upper boundaries.

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

(local (defthm lw-mib-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-mib-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-mib-zero-times (equal (* 0 a) 0)))

(local (defthm lw-mib-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-mib-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-mib-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-mib-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-mib-left-commutes)))))

(local (defthm lw-mib-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-mib-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-mib-times-negative (a b) (b a)))
                 :in-theory (disable lw-mib-times-negative)))))

(local (defthm lw-mib-point-form
 (implies (and (rationalp rate) (rationalp height))
  (equal (lw-mellin-basis-exponential-point kind rate height)
         (lw-complex-laplace-point (lw-mellin-basis-clearance kind rate) height)))
 :hints (("Goal" :in-theory (enable lw-mellin-basis-exponential-point lw-mellin-basis-clearance lw-complex-laplace-point)))))

(defun lw-mellin-ramp-interval-primitive (start length rate height index log-error delta)
 (let ((cutpoint (car (lw-log-bounds index log-error))))
  (lw-complex-sub
   (lw-complex-scale (/ index)
    (lw-complex-exp-clipped-primitive (lw-complex-laplace-point (- rate 1) height) start (+ start length) cutpoint delta))
   (lw-complex-exp-clipped-primitive (lw-complex-laplace-point rate height) start (+ start length) cutpoint delta))))

(defun lw-mellin-prime-interval-primitive (start length rate height count total model-error primitive-error delta)
 (declare (xargs :measure (nfix count)))
 (if (or (zp count) (equal count 1)) (cons 0 0)
  (lw-complex-add
   (lw-complex-scale (car (lw-mangoldt-bounds count primitive-error))
    (lw-mellin-ramp-interval-primitive start length rate height count (lw-smoothed-ramp-log-error count total model-error) delta))
   (lw-mellin-prime-interval-primitive start length rate height (- count 1) total model-error primitive-error delta))))

(defun lw-mellin-finite-interval-primitive (cap start length rate height model-error delta)
 (lw-complex-add
  (lw-complex-sub
   (lw-mellin-prime-interval-primitive start length rate height (lw-log-signal-ramp-count cap) (lw-log-signal-ramp-count cap) model-error (lw-signal-exponential-precision cap model-error) delta)
   (lw-complex-exp-clipped-moment-primitive (lw-complex-laplace-point (- rate 1) height) start (+ start length) 0 delta))
  (lw-complex-scale (+ 1 (car (lw-euler-bounds (lw-signal-exponential-precision cap model-error)))) (lw-complex-exp-clipped-primitive (lw-complex-laplace-point (- rate 1) height) start (+ start length) 0 delta))))

(local (in-theory (disable lw-mellin-ramp-interval-primitive
 lw-mellin-prime-interval-primitive lw-mellin-finite-interval-primitive
 lw-mellin-refined-endpoint lw-mellin-ramp-boundary)))

(defthm lw-mellin-ramp-interval-boundary
 (equal
  (lw-mellin-ramp-interval-primitive start length rate height index log-error delta)
  (lw-complex-sub
   (lw-mellin-ramp-boundary start rate height index log-error delta)
   (lw-mellin-ramp-boundary (+ start length) rate height index log-error delta)))
 :hints (("Goal"
  :in-theory (enable lw-mellin-ramp-interval-primitive lw-mellin-ramp-boundary
                     lw-complex-exp-clipped-primitive-boundaries
                     lw-complex-sub lw-complex-scale)
  :do-not-induct t)))

(local (defthm lw-mib-merge-differences
 (equal
  (lw-complex-add
   (lw-complex-scale weight (lw-complex-sub a b))
   (lw-complex-sub c d))
  (lw-complex-sub
   (lw-complex-add (lw-complex-scale weight a) c)
   (lw-complex-add (lw-complex-scale weight b) d)))
 :hints (("Goal" :in-theory (enable lw-complex-add lw-complex-sub lw-complex-scale)))))

(local (defthm lw-mib-sub-self
 (equal (lw-complex-sub a a) (cons 0 0))
 :hints (("Goal" :in-theory (enable lw-complex-sub)))))

(defthm lw-mellin-prime-interval-boundary
 (equal
  (lw-mellin-prime-interval-primitive start length rate height count total model-error primitive-error delta)
  (lw-complex-sub
   (lw-mellin-prime-boundary start rate height count total model-error primitive-error delta)
   (lw-mellin-prime-boundary (+ start length) rate height count total model-error primitive-error delta)))
 :hints (("Goal"
  :induct (lw-mellin-prime-interval-primitive start length rate height count total model-error primitive-error delta)
  :in-theory (enable (:induction lw-mellin-prime-interval-primitive)
                     (:definition lw-mellin-prime-interval-primitive)
                     (:definition lw-mellin-prime-boundary)))))

(local (defthm lw-mib-full-difference
 (equal
  (lw-complex-add
   (lw-complex-sub (lw-complex-sub a b) (lw-complex-sub c d))
   (lw-complex-scale factor (lw-complex-sub e f)))
  (lw-complex-sub
   (lw-complex-add (lw-complex-sub a c) (lw-complex-scale factor e))
   (lw-complex-add (lw-complex-sub b d) (lw-complex-scale factor f))))
 :hints (("Goal" :in-theory (enable lw-complex-add lw-complex-sub lw-complex-scale)))))

(defthm lw-mellin-finite-interval-boundary
 (implies
  (and (rationalp start) (<= 0 start) (rationalp length) (<= 0 length))
  (equal
   (lw-mellin-finite-interval-primitive cap start length rate height model-error delta)
   (lw-complex-sub
    (lw-mellin-finite-boundary cap start rate height model-error delta)
    (lw-mellin-finite-boundary cap (+ start length) rate height model-error delta))))
 :hints (("Goal"
  :in-theory (enable lw-mellin-finite-interval-primitive lw-mellin-finite-boundary
                     lw-complex-exp-clipped-primitive-boundaries
                     lw-complex-exp-clipped-moment-primitive-boundaries)
  :do-not-induct t)))

(local (in-theory (disable lw-mellin-ramp-interval-boundary
 lw-mellin-prime-interval-boundary lw-mellin-finite-interval-boundary
 lw-mib-merge-differences lw-mib-full-difference)))

(local (defthm lw-mib-scale-difference
 (equal (lw-complex-sub (lw-complex-scale factor left) (lw-complex-scale factor right))
        (lw-complex-scale factor (lw-complex-sub left right)))
 :hints (("Goal" :in-theory (enable lw-complex-sub lw-complex-scale)))))

(local (defthm lw-mib-add-differences
 (equal (lw-complex-sub (lw-complex-add left rest) (lw-complex-add right other))
        (lw-complex-add (lw-complex-sub left right) (lw-complex-sub rest other)))
 :hints (("Goal" :in-theory (enable lw-complex-sub lw-complex-add)))))

(local (defthm lw-mib-subtract-differences
 (equal (lw-complex-sub
         (lw-complex-sub (lw-complex-scale factor left) rest)
         (lw-complex-sub (lw-complex-scale factor right) other))
        (lw-complex-add
         (lw-complex-scale factor (lw-complex-sub left right))
         (lw-complex-scale -1 (lw-complex-sub rest other))))
 :hints (("Goal" :in-theory (enable lw-complex-sub lw-complex-add lw-complex-scale)))
 :rule-classes nil))

(local (defthm lw-mib-subtract-comparisons
 (implies (and (lw-complex-diskp (lw-complex-sub left right) radius)
               (lw-complex-diskp (lw-complex-sub rest other) other-radius)
               (rationalp factor))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-complex-sub (lw-complex-scale factor left) rest)
    (lw-complex-sub (lw-complex-scale factor right) other))
   (+ (* (abs factor) radius) other-radius)))
 :hints (("Goal"
   :use (lw-mib-subtract-differences
         (:instance lw-complex-scale-disk (point (lw-complex-sub left right)))
         (:instance lw-complex-scale-disk (point (lw-complex-sub rest other)) (factor -1) (radius other-radius))
         (:instance lw-complex-add-disk
          (left (lw-complex-scale factor (lw-complex-sub left right)))
          (right (lw-complex-scale -1 (lw-complex-sub rest other)))
          (radius (* (abs factor) radius))))
   :in-theory (disable lw-complex-scale-disk lw-complex-add-disk)
   :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-mib-log-data
 (implies (and (rationalp prime) (< 1 prime) (rationalp log-error) (< 0 log-error))
  (and (rationalp (car (lw-log-bounds prime log-error))) (<= 0 (car (lw-log-bounds prime log-error)))))
 :hints (("Goal"
   :use ((:instance lw-log-bounds-interval (value prime) (epsilon log-error))
         (:instance lw-log-bounds-lower-coarse (value prime) (epsilon log-error)))
   :in-theory (e/d (lw-intervalp) (lw-log-bounds-interval lw-log-bounds-lower-coarse))))
 :rule-classes nil))

(local (defthm lw-mib-zero-disk (lw-complex-diskp (cons 0 0) 0)
 :hints (("Goal" :in-theory (enable lw-complex-diskp lw-complexp lw-diskp)))))

(local (defthm lw-mib-ramp-comparison
 (implies
  (and (rationalp cap) (<= 0 cap) (rationalp start) (<= 0 start) (rationalp length) (<= 0 length) (rationalp rate) (< 1 rate) (rationalp height)
       (rationalp index) (< 1 index) (rationalp log-error) (< 0 log-error)
       (rationalp error) (< 0 error) (rationalp delta) (< 0 delta)
       (<= delta (lw-mellin-component-endpoint-precision 0 length rate error))
       (<= delta (lw-mellin-component-endpoint-precision 3 length rate error)))
  (lw-complex-diskp (lw-complex-sub (lw-mellin-ramp-endpoint cap start length (car (lw-log-bounds index log-error)) rate height index error) (lw-mellin-ramp-interval-primitive start length rate height index log-error delta)) (* (+ 1 (/ index)) 1/16 error)))
 :hints (("Goal"
  :use ((:instance lw-mib-log-data (prime index))
        (:instance lw-mellin-interval-component-precision-comparison (kind 0) (cutpoint (car (lw-log-bounds index log-error))))
        (:instance lw-mellin-interval-component-precision-comparison (kind 3) (cutpoint (car (lw-log-bounds index log-error))))
        (:instance lw-mib-subtract-comparisons
         (left (lw-mellin-component-endpoint-value 0 start length (car (lw-log-bounds index log-error)) rate height error)) (right (lw-complex-exp-clipped-primitive (lw-complex-laplace-point (- rate 1) height) start (+ start length) (car (lw-log-bounds index log-error)) delta))
         (rest (lw-mellin-component-endpoint-value 3 start length (car (lw-log-bounds index log-error)) rate height error)) (other (lw-complex-exp-clipped-primitive (lw-complex-laplace-point rate height) start (+ start length) (car (lw-log-bounds index log-error)) delta))
         (factor (/ index)) (radius (* 1/16 error)) (other-radius (* 1/16 error))))
  :in-theory (e/d (lw-mellin-ramp-endpoint lw-mellin-common-endpoint lw-mellin-ramp-interval-primitive lw-mellin-basis-clearance)
                  (lw-mellin-interval-component-precision-comparison))
  :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-mib-weighted-ramp-comparison
 (implies
  (and (rationalp cap) (<= 0 cap) (rationalp start) (<= 0 start) (rationalp length) (<= 0 length) (rationalp rate) (< 1 rate) (rationalp height)
       (natp count) (< 1 count) (natp total) (rationalp model-error) (< 0 model-error)
       (rationalp primitive-error) (< 0 primitive-error) (rationalp error) (< 0 error)
       (rationalp delta) (< 0 delta)
       (<= delta (lw-mellin-component-endpoint-precision 0 length rate error))
       (<= delta (lw-mellin-component-endpoint-precision 3 length rate error)))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-scale (car (lw-mangoldt-bounds count primitive-error)) (lw-mellin-ramp-endpoint cap start length (car (lw-log-bounds count (lw-smoothed-ramp-log-error count total model-error))) rate height count error)) (lw-complex-scale (car (lw-mangoldt-bounds count primitive-error)) (lw-mellin-ramp-interval-primitive start length rate height count (lw-smoothed-ramp-log-error count total model-error) delta)))
   (* (car (lw-mangoldt-bounds count primitive-error)) (+ 1 (/ count)) 1/16 error)))
 :hints (("Goal"
  :use ((:instance lw-smoothed-ramp-log-error-adequate (index count) (error model-error))
        (:instance lw-mangoldt-lower-coarse (index count) (epsilon primitive-error))
        (:instance lw-mib-ramp-comparison (index count) (log-error (lw-smoothed-ramp-log-error count total model-error)))
        (:instance lw-complex-scale-disk
         (factor (car (lw-mangoldt-bounds count primitive-error))) (point (lw-complex-sub (lw-mellin-ramp-endpoint cap start length (car (lw-log-bounds count (lw-smoothed-ramp-log-error count total model-error))) rate height count error) (lw-mellin-ramp-interval-primitive start length rate height count (lw-smoothed-ramp-log-error count total model-error) delta))) (radius (* (+ 1 (/ count)) 1/16 error))))
  :in-theory (disable lw-smoothed-ramp-log-error-adequate lw-mangoldt-lower-coarse lw-complex-scale-disk)
  :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(defthm lw-mellin-prime-interval-precision-comparison
 (implies
  (and (rationalp cap) (<= 0 cap) (rationalp start) (<= 0 start) (rationalp length) (<= 0 length) (rationalp rate) (< 1 rate) (rationalp height)
       (natp count) (natp total) (rationalp model-error) (< 0 model-error)
       (rationalp primitive-error) (< 0 primitive-error) (rationalp error) (< 0 error)
       (rationalp delta) (< 0 delta)
       (<= delta (lw-mellin-component-endpoint-precision 0 length rate error))
       (<= delta (lw-mellin-component-endpoint-precision 3 length rate error)))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-mellin-prime-endpoint cap start length rate height count total model-error primitive-error error)
    (lw-mellin-prime-interval-primitive start length rate height count total model-error primitive-error delta))
   (* (lw-mellin-prime-endpoint-mass count primitive-error) 1/16 error)))
 :hints (("Goal"
   :induct (lw-mellin-prime-endpoint cap start length rate height count total model-error primitive-error error)
   :in-theory (enable (:induction lw-mellin-prime-endpoint) (:definition lw-mellin-prime-endpoint)
                      (:definition lw-mellin-prime-interval-primitive) (:definition lw-mellin-prime-endpoint-mass)))
  (and stable-under-simplificationp
   '(:use (lw-mib-weighted-ramp-comparison
           (:instance lw-complex-add-disk
            (left (lw-complex-sub (lw-complex-scale (car (lw-mangoldt-bounds count primitive-error)) (lw-mellin-ramp-endpoint cap start length (car (lw-log-bounds count (lw-smoothed-ramp-log-error count total model-error))) rate height count error)) (lw-complex-scale (car (lw-mangoldt-bounds count primitive-error)) (lw-mellin-ramp-interval-primitive start length rate height count (lw-smoothed-ramp-log-error count total model-error) delta))))
            (right (lw-complex-sub
             (lw-mellin-prime-endpoint cap start length rate height (- count 1) total model-error primitive-error error)
             (lw-mellin-prime-interval-primitive start length rate height (- count 1) total model-error primitive-error delta)))
            (radius (* (car (lw-mangoldt-bounds count primitive-error)) (+ 1 (/ count)) 1/16 error))
            (other-radius (* (lw-mellin-prime-endpoint-mass (- count 1) primitive-error) 1/16 error))))
     :in-theory (disable lw-mellin-prime-endpoint lw-mellin-prime-interval-primitive
                         lw-mellin-prime-endpoint-mass lw-complex-add-disk)
     :nonlinearp nil :do-not-induct t))))

(local (defthm lw-mib-family-difference
 (equal
  (lw-complex-sub
   (lw-complex-add (lw-complex-sub a b) (lw-complex-scale factor c))
   (lw-complex-add (lw-complex-sub x y) (lw-complex-scale factor z)))
  (lw-complex-add
   (lw-complex-add (lw-complex-sub a x) (lw-complex-scale -1 (lw-complex-sub b y)))
   (lw-complex-scale factor (lw-complex-sub c z))))
 :hints (("Goal" :in-theory (enable lw-complex-sub lw-complex-add lw-complex-scale)))
 :rule-classes nil))

(local (defthm lw-mib-family-disk
 (implies (and (lw-complex-diskp (lw-complex-sub a x) radius)
               (lw-complex-diskp (lw-complex-sub b y) moment-radius)
               (lw-complex-diskp (lw-complex-sub c z) correction-radius) (rationalp factor))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-complex-add (lw-complex-sub a b) (lw-complex-scale factor c))
    (lw-complex-add (lw-complex-sub x y) (lw-complex-scale factor z)))
   (+ radius moment-radius (* (abs factor) correction-radius))))
 :hints (("Goal"
   :use (lw-mib-family-difference
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

(local (defthm lw-mib-parameters
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

(defthm lw-mellin-interval-endpoint-precision-comparison
 (implies
  (and (rationalp model-cap) (<= 0 model-cap) (rationalp cap) (<= 0 cap) (rationalp start) (<= 0 start) (rationalp length) (<= 0 length) (rationalp rate) (< 1 rate) (rationalp height)
       (rationalp model-error) (< 0 model-error) (rationalp error) (< 0 error)
       (rationalp delta) (< 0 delta)
       (<= delta (lw-mellin-component-endpoint-precision 0 length rate error))
       (<= delta (lw-mellin-component-endpoint-precision 3 length rate error))
       (<= delta (lw-mellin-interval-moment-precision cap start length rate error)))
  (lw-complex-diskp (lw-complex-sub (lw-mellin-refined-endpoint model-cap cap start length rate height model-error error) (lw-mellin-finite-interval-primitive model-cap start length rate height model-error delta))
                   (* (lw-mellin-endpoint-precision-factor model-cap model-error) 1/16 error)))
 :hints (("Goal"
  :use ((:instance lw-mib-parameters (cap model-cap))
        (:instance lw-mellin-endpoint-precision-factor-valid (cap model-cap))
        (:instance lw-mellin-prime-interval-precision-comparison (count (lw-log-signal-ramp-count model-cap)) (total (lw-log-signal-ramp-count model-cap)) (primitive-error (lw-signal-exponential-precision model-cap model-error)))
        (:instance lw-mellin-interval-moment-precision-comparison (cutpoint 0))
        (:instance lw-mellin-interval-component-precision-comparison (kind 0) (cutpoint 0))
        (:instance lw-mib-family-disk
         (a (lw-mellin-prime-endpoint cap start length rate height (lw-log-signal-ramp-count model-cap) (lw-log-signal-ramp-count model-cap) model-error (lw-signal-exponential-precision model-cap model-error) error))
         (x (lw-mellin-prime-interval-primitive start length rate height (lw-log-signal-ramp-count model-cap) (lw-log-signal-ramp-count model-cap) model-error (lw-signal-exponential-precision model-cap model-error) delta))
         (b (lw-mellin-moment-endpoint-value cap start length 0 rate height error))
         (y (lw-complex-exp-clipped-moment-primitive (lw-complex-laplace-point (- rate 1) height) start (+ start length) 0 delta))
         (c (lw-mellin-component-endpoint-value 0 start length 0 rate height error))
         (z (lw-complex-exp-clipped-primitive (lw-complex-laplace-point (- rate 1) height) start (+ start length) 0 delta))
         (factor (+ 1 (car (lw-euler-bounds (lw-signal-exponential-precision model-cap model-error))))) (radius (* (lw-mellin-prime-endpoint-mass (lw-log-signal-ramp-count model-cap) (lw-signal-exponential-precision model-cap model-error)) 1/16 error))
         (moment-radius (* 1/16 error)) (correction-radius (* 1/16 error)))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub (lw-mellin-refined-endpoint model-cap cap start length rate height model-error error) (lw-mellin-finite-interval-primitive model-cap start length rate height model-error delta)))
         (radius (+ (* (lw-mellin-prime-endpoint-mass (lw-log-signal-ramp-count model-cap) (lw-signal-exponential-precision model-cap model-error)) 1/16 error) (* 1/16 error) (* (abs (+ 1 (car (lw-euler-bounds (lw-signal-exponential-precision model-cap model-error))))) 1/16 error)))
         (cap (* (lw-mellin-endpoint-precision-factor model-cap model-error) 1/16 error))))
  :in-theory
   (e/d (lw-mellin-refined-endpoint lw-mellin-finite-interval-primitive lw-mellin-common-endpoint
         lw-mellin-basis-clearance lw-mellin-endpoint-precision-factor)
     (lw-mellin-prime-interval-precision-comparison lw-mellin-interval-moment-precision-comparison
      lw-mellin-interval-component-precision-comparison lw-mellin-endpoint-precision-factor-valid))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-mellin-prime-interval-primitive-rational
 (implies
  (and (rationalp start) (<= 0 start) (rationalp length) (<= 0 length)
       (rationalp rate) (< 1 rate) (rationalp height) (natp count) (natp total)
       (rationalp model-error) (< 0 model-error) (rationalp primitive-error) (< 0 primitive-error)
       (rationalp delta) (< 0 delta))
  (lw-complexp
   (lw-mellin-prime-interval-primitive start length rate height count total model-error primitive-error delta)))
 :hints (("Goal"
  :induct (lw-mellin-prime-interval-primitive start length rate height count total model-error primitive-error delta)
  :in-theory (enable (:induction lw-mellin-prime-interval-primitive)
                     (:definition lw-mellin-prime-interval-primitive)
                     lw-complexp lw-complex-add lw-complex-scale))
  (and stable-under-simplificationp
   '(:use ((:instance lw-smoothed-ramp-log-error-adequate (index count) (error model-error))
           (:instance lw-log-bounds-interval (value count)
            (epsilon (lw-smoothed-ramp-log-error count total model-error)))
           (:instance lw-mangoldt-lower-coarse (index count) (epsilon primitive-error))
           (:instance lw-complex-exp-clipped-primitive-rational
            (point (lw-complex-laplace-point (- rate 1) height)) (end (+ start length))
            (cutpoint (car (lw-log-bounds count (lw-smoothed-ramp-log-error count total model-error)))) (error delta))
           (:instance lw-complex-exp-clipped-primitive-rational
            (point (lw-complex-laplace-point rate height)) (end (+ start length))
            (cutpoint (car (lw-log-bounds count (lw-smoothed-ramp-log-error count total model-error)))) (error delta)))
     :expand ((lw-mellin-prime-interval-primitive start length rate height count total model-error primitive-error delta))
     :in-theory (e/d (lw-mellin-ramp-interval-primitive lw-complex-laplace-point
                      lw-intervalp lw-complexp lw-complex-add lw-complex-sub lw-complex-scale)
                     (lw-smoothed-ramp-log-error-adequate lw-log-bounds-interval lw-mangoldt-lower-coarse
                      lw-complex-exp-clipped-primitive-rational))
     :do-not-induct t))))

(defthm lw-mellin-finite-interval-primitive-rational
 (implies
  (and (rationalp cap) (<= 0 cap) (rationalp start) (<= 0 start)
       (rationalp length) (<= 0 length) (rationalp rate) (< 1 rate) (rationalp height)
       (rationalp model-error) (< 0 model-error) (rationalp delta) (< 0 delta))
  (lw-complexp (lw-mellin-finite-interval-primitive cap start length rate height model-error delta)))
 :hints (("Goal"
  :use (lw-mib-parameters
        (:instance lw-mellin-prime-interval-primitive-rational
         (count (lw-log-signal-ramp-count cap)) (total (lw-log-signal-ramp-count cap))
         (primitive-error (lw-signal-exponential-precision cap model-error)))
        (:instance lw-complex-exp-clipped-moment-primitive-rational
         (point (lw-complex-laplace-point (- rate 1) height)) (end (+ start length)) (cutpoint 0) (error delta))
        (:instance lw-complex-exp-clipped-primitive-rational
         (point (lw-complex-laplace-point (- rate 1) height)) (end (+ start length)) (cutpoint 0) (error delta)))
  :in-theory (e/d (lw-mellin-finite-interval-primitive lw-complex-laplace-point
                   lw-complexp lw-complex-add lw-complex-sub lw-complex-scale)
                  (lw-mellin-prime-interval-primitive-rational
                   lw-complex-exp-clipped-moment-primitive-rational lw-complex-exp-clipped-primitive-rational))
  :do-not-induct t)))
