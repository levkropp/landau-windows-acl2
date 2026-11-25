(in-package "ACL2")

(include-book "mellin-frozen-endpoints")
(include-book "mellin-improper-endpoints")

(include-book "mellin-refined-cutpoints")

; Endpoint comparison for fixed coefficients on an independent interval.
; Point-exponential and kernel precisions can be refined after its cap is set.

(local (in-theory
 (disable lw-log-bounds lw-exp-bounds lw-euler-bounds lw-mangoldt-bounds
          lw-smoothed-ramp-log-error lw-smoothed-ramp-unit-error
          lw-mellin-clipped-basis-dyadic lw-mellin-frozen-basis-dyadic
          lw-mellin-clipped-ramp-linearization lw-mellin-clipped-basis-before-cutpoint
          lw-mellin-clipped-prime-dyadic
          lw-mellin-common-depth lw-mellin-common-endpoint lw-mellin-component-minimum-depth
          lw-mellin-component-endpoint-value lw-mellin-moment-endpoint-value
          lw-mellin-exponential-moment-cap lw-complex-exp-uniform-cap
          lw-exp-lipschitz-cap lw-mellin-weight lw-mellin-phase
          lw-complexp lw-complex-add lw-complex-sub lw-complex-scale lw-complex-diskp lw-diskp
          lw-complex-disk-enlarge lw-disk-enlarge lw-complex-sub-add-first
          lw-complex-add-commutative lw-complex-add-left-commutes)))

(local (in-theory (disable lw-mellin-frozen-dyadic lw-mellin-dyadic-sum
 lw-mellin-clipped-linear-dyadic lw-mellin-prime-endpoint lw-mellin-prime-endpoint-mass
 lw-mellin-common-base-radius lw-log-signal-ramp-count lw-log-signal-spatial-cap lw-signal-count
 lw-signal-exponential-precision lw-signal-exponential-cost lw-kernel-spatial-cap lw-halved-width)))

(local (in-theory (disable lw-mellin-refined-dyadic lw-mellin-refined-clipped-linear-dyadic
 lw-mellin-refined-clipped-prime-dyadic lw-mellin-refined-dyadic-linearization)))

(local (defthm lw-mre-left-commutes
 (equal (* a (* b c)) (* b (* a c)))
 :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                       (:instance associativity-of-* (x b) (y a) (z c))
                       (:instance commutativity-of-* (x a) (y b)))
                 :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-mre-left-distributes
 (equal (* (+ a b) c) (+ (* a c) (* b c)))
 :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                 :in-theory (disable distributivity)))))

(local (defthm lw-mre-zero-times (equal (* 0 a) 0)))

(local (defthm lw-mre-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-mre-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-mre-times-negative (a b) (b a)))
                 :in-theory (disable lw-mre-times-negative)))))

(local (defthm lw-mre-scale-difference
 (equal (lw-complex-sub (lw-complex-scale factor left) (lw-complex-scale factor right))
        (lw-complex-scale factor (lw-complex-sub left right)))
 :hints (("Goal" :in-theory (enable lw-complex-sub lw-complex-scale)))))

(local (defthm lw-mre-add-differences
 (equal (lw-complex-sub (lw-complex-add left rest) (lw-complex-add right other))
        (lw-complex-add (lw-complex-sub left right) (lw-complex-sub rest other)))
 :hints (("Goal" :in-theory (enable lw-complex-sub lw-complex-add)))))

(local (defthm lw-mre-log-data
 (implies (and (rationalp prime) (< 1 prime) (rationalp log-error) (< 0 log-error))
  (and (rationalp (car (lw-log-bounds prime log-error))) (<= 0 (car (lw-log-bounds prime log-error)))))
 :hints (("Goal"
   :use ((:instance lw-log-bounds-interval (value prime) (epsilon log-error))
         (:instance lw-log-bounds-lower-coarse (value prime) (epsilon log-error)))
   :in-theory (e/d (lw-intervalp) (lw-log-bounds-interval lw-log-bounds-lower-coarse))))
 :rule-classes nil))

(local (defthm lw-mre-weighted-ramp
 (implies
  (and (rationalp cap) (<= 0 cap) (rationalp start) (<= 0 start)
       (rationalp length) (<= 0 length) (<= (+ start length) cap)
       (natp count) (< 1 count) (natp total)
       (rationalp sigma) (< 1 sigma) (rationalp height)
       (rationalp model-error) (< 0 model-error) (rationalp primitive-error) (< 0 primitive-error) (rationalp exp-error) (< 0 exp-error)
       (rationalp sample-error) (< 0 sample-error) (rationalp error) (< 0 error))
  (let ((cutpoint (car (lw-log-bounds count (lw-smoothed-ramp-log-error count total model-error))))
        (weight (car (lw-mangoldt-bounds count primitive-error))))
   (lw-complex-diskp
    (lw-complex-sub
     (lw-complex-scale weight
      (lw-mellin-clipped-basis-dyadic
       2 start (+ start length) (lw-mellin-common-depth cap start length sigma height error minimum-depth)
       cutpoint sigma height 0 exp-error count
       (lw-smoothed-ramp-log-error count total model-error) sample-error))
     (lw-complex-scale weight (lw-mellin-ramp-endpoint cap start length cutpoint sigma height count error)))
    (* weight (+ 1 (/ count)) (lw-mellin-common-base-radius cap length exp-error sample-error error)))))
 :hints (("Goal"
   :use ((:instance lw-smoothed-ramp-log-error-adequate (index count) (error model-error))
         (:instance lw-mre-log-data (prime count) (log-error (lw-smoothed-ramp-log-error count total model-error)))
         (:instance lw-mangoldt-lower-coarse (index count) (epsilon primitive-error))
         (:instance lw-mellin-common-ramp-comparison
          (cutpoint (car (lw-log-bounds count (lw-smoothed-ramp-log-error count total model-error))))
          (prime count) (log-error (lw-smoothed-ramp-log-error count total model-error)) (exp-error exp-error))
         (:instance lw-complex-scale-disk
          (factor (car (lw-mangoldt-bounds count primitive-error)))
          (point (lw-complex-sub
           (lw-mellin-clipped-basis-dyadic
            2 start (+ start length) (lw-mellin-common-depth cap start length sigma height error minimum-depth)
            (car (lw-log-bounds count (lw-smoothed-ramp-log-error count total model-error)))
            sigma height 0 exp-error count (lw-smoothed-ramp-log-error count total model-error) sample-error)
           (lw-mellin-ramp-endpoint cap start length
            (car (lw-log-bounds count (lw-smoothed-ramp-log-error count total model-error))) sigma height count error)))
          (radius (* (+ 1 (/ count)) (lw-mellin-common-base-radius cap length exp-error sample-error error)))))
   :in-theory (disable lw-smoothed-ramp-log-error-adequate lw-mangoldt-lower-coarse
                       lw-mellin-common-ramp-comparison lw-complex-scale-disk)
   :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-mre-sub-self (equal (lw-complex-sub point point) (cons 0 0))
 :hints (("Goal" :in-theory (enable lw-complex-sub)))))

(local (defthm lw-mre-zero-disk (lw-complex-diskp (cons 0 0) 0)
 :hints (("Goal" :in-theory (enable lw-complex-diskp lw-complexp lw-diskp)))))

(defthm lw-mellin-refined-prime-endpoint-comparison
 (implies
  (and (rationalp cap) (<= 0 cap) (rationalp start) (<= 0 start)
       (rationalp length) (<= 0 length) (<= (+ start length) cap)
       (natp count) (natp total) (rationalp sigma) (< 1 sigma) (rationalp height)
       (rationalp model-error) (< 0 model-error) (rationalp primitive-error) (< 0 primitive-error) (rationalp exp-error) (< 0 exp-error)
       (rationalp sample-error) (< 0 sample-error) (rationalp error) (< 0 error))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-mellin-refined-clipped-prime-dyadic
     start (+ start length) (lw-mellin-common-depth cap start length sigma height error minimum-depth)
     sigma height 0 count total model-error primitive-error sample-error exp-error)
    (lw-mellin-prime-endpoint cap start length sigma height count total model-error primitive-error error))
   (* (lw-mellin-prime-endpoint-mass count primitive-error)
      (lw-mellin-common-base-radius cap length exp-error sample-error error))))
 :hints (("Goal"
   :induct (lw-mellin-prime-endpoint cap start length sigma height count total model-error primitive-error error)
   :in-theory (enable lw-mellin-prime-endpoint lw-mellin-refined-clipped-prime-dyadic lw-mellin-prime-endpoint-mass))
  (and stable-under-simplificationp
   '(:use (lw-mre-weighted-ramp
           (:instance lw-complex-add-disk
            (left (lw-complex-sub
             (lw-complex-scale
              (car (lw-mangoldt-bounds count primitive-error))
              (lw-mellin-clipped-basis-dyadic
               2 start (+ start length) (lw-mellin-common-depth cap start length sigma height error minimum-depth)
               (car (lw-log-bounds count (lw-smoothed-ramp-log-error count total model-error)))
               sigma height 0 exp-error count (lw-smoothed-ramp-log-error count total model-error) sample-error))
             (lw-complex-scale
              (car (lw-mangoldt-bounds count primitive-error))
              (lw-mellin-ramp-endpoint cap start length
               (car (lw-log-bounds count (lw-smoothed-ramp-log-error count total model-error))) sigma height count error))))
            (right (lw-complex-sub
             (lw-mellin-refined-clipped-prime-dyadic
              start (+ start length) (lw-mellin-common-depth cap start length sigma height error minimum-depth)
              sigma height 0 (- count 1) total model-error primitive-error sample-error exp-error)
             (lw-mellin-prime-endpoint cap start length sigma height (- count 1) total model-error primitive-error error)))
            (radius (* (car (lw-mangoldt-bounds count primitive-error)) (+ 1 (/ count))
                       (lw-mellin-common-base-radius cap length exp-error sample-error error)))
            (other-radius (* (lw-mellin-prime-endpoint-mass (- count 1) primitive-error)
                             (lw-mellin-common-base-radius cap length exp-error sample-error error)))))
     :in-theory (disable lw-mellin-prime-endpoint lw-mellin-refined-clipped-prime-dyadic
                         lw-mellin-prime-endpoint-mass lw-complex-add-disk)
     :nonlinearp nil :do-not-induct t))))

(local (defthm lw-mre-family-difference
 (equal
  (lw-complex-sub
   (lw-complex-add (lw-complex-sub a b) (lw-complex-scale factor c))
   (lw-complex-add (lw-complex-sub x y) (lw-complex-scale factor z)))
  (lw-complex-add
   (lw-complex-add (lw-complex-sub a x) (lw-complex-scale -1 (lw-complex-sub b y)))
   (lw-complex-scale factor (lw-complex-sub c z))))
 :hints (("Goal" :in-theory (enable lw-complex-sub lw-complex-add lw-complex-scale)))
 :rule-classes nil))

(local (defthm lw-mre-family-disk
 (implies (and (lw-complex-diskp (lw-complex-sub a x) radius)
               (lw-complex-diskp (lw-complex-sub b y) moment-radius)
               (lw-complex-diskp (lw-complex-sub c z) correction-radius) (rationalp factor))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-complex-add (lw-complex-sub a b) (lw-complex-scale factor c))
    (lw-complex-add (lw-complex-sub x y) (lw-complex-scale factor z)))
   (+ radius moment-radius (* (abs factor) correction-radius))))
 :hints (("Goal"
   :use (lw-mre-family-difference
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

(defun lw-mellin-refined-endpoint (model-cap cap start length sigma height model-error error)
 (let ((count (lw-log-signal-ramp-count model-cap)) (epsilon (lw-signal-exponential-precision model-cap model-error)))
  (lw-complex-add
   (lw-complex-sub
    (lw-mellin-prime-endpoint cap start length sigma height count count model-error epsilon error)
    (lw-mellin-common-endpoint 1 cap start length 0 sigma height error))
   (lw-complex-scale (+ 1 (car (lw-euler-bounds epsilon)))
    (lw-mellin-common-endpoint 0 cap start length 0 sigma height error)))))

(defun lw-mellin-refined-endpoint-radius (model-cap cap length model-error sample-error error exp-error)
 (let* ((epsilon (lw-signal-exponential-precision model-cap model-error))
        (base (lw-mellin-common-base-radius cap length exp-error sample-error error)))
  (+ (* (lw-mellin-prime-endpoint-mass (lw-log-signal-ramp-count model-cap) epsilon) base)
     (* length cap (+ exp-error (* 2 (lw-complex-exp-uniform-cap cap) sample-error))) error
     (* (abs (+ 1 (car (lw-euler-bounds epsilon)))) base))))

(local (in-theory (disable lw-mellin-refined-endpoint lw-mellin-refined-endpoint-radius)))

(local (defthm lw-mre-parameters
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

(defthm lw-mellin-refined-clipped-linear-endpoint-comparison
 (implies
  (and (rationalp model-cap) (<= 0 model-cap)
       (rationalp exp-error) (< 0 exp-error)
       (rationalp cap) (<= 0 cap) (rationalp start) (<= 0 start)
       (rationalp length) (<= 0 length) (<= (+ start length) cap)
       (rationalp sigma) (< 1 sigma) (rationalp height)
       (rationalp model-error) (< 0 model-error) (rationalp sample-error) (< 0 sample-error)
       (rationalp error) (< 0 error))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-mellin-refined-clipped-linear-dyadic model-cap start (+ start length) (lw-mellin-common-depth cap start length sigma height error minimum-depth) sigma height 0 model-error sample-error exp-error)
    (lw-mellin-refined-endpoint model-cap cap start length sigma height model-error error))
   (lw-mellin-refined-endpoint-radius model-cap cap length model-error sample-error error exp-error)))
 :hints (("Goal"
  :use ((:instance lw-mre-parameters (cap model-cap))
        (:instance lw-mellin-refined-prime-endpoint-comparison (count (lw-log-signal-ramp-count model-cap)) (total (lw-log-signal-ramp-count model-cap)) (primitive-error (lw-signal-exponential-precision model-cap model-error)))
        (:instance lw-mellin-common-unclipped-comparison (kind 1) (exp-error exp-error) (prime 2) (log-error 1))
        (:instance lw-mellin-common-unclipped-comparison (kind 0) (exp-error exp-error) (prime 2) (log-error 1))
        (:instance lw-mre-family-disk
         (a (lw-mellin-refined-clipped-prime-dyadic start (+ start length) (lw-mellin-common-depth cap start length sigma height error minimum-depth) sigma height 0 (lw-log-signal-ramp-count model-cap) (lw-log-signal-ramp-count model-cap) model-error (lw-signal-exponential-precision model-cap model-error) sample-error exp-error)) (x (lw-mellin-prime-endpoint cap start length sigma height (lw-log-signal-ramp-count model-cap) (lw-log-signal-ramp-count model-cap) model-error (lw-signal-exponential-precision model-cap model-error) error)) (b (lw-mellin-frozen-basis-dyadic 1 start (+ start length) (lw-mellin-common-depth cap start length sigma height error minimum-depth) sigma height 0 exp-error 2 1 sample-error)) (y (lw-mellin-common-endpoint 1 cap start length 0 sigma height error)) (c (lw-mellin-frozen-basis-dyadic 0 start (+ start length) (lw-mellin-common-depth cap start length sigma height error minimum-depth) sigma height 0 exp-error 2 1 sample-error)) (z (lw-mellin-common-endpoint 0 cap start length 0 sigma height error)) (factor (+ 1 (car (lw-euler-bounds (lw-signal-exponential-precision model-cap model-error)))))
         (radius (* (lw-mellin-prime-endpoint-mass (lw-log-signal-ramp-count model-cap) (lw-signal-exponential-precision model-cap model-error)) (lw-mellin-common-base-radius cap length exp-error sample-error error))) (moment-radius (+ (* length cap (+ exp-error (* 2 (lw-complex-exp-uniform-cap cap) sample-error))) error)) (correction-radius (lw-mellin-common-base-radius cap length exp-error sample-error error))))
  :in-theory
  (e/d (lw-mellin-refined-clipped-linear-dyadic lw-mellin-refined-endpoint lw-mellin-refined-endpoint-radius
        lw-mellin-common-base-radius lw-mellin-exponential-moment-cap)
       (lw-mellin-refined-prime-endpoint-comparison lw-mellin-common-unclipped-comparison))
  :nonlinearp nil :do-not-induct t)))

(local (defthm lw-mre-telescope
         (equal (lw-complex-sub left right)
                (lw-complex-add (lw-complex-sub left middle) (lw-complex-sub middle right)))
         :hints (("Goal" :in-theory (enable lw-complex-add lw-complex-sub)))
         :rule-classes nil))

(local (defthm lw-mre-triangle
         (implies (and (lw-complex-diskp (lw-complex-sub left middle) radius)
                       (lw-complex-diskp (lw-complex-sub middle right) other-radius))
                  (lw-complex-diskp (lw-complex-sub left right) (+ radius other-radius)))
         :hints (("Goal"
                  :use (lw-mre-telescope
                        (:instance lw-complex-add-disk
                          (left (lw-complex-sub left middle)) (right (lw-complex-sub middle right))))
                  :in-theory (disable lw-complex-add-disk) :do-not-induct t))
         :rule-classes nil))

(defthm lw-mellin-refined-grid-endpoint-comparison
 (implies (and (rationalp model-cap) (<= 0 model-cap)
       (rationalp exp-error) (< 0 exp-error)
       (<= exp-error (lw-signal-exponential-precision model-cap model-error))
       (rationalp cap) (<= 0 cap) (rationalp start) (<= 0 start)
       (rationalp length) (<= 0 length) (<= (+ start length) cap)
       (rationalp sigma) (< 1 sigma) (rationalp height)
       (rationalp model-error) (< 0 model-error) (rationalp sample-error) (< 0 sample-error)
       (rationalp error) (< 0 error))
  (lw-complex-diskp (lw-complex-sub (lw-mellin-refined-dyadic model-cap start (+ start length) (lw-mellin-common-depth cap start length sigma height error minimum-depth) sigma height 0 model-error sample-error exp-error) (lw-mellin-refined-endpoint model-cap cap start length sigma height model-error error)) (+ (* (lw-halved-width length (lw-mellin-common-depth cap start length sigma height error minimum-depth)) (lw-kernel-spatial-cap cap 1) model-error) (lw-mellin-refined-endpoint-radius model-cap cap length model-error sample-error error exp-error))))
 :hints (("Goal"
  :use (lw-mellin-common-depth-adequate lw-mellin-refined-clipped-linear-endpoint-comparison
        (:instance lw-mellin-refined-clipped-family-comparison
         (end (+ start length)) (depth (lw-mellin-common-depth cap start length sigma height error minimum-depth)) (index 0))
        (:instance lw-mre-triangle
         (left (lw-mellin-refined-dyadic model-cap start (+ start length) (lw-mellin-common-depth cap start length sigma height error minimum-depth) sigma height 0 model-error sample-error exp-error)) (middle (lw-mellin-refined-clipped-linear-dyadic model-cap start (+ start length) (lw-mellin-common-depth cap start length sigma height error minimum-depth) sigma height 0 model-error sample-error exp-error)) (right (lw-mellin-refined-endpoint model-cap cap start length sigma height model-error error)) (radius (* (lw-halved-width length (lw-mellin-common-depth cap start length sigma height error minimum-depth)) (lw-kernel-spatial-cap cap 1) model-error)) (other-radius (lw-mellin-refined-endpoint-radius model-cap cap length model-error sample-error error exp-error))))
  :in-theory (disable lw-mellin-common-depth-adequate lw-mellin-refined-clipped-linear-endpoint-comparison
                      lw-mellin-refined-clipped-family-comparison)
  :nonlinearp nil :do-not-induct t)))

(defthm lw-mellin-refined-endpoint-rational
 (implies
  (and (rationalp model-cap) (<= 0 model-cap) (rationalp cap) (<= 0 cap) (rationalp start) (<= 0 start) (rationalp length) (<= 0 length)
       (rationalp sigma) (< 1 sigma) (rationalp height) (rationalp model-error) (< 0 model-error)
       (rationalp error) (< 0 error))
  (lw-complexp (lw-mellin-refined-endpoint model-cap cap start length sigma height model-error error)))
 :hints (("Goal"
   :use ((:instance lw-signal-exponential-parameters (cap model-cap) (error model-error))
         (:instance lw-signal-count-natural (value (lw-log-signal-spatial-cap model-cap)))
         (:instance lw-euler-bounds-interval (epsilon (lw-signal-exponential-precision model-cap model-error)))
         (:instance lw-mellin-prime-endpoint-rational
          (count (lw-log-signal-ramp-count model-cap)) (total (lw-log-signal-ramp-count model-cap))
          (primitive-error (lw-signal-exponential-precision model-cap model-error)))
         (:instance lw-mellin-common-endpoint-rational (kind 1) (cutpoint 0))
         (:instance lw-mellin-common-endpoint-rational (kind 0) (cutpoint 0)))
   :in-theory (e/d (lw-mellin-refined-endpoint lw-log-signal-ramp-count lw-intervalp
                   lw-complexp lw-complex-add lw-complex-sub lw-complex-scale)
     (lw-signal-exponential-parameters lw-euler-bounds-interval lw-mellin-prime-endpoint-rational
      lw-mellin-common-endpoint-rational))
   :nonlinearp nil :do-not-induct t)))

(local (defthm lw-mre-recover
 (implies (and (lw-complexp a) (lw-complexp b))
  (equal b (lw-complex-add a (lw-complex-sub b a))))
 :hints (("Goal" :in-theory (enable lw-complexp lw-complex-add lw-complex-sub)))
 :rule-classes nil))

(local (defthm lw-mre-approximation-tail
 (implies (and (lw-complexp b) (lw-complex-diskp a radius)
               (lw-complex-diskp (lw-complex-sub a b) error))
  (lw-complex-diskp b (+ radius error)))
 :hints (("Goal"
  :use (lw-mre-recover
        (:instance lw-complex-difference-symmetric (left a) (right b) (radius error))
        (:instance lw-complex-add-disk (left a) (right (lw-complex-sub b a)) (other-radius error)))
  :in-theory (disable lw-complex-add-disk)
  :do-not-induct t))
 :rule-classes nil))

(defthm lw-mellin-refined-endpoint-tail-bound
 (implies
  (and (rationalp model-cap) (<= 0 model-cap)
       (rationalp cap) (<= 0 cap) (rationalp start) (< 0 start)
       (rationalp length) (<= 0 length) (<= (+ start length) cap)
       (rationalp sigma) (< 2 sigma) (rationalp height)
       (<= 2 (* (- sigma 2) start))
       (rationalp model-error) (< 0 model-error) (<= model-error 1)
       (rationalp sample-error) (< 0 sample-error) (rationalp exp-error) (< 0 exp-error)
       (<= exp-error (lw-signal-exponential-precision model-cap model-error))
       (rationalp error) (< 0 error)
       (<= (lw-halved-width length (lw-mellin-common-depth cap start length sigma height error minimum-depth)) start))
  (lw-complex-diskp (lw-mellin-refined-endpoint model-cap cap start length sigma height model-error error)
   (+ (/ (* 10 (lw-mellin-tail-coefficient (- sigma 2) 0 1)) start) (+ (* (lw-halved-width length (lw-mellin-common-depth cap start length sigma height error minimum-depth)) (lw-kernel-spatial-cap cap 1) model-error) (lw-mellin-refined-endpoint-radius model-cap cap length model-error sample-error error exp-error)))))
 :hints (("Goal"
  :use (lw-mellin-refined-endpoint-rational
        lw-mellin-common-depth-adequate
        lw-mellin-refined-grid-endpoint-comparison
        (:instance lw-mellin-refined-dyadic-tail-bound
         (cap model-cap) (end (+ start length)) (depth (lw-mellin-common-depth cap start length sigma height error minimum-depth)) (index 0) (error sample-error))
        (:instance lw-mre-approximation-tail
         (a (lw-mellin-refined-dyadic model-cap start (+ start length) (lw-mellin-common-depth cap start length sigma height error minimum-depth) sigma height 0 model-error sample-error exp-error)) (b (lw-mellin-refined-endpoint model-cap cap start length sigma height model-error error))
         (radius (/ (* 10 (lw-mellin-tail-coefficient (- sigma 2) 0 1)) start)) (error (+ (* (lw-halved-width length (lw-mellin-common-depth cap start length sigma height error minimum-depth)) (lw-kernel-spatial-cap cap 1) model-error) (lw-mellin-refined-endpoint-radius model-cap cap length model-error sample-error error exp-error)))))
  :in-theory (disable lw-mellin-refined-endpoint-rational lw-mellin-common-depth-adequate
              lw-mellin-refined-grid-endpoint-comparison lw-mellin-refined-dyadic-tail-bound)
  :nonlinearp nil :do-not-induct t)))
