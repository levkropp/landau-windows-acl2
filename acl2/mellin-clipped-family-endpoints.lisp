(in-package "ACL2")

(include-book "mellin-clipped-common-mesh")
(include-book "mellin-frozen-cutpoint-sums")

; Endpoint normalization of the entire finite Mangoldt-weighted ramp
; family, on one computed mesh. Both the logarithmic cutpoints and all
; primitive coefficients stay fixed as the quadrature is refined.

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

(local (defthm lw-mfe-left-commutes
 (equal (* a (* b c)) (* b (* a c)))
 :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                       (:instance associativity-of-* (x b) (y a) (z c))
                       (:instance commutativity-of-* (x a) (y b)))
                 :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-mfe-left-distributes
 (equal (* (+ a b) c) (+ (* a c) (* b c)))
 :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                 :in-theory (disable distributivity)))))
(local (defthm lw-mfe-zero-times (equal (* 0 a) 0)))

(local (defthm lw-mfe-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))
(local (defthm lw-mfe-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-mfe-times-negative (a b) (b a)))
                 :in-theory (disable lw-mfe-times-negative)))))

(local (defthm lw-mfe-scale-difference
 (equal (lw-complex-sub (lw-complex-scale factor left) (lw-complex-scale factor right))
        (lw-complex-scale factor (lw-complex-sub left right)))
 :hints (("Goal" :in-theory (enable lw-complex-sub lw-complex-scale)))))
(local (defthm lw-mfe-add-differences
 (equal (lw-complex-sub (lw-complex-add left rest) (lw-complex-add right other))
        (lw-complex-add (lw-complex-sub left right) (lw-complex-sub rest other)))
 :hints (("Goal" :in-theory (enable lw-complex-sub lw-complex-add)))))
(local (defthm lw-mfe-subtract-differences
 (equal (lw-complex-sub
         (lw-complex-sub (lw-complex-scale factor left) rest)
         (lw-complex-sub (lw-complex-scale factor right) other))
        (lw-complex-add
         (lw-complex-scale factor (lw-complex-sub left right))
         (lw-complex-scale -1 (lw-complex-sub rest other))))
 :hints (("Goal" :in-theory (enable lw-complex-sub lw-complex-add lw-complex-scale)))
 :rule-classes nil))

(local (defthm lw-mfe-subtract-comparisons
 (implies (and (lw-complex-diskp (lw-complex-sub left right) radius)
               (lw-complex-diskp (lw-complex-sub rest other) other-radius)
               (rationalp factor))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-complex-sub (lw-complex-scale factor left) rest)
    (lw-complex-sub (lw-complex-scale factor right) other))
   (+ (* (abs factor) radius) other-radius)))
 :hints (("Goal"
   :use (lw-mfe-subtract-differences
         (:instance lw-complex-scale-disk (point (lw-complex-sub left right)))
         (:instance lw-complex-scale-disk (point (lw-complex-sub rest other)) (factor -1) (radius other-radius))
         (:instance lw-complex-add-disk
          (left (lw-complex-scale factor (lw-complex-sub left right)))
          (right (lw-complex-scale -1 (lw-complex-sub rest other)))
          (radius (* (abs factor) radius))))
   :in-theory (disable lw-complex-scale-disk lw-complex-add-disk)
   :do-not-induct t))
 :rule-classes nil))

(defun lw-mellin-common-base-radius (cap length exp-error sample-error error)
 (+ (* length (+ exp-error (* 2 (lw-complex-exp-uniform-cap cap) sample-error))) error))

(defun lw-mellin-ramp-endpoint (cap start length cutpoint sigma height prime error)
 (lw-complex-sub
  (lw-complex-scale (/ prime) (lw-mellin-common-endpoint 0 cap start length cutpoint sigma height error))
  (lw-mellin-common-endpoint 3 cap start length cutpoint sigma height error)))

(local (in-theory (disable lw-mellin-common-base-radius lw-mellin-ramp-endpoint)))

(defthm lw-mellin-common-ramp-comparison
 (implies
  (and (rationalp cap) (<= 0 cap) (rationalp start) (<= 0 start)
       (rationalp length) (<= 0 length) (<= (+ start length) cap)
       (rationalp cutpoint) (<= 0 cutpoint)
       (rationalp prime) (< 1 prime) (rationalp log-error) (< 0 log-error)
       (<= (car (lw-log-bounds prime log-error)) cutpoint)
       (rationalp sigma) (< 1 sigma) (rationalp height)
       (rationalp exp-error) (< 0 exp-error) (rationalp sample-error) (< 0 sample-error)
       (rationalp error) (< 0 error))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-mellin-clipped-basis-dyadic
     2 start (+ start length) (lw-mellin-common-depth cap start length sigma height error minimum-depth)
     cutpoint sigma height 0 exp-error prime log-error sample-error)
    (lw-mellin-ramp-endpoint cap start length cutpoint sigma height prime error))
   (* (+ 1 (/ prime)) (lw-mellin-common-base-radius cap length exp-error sample-error error))))
 :hints (("Goal"
   :use ((:instance lw-mellin-common-component-comparison (kind 0))
         (:instance lw-mellin-common-component-comparison (kind 3))
         (:instance lw-mellin-clipped-ramp-linearization
          (end (+ start length)) (index 0)
          (depth (lw-mellin-common-depth cap start length sigma height error minimum-depth)))
         (:instance lw-mfe-subtract-comparisons
          (left (lw-mellin-clipped-basis-dyadic
            0 start (+ start length) (lw-mellin-common-depth cap start length sigma height error minimum-depth)
            cutpoint sigma height 0 exp-error prime log-error sample-error))
          (right (lw-mellin-common-endpoint 0 cap start length cutpoint sigma height error))
          (rest (lw-mellin-clipped-basis-dyadic
            3 start (+ start length) (lw-mellin-common-depth cap start length sigma height error minimum-depth)
            cutpoint sigma height 0 exp-error prime log-error sample-error))
          (other (lw-mellin-common-endpoint 3 cap start length cutpoint sigma height error))
          (factor (/ prime))
          (radius (lw-mellin-common-base-radius cap length exp-error sample-error error))
          (other-radius (lw-mellin-common-base-radius cap length exp-error sample-error error))))
   :in-theory (e/d (lw-mellin-ramp-endpoint lw-mellin-common-base-radius lw-mellin-exponential-moment-cap)
     (lw-mellin-common-component-comparison lw-mellin-clipped-ramp-linearization))
   :do-not-induct t)))

(defun lw-mellin-prime-endpoint-mass (count primitive-error)
 (declare (xargs :measure (nfix count)))
 (if (or (zp count) (equal count 1)) 0
   (+ (* (car (lw-mangoldt-bounds count primitive-error)) (+ 1 (/ count)))
      (lw-mellin-prime-endpoint-mass (- count 1) primitive-error))))

(defun lw-mellin-prime-endpoint
 (cap start length sigma height count total model-error primitive-error error)
 (declare (xargs :measure (nfix count)))
 (if (or (zp count) (equal count 1)) (cons 0 0)
   (let ((cutpoint (car (lw-log-bounds count (lw-smoothed-ramp-log-error count total model-error)))))
    (lw-complex-add
     (lw-complex-scale
      (car (lw-mangoldt-bounds count primitive-error))
      (lw-mellin-ramp-endpoint cap start length cutpoint sigma height count error))
     (lw-mellin-prime-endpoint
      cap start length sigma height (- count 1) total model-error primitive-error error)))))

(local (defthm lw-mfe-nonnegative-product
 (implies (and (rationalp a) (<= 0 a) (rationalp b) (<= 0 b)) (<= 0 (* a b)))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defthm lw-mellin-prime-endpoint-mass-valid
 (implies (and (natp count) (rationalp primitive-error) (< 0 primitive-error))
  (and (rationalp (lw-mellin-prime-endpoint-mass count primitive-error))
       (<= 0 (lw-mellin-prime-endpoint-mass count primitive-error))))
 :hints (("Goal" :induct (lw-mellin-prime-endpoint-mass count primitive-error))
         (and stable-under-simplificationp
          '(:use ((:instance lw-mangoldt-lower-coarse (index count) (epsilon primitive-error))
                  (:instance lw-mfe-nonnegative-product
                    (a (car (lw-mangoldt-bounds count primitive-error))) (b (+ 1 (/ count)))))
            :in-theory (disable lw-mangoldt-lower-coarse)
            :nonlinearp nil :do-not-induct t))))

(local (in-theory (disable lw-mellin-prime-endpoint lw-mellin-prime-endpoint-mass)))

(local (defthm lw-mfe-log-data
 (implies (and (rationalp prime) (< 1 prime) (rationalp log-error) (< 0 log-error))
  (and (rationalp (car (lw-log-bounds prime log-error))) (<= 0 (car (lw-log-bounds prime log-error)))))
 :hints (("Goal"
   :use ((:instance lw-log-bounds-interval (value prime) (epsilon log-error))
         (:instance lw-log-bounds-lower-coarse (value prime) (epsilon log-error)))
   :in-theory (e/d (lw-intervalp) (lw-log-bounds-interval lw-log-bounds-lower-coarse))))
 :rule-classes nil))

(local (defthm lw-mfe-weighted-ramp
 (implies
  (and (rationalp cap) (<= 0 cap) (rationalp start) (<= 0 start)
       (rationalp length) (<= 0 length) (<= (+ start length) cap)
       (natp count) (< 1 count) (natp total)
       (rationalp sigma) (< 1 sigma) (rationalp height)
       (rationalp model-error) (< 0 model-error) (rationalp primitive-error) (< 0 primitive-error)
       (rationalp sample-error) (< 0 sample-error) (rationalp error) (< 0 error))
  (let ((cutpoint (car (lw-log-bounds count (lw-smoothed-ramp-log-error count total model-error))))
        (weight (car (lw-mangoldt-bounds count primitive-error))))
   (lw-complex-diskp
    (lw-complex-sub
     (lw-complex-scale weight
      (lw-mellin-clipped-basis-dyadic
       2 start (+ start length) (lw-mellin-common-depth cap start length sigma height error minimum-depth)
       cutpoint sigma height 0 primitive-error count
       (lw-smoothed-ramp-log-error count total model-error) sample-error))
     (lw-complex-scale weight (lw-mellin-ramp-endpoint cap start length cutpoint sigma height count error)))
    (* weight (+ 1 (/ count)) (lw-mellin-common-base-radius cap length primitive-error sample-error error)))))
 :hints (("Goal"
   :use ((:instance lw-smoothed-ramp-log-error-adequate (index count) (error model-error))
         (:instance lw-mfe-log-data (prime count) (log-error (lw-smoothed-ramp-log-error count total model-error)))
         (:instance lw-mangoldt-lower-coarse (index count) (epsilon primitive-error))
         (:instance lw-mellin-common-ramp-comparison
          (cutpoint (car (lw-log-bounds count (lw-smoothed-ramp-log-error count total model-error))))
          (prime count) (log-error (lw-smoothed-ramp-log-error count total model-error)) (exp-error primitive-error))
         (:instance lw-complex-scale-disk
          (factor (car (lw-mangoldt-bounds count primitive-error)))
          (point (lw-complex-sub
           (lw-mellin-clipped-basis-dyadic
            2 start (+ start length) (lw-mellin-common-depth cap start length sigma height error minimum-depth)
            (car (lw-log-bounds count (lw-smoothed-ramp-log-error count total model-error)))
            sigma height 0 primitive-error count (lw-smoothed-ramp-log-error count total model-error) sample-error)
           (lw-mellin-ramp-endpoint cap start length
            (car (lw-log-bounds count (lw-smoothed-ramp-log-error count total model-error))) sigma height count error)))
          (radius (* (+ 1 (/ count)) (lw-mellin-common-base-radius cap length primitive-error sample-error error)))))
   :in-theory (disable lw-smoothed-ramp-log-error-adequate lw-mangoldt-lower-coarse
                       lw-mellin-common-ramp-comparison lw-complex-scale-disk)
   :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-mfe-sub-self (equal (lw-complex-sub point point) (cons 0 0))
 :hints (("Goal" :in-theory (enable lw-complex-sub)))))
(local (defthm lw-mfe-zero-disk (lw-complex-diskp (cons 0 0) 0)
 :hints (("Goal" :in-theory (enable lw-complex-diskp lw-complexp lw-diskp)))))

(defthm lw-mellin-prime-endpoint-comparison
 (implies
  (and (rationalp cap) (<= 0 cap) (rationalp start) (<= 0 start)
       (rationalp length) (<= 0 length) (<= (+ start length) cap)
       (natp count) (natp total) (rationalp sigma) (< 1 sigma) (rationalp height)
       (rationalp model-error) (< 0 model-error) (rationalp primitive-error) (< 0 primitive-error)
       (rationalp sample-error) (< 0 sample-error) (rationalp error) (< 0 error))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-mellin-clipped-prime-dyadic
     start (+ start length) (lw-mellin-common-depth cap start length sigma height error minimum-depth)
     sigma height 0 count total model-error primitive-error sample-error)
    (lw-mellin-prime-endpoint cap start length sigma height count total model-error primitive-error error))
   (* (lw-mellin-prime-endpoint-mass count primitive-error)
      (lw-mellin-common-base-radius cap length primitive-error sample-error error))))
 :hints (("Goal"
   :induct (lw-mellin-prime-endpoint cap start length sigma height count total model-error primitive-error error)
   :in-theory (enable lw-mellin-prime-endpoint lw-mellin-clipped-prime-dyadic lw-mellin-prime-endpoint-mass))
  (and stable-under-simplificationp
   '(:use (lw-mfe-weighted-ramp
           (:instance lw-complex-add-disk
            (left (lw-complex-sub
             (lw-complex-scale
              (car (lw-mangoldt-bounds count primitive-error))
              (lw-mellin-clipped-basis-dyadic
               2 start (+ start length) (lw-mellin-common-depth cap start length sigma height error minimum-depth)
               (car (lw-log-bounds count (lw-smoothed-ramp-log-error count total model-error)))
               sigma height 0 primitive-error count (lw-smoothed-ramp-log-error count total model-error) sample-error))
             (lw-complex-scale
              (car (lw-mangoldt-bounds count primitive-error))
              (lw-mellin-ramp-endpoint cap start length
               (car (lw-log-bounds count (lw-smoothed-ramp-log-error count total model-error))) sigma height count error))))
            (right (lw-complex-sub
             (lw-mellin-clipped-prime-dyadic
              start (+ start length) (lw-mellin-common-depth cap start length sigma height error minimum-depth)
              sigma height 0 (- count 1) total model-error primitive-error sample-error)
             (lw-mellin-prime-endpoint cap start length sigma height (- count 1) total model-error primitive-error error)))
            (radius (* (car (lw-mangoldt-bounds count primitive-error)) (+ 1 (/ count))
                       (lw-mellin-common-base-radius cap length primitive-error sample-error error)))
            (other-radius (* (lw-mellin-prime-endpoint-mass (- count 1) primitive-error)
                             (lw-mellin-common-base-radius cap length primitive-error sample-error error)))))
     :in-theory (disable lw-mellin-prime-endpoint lw-mellin-clipped-prime-dyadic
                         lw-mellin-prime-endpoint-mass lw-complex-add-disk)
     :nonlinearp nil :do-not-induct t))))

