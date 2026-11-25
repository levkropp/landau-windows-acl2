(in-package "ACL2")

(include-book "mellin-frozen-endpoints")
(include-book "mellin-dyadic-normalization")

; Allocate the full finite endpoint error without using precision-dependent
; coefficient caps. The cost depends on the containing log interval, but
; not on sigma, height, the requested error or the common mesh depth.

(local (in-theory
 (disable lw-log-bounds lw-exp-bounds lw-euler-bounds lw-mangoldt-bounds
          lw-log-signal-ramp-count lw-log-signal-spatial-cap lw-signal-count
          lw-signal-exponential-precision lw-signal-exponential-cost
          lw-mellin-common-depth lw-mellin-component-minimum-depth
          lw-mellin-prime-endpoint-mass lw-mellin-common-base-radius
          lw-mellin-frozen-endpoint lw-mellin-frozen-endpoint-radius
          lw-mellin-bounded-endpoint-radius lw-mellin-bounded-integral
          lw-mellin-integral-depth lw-mellin-integral-precision
          lw-mellin-spatial-slope lw-mellin-spatial-error-factor
          lw-mellin-signal-spatial-cap lw-mellin-signal-spatial-slope
          lw-kernel-spatial-cap lw-kernel-spatial-slope lw-complex-exp-uniform-cap lw-exp-lipschitz-cap
          lw-halved-width lw-halving-depth lw-precision-fuel
          lw-complexp lw-complex-add lw-complex-sub lw-complex-scale lw-complex-diskp lw-diskp
          lw-complex-disk-enlarge lw-disk-enlarge)))

(local (defthm lw-meb-left-commutes
 (equal (* a (* b c)) (* b (* a c)))
 :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                       (:instance associativity-of-* (x b) (y a) (z c))
                       (:instance commutativity-of-* (x a) (y b)))
                 :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-meb-left-distributes
 (equal (* (+ a b) c) (+ (* a c) (* b c)))
 :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                 :in-theory (disable distributivity)))))
(local (defthm lw-meb-fold-constants
 (implies (syntaxp (and (quotep a) (quotep b)))
          (equal (* a (* b c)) (* (* a b) c)))
 :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                 :in-theory (disable associativity-of-*)))))
(local (defthm lw-meb-zero-times (equal (* 0 a) 0)))
(local (defthm lw-meb-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))
(local (defthm lw-meb-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-meb-times-negative (a b) (b a)))
                 :in-theory (disable lw-meb-times-negative)))))
(local (defthm lw-meb-multiply-order
 (implies (and (rationalp a) (rationalp b) (<= a b) (rationalp factor) (<= 0 factor))
          (<= (* a factor) (* b factor)))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-meb-nonnegative-product
 (implies (and (rationalp a) (<= 0 a) (rationalp b) (<= 0 b)) (<= 0 (* a b)))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-meb-weighted-term
 (implies (and (rationalp count) (<= 1 count) (rationalp weight) (<= 0 weight) (<= weight count))
          (<= (* weight (+ 1 (/ count))) (* 2 count)))
 :hints (("Goal"
   :use ((:instance lw-positive-division-bound (numerator weight) (divisor count) (bound 1)))
   :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(defthm lw-mellin-prime-endpoint-mass-bound
 (implies (and (natp count) (rationalp primitive-error) (< 0 primitive-error))
          (<= (lw-mellin-prime-endpoint-mass count primitive-error) (* count (+ 1 count))))
 :hints (("Goal" :induct (lw-mellin-prime-endpoint-mass count primitive-error)
                 :in-theory (enable (:induction lw-mellin-prime-endpoint-mass)
                                    (:definition lw-mellin-prime-endpoint-mass)))
         (and stable-under-simplificationp
          '(:use ((:instance lw-mangoldt-lower-coarse (index count) (epsilon primitive-error))
                  (:instance lw-meb-weighted-term (weight (car (lw-mangoldt-bounds count primitive-error)))))
            :in-theory (disable lw-mangoldt-lower-coarse)
            :nonlinearp nil :do-not-induct t))))

(local (defthm lw-meb-count-cost-data
 (implies (and (rationalp cap) (<= 0 cap))
  (and (natp (lw-log-signal-ramp-count cap))
       (rationalp (lw-signal-exponential-cost cap)) (<= 1 (lw-signal-exponential-cost cap))))
 :hints (("Goal"
   :use (lw-log-signal-spatial-cap-valid
         (:instance lw-signal-count-natural (value (lw-log-signal-spatial-cap cap)))
         (:instance lw-meb-nonnegative-product
          (a (* 2 (+ 1 (lw-log-signal-ramp-count cap)))) (b (lw-log-signal-spatial-cap cap))))
   :in-theory (e/d (lw-log-signal-ramp-count lw-signal-exponential-cost)
                  (lw-log-signal-spatial-cap-valid))
   :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-meb-primitive-precision-scalar
 (implies (and (rationalp cost) (<= 1 cost) (rationalp error) (< 0 error))
          (<= (min 1 (/ error (* 16 cost))) error))
 :hints (("Goal"
   :use ((:instance lw-positive-division-bound (numerator error) (divisor (* 16 cost)) (bound error)))
   :nonlinearp t :do-not-induct t))
 :rule-classes nil))

(defthm lw-signal-exponential-precision-at-most-request
 (implies (and (rationalp cap) (<= 0 cap) (rationalp error) (< 0 error))
          (<= (lw-signal-exponential-precision cap error) error))
 :hints (("Goal"
   :use (lw-meb-count-cost-data
         (:instance lw-meb-primitive-precision-scalar (cost (lw-signal-exponential-cost cap))))
   :in-theory (enable lw-signal-exponential-precision) :nonlinearp nil :do-not-induct t)))

(defun lw-mellin-endpoint-family-factor (cap)
 (let ((count (lw-log-signal-ramp-count cap)))
  (+ 4 cap (* count (+ 1 count)))))

(defun lw-mellin-endpoint-cost (cap)
 (let ((factor (lw-mellin-endpoint-family-factor cap)))
  (+ 1 (* 3 cap (lw-kernel-spatial-cap cap 1))
     (* cap factor (+ 1 (* 2 (lw-complex-exp-uniform-cap cap)))) factor)))

(local (in-theory (disable lw-mellin-endpoint-family-factor lw-mellin-endpoint-cost)))

(local (defthm lw-meb-cost-scalar
 (implies (and (natp count) (rationalp cap) (<= 0 cap)
               (rationalp kernel) (<= 0 kernel) (rationalp exponential) (<= 0 exponential))
  (let* ((factor (+ 4 cap (* count (+ 1 count))))
         (cost (+ 1 (* 3 cap kernel) (* cap factor (+ 1 (* 2 exponential))) factor)))
   (and (rationalp factor) (<= 4 factor) (rationalp cost) (<= 1 cost))))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defthm lw-mellin-endpoint-cost-valid
 (implies (and (rationalp cap) (<= 0 cap))
  (and (rationalp (lw-mellin-endpoint-family-factor cap)) (<= 4 (lw-mellin-endpoint-family-factor cap))
       (rationalp (lw-mellin-endpoint-cost cap)) (<= 1 (lw-mellin-endpoint-cost cap))))
 :hints (("Goal"
   :use (lw-meb-count-cost-data
         (:instance lw-kernel-spatial-parameters (sigma 0) (step 1))
         (:instance lw-complex-exp-uniform-cap-data (argument-cap cap))
         (:instance lw-meb-cost-scalar
          (count (lw-log-signal-ramp-count cap)) (kernel (lw-kernel-spatial-cap cap 1))
          (exponential (lw-complex-exp-uniform-cap cap))))
   :in-theory (e/d (lw-mellin-endpoint-family-factor lw-mellin-endpoint-cost)
                  (lw-kernel-spatial-parameters lw-complex-exp-uniform-cap-data))
   :nonlinearp nil :do-not-induct t)))

; Bound the endpoint family independently of its primitive precision.

(local (defthm lw-meb-family-data
 (implies (and (rationalp cap) (<= 0 cap) (rationalp model-error) (< 0 model-error))
  (let* ((beta (lw-signal-exponential-precision cap model-error))
         (coefficient (abs (+ 1 (car (lw-euler-bounds beta))))))
   (and (natp (lw-log-signal-ramp-count cap))
        (rationalp beta) (< 0 beta) (<= beta 1) (<= beta model-error)
        (rationalp coefficient) (<= 0 coefficient) (<= coefficient 3))))
 :hints (("Goal"
   :use (lw-meb-count-cost-data
         (:instance lw-signal-exponential-parameters (error model-error))
         (:instance lw-signal-exponential-precision-at-most-request (error model-error))
         (:instance lw-euler-bounds-interval (epsilon (lw-signal-exponential-precision cap model-error)))
         (:instance lw-euler-bounds-coarse (epsilon (lw-signal-exponential-precision cap model-error))))
   :in-theory (e/d (lw-intervalp)
     (lw-signal-exponential-parameters lw-signal-exponential-precision-at-most-request
      lw-euler-bounds-interval lw-euler-bounds-coarse lw-euler-bounds-overlap))
   :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-meb-family-scalar
 (implies
  (and (rationalp cap) (<= 0 cap)
       (rationalp mass) (<= 0 mass) (rationalp bound) (<= mass bound)
       (rationalp coefficient) (<= 0 coefficient) (<= coefficient 3)
       (rationalp value) (<= 0 value) (rationalp larger) (<= value larger)
       (rationalp error) (<= 0 error))
  (<= (+ (* mass (+ (* cap value) error)) (* cap cap value) error
         (* coefficient (+ (* cap value) error)))
      (+ (* cap (+ bound cap 4) larger) (* (+ bound cap 4) error))))
 :hints (("Goal"
   :use ((:instance lw-meb-nonnegative-product (a cap) (b value))
         (:instance lw-meb-nonnegative-product (a cap) (b (+ bound cap 3)))
         (:instance lw-meb-nonnegative-product (a cap) (b larger))
         (:instance lw-meb-nonnegative-product (a cap) (b error))
         (:instance lw-meb-multiply-order (a mass) (b bound) (factor (+ (* cap value) error)))
         (:instance lw-meb-multiply-order (a coefficient) (b 3) (factor (+ (* cap value) error)))
         (:instance lw-meb-multiply-order (a value) (b larger) (factor (* cap (+ bound cap 3)))))
   :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-meb-basis-error-data
 (implies (and (rationalp beta) (<= 0 beta) (rationalp model-error) (<= beta model-error)
               (rationalp exponential) (<= 0 exponential) (rationalp sample-error) (<= 0 sample-error))
  (and (rationalp (+ beta (* 2 exponential sample-error)))
       (<= 0 (+ beta (* 2 exponential sample-error)))
       (<= (+ beta (* 2 exponential sample-error)) (+ model-error (* 2 exponential sample-error)))))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defthm lw-mellin-frozen-endpoint-radius-bound
 (implies
  (and (rationalp cap) (<= 0 cap) (rationalp model-error) (< 0 model-error)
       (rationalp sample-error) (< 0 sample-error) (rationalp error) (< 0 error))
  (<= (lw-mellin-frozen-endpoint-radius cap cap model-error sample-error error)
      (+ (* cap (lw-mellin-endpoint-family-factor cap)
            (+ model-error (* 2 (lw-complex-exp-uniform-cap cap) sample-error)))
         (* (lw-mellin-endpoint-family-factor cap) error))))
 :hints (("Goal"
   :use (lw-meb-family-data
         (:instance lw-mellin-prime-endpoint-mass-valid
          (count (lw-log-signal-ramp-count cap)) (primitive-error (lw-signal-exponential-precision cap model-error)))
         (:instance lw-mellin-prime-endpoint-mass-bound
          (count (lw-log-signal-ramp-count cap)) (primitive-error (lw-signal-exponential-precision cap model-error)))
         (:instance lw-complex-exp-uniform-cap-data (argument-cap cap))
         (:instance lw-meb-basis-error-data
          (beta (lw-signal-exponential-precision cap model-error)) (exponential (lw-complex-exp-uniform-cap cap)))
         (:instance lw-meb-family-scalar
          (mass (lw-mellin-prime-endpoint-mass
                   (lw-log-signal-ramp-count cap) (lw-signal-exponential-precision cap model-error)))
          (bound (* (lw-log-signal-ramp-count cap) (+ 1 (lw-log-signal-ramp-count cap))))
          (coefficient (abs (+ 1 (car (lw-euler-bounds (lw-signal-exponential-precision cap model-error))))))
          (value (+ (lw-signal-exponential-precision cap model-error)
                    (* 2 (lw-complex-exp-uniform-cap cap) sample-error)))
          (larger (+ model-error (* 2 (lw-complex-exp-uniform-cap cap) sample-error)))))
   :in-theory (e/d (lw-mellin-frozen-endpoint-radius lw-mellin-common-base-radius lw-mellin-endpoint-family-factor)
     (lw-signal-exponential-parameters lw-signal-exponential-precision-at-most-request
      lw-mellin-prime-endpoint-mass-valid lw-mellin-prime-endpoint-mass-bound lw-complex-exp-uniform-cap-data))
   :nonlinearp nil :do-not-induct t)))

; A common refinement does not increase the native quadrature mesh error.

(local (defthm lw-meb-mesh-data
 (implies (and (rationalp width) (<= 0 width))
  (and (rationalp (lw-halved-width width depth)) (<= 0 (lw-halved-width width depth))
       (<= (lw-halved-width width depth) width)))
 :hints (("Goal" :induct (lw-halved-width width depth)
                 :in-theory (enable (:induction lw-halved-width) (:definition lw-halved-width))))
 :rule-classes nil))

(local (defthm lw-meb-cross-budget-scalar
 (implies
  (and (rationalp cap) (<= 0 cap) (rationalp slope) (<= 0 slope)
       (rationalp factor) (<= 0 factor) (rationalp fine) (rationalp coarse) (<= fine coarse)
       (rationalp precision) (rationalp error)
       (<= (* cap slope coarse) (* 1/4 error)) (<= (* cap factor precision) (* 1/4 error)))
  (<= (* cap (+ (* slope (+ coarse fine)) (* factor (+ precision precision)))) error))
 :hints (("Goal"
   :use ((:instance lw-meb-nonnegative-product (a cap) (b slope))
         (:instance lw-meb-multiply-order (a fine) (b coarse) (factor (* cap slope))))
   :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(defthm lw-mellin-common-cross-depth-budget
 (implies
  (and (rationalp cap) (<= 0 cap) (rationalp sigma) (< 1 sigma) (rationalp height)
       (rationalp integral-error) (< 0 integral-error) (rationalp error) (< 0 error))
  (let* ((native (lw-mellin-integral-depth cap sigma height integral-error))
         (common (lw-mellin-common-depth cap 0 cap sigma height error native))
         (xi (lw-mellin-integral-precision cap integral-error)))
   (<= (* cap (+ (* (lw-mellin-spatial-slope cap sigma height 1)
                   (+ (lw-halved-width cap native) (lw-halved-width cap common)))
                (* (lw-mellin-spatial-error-factor cap 1) (+ xi xi))))
       integral-error)))
 :hints (("Goal"
   :use ((:instance lw-mellin-spatial-parameters (step 1))
         (:instance lw-mellin-integral-depth-adequate (error integral-error))
         (:instance lw-mellin-integral-precision-valid (error integral-error))
         (:instance lw-mellin-common-depth-adequate (start 0) (length cap)
          (minimum-depth (lw-mellin-integral-depth cap sigma height integral-error)))
         (:instance lw-meb-mesh-data (width cap)
          (depth (lw-mellin-integral-depth cap sigma height integral-error)))
         (:instance lw-meb-mesh-data (width cap)
          (depth (lw-mellin-common-depth cap 0 cap sigma height error
                   (lw-mellin-integral-depth cap sigma height integral-error))))
         (:instance lw-halved-width-monotone-depth
          (width cap) (small (lw-mellin-integral-depth cap sigma height integral-error))
          (large (lw-mellin-common-depth cap 0 cap sigma height error
                   (lw-mellin-integral-depth cap sigma height integral-error))))
         (:instance lw-meb-cross-budget-scalar
          (slope (lw-mellin-spatial-slope cap sigma height 1))
          (factor (lw-mellin-spatial-error-factor cap 1))
          (coarse (lw-halved-width cap (lw-mellin-integral-depth cap sigma height integral-error)))
          (fine (lw-halved-width cap (lw-mellin-common-depth cap 0 cap sigma height error
                                     (lw-mellin-integral-depth cap sigma height integral-error))))
          (precision (lw-mellin-integral-precision cap integral-error)) (error integral-error)))
   :in-theory (disable lw-mellin-spatial-parameters lw-mellin-integral-depth-adequate
                       lw-mellin-integral-precision-valid lw-mellin-common-depth-adequate
                       lw-halved-width-monotone-depth)
   :nonlinearp nil :do-not-induct t)))

(local (defthm lw-meb-integral-precision-scalar
 (implies (and (rationalp cap) (<= 0 cap) (rationalp factor) (<= 0 factor)
               (rationalp error) (< 0 error))
          (<= (/ error (* 4 (+ 1 (* cap factor)))) (* 1/4 error)))
 :hints (("Goal"
   :use ((:instance lw-positive-division-bound
          (numerator error) (divisor (* 4 (+ 1 (* cap factor)))) (bound (* 1/4 error))))
   :nonlinearp t :do-not-induct t))
 :rule-classes nil))

(defthm lw-mellin-integral-precision-quarter-bound
 (implies (and (rationalp cap) (<= 0 cap) (rationalp error) (< 0 error))
          (<= (lw-mellin-integral-precision cap error) (* 1/4 error)))
 :hints (("Goal"
   :use ((:instance lw-mellin-spatial-parameters (sigma 0) (height 0) (step 1))
         (:instance lw-meb-integral-precision-scalar (factor (lw-mellin-spatial-error-factor cap 1))))
   :in-theory (e/d (lw-mellin-integral-precision) (lw-mellin-spatial-parameters))
   :nonlinearp nil :do-not-induct t)))

; The same internal request controls model, quadrature and component errors.

(local (defthm lw-meb-nonnegative-triple
 (implies (and (rationalp a) (<= 0 a) (rationalp b) (<= 0 b) (rationalp c) (<= 0 c))
          (<= 0 (* a b c)))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-meb-family-radius-rational
 (implies (and (rationalp cap) (<= 0 cap) (rationalp model-error) (< 0 model-error)
               (rationalp sample-error) (< 0 sample-error) (rationalp error) (< 0 error))
          (rationalp (lw-mellin-frozen-endpoint-radius cap cap model-error sample-error error)))
 :hints (("Goal"
   :use (lw-meb-family-data
         (:instance lw-mellin-prime-endpoint-mass-valid
          (count (lw-log-signal-ramp-count cap)) (primitive-error (lw-signal-exponential-precision cap model-error)))
         (:instance lw-euler-bounds-interval (epsilon (lw-signal-exponential-precision cap model-error)))
         (:instance lw-complex-exp-uniform-cap-data (argument-cap cap)))
   :in-theory (e/d (lw-mellin-frozen-endpoint-radius lw-mellin-common-base-radius lw-intervalp)
     (lw-signal-exponential-parameters lw-signal-exponential-precision-at-most-request
      lw-mellin-prime-endpoint-mass-valid lw-complex-exp-uniform-cap-data lw-euler-bounds-interval))
   :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-meb-diagonal-scalar
 (implies
  (and (rationalp cap) (<= 0 cap) (rationalp kernel) (<= 0 kernel)
       (rationalp factor) (<= 0 factor) (rationalp exponential) (<= 0 exponential)
       (rationalp error) (< 0 error) (rationalp precision) (<= 0 precision) (<= precision error)
       (rationalp mesh) (<= mesh cap)
       (rationalp cross-radius) (<= cross-radius error)
       (rationalp family-radius)
       (<= family-radius (+ (* cap factor (+ error (* 2 exponential precision))) (* factor error))))
  (<= (+ cross-radius (* cap kernel (+ precision error)) (* mesh kernel error) family-radius)
      (* (+ 1 (* 3 cap kernel) (* cap factor (+ 1 (* 2 exponential))) factor) error)))
 :hints (("Goal"
   :use ((:instance lw-meb-nonnegative-product (a cap) (b kernel))
         (:instance lw-meb-nonnegative-triple (a cap) (b factor) (c exponential))
         (:instance lw-meb-nonnegative-product (a kernel) (b error))
         (:instance lw-meb-multiply-order (a precision) (b error)
          (factor (+ (* cap kernel) (* 2 cap factor exponential))))
         (:instance lw-meb-multiply-order (a mesh) (b cap) (factor (* kernel error))))
   :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(defthm lw-mellin-bounded-endpoint-diagonal-budget
 (implies
  (and (rationalp cap) (<= 0 cap) (rationalp sigma) (< 1 sigma) (rationalp height)
       (rationalp error) (< 0 error))
  (<= (lw-mellin-bounded-endpoint-radius cap sigma height error error error)
      (* (lw-mellin-endpoint-cost cap) error)))
 :hints (("Goal"
   :use ((:instance lw-mellin-common-cross-depth-budget (integral-error error))
         (:instance lw-mellin-integral-precision-valid)
         (:instance lw-mellin-integral-precision-quarter-bound)
         (:instance lw-mellin-frozen-endpoint-radius-bound
          (model-error error) (sample-error (lw-mellin-integral-precision cap error)))
         (:instance lw-meb-family-radius-rational
          (model-error error) (sample-error (lw-mellin-integral-precision cap error)))
         lw-mellin-endpoint-cost-valid
         (:instance lw-mellin-spatial-parameters (step 1))
         (:instance lw-kernel-spatial-parameters (step 1))
         (:instance lw-complex-exp-uniform-cap-data (argument-cap cap))
         (:instance lw-meb-mesh-data (width cap) (depth (lw-mellin-integral-depth cap sigma height error)))
         (:instance lw-meb-mesh-data (width cap)
          (depth (lw-mellin-common-depth cap 0 cap sigma height error
                   (lw-mellin-integral-depth cap sigma height error))))
         (:instance lw-meb-diagonal-scalar
          (kernel (lw-kernel-spatial-cap cap 1))
          (factor (lw-mellin-endpoint-family-factor cap)) (exponential (lw-complex-exp-uniform-cap cap))
          (precision (lw-mellin-integral-precision cap error))
          (mesh (lw-halved-width cap (lw-mellin-common-depth cap 0 cap sigma height error
                                     (lw-mellin-integral-depth cap sigma height error))))
          (cross-radius
           (* cap (+ (* (lw-mellin-spatial-slope cap sigma height 1)
                        (+ (lw-halved-width cap (lw-mellin-integral-depth cap sigma height error))
                           (lw-halved-width cap (lw-mellin-common-depth cap 0 cap sigma height error
                                                 (lw-mellin-integral-depth cap sigma height error)))))
                     (* (lw-mellin-spatial-error-factor cap 1)
                        (+ (lw-mellin-integral-precision cap error) (lw-mellin-integral-precision cap error))))))
          (family-radius (lw-mellin-frozen-endpoint-radius cap cap error (lw-mellin-integral-precision cap error) error))))
   :in-theory (e/d (lw-mellin-bounded-endpoint-radius lw-mellin-endpoint-cost)
     (lw-mellin-common-cross-depth-budget lw-mellin-integral-precision-valid lw-mellin-integral-precision-quarter-bound
      lw-mellin-frozen-endpoint-radius-bound lw-mellin-endpoint-cost-valid lw-mellin-spatial-parameters
      lw-kernel-spatial-parameters lw-complex-exp-uniform-cap-data))
   :nonlinearp nil :do-not-induct t)))

; Compute one positive internal request for any desired total error.
; The divisor 16 leaves room for later improper-cutoff comparisons.

(defun lw-mellin-endpoint-request (cap error)
 (min 1 (/ error (* 16 (lw-mellin-endpoint-cost cap)))))

(defun lw-mellin-computed-bounded-endpoint (cap sigma height error)
 (let ((request (lw-mellin-endpoint-request cap error)))
  (lw-mellin-frozen-endpoint cap 0 cap sigma height request request)))

(local (in-theory (disable lw-mellin-endpoint-request lw-mellin-computed-bounded-endpoint)))

(local (defthm lw-meb-request-scalar
 (implies (and (rationalp cost) (<= 1 cost) (rationalp error) (< 0 error))
  (let ((request (min 1 (/ error (* 16 cost)))))
   (and (rationalp request) (< 0 request) (<= request 1) (<= request (* 1/16 error))
        (<= (* cost request) (* 1/16 error)))))
 :hints (("Goal"
   :use ((:instance lw-positive-division-bound (numerator error) (divisor (* 16 cost)) (bound (* 1/16 error)))
         (:instance lw-positive-division-bound
          (numerator (* cost error)) (divisor (* 16 cost)) (bound (* 1/16 error)))
         (:instance lw-meb-multiply-order
          (a (min 1 (/ error (* 16 cost)))) (b (/ error (* 16 cost))) (factor cost)))
   :nonlinearp t :do-not-induct t))
 :rule-classes nil))

(defthm lw-mellin-endpoint-request-valid
 (implies (and (rationalp cap) (<= 0 cap) (rationalp error) (< 0 error))
  (let ((request (lw-mellin-endpoint-request cap error)))
   (and (rationalp request) (< 0 request) (<= request 1) (<= request (* 1/16 error))
        (<= (* (lw-mellin-endpoint-cost cap) request) (* 1/16 error)))))
 :hints (("Goal"
   :use (lw-mellin-endpoint-cost-valid
         (:instance lw-meb-request-scalar (cost (lw-mellin-endpoint-cost cap))))
   :in-theory (e/d (lw-mellin-endpoint-request) (lw-mellin-endpoint-cost-valid))
   :nonlinearp nil :do-not-induct t)))

(defthm lw-mellin-computed-bounded-endpoint-comparison
 (implies
  (and (rationalp cap) (<= 0 cap) (rationalp sigma) (< 1 sigma) (rationalp height)
       (rationalp error) (< 0 error))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-mellin-bounded-integral cap sigma height 0 (lw-mellin-endpoint-request cap error))
    (lw-mellin-computed-bounded-endpoint cap sigma height error))
   (* 1/16 error)))
 :hints (("Goal"
   :use (lw-mellin-endpoint-request-valid
         (:instance lw-mellin-bounded-endpoint-comparison
          (model-error (lw-mellin-endpoint-request cap error))
          (integral-error (lw-mellin-endpoint-request cap error))
          (error (lw-mellin-endpoint-request cap error)))
         (:instance lw-mellin-bounded-endpoint-diagonal-budget
          (error (lw-mellin-endpoint-request cap error)))
         (:instance lw-complex-disk-enlarge
          (point (lw-complex-sub
           (lw-mellin-bounded-integral cap sigma height 0 (lw-mellin-endpoint-request cap error))
           (lw-mellin-computed-bounded-endpoint cap sigma height error)))
          (radius (lw-mellin-bounded-endpoint-radius cap sigma height
                    (lw-mellin-endpoint-request cap error) (lw-mellin-endpoint-request cap error)
                    (lw-mellin-endpoint-request cap error)))
          (cap (* 1/16 error))))
   :in-theory (e/d (lw-mellin-computed-bounded-endpoint)
     (lw-mellin-endpoint-request-valid lw-mellin-bounded-endpoint-comparison
      lw-mellin-bounded-endpoint-diagonal-budget))
   :nonlinearp nil :do-not-induct t)))





