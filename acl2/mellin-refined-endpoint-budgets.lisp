(in-package "ACL2")

(include-book "mellin-refined-endpoints")
(include-book "mellin-dyadic-normalization")

; Compute arbitrarily small quadrature/endpoint comparison error after
; choosing the interval, retaining the same finite coefficients/cutpoints.

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

(local (defthm lw-mrb-left-commutes
 (equal (* a (* b c)) (* b (* a c)))
 :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                       (:instance associativity-of-* (x b) (y a) (z c))
                       (:instance commutativity-of-* (x a) (y b)))
                 :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-mrb-left-distributes
 (equal (* (+ a b) c) (+ (* a c) (* b c)))
 :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                 :in-theory (disable distributivity)))))

(local (defthm lw-mrb-zero-times (equal (* 0 a) 0)))

(local (defthm lw-mrb-times-negative
         (equal (* a (- b)) (- (* a b)))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))

(local (defthm lw-mrb-negative-times
         (equal (* (- a) b) (- (* a b)))
         :hints (("Goal" :use ((:instance lw-mrb-times-negative (a b) (b a)))
                         :in-theory (disable lw-mrb-times-negative)))))

(local (defthm lw-mrb-multiply-order
 (implies (and (rationalp a) (rationalp b) (<= a b) (rationalp factor) (<= 0 factor))
  (<= (* a factor) (* b factor)))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-mrb-nonnegative-product
 (implies (and (rationalp a) (<= 0 a) (rationalp b) (<= 0 b)) (<= 0 (* a b)))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-mrb-input-data
 (implies
  (and (rationalp model-cap) (<= 0 model-cap)
       (rationalp cap) (<= 0 cap) (rationalp model-error) (< 0 model-error))
  (and (rationalp (lw-signal-exponential-precision model-cap model-error)) (< 0 (lw-signal-exponential-precision model-cap model-error))
       (rationalp (lw-mellin-prime-endpoint-mass (lw-log-signal-ramp-count model-cap) (lw-signal-exponential-precision model-cap model-error))) (<= 0 (lw-mellin-prime-endpoint-mass (lw-log-signal-ramp-count model-cap) (lw-signal-exponential-precision model-cap model-error)))
       (rationalp (abs (+ 1 (car (lw-euler-bounds (lw-signal-exponential-precision model-cap model-error)))))) (<= 0 (abs (+ 1 (car (lw-euler-bounds (lw-signal-exponential-precision model-cap model-error))))))
       (rationalp (lw-kernel-spatial-cap cap 1)) (<= 0 (lw-kernel-spatial-cap cap 1))
       (rationalp (lw-complex-exp-uniform-cap cap)) (<= 0 (lw-complex-exp-uniform-cap cap))))
 :hints (("Goal"
  :use ((:instance lw-signal-exponential-parameters (cap model-cap) (error model-error))
        (:instance lw-signal-count-natural (value (lw-log-signal-spatial-cap model-cap)))
        (:instance lw-mellin-prime-endpoint-mass-valid (count (lw-log-signal-ramp-count model-cap)) (primitive-error (lw-signal-exponential-precision model-cap model-error)))
        (:instance lw-euler-bounds-interval (epsilon (lw-signal-exponential-precision model-cap model-error)))
        (:instance lw-kernel-spatial-parameters (sigma 0) (step 1))
        (:instance lw-complex-exp-uniform-cap-data (argument-cap cap)))
  :in-theory (e/d (lw-log-signal-ramp-count lw-intervalp)
    (lw-signal-exponential-parameters lw-mellin-prime-endpoint-mass-valid
     lw-euler-bounds-interval lw-kernel-spatial-parameters lw-complex-exp-uniform-cap-data))
  :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(defun lw-mellin-refined-comparison-cost (model-cap cap length model-error)
 (let* ((beta (lw-signal-exponential-precision model-cap model-error)) (mass (lw-mellin-prime-endpoint-mass (lw-log-signal-ramp-count model-cap) beta))
        (coefficient (abs (+ 1 (car (lw-euler-bounds beta))))))
  (+ 1 (* (lw-kernel-spatial-cap cap 1) model-error)
     (* length (+ mass cap coefficient) (+ 1 (* 2 (lw-complex-exp-uniform-cap cap))))
     (+ mass 1 coefficient))))

(local (in-theory (disable lw-mellin-refined-comparison-cost)))

(local (defthm lw-mrb-cost-scalar
 (implies
  (and (rationalp cap) (<= 0 cap) (rationalp length) (<= 0 length)
       (rationalp mass) (<= 0 mass) (rationalp coefficient) (<= 0 coefficient)
       (rationalp kernel) (<= 0 kernel) (rationalp exponential) (<= 0 exponential)
       (rationalp model-error) (< 0 model-error))
  (let ((cost (+ 1 (* kernel model-error)
                 (* length (+ mass cap coefficient) (+ 1 (* 2 exponential)))
                 (+ mass 1 coefficient))))
   (and (rationalp cost) (<= 1 cost))))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defthm lw-mellin-refined-comparison-cost-valid
 (implies
  (and (rationalp model-cap) (<= 0 model-cap) (rationalp cap) (<= 0 cap)
       (rationalp length) (<= 0 length) (rationalp model-error) (< 0 model-error))
  (and (rationalp (lw-mellin-refined-comparison-cost model-cap cap length model-error)) (<= 1 (lw-mellin-refined-comparison-cost model-cap cap length model-error))))
 :hints (("Goal"
  :use (lw-mrb-input-data
        (:instance lw-mrb-cost-scalar (mass (lw-mellin-prime-endpoint-mass (lw-log-signal-ramp-count model-cap) (lw-signal-exponential-precision model-cap model-error))) (coefficient (abs (+ 1 (car (lw-euler-bounds (lw-signal-exponential-precision model-cap model-error))))))
         (kernel (lw-kernel-spatial-cap cap 1)) (exponential (lw-complex-exp-uniform-cap cap))))
  :in-theory (enable lw-mellin-refined-comparison-cost)
  :nonlinearp nil :do-not-induct t)))

(defun lw-mellin-refined-endpoint-request (model-cap cap length model-error error)
 (min 1 (min (lw-signal-exponential-precision model-cap model-error) (/ error (* 16 (lw-mellin-refined-comparison-cost model-cap cap length model-error))))))

(local (in-theory (disable lw-mellin-refined-endpoint-request)))

(local (defthm lw-mrb-request-scalar
 (implies (and (rationalp cost) (<= 1 cost) (rationalp beta) (< 0 beta)
               (rationalp error) (< 0 error))
  (let ((request (min 1 (min beta (/ error (* 16 cost))))))
   (and (rationalp request) (< 0 request) (<= request 1) (<= request beta)
        (<= request (* 1/16 error)) (<= (* cost request) (* 1/16 error)))))
 :hints (("Goal"
  :use ((:instance lw-positive-division-bound (numerator error) (divisor (* 16 cost)) (bound (* 1/16 error)))
        (:instance lw-positive-division-bound (numerator (* cost error)) (divisor (* 16 cost)) (bound (* 1/16 error)))
        (:instance lw-mrb-multiply-order
         (a (min 1 (min beta (/ error (* 16 cost))))) (b (/ error (* 16 cost))) (factor cost)))
  :nonlinearp t :do-not-induct t))
 :rule-classes nil))

(defthm lw-mellin-refined-endpoint-request-valid
 (implies
  (and (rationalp model-cap) (<= 0 model-cap) (rationalp cap) (<= 0 cap)
       (rationalp length) (<= 0 length) (rationalp model-error) (< 0 model-error)
       (rationalp error) (< 0 error))
  (and (rationalp (lw-mellin-refined-endpoint-request model-cap cap length model-error error)) (< 0 (lw-mellin-refined-endpoint-request model-cap cap length model-error error)) (<= (lw-mellin-refined-endpoint-request model-cap cap length model-error error) 1) (<= (lw-mellin-refined-endpoint-request model-cap cap length model-error error) (lw-signal-exponential-precision model-cap model-error))
       (<= (lw-mellin-refined-endpoint-request model-cap cap length model-error error) (* 1/16 error)) (<= (* (lw-mellin-refined-comparison-cost model-cap cap length model-error) (lw-mellin-refined-endpoint-request model-cap cap length model-error error)) (* 1/16 error))))
 :hints (("Goal"
  :use (lw-mrb-input-data lw-mellin-refined-comparison-cost-valid
        (:instance lw-mrb-request-scalar (cost (lw-mellin-refined-comparison-cost model-cap cap length model-error)) (beta (lw-signal-exponential-precision model-cap model-error))))
  :in-theory (e/d (lw-mellin-refined-endpoint-request) (lw-mellin-refined-comparison-cost-valid))
  :nonlinearp nil :do-not-induct t)))

(defun lw-mellin-refined-minimum-depth (length mesh)
 (lw-halving-depth length mesh (lw-precision-fuel length mesh)))

(local (in-theory (disable lw-mellin-refined-minimum-depth)))

(local (defthm lw-mrb-minimum-depth-data
 (implies (and (rationalp length) (<= 0 length) (rationalp mesh) (< 0 mesh))
  (and (natp (lw-mellin-refined-minimum-depth length mesh))
       (<= (lw-halved-width length (lw-mellin-refined-minimum-depth length mesh)) mesh)))
 :hints (("Goal"
  :use ((:instance lw-precision-fuel-adequate (width length) (epsilon mesh))
        (:instance lw-halving-depth-adequate (width length) (epsilon mesh) (fuel (lw-precision-fuel length mesh))))
  :in-theory (enable lw-mellin-refined-minimum-depth)
  :do-not-induct t))
 :rule-classes nil))

(defthm lw-mellin-refined-common-depth-budget
 (implies
  (and (rationalp cap) (<= 0 cap) (rationalp start) (< 0 start)
       (rationalp length) (<= 0 length) (rationalp sigma) (< 1 sigma)
       (rationalp height) (rationalp request) (< 0 request))
  (let ((depth (lw-mellin-common-depth cap start length sigma height request
                (lw-mellin-refined-minimum-depth length (min start request)))))
   (and (natp depth)
        (<= (lw-halved-width length depth) request)
        (<= (lw-halved-width length depth) start))))
 :hints (("Goal"
  :use ((:instance lw-mrb-minimum-depth-data (mesh (min start request)))
        (:instance lw-mellin-common-depth-adequate (error request)
         (minimum-depth (lw-mellin-refined-minimum-depth length (min start request))))
        (:instance lw-halved-width-monotone-depth (width length)
         (small (lw-mellin-refined-minimum-depth length (min start request)))
         (large (lw-mellin-common-depth cap start length sigma height request
                  (lw-mellin-refined-minimum-depth length (min start request))))))
  :in-theory (disable lw-mellin-common-depth-adequate lw-halved-width-monotone-depth)
  :do-not-induct t)))

(local (defthm lw-mrb-diagonal-scalar
 (implies
  (and (rationalp cap) (<= 0 cap) (rationalp length) (<= 0 length)
       (rationalp mass) (<= 0 mass) (rationalp coefficient) (<= 0 coefficient)
       (rationalp kernel) (<= 0 kernel) (rationalp exponential) (<= 0 exponential)
       (rationalp model-error) (< 0 model-error)
       (rationalp request) (< 0 request) (rationalp mesh) (<= mesh request))
  (<= (+ (* mesh kernel model-error)
         (* mass (+ (* length (+ request (* 2 exponential request))) request))
         (* length cap (+ request (* 2 exponential request))) request
         (* coefficient (+ (* length (+ request (* 2 exponential request))) request)))
      (* (+ 1 (* kernel model-error)
            (* length (+ mass cap coefficient) (+ 1 (* 2 exponential)))
            (+ mass 1 coefficient))
         request)))
 :hints (("Goal"
  :use ((:instance lw-mrb-nonnegative-product (a kernel) (b model-error))
        (:instance lw-mrb-multiply-order (a mesh) (b request) (factor (* kernel model-error))))
  :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-mrb-mesh-rational
 (implies (rationalp width) (rationalp (lw-halved-width width depth)))
 :hints (("Goal" :induct (lw-halved-width width depth)
                 :in-theory (enable (:definition lw-halved-width) (:induction lw-halved-width))))))

(defthm lw-mellin-refined-endpoint-comparison-budget
 (implies
  (and (rationalp model-cap) (<= 0 model-cap) (rationalp cap) (<= 0 cap)
       (rationalp start) (< 0 start) (rationalp length) (<= 0 length)
       (rationalp sigma) (< 1 sigma) (rationalp height)
       (rationalp model-error) (< 0 model-error) (rationalp error) (< 0 error))
  (<= (+ (* (lw-halved-width length (lw-mellin-common-depth cap start length sigma height (lw-mellin-refined-endpoint-request model-cap cap length model-error error) (lw-mellin-refined-minimum-depth length (min start (lw-mellin-refined-endpoint-request model-cap cap length model-error error))))) (lw-kernel-spatial-cap cap 1) model-error)
           (lw-mellin-refined-endpoint-radius model-cap cap length model-error (lw-mellin-refined-endpoint-request model-cap cap length model-error error) (lw-mellin-refined-endpoint-request model-cap cap length model-error error) (lw-mellin-refined-endpoint-request model-cap cap length model-error error))) (* 1/16 error)))
 :hints (("Goal"
  :use (lw-mrb-input-data lw-mellin-refined-endpoint-request-valid
        (:instance lw-mellin-refined-common-depth-budget (request (lw-mellin-refined-endpoint-request model-cap cap length model-error error)))
        (:instance lw-mrb-diagonal-scalar (mass (lw-mellin-prime-endpoint-mass (lw-log-signal-ramp-count model-cap) (lw-signal-exponential-precision model-cap model-error))) (coefficient (abs (+ 1 (car (lw-euler-bounds (lw-signal-exponential-precision model-cap model-error))))))
         (kernel (lw-kernel-spatial-cap cap 1)) (exponential (lw-complex-exp-uniform-cap cap))
         (request (lw-mellin-refined-endpoint-request model-cap cap length model-error error)) (mesh (lw-halved-width length (lw-mellin-common-depth cap start length sigma height (lw-mellin-refined-endpoint-request model-cap cap length model-error error) (lw-mellin-refined-minimum-depth length (min start (lw-mellin-refined-endpoint-request model-cap cap length model-error error))))))))
  :in-theory (e/d (lw-mellin-refined-endpoint-radius lw-mellin-common-base-radius lw-mellin-refined-comparison-cost)
    (lw-mellin-refined-endpoint-request-valid lw-mellin-refined-common-depth-budget))
  :nonlinearp nil :do-not-induct t)))

(defun lw-mellin-computed-refined-endpoint
 (model-cap cap start length sigma height model-error error)
 (lw-mellin-refined-endpoint model-cap cap start length sigma height model-error (lw-mellin-refined-endpoint-request model-cap cap length model-error error)))

(local (in-theory (disable lw-mellin-computed-refined-endpoint)))

(defthm lw-mellin-computed-refined-endpoint-tail-bound
 (implies
  (and (rationalp model-cap) (<= 0 model-cap) (rationalp cap) (<= 0 cap)
       (rationalp start) (< 0 start) (rationalp length) (<= 0 length) (<= (+ start length) cap)
       (rationalp sigma) (< 2 sigma) (rationalp height) (<= 2 (* (- sigma 2) start))
       (rationalp model-error) (< 0 model-error) (<= model-error 1)
       (rationalp error) (< 0 error))
  (lw-complex-diskp (lw-mellin-computed-refined-endpoint model-cap cap start length sigma height model-error error) (+ (/ (* 10 (lw-mellin-tail-coefficient (- sigma 2) 0 1)) start) (* 1/16 error))))
 :hints (("Goal"
  :use (lw-mellin-refined-endpoint-request-valid lw-mellin-refined-endpoint-comparison-budget
        (:instance lw-mellin-refined-common-depth-budget (request (lw-mellin-refined-endpoint-request model-cap cap length model-error error)))
        (:instance lw-mellin-refined-endpoint-tail-bound
         (sample-error (lw-mellin-refined-endpoint-request model-cap cap length model-error error)) (exp-error (lw-mellin-refined-endpoint-request model-cap cap length model-error error)) (error (lw-mellin-refined-endpoint-request model-cap cap length model-error error)) (minimum-depth (lw-mellin-refined-minimum-depth length (min start (lw-mellin-refined-endpoint-request model-cap cap length model-error error)))))
        (:instance lw-complex-disk-enlarge (point (lw-mellin-computed-refined-endpoint model-cap cap start length sigma height model-error error))
         (radius (+ (/ (* 10 (lw-mellin-tail-coefficient (- sigma 2) 0 1)) start) (+ (* (lw-halved-width length (lw-mellin-common-depth cap start length sigma height (lw-mellin-refined-endpoint-request model-cap cap length model-error error) (lw-mellin-refined-minimum-depth length (min start (lw-mellin-refined-endpoint-request model-cap cap length model-error error))))) (lw-kernel-spatial-cap cap 1) model-error)
           (lw-mellin-refined-endpoint-radius model-cap cap length model-error (lw-mellin-refined-endpoint-request model-cap cap length model-error error) (lw-mellin-refined-endpoint-request model-cap cap length model-error error) (lw-mellin-refined-endpoint-request model-cap cap length model-error error))))) (cap (+ (/ (* 10 (lw-mellin-tail-coefficient (- sigma 2) 0 1)) start) (* 1/16 error)))))
  :in-theory (e/d (lw-mellin-computed-refined-endpoint)
    (lw-mellin-refined-endpoint-request-valid lw-mellin-refined-endpoint-comparison-budget
     lw-mellin-refined-common-depth-budget lw-mellin-refined-endpoint-tail-bound))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-mellin-computed-refined-endpoint-at-integral-cutoff
 (implies
  (and (rationalp model-cap) (<= 0 model-cap)
       (rationalp sigma) (< 2 sigma) (rationalp height)
       (rationalp model-error) (< 0 model-error) (<= model-error 1)
       (rationalp error) (< 0 error) (rationalp cutoff-error) (< 0 cutoff-error)
       (rationalp end) (<= (lw-mellin-integral-cutoff sigma 0 cutoff-error) end))
  (lw-complex-diskp (lw-mellin-computed-refined-endpoint model-cap end (lw-mellin-integral-cutoff sigma 0 cutoff-error) (- end (lw-mellin-integral-cutoff sigma 0 cutoff-error)) sigma height model-error error) (+ (* 5/4 cutoff-error) (* 1/16 error))))
 :hints (("Goal"
  :use ((:instance lw-mellin-integral-cutoff-valid (index 0) (error cutoff-error))
        (:instance lw-mellin-tail-cutoff-adequate (rate (- sigma 2)) (index 0) (mass 4) (error cutoff-error))
        (:instance lw-mellin-computed-refined-endpoint-tail-bound
         (cap end) (start (lw-mellin-integral-cutoff sigma 0 cutoff-error)) (length (- end (lw-mellin-integral-cutoff sigma 0 cutoff-error))))
        (:instance lw-positive-division-bound
         (numerator (* 10 (lw-mellin-tail-coefficient (- sigma 2) 0 1)))
         (divisor (lw-mellin-integral-cutoff sigma 0 cutoff-error)) (bound (* 5/4 cutoff-error)))
        (:instance lw-complex-disk-enlarge (point (lw-mellin-computed-refined-endpoint model-cap end (lw-mellin-integral-cutoff sigma 0 cutoff-error) (- end (lw-mellin-integral-cutoff sigma 0 cutoff-error)) sigma height model-error error))
         (radius (+ (/ (* 10 (lw-mellin-tail-coefficient (- sigma 2) 0 1)) (lw-mellin-integral-cutoff sigma 0 cutoff-error)) (* 1/16 error)))
         (cap (+ (* 5/4 cutoff-error) (* 1/16 error)))))
  :in-theory (e/d (lw-mellin-integral-cutoff lw-mellin-tail-coefficient)
    (lw-mellin-integral-cutoff-valid lw-mellin-computed-refined-endpoint-tail-bound lw-rational-power))
  :nonlinearp t :do-not-induct t)))
