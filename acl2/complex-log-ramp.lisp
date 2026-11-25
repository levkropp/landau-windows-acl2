(in-package "ACL2")

(include-book "complex-laplace-ramp")
(include-book "complex-laplace-shifted")
(include-book "exp-log-ramp")

; Normalize a prime-power ramp starting at a computed logarithm.
; The shift, the logarithm error and both finite quadratures are computed;
; the logarithmic endpoint is not assumed exact.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-reciprocal lw-complex-norm-square
                 lw-complex-l1 lw-rational-power lw-complex-exp-value lw-complex-exp-cap
                 lw-complex-exp-uniform-cap lw-exp-lipschitz-cap lw-log-bounds
                 lw-complex-laplace-point lw-complex-laplace-shifted-value
                 lw-complex-laplace-shifted-grid lw-complex-mul-subtract
                 lw-complex-mul-commutative lw-complex-mul-left-commutes
                 lw-exp-bounds lw-exp-neg-bounds lw-exp-index lw-exp-band lw-exp-sum lw-exp-term
                 lw-damped-phase-sample lw-phase-value
                 lw-complex-exp-integral-value lw-complex-exp-integral-grid
                 lw-complex-exp-primitive-value lw-complex-exp-grid
                 lw-complex-disk-enlarge lw-disk-enlarge lw-precision-fuel)))

(local (defthm lw-clr-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-clr-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-clr-times-negative
         (implies (and (rationalp a) (rationalp b)) (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-clr-negative-times
         (implies (and (rationalp a) (rationalp b)) (equal (* (- a) b) (- (* a b))))))
(local (defthm lw-clr-zero-times (equal (* 0 a) 0)))
(local (defthm lw-clr-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))
(local (defthm lw-clr-double-negative (implies (rationalp a) (equal (- (- a)) a))))
(local (defthm lw-clr-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))
(local (defthm lw-clr-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))
(local (defthm lw-clr-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))
(local (defthm lw-clr-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))
(local (defthm lw-clr-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-clr-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-clr-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-clr-left-commutes)))))
(local (defthm lw-clr-fuel-natural
         (natp (lw-precision-fuel width error))
         :hints (("Goal" :in-theory (enable lw-precision-fuel)))
         :rule-classes (:rewrite :type-prescription)))
(local (defthm lw-clr-pair-complex
         (implies (and (rationalp a) (rationalp b)) (lw-complexp (cons a b)))
         :hints (("Goal" :in-theory (enable lw-complexp)))))


(defun lw-complex-log-ramp-start (index delta) (car (lw-log-bounds index delta)))

(defun lw-complex-log-ramp-exp (rate height index delta)
  (lw-complex-exp-value
    (lw-complex-scale (lw-complex-log-ramp-start index delta) (lw-complex-laplace-point rate height))
    delta))

(defun lw-complex-log-ramp-cap (rate height index)
  (+ (lw-complex-exp-uniform-cap (* (+ rate (abs height)) index))
     (lw-complex-exp-uniform-cap index) 2))

(local (defthm lw-clr-start-data
         (implies (and (rationalp index) (< 1 index) (rationalp delta) (< 0 delta))
                  (and (rationalp (lw-complex-log-ramp-start index delta))
                       (<= 0 (lw-complex-log-ramp-start index delta))
                       (<= (lw-complex-log-ramp-start index delta) index)))
         :hints (("Goal"
                  :use ((:instance lw-log-bounds-interval (value index) (epsilon delta))
                        (:instance lw-log-bounds-lower-coarse (value index) (epsilon delta)))
                  :in-theory (e/d (lw-intervalp)
                                  (lw-log-bounds-interval lw-log-bounds-lower-coarse))
                  :do-not-induct t))))

(local (defthm lw-clr-scale-laplace
         (implies (and (rationalp rate) (rationalp height) (rationalp start))
                  (equal (lw-complex-scale start (lw-complex-laplace-point rate height))
                         (cons (- (* rate start)) (- (* height start)))))
         :hints (("Goal" :in-theory (enable lw-complex-scale lw-complex-laplace-point)))))

(local (defthm lw-clr-point-data
         (implies (and (rationalp rate) (< 1 rate) (rationalp height)
                       (rationalp start) (<= 0 start) (rationalp index) (<= start index))
                  (and
                   (lw-complexp (cons start 0))
                   (lw-complexp (lw-complex-scale start (lw-complex-laplace-point rate height)))
                   (<= 0 (* rate start))
                   (<= 0 (* (+ rate (abs height)) index))
                   (<= (lw-complex-l1 (cons start 0)) index)
                   (<= (lw-complex-l1 (lw-complex-scale start (lw-complex-laplace-point rate height)))
                       (* (+ rate (abs height)) index))
                   (equal (lw-complex-add (cons start 0)
                             (lw-complex-scale start (lw-complex-laplace-point rate height)))
                          (lw-complex-scale start (lw-complex-laplace-point (- rate 1) height)))))
         :hints (("Goal" :cases ((<= 0 height))
                         :in-theory (enable lw-complexp lw-complex-add lw-complex-scale
                                            lw-complex-laplace-point lw-complex-l1)
                         :nonlinearp t))))

(local (defthm lw-clr-real-difference-disk
         (implies (and (rationalp a) (rationalp b) (rationalp error) (<= (abs (- a b)) error))
                  (lw-complex-diskp (lw-complex-sub (cons a 0) (cons b 0)) error))
         :hints (("Goal" :in-theory (enable lw-complex-diskp lw-complex-sub lw-complexp lw-diskp)
                         :cases ((<= a b)) :nonlinearp t))
         :rule-classes nil))

(local (defthm lw-clr-residual-identity
         (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c) (rationalp index))
                  (equal
                   (lw-complex-add (lw-complex-sub c (lw-complex-mul a b))
                     (lw-complex-mul (lw-complex-sub a (cons index 0)) b))
                   (lw-complex-sub c (lw-complex-scale index b))))
         :hints (("Goal" :in-theory
                  (enable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale)))))

(local (defthm lw-clr-residual-disk
         (implies
          (and (lw-complexp a) (lw-complexp b) (lw-complexp c) (rationalp index)
               (lw-complex-diskp b 2)
               (lw-complex-diskp (lw-complex-sub c (lw-complex-mul a b)) radius)
               (lw-complex-diskp (lw-complex-sub a (cons index 0)) real-error))
          (lw-complex-diskp (lw-complex-sub c (lw-complex-scale index b))
                            (+ radius (* 2 real-error))))
         :hints (("Goal"
                  :use ((:instance lw-complex-mul-disk
                          (left (lw-complex-sub a (cons index 0))) (right b)
                          (radius real-error) (other-radius 2))
                        (:instance lw-complex-add-disk
                          (left (lw-complex-sub c (lw-complex-mul a b)))
                          (right (lw-complex-mul (lw-complex-sub a (cons index 0)) b))
                          (other-radius (* 2 real-error))))
                  :in-theory (disable lw-complex-mul-disk lw-complex-add-disk lw-complex-sub-add-first)))
         :rule-classes nil))

(defthm lw-complex-log-ramp-exp-normalization
  (implies
   (and (rationalp rate) (< 1 rate) (rationalp height) (rationalp index) (< 1 index)
        (rationalp delta) (< 0 delta) (<= delta 1))
   (lw-complex-diskp
    (lw-complex-sub
      (lw-complex-log-ramp-exp (- rate 1) height index delta)
      (lw-complex-scale index (lw-complex-log-ramp-exp rate height index delta)))
    (* (+ (lw-complex-log-ramp-cap rate height index) (* 2 (lw-exp-lipschitz-cap index)) 4) delta)))
  :hints (("Goal"
           :use (lw-clr-start-data
                 (:instance lw-clr-point-data (start (lw-complex-log-ramp-start index delta)))
                 (:instance lw-exp-log-inverse-error (point index) (log-error delta) (exp-error delta))
                 (:instance lw-exp-bounds-valid (value (lw-complex-log-ramp-start index delta)) (epsilon delta))
                 (:instance lw-exp-lipschitz-cap-valid (cap index))
                 (:instance lw-complex-exp-cap-uniform
                   (point (cons (lw-complex-log-ramp-start index delta) 0)) (argument-cap index))
                 (:instance lw-complex-exp-cap-uniform
                   (point (lw-complex-scale (lw-complex-log-ramp-start index delta)
                                           (lw-complex-laplace-point rate height)))
                   (argument-cap (* (+ rate (abs height)) index)))
                 (:instance lw-complex-exp-value-multiplication
                   (left (cons (lw-complex-log-ramp-start index delta) 0))
                   (right (lw-complex-scale (lw-complex-log-ramp-start index delta)
                                            (lw-complex-laplace-point rate height)))
                   (left-error delta) (right-error delta) (sum-error delta))
                 (:instance lw-clr-multiply-order
                   (a (+ (lw-complex-exp-cap (cons (lw-complex-log-ramp-start index delta) 0))
                         (lw-complex-exp-cap
                           (lw-complex-scale (lw-complex-log-ramp-start index delta)
                                             (lw-complex-laplace-point rate height))) 2))
                   (b (lw-complex-log-ramp-cap rate height index)) (factor delta))
                 (:instance lw-complex-difference-symmetric
                   (left (lw-complex-mul
                     (lw-complex-exp-value (cons (lw-complex-log-ramp-start index delta) 0) delta)
                     (lw-complex-log-ramp-exp rate height index delta)))
                   (right (lw-complex-log-ramp-exp (- rate 1) height index delta))
                   (radius
                     (+ (* (lw-complex-exp-cap
                             (lw-complex-scale (lw-complex-log-ramp-start index delta)
                                               (lw-complex-laplace-point rate height))) delta)
                        (* (lw-complex-exp-cap (cons (lw-complex-log-ramp-start index delta) 0)) delta)
                        (* 2 delta))))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-complex-sub
                     (lw-complex-log-ramp-exp (- rate 1) height index delta)
                     (lw-complex-mul
                       (lw-complex-exp-value (cons (lw-complex-log-ramp-start index delta) 0) delta)
                       (lw-complex-log-ramp-exp rate height index delta))))
                   (radius
                     (+ (* (lw-complex-exp-cap
                             (lw-complex-scale (lw-complex-log-ramp-start index delta)
                                               (lw-complex-laplace-point rate height))) delta)
                        (* (lw-complex-exp-cap (cons (lw-complex-log-ramp-start index delta) 0)) delta)
                        (* 2 delta)))
                   (cap (* (lw-complex-log-ramp-cap rate height index) delta)))
                 (:instance lw-complex-exp-damped-cap
                   (value (* rate (lw-complex-log-ramp-start index delta)))
                   (angle (- (* height (lw-complex-log-ramp-start index delta)))) (error delta))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-complex-log-ramp-exp rate height index delta))
                   (radius (+ 1 delta)) (cap 2))
                 (:instance lw-clr-real-difference-disk
                   (a (car (lw-exp-bounds (lw-complex-log-ramp-start index delta) delta)))
                   (b index) (error (+ (* (lw-exp-lipschitz-cap index) delta) (* 2 delta))))
                 (:instance lw-clr-residual-disk
                   (a (lw-complex-exp-value (cons (lw-complex-log-ramp-start index delta) 0) delta))
                   (b (lw-complex-log-ramp-exp rate height index delta))
                   (c (lw-complex-log-ramp-exp (- rate 1) height index delta))
                   (radius (* (lw-complex-log-ramp-cap rate height index) delta))
                   (real-error (+ (* (lw-exp-lipschitz-cap index) delta) (* 2 delta))))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-complex-sub
                     (lw-complex-log-ramp-exp (- rate 1) height index delta)
                     (lw-complex-scale index (lw-complex-log-ramp-exp rate height index delta))))
                   (radius (+ (* (lw-complex-log-ramp-cap rate height index) delta)
                              (* 2 (+ (* (lw-exp-lipschitz-cap index) delta) (* 2 delta)))))
                   (cap (* (+ (lw-complex-log-ramp-cap rate height index)
                              (* 2 (lw-exp-lipschitz-cap index)) 4) delta))))
           :in-theory
           (e/d (lw-complex-log-ramp-exp lw-complex-log-ramp-start lw-intervalp)
                (lw-clr-start-data lw-clr-point-data lw-exp-log-inverse-error lw-exp-bounds-valid
                 lw-exp-lipschitz-cap-valid lw-complex-exp-cap-uniform lw-complex-exp-value-multiplication
                 lw-complex-exp-damped-cap lw-complex-sub-add-first))
           :nonlinearp nil :do-not-induct t)))

(defun lw-complex-log-ramp-endpoint (rate height index delta)
  (lw-complex-sub
    (lw-complex-scale (/ index)
      (lw-complex-mul (lw-complex-log-ramp-exp (- rate 1) height index delta)
                       (lw-complex-reciprocal (cons (- rate 1) height))))
    (lw-complex-mul (lw-complex-log-ramp-exp rate height index delta)
                     (lw-complex-reciprocal (cons rate height)))))

(defun lw-complex-log-ramp-model (rate height index delta)
  (lw-complex-mul (lw-complex-log-ramp-exp rate height index delta)
    (lw-complex-sub (lw-complex-reciprocal (cons (- rate 1) height))
                    (lw-complex-reciprocal (cons rate height)))))

(defthm lw-complex-log-ramp-exp-rational
  (implies (and (rationalp rate) (rationalp height) (rationalp index) (< 1 index)
                (rationalp delta) (< 0 delta))
           (lw-complexp (lw-complex-log-ramp-exp rate height index delta)))
  :hints (("Goal" :use (lw-clr-start-data)
                   :in-theory (disable lw-clr-start-data) :do-not-induct t)))

(defthm lw-complex-log-ramp-endpoints-rational
  (implies
   (and (rationalp rate) (< 1 rate) (rationalp height) (rationalp index) (< 1 index)
        (rationalp delta) (< 0 delta))
   (and (lw-complexp (lw-complex-log-ramp-endpoint rate height index delta))
        (lw-complexp (lw-complex-log-ramp-model rate height index delta))))
  :hints (("Goal" :use (lw-clr-start-data)
                   :in-theory (disable lw-clr-start-data)
                   :nonlinearp t :do-not-induct t)))

(defthm lw-complex-log-ramp-model-identity
  (implies
   (and (rationalp rate) (< 1 rate) (rationalp height) (rationalp index) (< 1 index)
        (rationalp delta) (< 0 delta))
   (equal
    (lw-complex-log-ramp-model rate height index delta)
    (lw-complex-mul (lw-complex-log-ramp-exp rate height index delta)
      (lw-complex-reciprocal (lw-complex-mul (cons (- rate 1) height) (cons rate height)))))))

(local (in-theory (disable lw-complex-log-ramp-model-identity lw-complex-log-ramp-exp
                          lw-complex-log-ramp-start lw-complex-log-ramp-cap)))

(local (defthm lw-clr-endpoint-difference
         (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp p) (lw-complexp q)
                       (rationalp index) (< 0 index))
                  (equal
                   (lw-complex-sub
                    (lw-complex-sub (lw-complex-scale (/ index) (lw-complex-mul a p))
                                     (lw-complex-mul b q))
                    (lw-complex-mul b (lw-complex-sub p q)))
                   (lw-complex-scale (/ index)
                     (lw-complex-mul (lw-complex-sub a (lw-complex-scale index b)) p))))
         :hints (("Goal"
                  :use ((:instance inverse-of-* (x index)))
                  :in-theory (e/d (lw-complexp lw-complex-add lw-complex-sub
                                    lw-complex-mul lw-complex-scale) (inverse-of-*))))))

(local (defthm lw-clr-positive-clearance
         (implies (and (rationalp rate) (< 0 rate) (rationalp height))
                  (<= (* rate rate) (lw-complex-norm-square (cons rate height))))
         :hints (("Goal" :in-theory (enable lw-complex-norm-square) :nonlinearp t))))

(defthm lw-complex-log-ramp-endpoint-normalization
  (implies
   (and (rationalp rate) (< 1 rate) (rationalp height) (rationalp index) (< 1 index)
        (rationalp delta) (< 0 delta) (<= delta 1))
   (lw-complex-diskp
    (lw-complex-sub (lw-complex-log-ramp-endpoint rate height index delta)
                    (lw-complex-log-ramp-model rate height index delta))
    (* (+ (lw-complex-log-ramp-cap rate height index) (* 2 (lw-exp-lipschitz-cap index)) 4)
       delta (/ index) (/ (- rate 1)))))
  :hints (("Goal"
           :use (lw-complex-log-ramp-exp-normalization lw-complex-log-ramp-endpoints-rational
                 (:instance lw-clr-positive-clearance (rate (- rate 1)))
                 (:instance lw-complex-reciprocal-disk-bound
                   (point (cons (- rate 1) height)) (lower (- rate 1)))
                 (:instance lw-complex-mul-disk
                   (left (lw-complex-sub
                     (lw-complex-log-ramp-exp (- rate 1) height index delta)
                     (lw-complex-scale index (lw-complex-log-ramp-exp rate height index delta))))
                   (radius (* (+ (lw-complex-log-ramp-cap rate height index)
                                 (* 2 (lw-exp-lipschitz-cap index)) 4) delta))
                   (right (lw-complex-reciprocal (cons (- rate 1) height))) (other-radius (/ (- rate 1))))
                 (:instance lw-complex-scale-disk
                   (factor (/ index))
                   (point (lw-complex-mul
                     (lw-complex-sub
                       (lw-complex-log-ramp-exp (- rate 1) height index delta)
                       (lw-complex-scale index (lw-complex-log-ramp-exp rate height index delta)))
                     (lw-complex-reciprocal (cons (- rate 1) height))))
                   (radius (* (+ (lw-complex-log-ramp-cap rate height index)
                                 (* 2 (lw-exp-lipschitz-cap index)) 4) delta (/ (- rate 1)))))
                 (:instance lw-clr-endpoint-difference
                   (a (lw-complex-log-ramp-exp (- rate 1) height index delta))
                   (b (lw-complex-log-ramp-exp rate height index delta))
                   (p (lw-complex-reciprocal (cons (- rate 1) height)))
                   (q (lw-complex-reciprocal (cons rate height)))))
           :in-theory
           (e/d (lw-complex-log-ramp-endpoint lw-complex-log-ramp-model)
                (lw-complex-log-ramp-exp-normalization lw-complex-log-ramp-endpoints-rational
                 lw-complex-reciprocal-disk-bound lw-complex-mul-disk lw-complex-scale-disk
                 lw-complex-scale-product lw-complex-laplace-ramp-reciprocal-identity
                 lw-complex-reciprocal-difference
                 lw-clr-endpoint-difference))
           :nonlinearp nil :do-not-induct t)))

(defun lw-complex-log-ramp-grid (rate height index delta)
  (lw-complex-sub
    (lw-complex-scale (/ index)
      (lw-complex-laplace-shifted-grid (- rate 1) height
        (lw-complex-log-ramp-start index delta) (* 64 delta (/ (- rate 1)))))
    (lw-complex-laplace-shifted-grid rate height
      (lw-complex-log-ramp-start index delta) (* 64 delta (/ rate)))))

(local (defthm lw-clr-ray-error-data
         (implies (and (rationalp rate) (< 0 rate) (rationalp delta) (< 0 delta))
                  (and (rationalp (* 64 delta (/ rate))) (< 0 (* 64 delta (/ rate)))
                       (equal (* 1/64 rate (* 64 delta (/ rate))) delta)))
         :hints (("Goal" :use ((:instance inverse-of-* (x rate)))
                         :in-theory (disable inverse-of-*) :nonlinearp t))))

(local (defthm lw-clr-shifted-value
         (implies (and (rationalp rate) (< 0 rate) (rationalp height)
                       (rationalp index) (< 1 index) (rationalp delta) (< 0 delta))
                  (equal
                   (lw-complex-laplace-shifted-value rate height
                     (lw-complex-log-ramp-start index delta) (* 64 delta (/ rate)))
                   (lw-complex-mul (lw-complex-log-ramp-exp rate height index delta)
                                    (lw-complex-reciprocal (cons rate height)))))
         :hints (("Goal"
                  :use (lw-clr-start-data lw-clr-ray-error-data
                        (:instance lw-complex-laplace-shifted-value-identity
                          (start (lw-complex-log-ramp-start index delta)) (error (* 64 delta (/ rate)))))
                  :in-theory (e/d (lw-complex-log-ramp-exp)
                                  (lw-clr-start-data lw-clr-ray-error-data
                                   lw-complex-laplace-shifted-value-identity))
                  :nonlinearp nil :do-not-induct t))))

(defthm lw-complex-log-ramp-grid-rational
  (implies
   (and (rationalp rate) (< 1 rate) (rationalp height) (rationalp index) (< 1 index)
        (rationalp delta) (< 0 delta))
   (lw-complexp (lw-complex-log-ramp-grid rate height index delta)))
  :hints (("Goal"
           :use (lw-clr-start-data lw-clr-ray-error-data
                 (:instance lw-clr-ray-error-data (rate (- rate 1))))
           :in-theory (disable lw-clr-start-data lw-clr-ray-error-data) :do-not-induct t)))

(local (defthm lw-clr-combination-differences
         (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c) (lw-complexp d)
                       (rationalp factor))
                  (equal
                   (lw-complex-sub (lw-complex-sub (lw-complex-scale factor a) b)
                                    (lw-complex-sub (lw-complex-scale factor c) d))
                   (lw-complex-sub (lw-complex-scale factor (lw-complex-sub a c))
                                    (lw-complex-sub b d))))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-sub lw-complex-scale)))))

(defthm lw-complex-log-ramp-grid-error
  (implies
   (and (rationalp rate) (< 1 rate) (rationalp height) (rationalp index) (< 1 index)
        (rationalp delta) (< 0 delta))
   (lw-complex-diskp
    (lw-complex-sub (lw-complex-log-ramp-endpoint rate height index delta)
                    (lw-complex-log-ramp-grid rate height index delta))
    (+ (* 64 delta (/ index) (/ (- rate 1))) (* 64 delta (/ rate)))))
  :hints (("Goal"
           :use (lw-clr-start-data lw-clr-ray-error-data
                 (:instance lw-clr-ray-error-data (rate (- rate 1)))
                 (:instance lw-complex-laplace-shifted-grid-endpoint
                   (rate (- rate 1)) (start (lw-complex-log-ramp-start index delta))
                   (error (* 64 delta (/ (- rate 1)))))
                 (:instance lw-complex-laplace-shifted-grid-endpoint
                   (start (lw-complex-log-ramp-start index delta)) (error (* 64 delta (/ rate))))
                 (:instance lw-clr-shifted-value (rate (- rate 1)))
                 lw-clr-shifted-value
                 (:instance lw-complex-scale-disk
                   (factor (/ index))
                   (point (lw-complex-sub
                     (lw-complex-mul (lw-complex-log-ramp-exp (- rate 1) height index delta)
                                      (lw-complex-reciprocal (cons (- rate 1) height)))
                     (lw-complex-laplace-shifted-grid (- rate 1) height
                       (lw-complex-log-ramp-start index delta) (* 64 delta (/ (- rate 1))))))
                   (radius (* 64 delta (/ (- rate 1)))))
                 (:instance lw-complex-sub-disk
                   (left (lw-complex-scale (/ index)
                     (lw-complex-sub
                       (lw-complex-mul (lw-complex-log-ramp-exp (- rate 1) height index delta)
                                        (lw-complex-reciprocal (cons (- rate 1) height)))
                       (lw-complex-laplace-shifted-grid (- rate 1) height
                         (lw-complex-log-ramp-start index delta) (* 64 delta (/ (- rate 1)))))))
                   (radius (* 64 delta (/ index) (/ (- rate 1))))
                   (right (lw-complex-sub
                     (lw-complex-mul (lw-complex-log-ramp-exp rate height index delta)
                                      (lw-complex-reciprocal (cons rate height)))
                     (lw-complex-laplace-shifted-grid rate height
                       (lw-complex-log-ramp-start index delta) (* 64 delta (/ rate)))))
                   (other-radius (* 64 delta (/ rate)))))
           :in-theory
           (e/d (lw-complex-log-ramp-grid lw-complex-log-ramp-endpoint)
                (lw-clr-start-data lw-clr-ray-error-data lw-clr-shifted-value
                 lw-complex-laplace-shifted-grid-endpoint lw-complex-scale-disk lw-complex-sub-disk
                 lw-complex-scale-product lw-complex-sub-add-first))
           :nonlinearp nil :do-not-induct t)))

(defun lw-complex-log-ramp-cost (rate height index)
  (* (+ 128 (lw-complex-log-ramp-cap rate height index) (* 2 (lw-exp-lipschitz-cap index)))
     (+ 1 (/ (- rate 1)) (/ rate))))

(defun lw-complex-log-ramp-precision (rate height index error)
  (min 1 (/ error (* 4 (lw-complex-log-ramp-cost rate height index)))))

(defun lw-complex-log-ramp-value (rate height index error)
  (lw-complex-log-ramp-grid rate height index (lw-complex-log-ramp-precision rate height index error)))

(local (defthm lw-clr-cap-data
         (implies (and (rationalp rate) (< 1 rate) (rationalp height) (rationalp index) (< 1 index))
                  (and (rationalp (lw-complex-log-ramp-cap rate height index))
                       (<= 4 (lw-complex-log-ramp-cap rate height index))
                       (rationalp (lw-exp-lipschitz-cap index))
                       (<= 1 (lw-exp-lipschitz-cap index))))
         :hints (("Goal"
                  :use ((:instance lw-clr-point-data (start 0))
                        (:instance lw-complex-exp-uniform-cap-data (argument-cap index))
                        (:instance lw-complex-exp-uniform-cap-data (argument-cap (* (+ rate (abs height)) index)))
                        (:instance lw-exp-lipschitz-cap-valid (cap index)))
                  :in-theory (e/d (lw-complex-log-ramp-cap)
                                  (lw-clr-point-data lw-complex-exp-uniform-cap-data lw-exp-lipschitz-cap-valid))
                  :do-not-induct t))))

(local (defthm lw-clr-small-precision
         (implies (and (rationalp cost) (< 0 cost) (rationalp error) (< 0 error))
                  (let ((delta (min 1 (/ error (* 4 cost)))))
                    (and (rationalp delta) (< 0 delta) (<= delta 1) (<= (* cost delta) (* 1/4 error)))))
         :hints (("Goal"
                  :use ((:instance lw-clr-multiply-order
                          (a (min 1 (/ error (* 4 cost)))) (b (/ error (* 4 cost))) (factor cost))
                        (:instance lw-positive-division-bound
                          (numerator (* cost error)) (divisor (* 4 cost)) (bound (* 1/4 error))))
                  :nonlinearp t :do-not-induct t))
         :rule-classes nil))

(local (defthm lw-clr-scalar-budget
         (implies
          (and (rationalp rate) (< 1 rate) (rationalp index) (< 1 index)
               (rationalp cap) (<= 128 cap) (rationalp delta) (< 0 delta)
               (rationalp error) (< 0 error)
               (<= (* cap (+ 1 (/ (- rate 1)) (/ rate)) delta) (* 1/4 error)))
          (<= (+ (* (- cap 60) delta (/ index) (/ (- rate 1))) (* 64 delta (/ rate))) error))
         :hints (("Goal"
                  :use ((:instance lw-reciprocal-antitone (left 1) (right index))
                        (:instance lw-clr-positive-product (a delta) (b (/ (- rate 1))))
                        (:instance lw-clr-positive-product (a (- cap 60)) (b (* delta (/ (- rate 1)))))
                        (:instance lw-clr-positive-product (a delta) (b (/ rate)))
                        (:instance lw-clr-positive-product (a cap) (b delta))
                        (:instance lw-clr-multiply-order
                          (a (/ index)) (b 1) (factor (* (- cap 60) delta (/ (- rate 1)))))
                        (:instance lw-clr-multiply-order
                          (a (- cap 60)) (b cap) (factor (* delta (/ (- rate 1)))))
                        (:instance lw-clr-multiply-order
                          (a 64) (b cap) (factor (* delta (/ rate)))))
                  :in-theory (disable lw-reciprocal-antitone)
                  :nonlinearp nil :do-not-induct t))
         :rule-classes nil))

(defthm lw-complex-log-ramp-precision-adequate
  (implies
   (and (rationalp rate) (< 1 rate) (rationalp height) (rationalp index) (< 1 index)
        (rationalp error) (< 0 error))
   (let ((delta (lw-complex-log-ramp-precision rate height index error)))
     (and (rationalp delta) (< 0 delta) (<= delta 1)
          (<= (+ (* (+ (lw-complex-log-ramp-cap rate height index) (* 2 (lw-exp-lipschitz-cap index)) 4)
                    delta (/ index) (/ (- rate 1)))
                 (* 64 delta (/ index) (/ (- rate 1))) (* 64 delta (/ rate)))
              error))))
  :hints (("Goal"
           :use (lw-clr-cap-data
                 (:instance lw-clr-positive-product
                   (a (+ 128 (lw-complex-log-ramp-cap rate height index) (* 2 (lw-exp-lipschitz-cap index))))
                   (b (+ 1 (/ (- rate 1)) (/ rate))))
                 (:instance lw-clr-small-precision (cost (lw-complex-log-ramp-cost rate height index)))
                 (:instance lw-clr-scalar-budget
                   (cap (+ 128 (lw-complex-log-ramp-cap rate height index) (* 2 (lw-exp-lipschitz-cap index))))
                   (delta (lw-complex-log-ramp-precision rate height index error))))
           :in-theory (e/d (lw-complex-log-ramp-precision lw-complex-log-ramp-cost)
                           (lw-clr-cap-data lw-exp-lipschitz-cap-valid))
           :nonlinearp nil :do-not-induct t)))

(local (in-theory
        (disable lw-complex-log-ramp-cost lw-complex-log-ramp-precision
                 lw-complex-log-ramp-grid lw-complex-log-ramp-endpoint lw-complex-log-ramp-model)))

(defthm lw-complex-log-ramp-value-rational
  (implies
   (and (rationalp rate) (< 1 rate) (rationalp height) (rationalp index) (< 1 index)
        (rationalp error) (< 0 error))
   (lw-complexp (lw-complex-log-ramp-value rate height index error)))
  :hints (("Goal" :use (lw-complex-log-ramp-precision-adequate)
                   :in-theory (disable lw-complex-log-ramp-precision-adequate) :do-not-induct t)))

(defthm lw-complex-log-ramp-computed-normalization
  (implies
   (and (rationalp rate) (< 1 rate) (rationalp height) (rationalp index) (< 1 index)
        (rationalp error) (< 0 error))
   (let ((delta (lw-complex-log-ramp-precision rate height index error)))
     (lw-complex-diskp
      (lw-complex-sub
       (lw-complex-mul (lw-complex-log-ramp-exp rate height index delta)
         (lw-complex-reciprocal (lw-complex-mul (cons (- rate 1) height) (cons rate height))))
       (lw-complex-log-ramp-value rate height index error))
      error)))
  :hints (("Goal"
           :use (lw-complex-log-ramp-precision-adequate
                 (:instance lw-complex-log-ramp-endpoint-normalization (delta (lw-complex-log-ramp-precision rate height index error)))
                 (:instance lw-complex-log-ramp-grid-error (delta (lw-complex-log-ramp-precision rate height index error)))
                 (:instance lw-complex-log-ramp-endpoints-rational (delta (lw-complex-log-ramp-precision rate height index error)))
                 (:instance lw-complex-log-ramp-model-identity (delta (lw-complex-log-ramp-precision rate height index error)))
                 (:instance lw-complex-difference-symmetric
                   (left (lw-complex-log-ramp-endpoint rate height index (lw-complex-log-ramp-precision rate height index error))) (right (lw-complex-log-ramp-model rate height index (lw-complex-log-ramp-precision rate height index error))) (radius (* (+ (lw-complex-log-ramp-cap rate height index) (* 2 (lw-exp-lipschitz-cap index)) 4)
                       (lw-complex-log-ramp-precision rate height index error) (/ index) (/ (- rate 1)))))
                 (:instance lw-complex-difference-triangle
                   (left (lw-complex-log-ramp-model rate height index (lw-complex-log-ramp-precision rate height index error))) (middle (lw-complex-log-ramp-endpoint rate height index (lw-complex-log-ramp-precision rate height index error))) (right (lw-complex-log-ramp-grid rate height index (lw-complex-log-ramp-precision rate height index error)))
                   (radius (* (+ (lw-complex-log-ramp-cap rate height index) (* 2 (lw-exp-lipschitz-cap index)) 4)
                       (lw-complex-log-ramp-precision rate height index error) (/ index) (/ (- rate 1)))) (other-radius (+ (* 64 (lw-complex-log-ramp-precision rate height index error) (/ index) (/ (- rate 1)))
                        (* 64 (lw-complex-log-ramp-precision rate height index error) (/ rate)))))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-complex-sub (lw-complex-mul (lw-complex-log-ramp-exp rate height index (lw-complex-log-ramp-precision rate height index error))
                     (lw-complex-reciprocal (lw-complex-mul (cons (- rate 1) height) (cons rate height)))) (lw-complex-log-ramp-value rate height index error)))
                   (radius (+ (* (+ (lw-complex-log-ramp-cap rate height index) (* 2 (lw-exp-lipschitz-cap index)) 4)
                       (lw-complex-log-ramp-precision rate height index error) (/ index) (/ (- rate 1))) (+ (* 64 (lw-complex-log-ramp-precision rate height index error) (/ index) (/ (- rate 1)))
                        (* 64 (lw-complex-log-ramp-precision rate height index error) (/ rate))))) (cap error)))
           :in-theory
           (disable lw-complex-log-ramp-precision-adequate lw-complex-log-ramp-endpoint-normalization
                    lw-complex-log-ramp-grid-error lw-complex-log-ramp-endpoints-rational
                    lw-complex-difference-triangle lw-complex-sub-add-first)
           :nonlinearp nil :do-not-induct t)))
