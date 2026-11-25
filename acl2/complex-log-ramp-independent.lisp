(in-package "ACL2")

(include-book "complex-log-ramp")

; Normalize at a fixed computed logarithm while the exponential node
; precision is refined independently. The frozen Mellin family uses
; exactly this separation of the two errors.

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

(local (in-theory (disable lw-complex-log-ramp-exp lw-complex-log-ramp-endpoint lw-complex-log-ramp-model)))

(local (defthm lw-cli-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-cli-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-cli-times-negative
         (implies (and (rationalp a) (rationalp b)) (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))

(local (defthm lw-cli-negative-times
         (implies (and (rationalp a) (rationalp b)) (equal (* (- a) b) (- (* a b))))))

(local (defthm lw-cli-zero-times (equal (* 0 a) 0)))

(local (defthm lw-cli-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-cli-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-cli-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-cli-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-cli-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-cli-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-cli-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cli-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cli-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-cli-left-commutes)))))

(local (defthm lw-cli-fuel-natural
         (natp (lw-precision-fuel width error))
         :hints (("Goal" :in-theory (enable lw-precision-fuel)))
         :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-cli-pair-complex
         (implies (and (rationalp a) (rationalp b)) (lw-complexp (cons a b)))
         :hints (("Goal" :in-theory (enable lw-complexp)))))

(local (defthm lw-cli-start-data
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

(local (defthm lw-cli-scale-laplace
         (implies (and (rationalp rate) (rationalp height) (rationalp start))
                  (equal (lw-complex-scale start (lw-complex-laplace-point rate height))
                         (cons (- (* rate start)) (- (* height start)))))
         :hints (("Goal" :in-theory (enable lw-complex-scale lw-complex-laplace-point)))))

(local (defthm lw-cli-point-data
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

(local (defthm lw-cli-real-difference-disk
         (implies (and (rationalp a) (rationalp b) (rationalp error) (<= (abs (- a b)) error))
                  (lw-complex-diskp (lw-complex-sub (cons a 0) (cons b 0)) error))
         :hints (("Goal" :in-theory (enable lw-complex-diskp lw-complex-sub lw-complexp lw-diskp)
                         :cases ((<= a b)) :nonlinearp t))
         :rule-classes nil))

(local (defthm lw-cli-residual-identity
         (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c) (rationalp index))
                  (equal
                   (lw-complex-add (lw-complex-sub c (lw-complex-mul a b))
                     (lw-complex-mul (lw-complex-sub a (cons index 0)) b))
                   (lw-complex-sub c (lw-complex-scale index b))))
         :hints (("Goal" :in-theory
                  (enable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale)))))

(local (defthm lw-cli-residual-disk
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

(defun lw-complex-log-ramp-independent-exp (rate height index log-error delta)
  (lw-complex-exp-value
    (lw-complex-scale (lw-complex-log-ramp-start index log-error) (lw-complex-laplace-point rate height))
    delta))

(defthm lw-complex-log-ramp-independent-exp-normalization
  (implies
   (and (rationalp rate) (< 1 rate) (rationalp height) (rationalp index) (< 1 index)
        (rationalp log-error) (< 0 log-error) (<= log-error 1)
        (rationalp delta) (< 0 delta) (<= delta 1))
   (lw-complex-diskp
    (lw-complex-sub
      (lw-complex-log-ramp-independent-exp (- rate 1) height index log-error delta)
      (lw-complex-scale index (lw-complex-log-ramp-independent-exp rate height index log-error delta)))
    (+ (* (+ (lw-complex-log-ramp-cap rate height index) 4) delta) (* 2 (lw-exp-lipschitz-cap index) log-error))))
  :hints (("Goal"
           :use ((:instance lw-cli-start-data (delta log-error))
                 (:instance lw-cli-point-data (start (lw-complex-log-ramp-start index log-error)))
                 (:instance lw-exp-log-inverse-error (point index) (log-error log-error) (exp-error delta))
                 (:instance lw-exp-bounds-valid (value (lw-complex-log-ramp-start index log-error)) (epsilon delta))
                 (:instance lw-exp-lipschitz-cap-valid (cap index))
                 (:instance lw-complex-exp-cap-uniform
                   (point (cons (lw-complex-log-ramp-start index log-error) 0)) (argument-cap index))
                 (:instance lw-complex-exp-cap-uniform
                   (point (lw-complex-scale (lw-complex-log-ramp-start index log-error)
                                           (lw-complex-laplace-point rate height)))
                   (argument-cap (* (+ rate (abs height)) index)))
                 (:instance lw-complex-exp-value-multiplication
                   (left (cons (lw-complex-log-ramp-start index log-error) 0))
                   (right (lw-complex-scale (lw-complex-log-ramp-start index log-error)
                                            (lw-complex-laplace-point rate height)))
                   (left-error delta) (right-error delta) (sum-error delta))
                 (:instance lw-cli-multiply-order
                   (a (+ (lw-complex-exp-cap (cons (lw-complex-log-ramp-start index log-error) 0))
                         (lw-complex-exp-cap
                           (lw-complex-scale (lw-complex-log-ramp-start index log-error)
                                             (lw-complex-laplace-point rate height))) 2))
                   (b (lw-complex-log-ramp-cap rate height index)) (factor delta))
                 (:instance lw-complex-difference-symmetric
                   (left (lw-complex-mul
                     (lw-complex-exp-value (cons (lw-complex-log-ramp-start index log-error) 0) delta)
                     (lw-complex-log-ramp-independent-exp rate height index log-error delta)))
                   (right (lw-complex-log-ramp-independent-exp (- rate 1) height index log-error delta))
                   (radius
                     (+ (* (lw-complex-exp-cap
                             (lw-complex-scale (lw-complex-log-ramp-start index log-error)
                                               (lw-complex-laplace-point rate height))) delta)
                        (* (lw-complex-exp-cap (cons (lw-complex-log-ramp-start index log-error) 0)) delta)
                        (* 2 delta))))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-complex-sub
                     (lw-complex-log-ramp-independent-exp (- rate 1) height index log-error delta)
                     (lw-complex-mul
                       (lw-complex-exp-value (cons (lw-complex-log-ramp-start index log-error) 0) delta)
                       (lw-complex-log-ramp-independent-exp rate height index log-error delta))))
                   (radius
                     (+ (* (lw-complex-exp-cap
                             (lw-complex-scale (lw-complex-log-ramp-start index log-error)
                                               (lw-complex-laplace-point rate height))) delta)
                        (* (lw-complex-exp-cap (cons (lw-complex-log-ramp-start index log-error) 0)) delta)
                        (* 2 delta)))
                   (cap (* (lw-complex-log-ramp-cap rate height index) delta)))
                 (:instance lw-complex-exp-damped-cap
                   (value (* rate (lw-complex-log-ramp-start index log-error)))
                   (angle (- (* height (lw-complex-log-ramp-start index log-error)))) (error delta))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-complex-log-ramp-independent-exp rate height index log-error delta))
                   (radius (+ 1 delta)) (cap 2))
                 (:instance lw-cli-real-difference-disk
                   (a (car (lw-exp-bounds (lw-complex-log-ramp-start index log-error) delta)))
                   (b index) (error (+ (* (lw-exp-lipschitz-cap index) log-error) (* 2 delta))))
                 (:instance lw-cli-residual-disk
                   (a (lw-complex-exp-value (cons (lw-complex-log-ramp-start index log-error) 0) delta))
                   (b (lw-complex-log-ramp-independent-exp rate height index log-error delta))
                   (c (lw-complex-log-ramp-independent-exp (- rate 1) height index log-error delta))
                   (radius (* (lw-complex-log-ramp-cap rate height index) delta))
                   (real-error (+ (* (lw-exp-lipschitz-cap index) log-error) (* 2 delta))))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-complex-sub
                     (lw-complex-log-ramp-independent-exp (- rate 1) height index log-error delta)
                     (lw-complex-scale index (lw-complex-log-ramp-independent-exp rate height index log-error delta))))
                   (radius (+ (* (lw-complex-log-ramp-cap rate height index) delta)
                              (* 2 (+ (* (lw-exp-lipschitz-cap index) log-error) (* 2 delta)))))
                   (cap (+ (* (+ (lw-complex-log-ramp-cap rate height index) 4) delta) (* 2 (lw-exp-lipschitz-cap index) log-error)))))
           :in-theory
           (e/d (lw-complex-log-ramp-independent-exp lw-complex-log-ramp-start lw-intervalp)
                (lw-cli-start-data lw-cli-point-data lw-exp-log-inverse-error lw-exp-bounds-valid
                 lw-exp-lipschitz-cap-valid lw-complex-exp-cap-uniform lw-complex-exp-value-multiplication
                 lw-complex-exp-damped-cap lw-complex-sub-add-first))
           :nonlinearp nil :do-not-induct t)))

(defun lw-complex-log-ramp-independent-endpoint (rate height index log-error delta)
  (lw-complex-sub
    (lw-complex-scale (/ index)
      (lw-complex-mul (lw-complex-log-ramp-independent-exp (- rate 1) height index log-error delta)
                       (lw-complex-reciprocal (cons (- rate 1) height))))
    (lw-complex-mul (lw-complex-log-ramp-independent-exp rate height index log-error delta)
                     (lw-complex-reciprocal (cons rate height)))))

(defun lw-complex-log-ramp-independent-model (rate height index log-error delta)
  (lw-complex-mul (lw-complex-log-ramp-independent-exp rate height index log-error delta)
    (lw-complex-sub (lw-complex-reciprocal (cons (- rate 1) height))
                    (lw-complex-reciprocal (cons rate height)))))

(defthm lw-complex-log-ramp-independent-exp-rational
  (implies (and (rationalp rate) (rationalp height) (rationalp index) (< 1 index)
                (rationalp log-error) (< 0 log-error)
        (rationalp delta) (< 0 delta))
           (lw-complexp (lw-complex-log-ramp-independent-exp rate height index log-error delta)))
  :hints (("Goal" :use ((:instance lw-cli-start-data (delta log-error)))
                   :in-theory (disable lw-cli-start-data) :do-not-induct t)))

(defthm lw-complex-log-ramp-independent-endpoints-rational
  (implies
   (and (rationalp rate) (< 1 rate) (rationalp height) (rationalp index) (< 1 index)
        (rationalp log-error) (< 0 log-error)
        (rationalp delta) (< 0 delta))
   (and (lw-complexp (lw-complex-log-ramp-independent-endpoint rate height index log-error delta))
        (lw-complexp (lw-complex-log-ramp-independent-model rate height index log-error delta))))
  :hints (("Goal" :use ((:instance lw-cli-start-data (delta log-error)))
                   :in-theory (disable lw-cli-start-data)
                   :nonlinearp t :do-not-induct t)))

(defthm lw-complex-log-ramp-independent-model-identity
  (implies
   (and (rationalp rate) (< 1 rate) (rationalp height) (rationalp index) (< 1 index)
        (rationalp log-error) (< 0 log-error)
        (rationalp delta) (< 0 delta))
   (equal
    (lw-complex-log-ramp-independent-model rate height index log-error delta)
    (lw-complex-mul (lw-complex-log-ramp-independent-exp rate height index log-error delta)
      (lw-complex-reciprocal (lw-complex-mul (cons (- rate 1) height) (cons rate height)))))))

(local (in-theory (disable lw-complex-log-ramp-independent-model-identity lw-complex-log-ramp-independent-exp
                          lw-complex-log-ramp-start lw-complex-log-ramp-cap)))

(local (defthm lw-cli-endpoint-difference
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

(local (defthm lw-cli-positive-clearance
         (implies (and (rationalp rate) (< 0 rate) (rationalp height))
                  (<= (* rate rate) (lw-complex-norm-square (cons rate height))))
         :hints (("Goal" :in-theory (enable lw-complex-norm-square) :nonlinearp t))))

(defthm lw-complex-log-ramp-independent-endpoint-normalization
  (implies
   (and (rationalp rate) (< 1 rate) (rationalp height) (rationalp index) (< 1 index)
        (rationalp log-error) (< 0 log-error) (<= log-error 1)
        (rationalp delta) (< 0 delta) (<= delta 1))
   (lw-complex-diskp
    (lw-complex-sub (lw-complex-log-ramp-independent-endpoint rate height index log-error delta)
                    (lw-complex-log-ramp-independent-model rate height index log-error delta))
    (* (+ (* (+ (lw-complex-log-ramp-cap rate height index) 4) delta) (* 2 (lw-exp-lipschitz-cap index) log-error)) (/ index) (/ (- rate 1)))))
  :hints (("Goal"
           :use (lw-complex-log-ramp-independent-exp-normalization lw-complex-log-ramp-independent-endpoints-rational
                 (:instance lw-cli-positive-clearance (rate (- rate 1)))
                 (:instance lw-complex-reciprocal-disk-bound
                   (point (cons (- rate 1) height)) (lower (- rate 1)))
                 (:instance lw-complex-mul-disk
                   (left (lw-complex-sub
                     (lw-complex-log-ramp-independent-exp (- rate 1) height index log-error delta)
                     (lw-complex-scale index (lw-complex-log-ramp-independent-exp rate height index log-error delta))))
                   (radius (+ (* (+ (lw-complex-log-ramp-cap rate height index) 4) delta) (* 2 (lw-exp-lipschitz-cap index) log-error)))
                   (right (lw-complex-reciprocal (cons (- rate 1) height))) (other-radius (/ (- rate 1))))
                 (:instance lw-complex-scale-disk
                   (factor (/ index))
                   (point (lw-complex-mul
                     (lw-complex-sub
                       (lw-complex-log-ramp-independent-exp (- rate 1) height index log-error delta)
                       (lw-complex-scale index (lw-complex-log-ramp-independent-exp rate height index log-error delta)))
                     (lw-complex-reciprocal (cons (- rate 1) height))))
                   (radius (* (+ (* (+ (lw-complex-log-ramp-cap rate height index) 4) delta) (* 2 (lw-exp-lipschitz-cap index) log-error)) (/ (- rate 1)))))
                 (:instance lw-cli-endpoint-difference
                   (a (lw-complex-log-ramp-independent-exp (- rate 1) height index log-error delta))
                   (b (lw-complex-log-ramp-independent-exp rate height index log-error delta))
                   (p (lw-complex-reciprocal (cons (- rate 1) height)))
                   (q (lw-complex-reciprocal (cons rate height)))))
           :in-theory
           (e/d (lw-complex-log-ramp-independent-endpoint lw-complex-log-ramp-independent-model)
                (lw-complex-log-ramp-independent-exp-normalization lw-complex-log-ramp-independent-endpoints-rational
                 lw-complex-reciprocal-disk-bound lw-complex-mul-disk lw-complex-scale-disk
                 lw-complex-scale-product lw-complex-laplace-ramp-reciprocal-identity
                 lw-complex-reciprocal-difference
                 lw-cli-endpoint-difference))
           :nonlinearp nil :do-not-induct t)))

