(in-package "ACL2")

(include-book "zeta-series")

; A right-half-plane clearance for the actual ordinary zeta series.
; Recover cubic unweighted decay by dividing the certified weighted
; bound by its index, then sum a rational reciprocal potential.

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

(local (in-theory
 (disable lw-complex-log-ramp-start lw-complex-log-ramp-cap
          lw-complex-log-ramp-independent-exp lw-complex-log-ramp-independent-endpoint
          lw-complex-log-ramp-independent-model
          lw-complex-log-ramp-independent-model-identity
          lw-smoothed-ramp-log-error lw-smoothed-ramp-unit-error lw-mangoldt-bounds
          lw-complex-sub-add-first lw-complex-add-commutative lw-complex-add-left-commutes)))

(local (defthm lw-zcl-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-zcl-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-zcl-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-zcl-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-zcl-times-negative (a b) (b a)))
                 :in-theory (disable lw-zcl-times-negative)))))

(local (defthm lw-zcl-zero-times (equal (* 0 a) 0)))

(local (defthm lw-zcl-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-zcl-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-zcl-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-zcl-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-zcl-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-zcl-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-zcl-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-zcl-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-zcl-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-zcl-left-commutes)))))

(local (in-theory
 (disable lw-dirichlet-cubic-node-cost lw-dirichlet-cubic-cost
          lw-complex-zeta-partial-sum lw-complex-zeta-finite-value
          lw-complex-zeta-tail-value lw-complex-zeta-series-value lw-zeta-dirichlet-weight
          lw-dirichlet-finite-model-precision lw-dirichlet-finite-coefficient-precision
          lw-dirichlet-finite-node-precision lw-dirichlet-tail-node-precision
          lw-dirichlet-series-count lw-dirichlet-tail-precisions-valid
          lw-dirichlet-finite-precisions-valid lw-dirichlet-cubic-cost-valid
          lw-exp-lipschitz-cap-valid lw-complex-exp-uniform-cap-data)))

(local (defthm lw-zcl-inverse-scale
 (implies (and (lw-complexp b) (rationalp index) (< 0 index))
  (equal (lw-complex-scale (/ index) (lw-complex-scale index b)) b))
 :hints (("Goal" :use ((:instance inverse-of-* (x index)))
                 :in-theory (e/d (lw-complexp lw-complex-scale) (inverse-of-*))
                 :nonlinearp t :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-zcl-cancel-equality
 (implies (and (rationalp factor) (< 0 factor) (rationalp a) (rationalp b)
               (equal (* factor a) (* factor b)))
  (equal a b))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-zcl-inverse-product
 (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b))
  (equal (/ (* a b)) (* (/ a) (/ b))))
 :hints (("Goal"
  :use ((:instance inverse-of-* (x a)) (:instance inverse-of-* (x b))
        (:instance inverse-of-* (x (* a b)))
        (:instance lw-zcl-cancel-equality
         (factor (* a b)) (a (/ (* a b))) (b (* (/ a) (/ b)))))
  :in-theory (disable inverse-of-*) :nonlinearp t))
 :rule-classes nil))

(local (defthm lw-zcl-reciprocal-difference
 (implies (and (rationalp count) (< 1 count))
  (equal (- (/ (- count 1)) (/ count))
         (* (/ count) (/ (- count 1)))))
 :hints (("Goal"
  :use ((:instance lw-zcl-inverse-factor
         (divisor count) (coefficient (/ (- count 1))))
        (:instance lw-zcl-inverse-factor
         (divisor (- count 1)) (coefficient (/ count))))
  :in-theory (disable lw-zcl-inverse-factor)
  :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-zcl-square-nonnegative
 (implies (rationalp value) (<= 0 (* value value)))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-zcl-quadratic-gap
 (implies (rationalp count) (<= (* 4 (- count 1)) (* count count)))
 :hints (("Goal" :use ((:instance lw-zcl-square-nonnegative (value (- count 2))))
                 :nonlinearp nil))
 :rule-classes nil))

(local (defthm lw-zcl-cubic-reciprocal-step
 (implies (and (rationalp count) (< 1 count))
  (<= (* 2 (/ count) (/ count) (/ count))
      (* 1/2 (- (/ (- count 1)) (/ count)))))
 :hints (("Goal"
  :use (lw-zcl-reciprocal-difference lw-zcl-quadratic-gap
        (:instance lw-zcl-inverse-product (a count) (b count))
        (:instance lw-zcl-inverse-product (a 4) (b (- count 1)))
        (:instance lw-reciprocal-antitone (left (* 4 (- count 1))) (right (* count count)))
        (:instance lw-zcl-multiply-order
         (a (/ (* count count))) (b (/ (* 4 (- count 1)))) (factor (* 2 (/ count)))))
  :in-theory (disable lw-reciprocal-antitone)
  :nonlinearp t :do-not-induct t))
 :rule-classes nil))

(defthm lw-complex-dirichlet-unweighted-cubic-bound
 (implies (and (rationalp rate) (< 3 rate) (rationalp height) (rationalp index) (< 1 index)
               (rationalp log-error) (< 0 log-error) (<= log-error 1)
               (rationalp error) (< 0 error) (<= error 1))
  (lw-complex-diskp (lw-complex-log-ramp-independent-exp rate height index log-error error) (+ (* 2 (/ index) (/ index) (/ index)) (+ (* (lw-dirichlet-cubic-node-cost rate height index) error) (* 6 (lw-exp-lipschitz-cap index) log-error)))))
 :hints (("Goal"
  :use (lw-dirichlet-cubic-node-cost-valid
        (:instance lw-exp-lipschitz-cap-valid (cap index))
        (:instance lw-complex-log-ramp-independent-exp-rational (delta error))
        (:instance lw-complex-dirichlet-cubic-point-bound (weight index))
        (:instance lw-zcl-inverse-scale (b (lw-complex-log-ramp-independent-exp rate height index log-error error)))
        (:instance lw-reciprocal-antitone (left 1) (right index))
        (:instance lw-zcl-multiply-order (a (/ index)) (b 1) (factor (+ (* (lw-dirichlet-cubic-node-cost rate height index) error) (* 6 (lw-exp-lipschitz-cap index) log-error))))
        (:instance lw-complex-scale-disk (point (lw-complex-scale index (lw-complex-log-ramp-independent-exp rate height index log-error error)))
         (factor (/ index)) (radius (+ (* 2 (/ index) (/ index)) (+ (* (lw-dirichlet-cubic-node-cost rate height index) error) (* 6 (lw-exp-lipschitz-cap index) log-error)))))
        (:instance lw-complex-disk-enlarge (point (lw-complex-log-ramp-independent-exp rate height index log-error error)) (radius (* (/ index) (+ (* 2 (/ index) (/ index)) (+ (* (lw-dirichlet-cubic-node-cost rate height index) error) (* 6 (lw-exp-lipschitz-cap index) log-error))))) (cap (+ (* 2 (/ index) (/ index) (/ index)) (+ (* (lw-dirichlet-cubic-node-cost rate height index) error) (* 6 (lw-exp-lipschitz-cap index) log-error))))))
  :in-theory (disable lw-dirichlet-cubic-node-cost-valid lw-complex-log-ramp-independent-exp-rational
                      lw-complex-dirichlet-cubic-point-bound lw-reciprocal-antitone lw-complex-scale-disk)
  :nonlinearp t :do-not-induct t)))

(local (defthm lw-zcl-unit-data
 (implies (and (natp total) (rationalp model-error) (< 0 model-error))
  (and (rationalp (lw-smoothed-ramp-unit-error total model-error)) (< 0 (lw-smoothed-ramp-unit-error total model-error))))
 :hints (("Goal" :in-theory (enable lw-smoothed-ramp-unit-error) :nonlinearp t))
 :rule-classes nil))

(local (defun lw-zcl-tail-induction (count start)
 (declare (xargs :measure (nfix count)))
 (if (or (zp count) (<= count start)) count
  (lw-zcl-tail-induction (- count 1) start))))

(local (defthm lw-zcl-add-subtract
 (equal (lw-complex-sub (lw-complex-add term rest) prefix)
        (lw-complex-add term (lw-complex-sub rest prefix)))
 :hints (("Goal" :in-theory (enable lw-complex-add lw-complex-sub)))))

(local (defthm lw-zcl-sub-self
 (equal (lw-complex-sub point point) (cons 0 0))
 :hints (("Goal" :in-theory (enable lw-complex-sub)))))

(local (defthm lw-zcl-zero-disk
 (implies (and (rationalp radius) (<= 0 radius))
  (lw-complex-diskp (cons 0 0) radius))
 :hints (("Goal" :in-theory (enable lw-complex-diskp lw-complexp lw-diskp)))))

(local (defthm lw-zcl-weight-nil
 (equal (lw-zeta-dirichlet-weight nil index epsilon) 1)
 :hints (("Goal" :in-theory (enable lw-zeta-dirichlet-weight)))))

(local (defthm lw-zcl-scale-one
 (implies (lw-complexp point) (equal (lw-complex-scale 1 point) point))
 :hints (("Goal" :in-theory (enable lw-complexp lw-complex-scale)))))

(local (defthm lw-zcl-cost-one
 (equal (lw-dirichlet-cubic-cost rate height 1) 0)
 :hints (("Goal" :expand ((lw-dirichlet-cubic-cost rate height 1))))))

(local (defthm lw-zcl-sum-one
 (equal (lw-complex-zeta-partial-sum nil rate height 1 total model-error primitive-error error) (cons 1 0))
 :hints (("Goal" :expand ((lw-complex-zeta-partial-sum nil rate height 1 total model-error primitive-error error))))))

(local (defun lw-zcl-ordinary-radius (rate height count total model-error error)
 (+ (* 1/2 (- 1 (/ count))) (* (lw-dirichlet-cubic-cost rate height count) error) (* 6 (- count 1) (lw-smoothed-ramp-unit-error total model-error)))))

(local (in-theory (disable lw-zcl-ordinary-radius)))

(local (defthm lw-zcl-radius-one
 (equal (lw-zcl-ordinary-radius rate height 1 total model-error error) 0)
 :hints (("Goal" :in-theory (enable lw-zcl-ordinary-radius)))))

(local (defthm lw-zcl-radius-data
 (implies (and (rationalp rate) (< 3 rate) (rationalp height) (posp count) (natp total)
       (rationalp model-error) (< 0 model-error) (rationalp primitive-error) (< 0 primitive-error)
       (rationalp error) (< 0 error) (<= error 1))
  (and (rationalp (lw-zcl-ordinary-radius rate height count total model-error error)) (<= 0 (lw-zcl-ordinary-radius rate height count total model-error error))))
 :hints (("Goal"
  :use (lw-zcl-unit-data lw-dirichlet-cubic-cost-valid
        (:instance lw-reciprocal-antitone (left 1) (right count)))
  :in-theory (e/d (lw-zcl-ordinary-radius) (lw-reciprocal-antitone))
  :nonlinearp t :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-zcl-radius-step
 (implies (and (and (rationalp rate) (< 3 rate) (rationalp height) (posp count) (natp total)
       (rationalp model-error) (< 0 model-error) (rationalp primitive-error) (< 0 primitive-error)
       (rationalp error) (< 0 error) (<= error 1)) (< 1 count))
  (<= (+ (+ (* 2 (/ count) (/ count) (/ count)) (* (lw-dirichlet-cubic-node-cost rate height count) error) (* 6 (lw-smoothed-ramp-unit-error total model-error))) (lw-zcl-ordinary-radius rate height (- count 1) total model-error error)) (lw-zcl-ordinary-radius rate height count total model-error error)))
 :hints (("Goal"
  :use (lw-zcl-unit-data lw-zcl-cubic-reciprocal-step lw-dirichlet-cubic-cost-valid
        (:instance lw-dirichlet-cubic-cost-valid (count (- count 1)))
        (:instance lw-dirichlet-cubic-node-cost-valid (index count)))
  :expand ((lw-dirichlet-cubic-cost rate height count))
  :in-theory (e/d (lw-zcl-ordinary-radius) (lw-dirichlet-cubic-node-cost-valid))
  :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-zcl-ordinary-term
 (implies (and (and (rationalp rate) (< 3 rate) (rationalp height) (posp count) (natp total)
       (rationalp model-error) (< 0 model-error) (rationalp primitive-error) (< 0 primitive-error)
       (rationalp error) (< 0 error) (<= error 1)) (< 1 count))
  (lw-complex-diskp (lw-complex-scale (lw-zeta-dirichlet-weight nil count primitive-error) (lw-complex-log-ramp-independent-exp rate height count (lw-smoothed-ramp-log-error count total model-error) error)) (+ (* 2 (/ count) (/ count) (/ count)) (* (lw-dirichlet-cubic-node-cost rate height count) error) (* 6 (lw-smoothed-ramp-unit-error total model-error)))))
 :hints (("Goal"
  :use (lw-zcl-unit-data
        (:instance lw-dirichlet-cubic-node-cost-valid (index count))
        (:instance lw-smoothed-ramp-log-error-adequate (index count) (error model-error))
        (:instance lw-complex-log-ramp-independent-exp-rational (index count) (log-error (lw-smoothed-ramp-log-error count total model-error)) (delta error))
        (:instance lw-complex-dirichlet-unweighted-cubic-bound (index count) (log-error (lw-smoothed-ramp-log-error count total model-error)))
        (:instance lw-zcl-multiply-order (a (* (lw-exp-lipschitz-cap count) (lw-smoothed-ramp-log-error count total model-error))) (b (lw-smoothed-ramp-unit-error total model-error)) (factor 6))
        (:instance lw-complex-disk-enlarge (point (lw-complex-log-ramp-independent-exp rate height count (lw-smoothed-ramp-log-error count total model-error) error))
         (radius (+ (* 2 (/ count) (/ count) (/ count)) (* (lw-dirichlet-cubic-node-cost rate height count) error)
                    (* 6 (lw-exp-lipschitz-cap count) (lw-smoothed-ramp-log-error count total model-error))))
         (cap (+ (* 2 (/ count) (/ count) (/ count)) (* (lw-dirichlet-cubic-node-cost rate height count) error) (* 6 (lw-smoothed-ramp-unit-error total model-error))))))
  :in-theory (disable lw-dirichlet-cubic-node-cost-valid lw-smoothed-ramp-log-error-adequate
                      lw-complex-log-ramp-independent-exp-rational lw-complex-dirichlet-unweighted-cubic-bound)
  :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-zcl-tight-ordinary-bound
 (implies (and (rationalp rate) (< 3 rate) (rationalp height) (posp count) (natp total)
       (rationalp model-error) (< 0 model-error) (rationalp primitive-error) (< 0 primitive-error)
       (rationalp error) (< 0 error) (<= error 1))
  (lw-complex-diskp (lw-complex-sub (lw-complex-zeta-partial-sum nil rate height count total model-error primitive-error error) (cons 1 0)) (lw-zcl-ordinary-radius rate height count total model-error error)))
 :hints (("Goal"
  :induct (lw-zcl-tail-induction count 1)
  :in-theory (disable lw-complex-add-disk))
  (and stable-under-simplificationp
   '(:use (lw-zcl-radius-data lw-zcl-radius-step lw-zcl-ordinary-term
           (:instance lw-complex-add-disk (left (lw-complex-scale (lw-zeta-dirichlet-weight nil count primitive-error) (lw-complex-log-ramp-independent-exp rate height count (lw-smoothed-ramp-log-error count total model-error) error)))
            (right (lw-complex-sub (lw-complex-zeta-partial-sum nil rate height (- count 1) total model-error primitive-error error) (cons 1 0)))
            (radius (+ (* 2 (/ count) (/ count) (/ count)) (* (lw-dirichlet-cubic-node-cost rate height count) error) (* 6 (lw-smoothed-ramp-unit-error total model-error)))) (other-radius (lw-zcl-ordinary-radius rate height (- count 1) total model-error error)))
           (:instance lw-complex-disk-enlarge
            (point (lw-complex-sub (lw-complex-zeta-partial-sum nil rate height count total model-error primitive-error error) (cons 1 0)))
            (radius (+ (+ (* 2 (/ count) (/ count) (/ count)) (* (lw-dirichlet-cubic-node-cost rate height count) error) (* 6 (lw-smoothed-ramp-unit-error total model-error))) (lw-zcl-ordinary-radius rate height (- count 1) total model-error error))) (cap (lw-zcl-ordinary-radius rate height count total model-error error))))
     :expand ((lw-complex-zeta-partial-sum nil rate height count total model-error primitive-error error))
     :in-theory (disable lw-complex-zeta-partial-sum lw-complex-add-disk)
     :nonlinearp nil :do-not-induct t)))
 :rule-classes nil))

(local (defthm lw-zcl-count-unit-budget
 (implies (and (natp count) (natp total) (<= count total)
               (rationalp model-error) (< 0 model-error))
  (<= (* count (lw-smoothed-ramp-unit-error total model-error)) (* 1/16 model-error)))
 :hints (("Goal"
  :use ((:instance lw-zcl-multiply-order (a count) (b (+ 1 total)) (factor model-error))
        (:instance lw-positive-division-bound
         (numerator (* count model-error)) (divisor (+ 1 total)) (bound model-error)))
  :in-theory (enable lw-smoothed-ramp-unit-error)
  :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(defthm lw-complex-zeta-ordinary-finite-bound
 (implies (and (and (rationalp rate) (< 3 rate) (rationalp height) (posp count) (natp total)
       (rationalp model-error) (< 0 model-error) (rationalp primitive-error) (< 0 primitive-error)
       (rationalp error) (< 0 error) (<= error 1)) (<= count total))
  (lw-complex-diskp (lw-complex-sub (lw-complex-zeta-partial-sum nil rate height count total model-error primitive-error error) (cons 1 0))
                   (+ 1/2 (* (lw-dirichlet-cubic-cost rate height count) error) (* 3/8 model-error))))
 :hints (("Goal"
  :use (lw-zcl-tight-ordinary-bound lw-zcl-unit-data lw-zcl-count-unit-budget
        lw-dirichlet-cubic-cost-valid
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub (lw-complex-zeta-partial-sum nil rate height count total model-error primitive-error error) (cons 1 0))) (radius (lw-zcl-ordinary-radius rate height count total model-error error))
         (cap (+ 1/2 (* (lw-dirichlet-cubic-cost rate height count) error) (* 3/8 model-error)))))
  :in-theory (enable lw-zcl-ordinary-radius)
  :nonlinearp nil :do-not-induct t)))

(local (defthm lw-zcl-tail-rational
 (implies
  (and (rationalp rate) (< 3 rate) (rationalp height) (natp count) (natp total)
       (rationalp error) (< 0 error))
  (lw-complexp (lw-complex-zeta-tail-value logp rate height count total error)))
 :hints (("Goal"
  :use ((:instance lw-dirichlet-tail-precisions-valid (count total))
        (:instance lw-complex-zeta-partial-sum-rational
         (model-error (lw-dirichlet-finite-model-precision rate height error)) (primitive-error (lw-dirichlet-finite-coefficient-precision total error)) (delta (lw-dirichlet-tail-node-precision rate height total error))))
  :in-theory (e/d (lw-complex-zeta-tail-value)
                  (lw-complex-zeta-partial-sum-rational))
  :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-zcl-auxiliary-comparison
 (implies (and (rationalp rate) (< 3 rate) (rationalp height) (posp count) (rationalp error) (< 0 error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-zeta-tail-value logp rate height count count error) (lw-complex-zeta-finite-value logp rate height count error)) (* 2 error)))
 :hints (("Goal"
  :use (lw-dirichlet-tail-precisions-valid
        (:instance lw-complex-zeta-partial-sum-finite-comparison
         (total count) (model-error (lw-dirichlet-finite-model-precision rate height error)) (primitive-error (lw-dirichlet-finite-coefficient-precision count error)) (delta (lw-dirichlet-tail-node-precision rate height count error)))
        (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-zeta-partial-sum logp rate height count count (lw-dirichlet-finite-model-precision rate height error) (lw-dirichlet-finite-coefficient-precision count error) (lw-dirichlet-tail-node-precision rate height count error)) (lw-complex-zeta-finite-value logp rate height count error)))
         (radius (+ (* (* 2 (+ rate (abs height))) 1/16 (lw-dirichlet-finite-model-precision rate height error)) (* 16 (* count (+ 1 count)) (lw-dirichlet-tail-node-precision rate height count error)) (* 2 count (lw-dirichlet-finite-coefficient-precision count error)) error)) (cap (* 2 error))))
  :in-theory (e/d (lw-complex-zeta-tail-value)
                  (lw-complex-zeta-partial-sum-finite-comparison))
  :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-zcl-auxiliary-ordinary-cap
 (implies (and (rationalp rate) (< 3 rate) (rationalp height) (posp count) (rationalp error) (< 0 error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-zeta-tail-value nil rate height count count error) (cons 1 0)) (+ 1/2 error)))
 :hints (("Goal"
  :use (lw-dirichlet-tail-precisions-valid
        (:instance lw-complex-zeta-ordinary-finite-bound
         (total count) (model-error (lw-dirichlet-finite-model-precision rate height error)) (primitive-error (lw-dirichlet-finite-coefficient-precision count error)) (error (lw-dirichlet-tail-node-precision rate height count error)))
        (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-zeta-partial-sum nil rate height count count (lw-dirichlet-finite-model-precision rate height error) (lw-dirichlet-finite-coefficient-precision count error) (lw-dirichlet-tail-node-precision rate height count error)) (cons 1 0)))
         (radius (+ 1/2 (* (lw-dirichlet-cubic-cost rate height count) (lw-dirichlet-tail-node-precision rate height count error)) (* 3/8 (lw-dirichlet-finite-model-precision rate height error)))) (cap (+ 1/2 error))))
  :in-theory (e/d (lw-complex-zeta-tail-value)
                  (lw-complex-zeta-ordinary-finite-bound))
  :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-zcl-log-sum-one
 (equal (lw-complex-zeta-partial-sum t rate height 1 total model-error primitive-error error) (cons 0 0))
 :hints (("Goal" :expand ((lw-complex-zeta-partial-sum t rate height 1 total model-error primitive-error error))))))

(local (defthm lw-zcl-sub-zero
 (implies (lw-complexp point) (equal (lw-complex-sub point (cons 0 0)) point))
 :hints (("Goal" :in-theory (enable lw-complexp lw-complex-sub)))))

(local (defthm lw-zcl-auxiliary-log-cap
 (implies (and (rationalp rate) (< 3 rate) (rationalp height) (posp count) (rationalp error) (< 0 error))
  (lw-complex-diskp (lw-complex-zeta-tail-value t rate height count count error) (+ 2 error)))
 :hints (("Goal"
  :use (lw-dirichlet-tail-precisions-valid
        (:instance lw-complex-zeta-partial-sum-rational
         (logp t) (total count) (model-error (lw-dirichlet-finite-model-precision rate height error)) (primitive-error (lw-dirichlet-finite-coefficient-precision count error)) (delta (lw-dirichlet-tail-node-precision rate height count error)))
        (:instance lw-complex-zeta-uniform-tail
         (logp t) (start 1) (total count) (model-error (lw-dirichlet-finite-model-precision rate height error)) (primitive-error (lw-dirichlet-finite-coefficient-precision count error)) (error (lw-dirichlet-tail-node-precision rate height count error)))
        (:instance lw-complex-disk-enlarge (point (lw-complex-zeta-partial-sum t rate height count count (lw-dirichlet-finite-model-precision rate height error) (lw-dirichlet-finite-coefficient-precision count error) (lw-dirichlet-tail-node-precision rate height count error)))
         (radius (+ 2 (* (lw-dirichlet-cubic-cost rate height count) (lw-dirichlet-tail-node-precision rate height count error)) (* 3/8 (lw-dirichlet-finite-model-precision rate height error)))) (cap (+ 2 error))))
  :in-theory (e/d (lw-complex-zeta-tail-value)
    (lw-complex-zeta-partial-sum-rational lw-complex-zeta-uniform-tail))
  :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-zcl-near-center
 (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c)
               (lw-complex-diskp (lw-complex-sub b a) radius)
               (lw-complex-diskp (lw-complex-sub b c) other-radius))
  (lw-complex-diskp (lw-complex-sub a c) (+ radius other-radius)))
 :hints (("Goal"
  :use ((:instance lw-complex-difference-symmetric (left b) (right a))
        (:instance lw-complex-difference-triangle (left a) (middle b) (right c)))
  :in-theory (disable lw-complex-difference-triangle)
  :do-not-induct t))
 :rule-classes nil))

(defthm lw-complex-zeta-finite-ordinary-cap
 (implies (and (rationalp rate) (< 3 rate) (rationalp height) (posp count) (rationalp error) (< 0 error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-zeta-finite-value nil rate height count error) (cons 1 0)) (+ 1/2 (* 3 error))))
 :hints (("Goal"
  :use ((:instance lw-complex-zeta-finite-value-rational (logp nil))
        (:instance lw-zcl-tail-rational (logp nil) (total count))
        (:instance lw-zcl-auxiliary-comparison (logp nil))
        lw-zcl-auxiliary-ordinary-cap
        (:instance lw-zcl-near-center (a (lw-complex-zeta-finite-value nil rate height count error)) (b (lw-complex-zeta-tail-value nil rate height count count error)) (c (cons 1 0))
         (radius (* 2 error)) (other-radius (+ 1/2 error)))
        (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-zeta-finite-value nil rate height count error) (cons 1 0)))
         (radius (+ (* 2 error) (+ 1/2 error))) (cap (+ 1/2 (* 3 error)))))
  :in-theory (disable lw-complex-zeta-finite-value-rational)
  :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-zeta-finite-log-cap
 (implies (and (rationalp rate) (< 3 rate) (rationalp height) (posp count) (rationalp error) (< 0 error))
  (lw-complex-diskp (lw-complex-zeta-finite-value t rate height count error) (+ 2 (* 3 error))))
 :hints (("Goal"
  :use ((:instance lw-complex-zeta-finite-value-rational (logp t))
        (:instance lw-zcl-tail-rational (logp t) (total count))
        (:instance lw-zcl-auxiliary-comparison (logp t))
        lw-zcl-auxiliary-log-cap
        (:instance lw-zcl-near-center (a (lw-complex-zeta-finite-value t rate height count error)) (b (lw-complex-zeta-tail-value t rate height count count error)) (c (cons 0 0))
         (radius (* 2 error)) (other-radius (+ 2 error)))
        (:instance lw-complex-disk-enlarge (point (lw-complex-zeta-finite-value t rate height count error))
         (radius (+ (* 2 error) (+ 2 error))) (cap (+ 2 (* 3 error)))))
  :in-theory (disable lw-complex-zeta-finite-value-rational)
  :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-zeta-series-ordinary-cap
 (implies (and (rationalp rate) (< 3 rate) (rationalp height) (rationalp error) (< 0 error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-zeta-series-value nil rate height error) (cons 1 0)) (+ 1/2 error)))
 :hints (("Goal"
  :use (lw-dirichlet-series-count-valid
        (:instance lw-complex-zeta-finite-ordinary-cap (count (lw-dirichlet-series-count error)) (error (* 1/32 error)))
        (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-zeta-series-value nil rate height error) (cons 1 0)))
         (radius (+ 1/2 (* 3 (* 1/32 error)))) (cap (+ 1/2 error))))
  :in-theory (e/d (lw-complex-zeta-series-value)
    (lw-dirichlet-series-count-valid lw-complex-zeta-finite-ordinary-cap))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-zeta-series-log-cap
 (implies (and (and (rationalp rate) (< 3 rate) (rationalp height) (rationalp error) (< 0 error)) (<= error 1/4))
  (lw-complex-diskp (lw-complex-zeta-series-value t rate height error) 3))
 :hints (("Goal"
  :use (lw-dirichlet-series-count-valid
        (:instance lw-complex-zeta-finite-log-cap (count (lw-dirichlet-series-count error)) (error (* 1/32 error)))
        (:instance lw-complex-disk-enlarge (point (lw-complex-zeta-series-value t rate height error))
         (radius (+ 2 (* 3 (* 1/32 error)))) (cap 3)))
  :in-theory (e/d (lw-complex-zeta-series-value)
    (lw-dirichlet-series-count-valid lw-complex-zeta-finite-log-cap))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-zeta-series-clearance
 (implies (and (and (rationalp rate) (< 3 rate) (rationalp height) (rationalp error) (< 0 error)) (<= error 1/4))
  (and (<= 1/16 (lw-complex-norm-square (lw-complex-zeta-series-value nil rate height error)))
       (not (equal (lw-complex-zeta-series-value nil rate height error) (cons 0 0)))))
 :hints (("Goal"
  :use (lw-complex-zeta-series-ordinary-cap
        (:instance lw-complex-zeta-series-value-rational (logp nil))
        (:instance lw-zcl-square-nonnegative (value (cdr (lw-complex-zeta-series-value nil rate height error))))
        (:instance lw-complex-disk-coordinates
         (point (lw-complex-sub (lw-complex-zeta-series-value nil rate height error) (cons 1 0))) (radius (+ 1/2 error))))
  :in-theory (e/d (lw-complexp lw-complex-sub lw-complex-norm-square)
    (lw-complex-zeta-series-ordinary-cap lw-complex-zeta-series-value-rational lw-complex-disk-coordinates))
  :nonlinearp t :do-not-induct t)))

(defthm lw-complex-zeta-series-reciprocal-cap
 (implies (and (and (rationalp rate) (< 3 rate) (rationalp height) (rationalp error) (< 0 error)) (<= error 1/4))
  (lw-complex-diskp (lw-complex-reciprocal (lw-complex-zeta-series-value nil rate height error)) 4))
 :hints (("Goal"
  :use (lw-complex-zeta-series-clearance
        (:instance lw-complex-zeta-series-value-rational (logp nil))
        (:instance lw-complex-reciprocal-disk-bound (point (lw-complex-zeta-series-value nil rate height error)) (lower 1/4)))
  :in-theory (disable lw-complex-zeta-series-clearance lw-complex-zeta-series-value-rational
                      lw-complex-reciprocal-disk-bound)
  :do-not-induct t)))




