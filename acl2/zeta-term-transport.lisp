(in-package "ACL2")

(include-book "dirichlet-term-transport")

; Ordinary and logarithm-weighted Dirichlet terms, with coefficients
; 1 and the existing computed lower logarithm. Transport follows the
; certified Mangoldt term proof with these explicit coefficients.

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

(local (defthm lw-ztt-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ztt-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ztt-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ztt-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ztt-times-negative (a b) (b a)))
                 :in-theory (disable lw-ztt-times-negative)))))

(local (defthm lw-ztt-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ztt-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ztt-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ztt-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ztt-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ztt-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ztt-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ztt-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ztt-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ztt-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ztt-left-commutes)))))

(local (in-theory (disable lw-complex-laplace-point lw-smoothed-ramp-log-error lw-smoothed-ramp-unit-error
                          lw-log-bounds-nonnegative lw-log-bounds-lower-coarse)))


(defun lw-zeta-dirichlet-weight (logp index epsilon)
 (if logp (car (lw-log-bounds index epsilon)) 1))

(defthm lw-zeta-dirichlet-weight-valid
 (implies (and (rationalp index) (< 1 index) (rationalp epsilon) (< 0 epsilon))
  (and (rationalp (lw-zeta-dirichlet-weight logp index epsilon))
       (<= 0 (lw-zeta-dirichlet-weight logp index epsilon))
       (<= (lw-zeta-dirichlet-weight logp index epsilon) index)))
 :hints (("Goal"
  :use ((:instance lw-log-bounds-lower-coarse (value index))
        (:instance lw-log-bounds-interval (value index)))
  :in-theory (e/d (lw-zeta-dirichlet-weight lw-intervalp)
                  (lw-log-bounds-lower-coarse lw-log-bounds-interval))
  :do-not-induct t)))

(defthm lw-zeta-dirichlet-weight-cauchy
 (implies (and (rationalp index) (< 1 index)
               (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
  (<= (abs (- (lw-zeta-dirichlet-weight logp index left-error)
              (lw-zeta-dirichlet-weight logp index right-error)))
      (+ left-error right-error)))
 :hints (("Goal"
  :use ((:instance lw-log-lower-cauchy (value index)))
  :in-theory (e/d (lw-zeta-dirichlet-weight) (lw-log-lower-cauchy))
  :do-not-induct t)))

(local (in-theory (disable lw-zeta-dirichlet-weight)))


(local (defthm lw-ztt-power-one
 (implies (rationalp value) (equal (lw-rational-power value 1) value))
 :hints (("Goal" :expand ((lw-rational-power value 1) (lw-rational-power value 0))))))

(local (defthm lw-ztt-exp-cap-dominates
 (implies (natp index) (<= index (lw-exp-lipschitz-cap index)))
 :hints (("Goal"
  :use ((:instance lw-exp-linear-power-le-upper (value index) (index 1) (error 1)))
  :in-theory (e/d (lw-exp-lipschitz-cap) (lw-exp-linear-power-le-upper))
  :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-ztt-unit-data
 (implies (and (natp total) (rationalp model-error) (< 0 model-error))
  (and (rationalp (lw-smoothed-ramp-unit-error total model-error))
       (< 0 (lw-smoothed-ramp-unit-error total model-error))))
 :hints (("Goal" :in-theory (enable lw-smoothed-ramp-unit-error) :nonlinearp t))
 :rule-classes nil))

(local (defthm lw-ztt-weighted-log-budget
 (implies
  (and (natp count) (< 1 count) (natp total) (rationalp model-error) (< 0 model-error)
       (rationalp primitive-error) (< 0 primitive-error))
  (<= (* (lw-zeta-dirichlet-weight logp count primitive-error) (lw-smoothed-ramp-log-error count total model-error))
      (lw-smoothed-ramp-unit-error total model-error)))
 :hints (("Goal"
  :use ((:instance lw-ztt-exp-cap-dominates (index count))
        (:instance lw-smoothed-ramp-log-error-adequate (index count) (error model-error))
        (:instance lw-zeta-dirichlet-weight-valid (index count) (epsilon primitive-error))
        (:instance lw-ztt-multiply-order
         (a (lw-zeta-dirichlet-weight logp count primitive-error)) (b (lw-exp-lipschitz-cap count))
         (factor (lw-smoothed-ramp-log-error count total model-error))))
  :in-theory (disable lw-smoothed-ramp-log-error-adequate lw-zeta-dirichlet-weight-valid)
  :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-ztt-scale-difference
 (equal (lw-complex-sub (lw-complex-scale factor a) (lw-complex-scale factor b))
        (lw-complex-scale factor (lw-complex-sub a b)))
 :hints (("Goal" :in-theory (enable lw-complex-sub lw-complex-scale)))))

(local (defthm lw-ztt-weighted-log-transport
 (implies (and (rationalp rate) (<= 0 rate) (rationalp height) (natp count) (< 1 count) (natp left-total) (natp right-total)
       (rationalp left-model-error) (< 0 left-model-error) (rationalp right-model-error) (< 0 right-model-error)
       (rationalp left-primitive-error) (< 0 left-primitive-error) (rationalp right-primitive-error) (< 0 right-primitive-error)
       (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-scale (lw-zeta-dirichlet-weight logp count left-primitive-error) (lw-complex-log-ramp-independent-exp rate height count (lw-smoothed-ramp-log-error count left-total left-model-error) left-error)) (lw-complex-scale (lw-zeta-dirichlet-weight logp count left-primitive-error) (lw-complex-log-ramp-independent-exp rate height count (lw-smoothed-ramp-log-error count right-total right-model-error) right-error))) (+ (* (* 2 (+ rate (abs height))) (+ (lw-smoothed-ramp-unit-error left-total left-model-error) (lw-smoothed-ramp-unit-error right-total right-model-error))) (* 32 count (+ left-error right-error)))))
 :hints (("Goal"
  :use ((:instance lw-smoothed-ramp-log-error-adequate (index count) (total left-total) (error left-model-error))
        (:instance lw-smoothed-ramp-log-error-adequate (index count) (total right-total) (error right-model-error))
        (:instance lw-ztt-unit-data (total left-total) (model-error left-model-error))
        (:instance lw-ztt-unit-data (total right-total) (model-error right-model-error))
        (:instance lw-zeta-dirichlet-weight-valid (index count) (epsilon left-primitive-error))
        (:instance lw-ztt-weighted-log-budget (total left-total) (model-error left-model-error) (primitive-error left-primitive-error))
        (:instance lw-ztt-weighted-log-budget (total right-total) (model-error right-model-error) (primitive-error left-primitive-error))
        (:instance lw-complex-log-ramp-exp-log-transport
         (index count) (left-log-error (lw-smoothed-ramp-log-error count left-total left-model-error)) (right-log-error (lw-smoothed-ramp-log-error count right-total right-model-error)))
        (:instance lw-complex-scale-disk (point (lw-complex-sub (lw-complex-log-ramp-independent-exp rate height count (lw-smoothed-ramp-log-error count left-total left-model-error) left-error) (lw-complex-log-ramp-independent-exp rate height count (lw-smoothed-ramp-log-error count right-total right-model-error) right-error))) (factor (lw-zeta-dirichlet-weight logp count left-primitive-error))
         (radius (+ (* (* 2 (+ rate (abs height))) (+ (lw-smoothed-ramp-log-error count left-total left-model-error) (lw-smoothed-ramp-log-error count right-total right-model-error))) (* 32 (+ left-error right-error)))))
        (:instance lw-ztt-multiply-order
         (a (* (lw-zeta-dirichlet-weight logp count left-primitive-error) (+ (lw-smoothed-ramp-log-error count left-total left-model-error) (lw-smoothed-ramp-log-error count right-total right-model-error)))) (b (+ (lw-smoothed-ramp-unit-error left-total left-model-error) (lw-smoothed-ramp-unit-error right-total right-model-error))) (factor (* 2 (+ rate (abs height)))))
        (:instance lw-ztt-multiply-order (a (lw-zeta-dirichlet-weight logp count left-primitive-error)) (b count) (factor (* 32 (+ left-error right-error))))
        (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-scale (lw-zeta-dirichlet-weight logp count left-primitive-error) (lw-complex-log-ramp-independent-exp rate height count (lw-smoothed-ramp-log-error count left-total left-model-error) left-error)) (lw-complex-scale (lw-zeta-dirichlet-weight logp count left-primitive-error) (lw-complex-log-ramp-independent-exp rate height count (lw-smoothed-ramp-log-error count right-total right-model-error) right-error))))
         (radius (* (lw-zeta-dirichlet-weight logp count left-primitive-error) (+ (* (* 2 (+ rate (abs height))) (+ (lw-smoothed-ramp-log-error count left-total left-model-error) (lw-smoothed-ramp-log-error count right-total right-model-error))) (* 32 (+ left-error right-error))))) (cap (+ (* (* 2 (+ rate (abs height))) (+ (lw-smoothed-ramp-unit-error left-total left-model-error) (lw-smoothed-ramp-unit-error right-total right-model-error))) (* 32 count (+ left-error right-error))))))
  :in-theory (disable lw-smoothed-ramp-log-error-adequate lw-zeta-dirichlet-weight-valid
                      lw-complex-log-ramp-exp-log-transport lw-complex-scale-disk)
  :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-ztt-coefficient-change
 (equal
  (lw-complex-sub (lw-complex-scale a x) (lw-complex-scale b y))
  (lw-complex-add
   (lw-complex-sub (lw-complex-scale a x) (lw-complex-scale a y))
   (lw-complex-scale (- a b) y)))
 :hints (("Goal" :in-theory (enable lw-complex-add lw-complex-sub lw-complex-scale)))
 :rule-classes nil))

(defthm lw-complex-zeta-term-precision-cauchy
 (implies
  (and (rationalp rate) (<= 0 rate) (rationalp height) (natp count) (< 1 count) (natp left-total) (natp right-total)
       (rationalp left-model-error) (< 0 left-model-error) (rationalp right-model-error) (< 0 right-model-error)
       (rationalp left-primitive-error) (< 0 left-primitive-error) (rationalp right-primitive-error) (< 0 right-primitive-error)
       (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error) (<= right-error 1))
  (lw-complex-diskp (lw-complex-sub (lw-complex-scale (lw-zeta-dirichlet-weight logp count left-primitive-error) (lw-complex-log-ramp-independent-exp rate height count (lw-smoothed-ramp-log-error count left-total left-model-error) left-error)) (lw-complex-scale (lw-zeta-dirichlet-weight logp count right-primitive-error) (lw-complex-log-ramp-independent-exp rate height count (lw-smoothed-ramp-log-error count right-total right-model-error) right-error))) (+ (+ (* (* 2 (+ rate (abs height))) (+ (lw-smoothed-ramp-unit-error left-total left-model-error) (lw-smoothed-ramp-unit-error right-total right-model-error))) (* 32 count (+ left-error right-error))) (* 2 (+ left-primitive-error right-primitive-error)))))
 :hints (("Goal"
  :use (lw-ztt-weighted-log-transport
        (:instance lw-zeta-dirichlet-weight-valid (index count) (epsilon left-primitive-error))
        (:instance lw-zeta-dirichlet-weight-valid (index count) (epsilon right-primitive-error))
        (:instance lw-zeta-dirichlet-weight-cauchy
         (index count) (left-error left-primitive-error) (right-error right-primitive-error))
        (:instance lw-smoothed-ramp-log-error-adequate (index count) (total right-total) (error right-model-error))
        (:instance lw-complex-log-ramp-independent-exp-unit-cap
         (index count) (log-error (lw-smoothed-ramp-log-error count right-total right-model-error)) (error right-error))
        (:instance lw-ztt-coefficient-change (a (lw-zeta-dirichlet-weight logp count left-primitive-error)) (b (lw-zeta-dirichlet-weight logp count right-primitive-error)) (x (lw-complex-log-ramp-independent-exp rate height count (lw-smoothed-ramp-log-error count left-total left-model-error) left-error)) (y (lw-complex-log-ramp-independent-exp rate height count (lw-smoothed-ramp-log-error count right-total right-model-error) right-error)))
        (:instance lw-complex-scale-disk (point (lw-complex-log-ramp-independent-exp rate height count (lw-smoothed-ramp-log-error count right-total right-model-error) right-error)) (factor (- (lw-zeta-dirichlet-weight logp count left-primitive-error) (lw-zeta-dirichlet-weight logp count right-primitive-error))) (radius 2))
        (:instance lw-complex-add-disk (left (lw-complex-sub (lw-complex-scale (lw-zeta-dirichlet-weight logp count left-primitive-error) (lw-complex-log-ramp-independent-exp rate height count (lw-smoothed-ramp-log-error count left-total left-model-error) left-error)) (lw-complex-scale (lw-zeta-dirichlet-weight logp count left-primitive-error) (lw-complex-log-ramp-independent-exp rate height count (lw-smoothed-ramp-log-error count right-total right-model-error) right-error)))) (right (lw-complex-scale (- (lw-zeta-dirichlet-weight logp count left-primitive-error) (lw-zeta-dirichlet-weight logp count right-primitive-error)) (lw-complex-log-ramp-independent-exp rate height count (lw-smoothed-ramp-log-error count right-total right-model-error) right-error)))
         (radius (+ (* (* 2 (+ rate (abs height))) (+ (lw-smoothed-ramp-unit-error left-total left-model-error) (lw-smoothed-ramp-unit-error right-total right-model-error))) (* 32 count (+ left-error right-error)))) (other-radius (* (abs (- (lw-zeta-dirichlet-weight logp count left-primitive-error) (lw-zeta-dirichlet-weight logp count right-primitive-error))) 2)))
        (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-scale (lw-zeta-dirichlet-weight logp count left-primitive-error) (lw-complex-log-ramp-independent-exp rate height count (lw-smoothed-ramp-log-error count left-total left-model-error) left-error)) (lw-complex-scale (lw-zeta-dirichlet-weight logp count right-primitive-error) (lw-complex-log-ramp-independent-exp rate height count (lw-smoothed-ramp-log-error count right-total right-model-error) right-error))))
         (radius (+ (+ (* (* 2 (+ rate (abs height))) (+ (lw-smoothed-ramp-unit-error left-total left-model-error) (lw-smoothed-ramp-unit-error right-total right-model-error))) (* 32 count (+ left-error right-error))) (* (abs (- (lw-zeta-dirichlet-weight logp count left-primitive-error) (lw-zeta-dirichlet-weight logp count right-primitive-error))) 2)))
         (cap (+ (+ (* (* 2 (+ rate (abs height))) (+ (lw-smoothed-ramp-unit-error left-total left-model-error) (lw-smoothed-ramp-unit-error right-total right-model-error))) (* 32 count (+ left-error right-error))) (* 2 (+ left-primitive-error right-primitive-error))))))
  :in-theory (disable lw-zeta-dirichlet-weight-valid lw-zeta-dirichlet-weight-cauchy
                      lw-smoothed-ramp-log-error-adequate lw-complex-log-ramp-independent-exp-unit-cap
                      lw-complex-scale-disk lw-complex-add-disk)
  :nonlinearp nil :do-not-induct t)))

