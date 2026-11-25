(in-package "ACL2")

(include-book "zeta-term-transport")
(include-book "dirichlet-family-precision")

; Explicit ordinary and logarithm-weighted finite zeta sums. The n=1
; term is exactly 1 in ordinary mode and 0 in logarithm mode.
; The precision proofs specialize the existing finite-family argument.

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

(local (defthm lw-zfp-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-zfp-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-zfp-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-zfp-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-zfp-times-negative (a b) (b a)))
                 :in-theory (disable lw-zfp-times-negative)))))

(local (defthm lw-zfp-zero-times (equal (* 0 a) 0)))

(local (defthm lw-zfp-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-zfp-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-zfp-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-zfp-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-zfp-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-zfp-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-zfp-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-zfp-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-zfp-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-zfp-left-commutes)))))

(defun lw-complex-zeta-partial-sum (logp rate height count total model-error primitive-error delta)
 (declare (xargs :measure (nfix count)))
 (if (zp count) (cons 0 0)
  (if (equal count 1) (if logp (cons 0 0) (cons 1 0))
   (lw-complex-add
    (lw-complex-scale (lw-zeta-dirichlet-weight logp count primitive-error)
     (lw-complex-log-ramp-independent-exp rate height count
      (lw-smoothed-ramp-log-error count total model-error) delta))
    (lw-complex-zeta-partial-sum logp rate height (- count 1) total model-error primitive-error delta)))))

(local (in-theory (disable lw-complex-zeta-partial-sum lw-zeta-dirichlet-weight
 lw-dirichlet-family-precision-radius
 lw-smoothed-ramp-log-error lw-smoothed-ramp-unit-error)))

(defthm lw-complex-zeta-partial-sum-rational
 (implies
  (and (rationalp rate) (< 1 rate) (rationalp height) (natp count) (natp total)
       (rationalp model-error) (< 0 model-error) (rationalp primitive-error) (< 0 primitive-error)
       (rationalp delta) (< 0 delta))
  (lw-complexp (lw-complex-zeta-partial-sum logp rate height count total model-error primitive-error delta)))
 :hints (("Goal"
   :induct (lw-complex-zeta-partial-sum logp rate height count total model-error primitive-error delta)
   :in-theory (enable (:induction lw-complex-zeta-partial-sum) (:definition lw-complex-zeta-partial-sum)
                      lw-complexp lw-complex-add lw-complex-scale))
  (and stable-under-simplificationp
   '(:use ((:instance lw-smoothed-ramp-log-error-adequate (index count) (error model-error))
           (:instance lw-zeta-dirichlet-weight-valid (index count) (epsilon primitive-error))
           (:instance lw-complex-log-ramp-independent-exp-rational
            (index count) (log-error (lw-smoothed-ramp-log-error count total model-error))))
     :in-theory (e/d (lw-complexp lw-complex-add lw-complex-scale)
       (lw-complex-log-ramp-independent-exp-rational lw-smoothed-ramp-log-error-adequate lw-zeta-dirichlet-weight-valid))
     :do-not-induct t))))

(local (defthm lw-zfp-unit-data
 (implies (and (natp total) (rationalp model-error) (< 0 model-error))
  (and (rationalp (lw-smoothed-ramp-unit-error total model-error))
       (< 0 (lw-smoothed-ramp-unit-error total model-error))))
 :hints (("Goal" :in-theory (enable lw-smoothed-ramp-unit-error) :nonlinearp t))
 :rule-classes nil))

(local (defthm lw-zfp-radius-data
 (implies (and (rationalp rate) (<= 0 rate) (rationalp height) (natp count) (natp left-total) (natp right-total)
       (rationalp left-model-error) (< 0 left-model-error) (rationalp right-model-error) (< 0 right-model-error)
       (rationalp left-primitive-error) (< 0 left-primitive-error) (rationalp right-primitive-error) (< 0 right-primitive-error)
       (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
  (and (rationalp (lw-dirichlet-family-precision-radius rate height count left-total right-total left-model-error right-model-error left-primitive-error right-primitive-error left-error right-error)) (<= 0 (lw-dirichlet-family-precision-radius rate height count left-total right-total left-model-error right-model-error left-primitive-error right-primitive-error left-error right-error))))
 :hints (("Goal"
  :use ((:instance lw-zfp-unit-data (total left-total) (model-error left-model-error))
        (:instance lw-zfp-unit-data (total right-total) (model-error right-model-error)))
  :in-theory (enable lw-dirichlet-family-precision-radius)
  :nonlinearp t :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-zfp-radius-step
 (implies (and (rationalp rate) (<= 0 rate) (rationalp height) (natp count) (natp left-total) (natp right-total)
       (rationalp left-model-error) (< 0 left-model-error) (rationalp right-model-error) (< 0 right-model-error)
       (rationalp left-primitive-error) (< 0 left-primitive-error) (rationalp right-primitive-error) (< 0 right-primitive-error)
       (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error) (< 1 count))
  (equal (lw-dirichlet-family-precision-radius rate height count left-total right-total left-model-error right-model-error left-primitive-error right-primitive-error left-error right-error) (+ (+ (+ (* (* 2 (+ rate (abs height))) (+ (lw-smoothed-ramp-unit-error left-total left-model-error) (lw-smoothed-ramp-unit-error right-total right-model-error))) (* 32 count (+ left-error right-error))) (* 2 (+ left-primitive-error right-primitive-error))) (lw-dirichlet-family-precision-radius rate height (- count 1) left-total right-total left-model-error right-model-error left-primitive-error right-primitive-error left-error right-error))))
 :hints (("Goal"
  :use ((:instance lw-zfp-unit-data (total left-total) (model-error left-model-error))
        (:instance lw-zfp-unit-data (total right-total) (model-error right-model-error)))
  :in-theory (enable lw-dirichlet-family-precision-radius)
  :nonlinearp t :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-zfp-add-differences
 (equal (lw-complex-sub (lw-complex-add left rest) (lw-complex-add right other))
        (lw-complex-add (lw-complex-sub left right) (lw-complex-sub rest other)))
 :hints (("Goal" :in-theory (enable lw-complex-sub lw-complex-add)))))

(local (defthm lw-zfp-sub-self (equal (lw-complex-sub point point) (cons 0 0))
 :hints (("Goal" :in-theory (enable lw-complex-sub)))))

(local (defthm lw-zfp-zero-disk
 (implies (and (rationalp radius) (<= 0 radius)) (lw-complex-diskp (cons 0 0) radius))
 :hints (("Goal" :in-theory (enable lw-complex-diskp lw-complexp lw-diskp)))))

(local (defthm lw-zfp-radius-zero
 (equal (lw-dirichlet-family-precision-radius rate height 0 left-total right-total left-model-error right-model-error left-primitive-error right-primitive-error left-error right-error) 0)
 :hints (("Goal" :in-theory (enable lw-dirichlet-family-precision-radius)))))

(local (defthm lw-zfp-one-zero-disk
 (implies (and (rationalp rate) (<= 0 rate) (rationalp height) (natp left-total) (natp right-total)
       (rationalp left-model-error) (< 0 left-model-error) (rationalp right-model-error) (< 0 right-model-error)
       (rationalp left-primitive-error) (< 0 left-primitive-error) (rationalp right-primitive-error) (< 0 right-primitive-error)
       (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
  (lw-complex-diskp (cons 0 0) (lw-dirichlet-family-precision-radius rate height 1 left-total right-total left-model-error right-model-error left-primitive-error right-primitive-error left-error right-error)))
 :hints (("Goal" :use ((:instance lw-zfp-radius-data (count 1))) :do-not-induct t))))

(defthm lw-complex-zeta-partial-sum-precision-cauchy
 (implies (and (rationalp rate) (<= 0 rate) (rationalp height) (natp count) (natp left-total) (natp right-total)
       (rationalp left-model-error) (< 0 left-model-error) (rationalp right-model-error) (< 0 right-model-error)
       (rationalp left-primitive-error) (< 0 left-primitive-error) (rationalp right-primitive-error) (< 0 right-primitive-error)
       (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error) (<= right-error 1))
  (lw-complex-diskp (lw-complex-sub (lw-complex-zeta-partial-sum logp rate height count left-total left-model-error left-primitive-error left-error) (lw-complex-zeta-partial-sum logp rate height count right-total right-model-error right-primitive-error right-error)) (lw-dirichlet-family-precision-radius rate height count left-total right-total left-model-error right-model-error left-primitive-error right-primitive-error left-error right-error)))
 :hints (("Goal"
  :induct (lw-complex-zeta-partial-sum logp rate height count left-total left-model-error left-primitive-error left-error)
  :in-theory (enable (:induction lw-complex-zeta-partial-sum) (:definition lw-complex-zeta-partial-sum)))
  (and stable-under-simplificationp
   '(:use (lw-zfp-radius-data lw-zfp-radius-step
           lw-complex-zeta-term-precision-cauchy
           (:instance lw-complex-add-disk (left (lw-complex-sub (lw-complex-scale (lw-zeta-dirichlet-weight logp count left-primitive-error) (lw-complex-log-ramp-independent-exp rate height count (lw-smoothed-ramp-log-error count left-total left-model-error) left-error)) (lw-complex-scale (lw-zeta-dirichlet-weight logp count right-primitive-error) (lw-complex-log-ramp-independent-exp rate height count (lw-smoothed-ramp-log-error count right-total right-model-error) right-error)))) (right (lw-complex-sub (lw-complex-zeta-partial-sum logp rate height (- count 1) left-total left-model-error left-primitive-error left-error) (lw-complex-zeta-partial-sum logp rate height (- count 1) right-total right-model-error right-primitive-error right-error)))
            (radius (+ (+ (* (* 2 (+ rate (abs height))) (+ (lw-smoothed-ramp-unit-error left-total left-model-error) (lw-smoothed-ramp-unit-error right-total right-model-error))) (* 32 count (+ left-error right-error))) (* 2 (+ left-primitive-error right-primitive-error)))) (other-radius (lw-dirichlet-family-precision-radius rate height (- count 1) left-total right-total left-model-error right-model-error left-primitive-error right-primitive-error left-error right-error)))
           (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-zeta-partial-sum logp rate height count left-total left-model-error left-primitive-error left-error) (lw-complex-zeta-partial-sum logp rate height count right-total right-model-error right-primitive-error right-error))) (radius (+ (+ (+ (* (* 2 (+ rate (abs height))) (+ (lw-smoothed-ramp-unit-error left-total left-model-error) (lw-smoothed-ramp-unit-error right-total right-model-error))) (* 32 count (+ left-error right-error))) (* 2 (+ left-primitive-error right-primitive-error))) (lw-dirichlet-family-precision-radius rate height (- count 1) left-total right-total left-model-error right-model-error left-primitive-error right-primitive-error left-error right-error))) (cap (lw-dirichlet-family-precision-radius rate height count left-total right-total left-model-error right-model-error left-primitive-error right-primitive-error left-error right-error))))
     :in-theory (disable lw-complex-zeta-partial-sum lw-complex-zeta-term-precision-cauchy
                         lw-complex-add-disk)
     :nonlinearp nil :do-not-induct t))))

(local (defthm lw-zfp-count-log-budget
 (implies (and (natp count) (natp total) (<= count total)
               (rationalp model-error) (< 0 model-error))
  (<= (* count (lw-smoothed-ramp-unit-error total model-error)) (* 1/16 model-error)))
 :hints (("Goal"
  :use ((:instance lw-zfp-multiply-order (a count) (b (+ 1 total)) (factor model-error))
        (:instance lw-positive-division-bound
         (numerator (* count model-error)) (divisor (+ 1 total)) (bound model-error)))
  :in-theory (enable lw-smoothed-ramp-unit-error)
  :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(defthm lw-complex-zeta-partial-sum-uniform-precision-cauchy
 (implies (and (rationalp rate) (<= 0 rate) (rationalp height) (natp count) (natp left-total) (natp right-total)
       (rationalp left-model-error) (< 0 left-model-error) (rationalp right-model-error) (< 0 right-model-error)
       (rationalp left-primitive-error) (< 0 left-primitive-error) (rationalp right-primitive-error) (< 0 right-primitive-error)
       (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error) (<= count left-total) (<= count right-total) (<= right-error 1))
  (lw-complex-diskp (lw-complex-sub (lw-complex-zeta-partial-sum logp rate height count left-total left-model-error left-primitive-error left-error) (lw-complex-zeta-partial-sum logp rate height count right-total right-model-error right-primitive-error right-error)) (+ (* (* 2 (+ rate (abs height))) 1/16 (+ left-model-error right-model-error))
     (* 16 count (+ 1 count) (+ left-error right-error))
     (* 2 count (+ left-primitive-error right-primitive-error)))))
 :hints (("Goal"
  :use (lw-complex-zeta-partial-sum-precision-cauchy
        (:instance lw-zfp-unit-data (total left-total) (model-error left-model-error))
        (:instance lw-zfp-unit-data (total right-total) (model-error right-model-error))
        (:instance lw-zfp-count-log-budget (total left-total) (model-error left-model-error))
        (:instance lw-zfp-count-log-budget (total right-total) (model-error right-model-error))
        (:instance lw-zfp-multiply-order
         (a (* count (+ (lw-smoothed-ramp-unit-error left-total left-model-error) (lw-smoothed-ramp-unit-error right-total right-model-error)))) (b (* 1/16 (+ left-model-error right-model-error))) (factor (* 2 (+ rate (abs height)))))
        (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-zeta-partial-sum logp rate height count left-total left-model-error left-primitive-error left-error) (lw-complex-zeta-partial-sum logp rate height count right-total right-model-error right-primitive-error right-error))) (radius (lw-dirichlet-family-precision-radius rate height count left-total right-total left-model-error right-model-error left-primitive-error right-primitive-error left-error right-error)) (cap (+ (* (* 2 (+ rate (abs height))) 1/16 (+ left-model-error right-model-error))
     (* 16 count (+ 1 count) (+ left-error right-error))
     (* 2 count (+ left-primitive-error right-primitive-error))))))
  :in-theory (e/d (lw-dirichlet-family-precision-radius)
    (lw-complex-zeta-partial-sum-precision-cauchy))
  :nonlinearp nil :do-not-induct t)))

(local (in-theory (disable lw-dirichlet-finite-model-precision
 lw-dirichlet-finite-coefficient-precision lw-dirichlet-finite-node-precision)))

(defun lw-complex-zeta-finite-value (logp rate height count error)
 (lw-complex-zeta-partial-sum logp rate height count count (lw-dirichlet-finite-model-precision rate height error) (lw-dirichlet-finite-coefficient-precision count error) (lw-dirichlet-finite-node-precision count error)))

(local (in-theory (disable lw-complex-zeta-finite-value)))

(defthm lw-complex-zeta-finite-value-rational
 (implies
  (and (rationalp rate) (< 1 rate) (rationalp height) (natp count) (rationalp error) (< 0 error))
  (lw-complexp (lw-complex-zeta-finite-value logp rate height count error)))
 :hints (("Goal"
  :use (lw-dirichlet-finite-precisions-valid
        (:instance lw-complex-zeta-partial-sum-rational
         (total count) (model-error (lw-dirichlet-finite-model-precision rate height error)) (primitive-error (lw-dirichlet-finite-coefficient-precision count error)) (delta (lw-dirichlet-finite-node-precision count error))))
  :in-theory (e/d (lw-complex-zeta-finite-value)
    (lw-dirichlet-finite-precisions-valid lw-complex-zeta-partial-sum-rational))
  :do-not-induct t)))

(defthm lw-complex-zeta-finite-value-cauchy
 (implies
  (and (rationalp rate) (< 1 rate) (rationalp height) (natp count)
       (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-zeta-finite-value logp rate height count left-error) (lw-complex-zeta-finite-value logp rate height count right-error)) (+ left-error right-error)))
 :hints (("Goal"
  :use ((:instance lw-dirichlet-finite-precisions-valid (error left-error))
        (:instance lw-dirichlet-finite-precisions-valid (error right-error))
        (:instance lw-complex-zeta-partial-sum-uniform-precision-cauchy (left-total count) (right-total count)
         (left-model-error (lw-dirichlet-finite-model-precision rate height left-error)) (right-model-error (lw-dirichlet-finite-model-precision rate height right-error))
         (left-primitive-error (lw-dirichlet-finite-coefficient-precision count left-error)) (right-primitive-error (lw-dirichlet-finite-coefficient-precision count right-error))
         (left-error (lw-dirichlet-finite-node-precision count left-error)) (right-error (lw-dirichlet-finite-node-precision count right-error)))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub (lw-complex-zeta-finite-value logp rate height count left-error) (lw-complex-zeta-finite-value logp rate height count right-error))) (radius (+ (* (* 2 (+ rate (abs height))) 1/16 (+ (lw-dirichlet-finite-model-precision rate height left-error) (lw-dirichlet-finite-model-precision rate height right-error)))
   (* 16 count (+ 1 count) (+ (lw-dirichlet-finite-node-precision count left-error) (lw-dirichlet-finite-node-precision count right-error)))
   (* 2 count (+ (lw-dirichlet-finite-coefficient-precision count left-error) (lw-dirichlet-finite-coefficient-precision count right-error))))) (cap (+ left-error right-error))))
  :in-theory (e/d (lw-complex-zeta-finite-value)
    (lw-dirichlet-finite-precisions-valid lw-complex-zeta-partial-sum-uniform-precision-cauchy))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-zeta-partial-sum-finite-comparison
 (implies
  (and (rationalp rate) (< 1 rate) (rationalp height) (natp count) (natp total) (<= count total)
       (rationalp model-error) (< 0 model-error) (rationalp primitive-error) (< 0 primitive-error)
       (rationalp delta) (< 0 delta) (rationalp error) (< 0 error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-zeta-partial-sum logp rate height count total model-error primitive-error delta) (lw-complex-zeta-finite-value logp rate height count error)) (+ (* (* 2 (+ rate (abs height))) 1/16 model-error) (* 16 (* count (+ 1 count)) delta) (* 2 count primitive-error) error)))
 :hints (("Goal"
  :use (lw-dirichlet-finite-precisions-valid
        (:instance lw-complex-zeta-partial-sum-uniform-precision-cauchy (left-total total) (right-total count)
         (left-model-error model-error) (right-model-error (lw-dirichlet-finite-model-precision rate height error))
         (left-primitive-error primitive-error) (right-primitive-error (lw-dirichlet-finite-coefficient-precision count error))
         (left-error delta) (right-error (lw-dirichlet-finite-node-precision count error)))
        (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-zeta-partial-sum logp rate height count total model-error primitive-error delta) (lw-complex-zeta-finite-value logp rate height count error)))
         (radius (+ (* (* 2 (+ rate (abs height))) 1/16 (+ model-error (lw-dirichlet-finite-model-precision rate height error))) (* 16 count (+ 1 count) (+ delta (lw-dirichlet-finite-node-precision count error))) (* 2 count (+ primitive-error (lw-dirichlet-finite-coefficient-precision count error))))) (cap (+ (* (* 2 (+ rate (abs height))) 1/16 model-error) (* 16 (* count (+ 1 count)) delta) (* 2 count primitive-error) error))))
  :in-theory (e/d (lw-complex-zeta-finite-value)
    (lw-dirichlet-finite-precisions-valid lw-complex-zeta-partial-sum-uniform-precision-cauchy))
  :nonlinearp nil :do-not-induct t)))

