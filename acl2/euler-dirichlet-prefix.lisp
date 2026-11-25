(in-package "ACL2")

(include-book "euler-dirichlet-cells")
(include-book "dirichlet-common-precision")

; Exact Euler telescoping for the actual common-precision native sums.
; The boundary term is retained explicitly.

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

(local (in-theory
 (disable lw-log-bounds-nonnegative lw-log-bounds-lower-coarse
          lw-exp-lipschitz-cap-valid lw-complex-exp-uniform-cap-data)))

(local (in-theory (disable lw-complex-common-dirichlet-prefix lw-dirichlet-sample
 lw-common-dirichlet-coefficient lw-zeta-dirichlet-weight
 lw-complex-euler-dirichlet-cell)))

(local (defthm lw-edp-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-edp-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-edp-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-edp-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-edp-times-negative (a b) (b a)))
                 :in-theory (disable lw-edp-times-negative)))))

(local (defthm lw-edp-zero-times (equal (* 0 a) 0)))

(local (defthm lw-edp-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-edp-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-edp-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-edp-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-edp-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-edp-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-edp-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-edp-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-edp-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-edp-left-commutes)))))

(defun lw-complex-euler-dirichlet-prefix (rate height count error)
 (lw-complex-add
  (lw-complex-mul (cons (- rate 1) height)
   (lw-complex-common-dirichlet-prefix nil nil rate height count error))
  (lw-complex-scale (+ 1 count)
   (lw-dirichlet-sample rate height (+ 1 count) error error))))

(defun lw-complex-euler-dirichlet-sum (rate height count error)
 (declare (xargs :measure (nfix count)))
 (if (or (zp count) (equal count 1)) (cons 0 0)
  (lw-complex-add (lw-complex-euler-dirichlet-cell rate height count error)
   (lw-complex-euler-dirichlet-sum rate height (- count 1) error))))

(local (in-theory (disable lw-complex-euler-dirichlet-prefix lw-complex-euler-dirichlet-sum)))

(defthm lw-complex-euler-dirichlet-prefix-rational
 (implies (and (rationalp rate) (rationalp height) (natp count) (rationalp error) (< 0 error))
  (lw-complexp (lw-complex-euler-dirichlet-prefix rate height count error)))
 :hints (("Goal"
  :in-theory (enable lw-complex-euler-dirichlet-prefix lw-complexp)
  :do-not-induct t)))

(defthm lw-complex-euler-dirichlet-sum-rational
 (implies (and (rationalp rate) (rationalp height) (natp count) (rationalp error) (< 0 error))
  (lw-complexp (lw-complex-euler-dirichlet-sum rate height count error)))
 :hints (("Goal" :induct (lw-complex-euler-dirichlet-sum rate height count error)
                 :in-theory (enable lw-complex-euler-dirichlet-sum lw-complexp))))

(local (defthm lw-edp-prefix-step-algebra
 (implies (and (rationalp rate) (rationalp height) (rationalp count)
               (lw-complexp here) (lw-complexp next) (lw-complexp rest))
  (equal
   (lw-complex-add
    (lw-complex-mul (cons (- rate 1) height) (lw-complex-add here rest))
    (lw-complex-scale (+ 1 count) next))
   (lw-complex-add
    (lw-complex-add (lw-complex-mul (cons (- rate 1) height) rest)
                   (lw-complex-scale count here))
    (lw-complex-add (lw-complex-mul (cons rate height) here)
     (lw-complex-scale (+ 1 count) (lw-complex-sub next here))))))
 :hints (("Goal"
  :in-theory (enable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale)
  :nonlinearp nil :do-not-induct t)) :rule-classes nil))

(defthm lw-complex-euler-dirichlet-prefix-step
 (implies (and (rationalp rate) (rationalp height) (natp count) (< 1 count)
               (rationalp error) (< 0 error))
  (equal (lw-complex-euler-dirichlet-prefix rate height count error)
   (lw-complex-add (lw-complex-euler-dirichlet-prefix rate height (- count 1) error)
                  (lw-complex-euler-dirichlet-cell rate height count error))))
 :hints (("Goal"
  :expand ((lw-complex-common-dirichlet-prefix nil nil rate height count error))
  :use ((:instance lw-complex-common-dirichlet-prefix-rational (mangoldtp nil) (logp nil) (count (- count 1)))
        (:instance lw-complex-log-ramp-independent-exp-rational (index count) (log-error error) (delta error))
        (:instance lw-complex-log-ramp-independent-exp-rational (index (+ count 1)) (log-error error) (delta error))
        (:instance lw-edp-prefix-step-algebra
         (here (lw-complex-log-ramp-independent-exp rate height count error error))
         (next (lw-complex-log-ramp-independent-exp rate height (+ count 1) error error))
         (rest (lw-complex-common-dirichlet-prefix nil nil rate height (- count 1) error))))
  :in-theory (e/d (lw-complex-euler-dirichlet-prefix lw-complex-euler-dirichlet-cell
                   lw-dirichlet-sample lw-common-dirichlet-coefficient lw-zeta-dirichlet-weight
                   lw-complexp)
   (lw-complex-common-dirichlet-prefix-rational lw-complex-log-ramp-independent-exp-rational))
  :nonlinearp nil :do-not-induct t)))

(local (defthm lw-edp-reassociate
 (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c))
  (equal (lw-complex-add (lw-complex-add a b) c)
         (lw-complex-add a (lw-complex-add c b))))
 :hints (("Goal" :in-theory (enable lw-complexp lw-complex-add)))))

(local (defthm lw-edp-add-zero
 (implies (lw-complexp point)
  (equal (lw-complex-add point (cons 0 0)) point))
 :hints (("Goal" :in-theory (enable lw-complexp lw-complex-add)))))

(defthm lw-complex-euler-dirichlet-prefix-telescope
 (implies (and (rationalp rate) (rationalp height) (posp count)
               (rationalp error) (< 0 error))
  (equal (lw-complex-euler-dirichlet-prefix rate height count error)
   (lw-complex-add (lw-complex-euler-dirichlet-prefix rate height 1 error)
                  (lw-complex-euler-dirichlet-sum rate height count error))))
 :hints (("Goal" :induct (lw-complex-euler-dirichlet-sum rate height count error)
                 :in-theory (e/d ((:induction lw-complex-euler-dirichlet-sum))
                                  (lw-complex-euler-dirichlet-prefix-step)))
         (and stable-under-simplificationp
          '(:expand ((lw-complex-euler-dirichlet-sum rate height count error)
                     (lw-complex-euler-dirichlet-sum rate height 1 error))
            :use (lw-complex-euler-dirichlet-prefix-step)
            :do-not-induct t))))

