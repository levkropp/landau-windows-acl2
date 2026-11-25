(in-package "ACL2")

(include-book "euler-dirichlet-tail")

; Computed dyadic cutoff and roundoff budget for any positive tail error.

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
(local (in-theory (disable lw-complex-euler-dyadic-prefix lw-complex-euler-dyadic-tail
 lw-complex-euler-dyadic-tail-telescope lw-complex-euler-dyadic-tail-difference
 lw-complex-euler-dyadic-tail-square-bound lw-complex-euler-dyadic-prefix-tail-bound
 lw-euler-dyadic-tail-rounding lw-ceiling-rational)))

(local (defthm lw-edtb-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-edtb-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-edtb-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-edtb-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-edtb-times-negative (a b) (b a)))
                 :in-theory (disable lw-edtb-times-negative)))))

(local (defthm lw-edtb-zero-times (equal (* 0 a) 0)))

(local (defthm lw-edtb-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-edtb-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-edtb-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-edtb-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-edtb-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-edtb-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-edtb-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-edtb-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-edtb-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-edtb-left-commutes)))))

(defun lw-euler-continuation-tail-cap (rate height)
 (* 32 (lw-euler-dirichlet-cell-cap rate height) (/ rate) (/ rate)))

(local (in-theory (disable lw-euler-continuation-tail-cap)))

(defthm lw-euler-continuation-tail-cap-valid
 (implies (and (rationalp rate) (< 0 rate) (rationalp height))
  (and (rationalp (lw-euler-continuation-tail-cap rate height))
       (< 0 (lw-euler-continuation-tail-cap rate height))))
 :hints (("Goal" :use (lw-euler-dirichlet-cell-cap-valid)
                 :in-theory (e/d (lw-euler-continuation-tail-cap)
                                  (lw-euler-dirichlet-cell-cap-valid))
                 :nonlinearp t :do-not-induct t)))

(defun lw-euler-continuation-block-cutoff (rate height error)
 (+ 2 (lw-ceiling-rational (+ rate (abs height)))
      (lw-ceiling-rational (* 2 (lw-euler-continuation-tail-cap rate height) (/ error)))))

(local (in-theory (disable lw-euler-continuation-block-cutoff)))

(defthm lw-euler-continuation-block-cutoff-natural
 (and (natp (lw-euler-continuation-block-cutoff rate height error))
      (<= 2 (lw-euler-continuation-block-cutoff rate height error)))
 :hints (("Goal" :in-theory (enable lw-euler-continuation-block-cutoff)))
 :rule-classes (:rewrite :type-prescription))

(local (defthm lw-edtb-cutoff-scalar
 (implies (and (rationalp cap) (<= 0 cap) (rationalp mass) (<= 0 mass)
               (rationalp error) (< 0 error))
  (let ((index (+ 2 (lw-ceiling-rational cap)
                   (lw-ceiling-rational (* 2 mass (/ error))))))
   (and (<= cap index) (<= (* mass (/ (- index 1))) (/ error 2)))))
 :hints (("Goal"
  :use ((:instance lw-ceiling-rational-bracket (value cap))
        (:instance lw-ceiling-rational-bracket (value (* 2 mass (/ error))))
        (:instance lw-edtb-inverse-factor (divisor error) (coefficient (* 2 mass)))
        (:instance lw-edtb-multiply-order
         (a (* 2 mass (/ error)))
         (b (+ 1 (lw-ceiling-rational cap) (lw-ceiling-rational (* 2 mass (/ error)))))
         (factor error))
        (:instance lw-positive-division-bound
         (numerator mass)
         (divisor (+ 1 (lw-ceiling-rational cap) (lw-ceiling-rational (* 2 mass (/ error)))))
         (bound (/ error 2))))
  :in-theory (disable lw-ceiling-rational-bracket lw-edtb-inverse-factor)
  :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(defthm lw-euler-continuation-block-cutoff-bounds
 (implies (and (rationalp rate) (< 0 rate) (rationalp height)
               (rationalp error) (< 0 error))
  (and (<= (+ rate (abs height)) (lw-euler-continuation-block-cutoff rate height error))
       (<= (* (lw-euler-continuation-tail-cap rate height)
              (/ (- (lw-euler-continuation-block-cutoff rate height error) 1)))
           (/ error 2))))
 :hints (("Goal"
  :use (lw-euler-continuation-tail-cap-valid
        (:instance lw-edtb-cutoff-scalar
         (cap (+ rate (abs height))) (mass (lw-euler-continuation-tail-cap rate height))))
  :in-theory (e/d (lw-euler-continuation-block-cutoff)
                  (lw-euler-continuation-tail-cap-valid))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-euler-continuation-tail-cutoff-sufficient
 (implies (and (rationalp rate) (< 0 rate) (rationalp height)
               (rationalp error) (< 0 error) (natp start)
               (<= (lw-euler-continuation-block-cutoff rate height error) start))
  (and (<= 2 start)
       (<= (+ rate (abs height)) (lw-rational-power 2 start))
       (<= (* (lw-euler-continuation-tail-cap rate height) (/ (- start 1))) (/ error 2))))
 :hints (("Goal"
  :use (lw-euler-continuation-tail-cap-valid
        lw-euler-continuation-block-cutoff-natural lw-euler-continuation-block-cutoff-bounds
        (:instance lw-rational-power-bernoulli (base 2) (exponent start))
        (:instance lw-reciprocal-antitone
         (left (- (lw-euler-continuation-block-cutoff rate height error) 1))
         (right (- start 1)))
        (:instance lw-edtb-multiply-order
         (a (/ (- start 1))) (b (/ (- (lw-euler-continuation-block-cutoff rate height error) 1)))
         (factor (lw-euler-continuation-tail-cap rate height))))
  :in-theory (union-theories
   '(natp posp fix lw-edtb-left-commutes lw-edtb-fold-constants
     commutativity-of-* associativity-of-* commutativity-of-+
     commutativity-2-of-+ associativity-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(defun lw-euler-rounding-precision (cost error)
 (min 1 (/ error (+ 2 (* 2 cost)))))

(local (in-theory (disable lw-euler-rounding-precision)))

(defthm lw-euler-rounding-precision-valid
 (implies (and (rationalp cost) (<= 0 cost) (rationalp error) (< 0 error))
  (let ((request (lw-euler-rounding-precision cost error)))
   (and (rationalp request) (< 0 request) (<= request 1)
        (<= (* cost request) (/ error 2)))))
 :hints (("Goal"
  :use ((:instance lw-positive-division-bound
         (numerator (* cost error)) (divisor (+ 2 (* 2 cost))) (bound (/ error 2)))
        (:instance lw-edtb-multiply-order
         (a (min 1 (/ error (+ 2 (* 2 cost)))))
         (b (/ error (+ 2 (* 2 cost)))) (factor cost)))
  :in-theory (enable lw-euler-rounding-precision)
  :nonlinearp t :do-not-induct t)))

(defthm lw-complex-euler-dyadic-prefix-computed-tail
 (implies (and (rationalp rate) (< 0 rate) (rationalp height)
               (rationalp error) (< 0 error) (natp start) (natp count) (<= start count)
               (<= (lw-euler-continuation-block-cutoff rate height error) start)
               (rationalp request) (< 0 request)
               (<= request (lw-euler-rounding-precision
                            (lw-euler-dyadic-tail-rounding rate height count start) error)))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-euler-dyadic-prefix rate height count request)
                   (lw-complex-euler-dyadic-prefix rate height start request))
   error))
 :hints (("Goal"
  :use (lw-euler-continuation-tail-cutoff-sufficient
        lw-euler-continuation-tail-cap-valid
        lw-euler-dyadic-tail-rounding-nonnegative
        (:instance lw-euler-rounding-precision-valid
         (cost (lw-euler-dyadic-tail-rounding rate height count start)))
        (:instance lw-edtb-multiply-order
         (a request)
         (b (lw-euler-rounding-precision (lw-euler-dyadic-tail-rounding rate height count start) error))
         (factor (lw-euler-dyadic-tail-rounding rate height count start)))
        (:instance lw-complex-euler-dyadic-prefix-tail-bound (error request))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub (lw-complex-euler-dyadic-prefix rate height count request)
                                (lw-complex-euler-dyadic-prefix rate height start request)))
         (radius (+ (* (lw-euler-continuation-tail-cap rate height) (/ (- start 1)))
                    (* (lw-euler-dyadic-tail-rounding rate height count start) request)))
         (cap error)))
  :in-theory (union-theories
   '(lw-euler-continuation-tail-cap natp posp fix lw-edtb-left-commutes
     lw-edtb-fold-constants commutativity-of-* associativity-of-*
     commutativity-of-+ associativity-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

