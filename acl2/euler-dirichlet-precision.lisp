(in-package "ACL2")

(include-book "euler-dirichlet-tail-budget")

; Independent point precisions for the actual ordinary zeta and
; pole-removed Euler prefixes throughout sigma >= 0.

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
 lw-complex-euler-dyadic-prefix-computed-tail
 lw-complex-common-dirichlet-prefix lw-common-dirichlet-coefficient
 lw-zeta-dirichlet-weight lw-dirichlet-sample
 lw-euler-continuation-tail-cap lw-euler-continuation-block-cutoff
 lw-euler-rounding-precision lw-euler-dyadic-tail-rounding)))

(local (defthm lw-edpr-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-edpr-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-edpr-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-edpr-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-edpr-times-negative (a b) (b a)))
                 :in-theory (disable lw-edpr-times-negative)))))

(local (defthm lw-edpr-zero-times (equal (* 0 a) 0)))

(local (defthm lw-edpr-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-edpr-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-edpr-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-edpr-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-edpr-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-edpr-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-edpr-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-edpr-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-edpr-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-edpr-left-commutes)))))

(local (defthm lw-edpr-ordinary-step
 (implies (and (rationalp rate) (rationalp height) (natp count) (< 1 count)
               (rationalp error) (< 0 error))
  (equal (lw-complex-common-dirichlet-prefix nil nil rate height count error)
   (lw-complex-add (lw-complex-log-ramp-independent-exp rate height count error error)
    (lw-complex-common-dirichlet-prefix nil nil rate height (- count 1) error))))
 :hints (("Goal"
  :expand ((lw-complex-common-dirichlet-prefix nil nil rate height count error))
  :use ((:instance lw-complex-log-ramp-independent-exp-rational
         (index count) (log-error error) (delta error)))
  :in-theory (enable lw-common-dirichlet-coefficient lw-zeta-dirichlet-weight lw-dirichlet-sample)
  :do-not-induct t))))

(local (defthm lw-edpr-difference-add
 (equal (lw-complex-sub (lw-complex-add a b) (lw-complex-add c d))
        (lw-complex-add (lw-complex-sub a c) (lw-complex-sub b d)))
 :hints (("Goal" :in-theory (enable lw-complex-add lw-complex-sub)))))

(local (defthm lw-edpr-sub-self
 (equal (lw-complex-sub point point) (cons 0 0))
 :hints (("Goal" :in-theory (enable lw-complex-sub)))))

(local (defthm lw-edpr-zero-disk
 (implies (and (rationalp radius) (<= 0 radius)) (lw-complex-diskp (cons 0 0) radius))
 :hints (("Goal" :in-theory (enable lw-complex-diskp lw-complexp lw-diskp)))))

(local (defun lw-edpr-countdown (count)
 (declare (xargs :measure (nfix count)))
 (if (zp count) nil (lw-edpr-countdown (- count 1)))))

(local (defthm lw-edpr-size-data
 (implies (and (rationalp rate) (<= 0 rate) (rationalp height))
  (and (rationalp (abs height)) (<= 0 (abs height))
       (rationalp (+ rate (abs height))) (<= 0 (+ rate (abs height)))))
 :rule-classes nil))

(defthm lw-complex-ordinary-prefix-precision-cauchy
 (implies (and (rationalp rate) (<= 0 rate) (rationalp height) (natp count)
               (rationalp left-error) (< 0 left-error)
               (rationalp right-error) (< 0 right-error))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-complex-common-dirichlet-prefix nil nil rate height count left-error)
    (lw-complex-common-dirichlet-prefix nil nil rate height count right-error))
   (* count (+ (* 2 (+ rate (abs height))) 32) (+ left-error right-error))))
 :hints (("Goal" :induct (lw-edpr-countdown count)
                 :in-theory
                  (union-theories
                   '(lw-edpr-countdown lw-edpr-zero-disk lw-edpr-sub-self lw-edpr-difference-add
                     lw-edpr-ordinary-step
                     lw-edpr-left-commutes lw-edpr-left-distributes lw-edpr-fold-constants
                     lw-edpr-times-negative lw-edpr-negative-times lw-edpr-zero-times
                     lw-edpr-minus-one lw-edpr-double-negative lw-edpr-add-cancel
                     lw-edpr-double lw-edpr-add-double natp posp zp fix car-cons cdr-cons
                     commutativity-of-* associativity-of-* commutativity-of-+
                     commutativity-2-of-+ associativity-of-+ distributivity
                     distributivity-of-minus-over-+ inverse-of-+
                     unicity-of-0 unicity-of-1)
                   (theory 'minimal-theory)))
         (and stable-under-simplificationp
          '(:cases ((equal count 1))
            :expand ((lw-complex-common-dirichlet-prefix nil nil rate height 0 left-error)
                     (lw-complex-common-dirichlet-prefix nil nil rate height 0 right-error)
                     (lw-complex-common-dirichlet-prefix nil nil rate height 1 left-error)
                     (lw-complex-common-dirichlet-prefix nil nil rate height 1 right-error))
            :use (lw-edpr-size-data
                  (:instance lw-edpr-ordinary-step (error left-error))
                  (:instance lw-edpr-ordinary-step (error right-error))
                  (:instance lw-complex-log-ramp-exp-log-transport
                   (index count) (left-log-error left-error) (right-log-error right-error))
                  (:instance lw-complex-add-disk
                   (left (lw-complex-sub
                    (lw-complex-log-ramp-independent-exp rate height count left-error left-error)
                    (lw-complex-log-ramp-independent-exp rate height count right-error right-error)))
                   (right (lw-complex-sub
                    (lw-complex-common-dirichlet-prefix nil nil rate height (- count 1) left-error)
                    (lw-complex-common-dirichlet-prefix nil nil rate height (- count 1) right-error)))
                   (radius (* (+ (* 2 (+ rate (abs height))) 32) (+ left-error right-error)))
                   (other-radius (* (- count 1) (+ (* 2 (+ rate (abs height))) 32)
                                    (+ left-error right-error)))))
            :nonlinearp t :do-not-induct t))))

(defun lw-euler-prefix-transport-cost (rate height count)
 (+ (* (+ rate (abs height) 1) count (+ (* 2 (+ rate (abs height))) 32))
    (* (+ count 1) (+ (* 2 (+ rate (abs height))) 32))))

(local (in-theory (disable lw-euler-prefix-transport-cost)))

(defthm lw-euler-prefix-transport-cost-valid
 (implies (and (rationalp rate) (<= 0 rate) (rationalp height) (natp count))
  (and (rationalp (lw-euler-prefix-transport-cost rate height count))
       (< 0 (lw-euler-prefix-transport-cost rate height count))))
 :hints (("Goal" :in-theory (enable lw-euler-prefix-transport-cost) :nonlinearp t)))

(local (defthm lw-edpr-shifted-point-cap
 (implies (and (rationalp rate) (<= 0 rate) (rationalp height))
  (lw-complex-diskp (cons (- rate 1) height) (+ rate (abs height) 1)))
 :hints (("Goal"
  :cases ((<= 1 rate))
  :use ((:instance lw-complex-l1-bound (point (cons (- rate 1) height)))
        (:instance lw-complex-disk-enlarge
         (point (cons (- rate 1) height)) (radius (+ (abs (- rate 1)) (abs height)))
         (cap (+ rate (abs height) 1))))
  :in-theory (e/d (lw-complexp lw-complex-l1) (lw-complex-l1-bound))
  :nonlinearp nil :do-not-induct t))))

(local (defthm lw-edpr-prefix-residual
 (implies (and (lw-complexp point) (lw-complexp a) (lw-complexp b)
               (lw-complexp c) (lw-complexp d) (rationalp factor))
  (equal
   (lw-complex-sub
    (lw-complex-add (lw-complex-mul point a) (lw-complex-scale factor b))
    (lw-complex-add (lw-complex-mul point c) (lw-complex-scale factor d)))
   (lw-complex-add (lw-complex-mul point (lw-complex-sub a c))
                   (lw-complex-scale factor (lw-complex-sub b d)))))
 :hints (("Goal" :in-theory (enable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale)
                 :nonlinearp nil :do-not-induct t)) :rule-classes nil))

(local (defthm lw-edpr-successor-abs
 (implies (posp count) (equal (abs (+ 1 count)) (+ 1 count)))))

(defthm lw-complex-euler-dirichlet-prefix-precision-cauchy
 (implies (and (rationalp rate) (<= 0 rate) (rationalp height) (posp count)
               (rationalp left-error) (< 0 left-error)
               (rationalp right-error) (< 0 right-error))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-euler-dirichlet-prefix rate height count left-error)
                   (lw-complex-euler-dirichlet-prefix rate height count right-error))
   (* (lw-euler-prefix-transport-cost rate height count) (+ left-error right-error))))
 :hints (("Goal"
  :use (lw-edpr-size-data lw-complex-ordinary-prefix-precision-cauchy lw-edpr-shifted-point-cap
        (:instance lw-complex-common-dirichlet-prefix-rational (mangoldtp nil) (logp nil) (error left-error))
        (:instance lw-complex-common-dirichlet-prefix-rational (mangoldtp nil) (logp nil) (error right-error))
        (:instance lw-complex-log-ramp-independent-exp-rational
         (index (+ count 1)) (log-error left-error) (delta left-error))
        (:instance lw-complex-log-ramp-independent-exp-rational
         (index (+ count 1)) (log-error right-error) (delta right-error))
        (:instance lw-complex-log-ramp-exp-log-transport
         (index (+ count 1)) (left-log-error left-error) (right-log-error right-error))
        (:instance lw-edpr-prefix-residual
         (point (cons (- rate 1) height))
         (a (lw-complex-common-dirichlet-prefix nil nil rate height count left-error))
         (b (lw-complex-log-ramp-independent-exp rate height (+ count 1) left-error left-error))
         (c (lw-complex-common-dirichlet-prefix nil nil rate height count right-error))
         (d (lw-complex-log-ramp-independent-exp rate height (+ count 1) right-error right-error))
         (factor (+ count 1)))
        (:instance lw-complex-mul-disk
         (left (cons (- rate 1) height))
         (right (lw-complex-sub
          (lw-complex-common-dirichlet-prefix nil nil rate height count left-error)
          (lw-complex-common-dirichlet-prefix nil nil rate height count right-error)))
         (radius (+ rate (abs height) 1))
         (other-radius (* count (+ (* 2 (+ rate (abs height))) 32) (+ left-error right-error))))
        (:instance lw-complex-scale-disk
         (point (lw-complex-sub
          (lw-complex-log-ramp-independent-exp rate height (+ count 1) left-error left-error)
          (lw-complex-log-ramp-independent-exp rate height (+ count 1) right-error right-error)))
         (factor (+ count 1))
         (radius (* (+ (* 2 (+ rate (abs height))) 32) (+ left-error right-error))))
        (:instance lw-complex-add-disk
         (left (lw-complex-mul (cons (- rate 1) height)
          (lw-complex-sub
           (lw-complex-common-dirichlet-prefix nil nil rate height count left-error)
           (lw-complex-common-dirichlet-prefix nil nil rate height count right-error))))
         (right (lw-complex-scale (+ count 1)
          (lw-complex-sub
           (lw-complex-log-ramp-independent-exp rate height (+ count 1) left-error left-error)
           (lw-complex-log-ramp-independent-exp rate height (+ count 1) right-error right-error))))
         (radius (* (+ rate (abs height) 1) count (+ (* 2 (+ rate (abs height))) 32)
                    (+ left-error right-error)))
         (other-radius (* (+ count 1) (+ (* 2 (+ rate (abs height))) 32) (+ left-error right-error)))))
  :in-theory (union-theories
   '(lw-complex-euler-dirichlet-prefix lw-dirichlet-sample
     lw-euler-prefix-transport-cost lw-complexp
     lw-edpr-left-commutes lw-edpr-left-distributes lw-edpr-fold-constants
     lw-edpr-times-negative lw-edpr-negative-times lw-edpr-zero-times
     lw-edpr-minus-one lw-edpr-double-negative lw-edpr-add-cancel
     lw-edpr-double lw-edpr-add-double lw-edpr-successor-abs
     natp posp fix car-cons cdr-cons
     commutativity-of-* associativity-of-* commutativity-of-+
     commutativity-2-of-+ associativity-of-+ distributivity
     distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(local (defthm lw-edpr-power-two-natural
 (natp (lw-rational-power 2 count))
 :hints (("Goal" :in-theory (enable lw-rational-power)))
 :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-edpr-power-two-four
 (implies (and (natp count) (<= 2 count)) (<= 4 (lw-rational-power 2 count)))
 :hints (("Goal" :use ((:instance lw-rational-power-monotone-exponent
                       (base 2) (small 2) (large count)))))
 :rule-classes nil))

(defun lw-euler-dyadic-transport-cost (rate height count)
 (lw-euler-prefix-transport-cost rate height (- (lw-rational-power 2 count) 1)))

(local (in-theory (disable lw-euler-dyadic-transport-cost)))

(defthm lw-euler-dyadic-transport-cost-valid
 (implies (and (rationalp rate) (<= 0 rate) (rationalp height) (natp count) (<= 2 count))
  (and (rationalp (lw-euler-dyadic-transport-cost rate height count))
       (< 0 (lw-euler-dyadic-transport-cost rate height count))))
 :hints (("Goal"
  :use (lw-edpr-power-two-natural lw-edpr-power-two-four
        (:instance lw-euler-prefix-transport-cost-valid (count (- (lw-rational-power 2 count) 1))))
  :in-theory (union-theories '(lw-euler-dyadic-transport-cost natp posp fix)
                             (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-complex-euler-dyadic-prefix-precision-cauchy
 (implies (and (rationalp rate) (<= 0 rate) (rationalp height) (natp count) (<= 2 count)
               (rationalp left-error) (< 0 left-error)
               (rationalp right-error) (< 0 right-error))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-euler-dyadic-prefix rate height count left-error)
                   (lw-complex-euler-dyadic-prefix rate height count right-error))
   (* (lw-euler-dyadic-transport-cost rate height count) (+ left-error right-error))))
 :hints (("Goal"
  :use (lw-edpr-power-two-natural lw-edpr-power-two-four
        (:instance lw-complex-euler-dirichlet-prefix-precision-cauchy
         (count (- (lw-rational-power 2 count) 1))))
  :in-theory (union-theories
   '(lw-complex-euler-dyadic-prefix lw-euler-dyadic-transport-cost natp posp fix)
   (theory 'minimal-theory))
  :do-not-induct t)))


