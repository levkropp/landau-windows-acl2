(in-package "ACL2")

(include-book "euler-dirichlet-precision")

; A computed rational Cauchy name from Euler-corrected zeta prefixes.
; Agreement with the right-plane zeta name and analytic meaning are
; separate obligations; no analytic continuation oracle is introduced.

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
 lw-euler-continuation-tail-cap lw-euler-continuation-block-cutoff
 lw-euler-rounding-precision lw-euler-dyadic-tail-rounding
 lw-euler-prefix-transport-cost lw-euler-dyadic-transport-cost)))

(local (defthm lw-ecv-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ecv-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ecv-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ecv-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ecv-times-negative (a b) (b a)))
                 :in-theory (disable lw-ecv-times-negative)))))

(local (defthm lw-ecv-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ecv-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ecv-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ecv-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ecv-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ecv-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ecv-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ecv-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecv-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecv-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ecv-left-commutes)))))

(defun lw-euler-continuation-cutoff (rate height error)
 (lw-euler-continuation-block-cutoff rate height (/ error 4)))

(defun lw-euler-continuation-point-error (rate height error)
 (lw-euler-rounding-precision
  (lw-euler-dyadic-transport-cost rate height (lw-euler-continuation-cutoff rate height error))
  (/ error 4)))

(defun lw-complex-euler-continuation-value (rate height error)
 (lw-complex-euler-dyadic-prefix rate height
  (lw-euler-continuation-cutoff rate height error)
  (lw-euler-continuation-point-error rate height error)))

(local (in-theory (disable lw-euler-continuation-cutoff lw-euler-continuation-point-error
 lw-complex-euler-continuation-value)))

(defthm lw-euler-continuation-constructor-data
 (implies (and (rationalp rate) (< 0 rate) (rationalp height) (rationalp error) (< 0 error))
  (let ((index (lw-euler-continuation-cutoff rate height error))
        (request (lw-euler-continuation-point-error rate height error)))
   (and (natp index) (<= 2 index)
        (rationalp request) (< 0 request) (<= request 1)
        (<= (* (lw-euler-dyadic-transport-cost rate height index) request) (/ error 8))
        (<= (+ rate (abs height)) (lw-rational-power 2 index))
        (<= (* (lw-euler-continuation-tail-cap rate height) (/ (- index 1))) (/ error 8)))))
 :hints (("Goal"
  :use ((:instance lw-euler-continuation-block-cutoff-natural (error (/ error 4)))
        (:instance lw-euler-continuation-tail-cutoff-sufficient
         (error (/ error 4)) (start (lw-euler-continuation-block-cutoff rate height (/ error 4))))
        (:instance lw-euler-dyadic-transport-cost-valid
         (count (lw-euler-continuation-block-cutoff rate height (/ error 4))))
        (:instance lw-euler-rounding-precision-valid
         (cost (lw-euler-dyadic-transport-cost rate height
                (lw-euler-continuation-block-cutoff rate height (/ error 4))))
         (error (/ error 4))))
  :in-theory (union-theories
   '(lw-euler-continuation-cutoff lw-euler-continuation-point-error natp posp fix
     lw-ecv-left-commutes lw-ecv-fold-constants commutativity-of-* associativity-of-*
     commutativity-of-+ associativity-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-euler-continuation-value-rational
 (implies (and (rationalp rate) (< 0 rate) (rationalp height) (rationalp error) (< 0 error))
  (lw-complexp (lw-complex-euler-continuation-value rate height error)))
 :hints (("Goal"
  :use (lw-euler-continuation-constructor-data
        (:instance lw-complex-euler-dyadic-prefix-rational
         (count (lw-euler-continuation-cutoff rate height error))
         (error (lw-euler-continuation-point-error rate height error))))
  :in-theory (union-theories '(lw-complex-euler-continuation-value natp)
                             (theory 'minimal-theory))
  :do-not-induct t)))

(defun lw-euler-continuation-comparison-cost (rate height count error)
 (+ (lw-euler-dyadic-transport-cost rate height (lw-euler-continuation-cutoff rate height error))
    (lw-euler-dyadic-tail-rounding rate height count (lw-euler-continuation-cutoff rate height error))))

(local (in-theory (disable lw-euler-continuation-comparison-cost)))

(defthm lw-euler-continuation-comparison-cost-valid
 (implies (and (rationalp rate) (< 0 rate) (rationalp height) (rationalp error) (< 0 error)
               (natp count) (<= (lw-euler-continuation-cutoff rate height error) count))
  (and (rationalp (lw-euler-continuation-comparison-cost rate height count error))
       (< 0 (lw-euler-continuation-comparison-cost rate height count error))))
 :hints (("Goal"
  :use (lw-euler-continuation-constructor-data
        (:instance lw-euler-dyadic-transport-cost-valid
         (count (lw-euler-continuation-cutoff rate height error)))
        (:instance lw-euler-dyadic-tail-rounding-nonnegative
         (start (lw-euler-continuation-cutoff rate height error))))
  :in-theory (union-theories '(lw-euler-continuation-comparison-cost natp posp fix)
                             (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-complex-euler-continuation-prefix-comparison
 (implies (and (rationalp rate) (< 0 rate) (rationalp height) (rationalp error) (< 0 error)
               (natp count) (<= (lw-euler-continuation-cutoff rate height error) count)
               (rationalp request) (< 0 request) (<= request 1))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-euler-continuation-value rate height error)
                   (lw-complex-euler-dyadic-prefix rate height count request))
   (+ (/ error 4) (* (lw-euler-continuation-comparison-cost rate height count error) request))))
 :hints (("Goal"
  :use (lw-euler-continuation-constructor-data lw-complex-euler-continuation-value-rational
        lw-euler-continuation-comparison-cost-valid
        lw-euler-dirichlet-cell-cap-valid
        (:instance lw-euler-dyadic-transport-cost-valid
         (count (lw-euler-continuation-cutoff rate height error)))
        (:instance lw-euler-dyadic-tail-rounding-nonnegative
         (start (lw-euler-continuation-cutoff rate height error)))
        (:instance lw-complex-euler-dyadic-prefix-rational (error request))
        (:instance lw-complex-euler-dyadic-prefix-rational
         (count (lw-euler-continuation-cutoff rate height error)) (error request))
        (:instance lw-complex-euler-dyadic-prefix-precision-cauchy
         (count (lw-euler-continuation-cutoff rate height error))
         (left-error (lw-euler-continuation-point-error rate height error)) (right-error request))
        (:instance lw-complex-euler-dyadic-prefix-tail-bound
         (start (lw-euler-continuation-cutoff rate height error)) (error request))
        (:instance lw-complex-difference-symmetric
         (left (lw-complex-euler-dyadic-prefix rate height count request))
         (right (lw-complex-euler-dyadic-prefix rate height
                  (lw-euler-continuation-cutoff rate height error) request))
         (radius
          (+ (* (lw-euler-continuation-tail-cap rate height)
                (/ (- (lw-euler-continuation-cutoff rate height error) 1)))
             (* (lw-euler-dyadic-tail-rounding rate height count
                  (lw-euler-continuation-cutoff rate height error)) request))))
        (:instance lw-complex-difference-triangle
         (left (lw-complex-euler-continuation-value rate height error))
         (middle (lw-complex-euler-dyadic-prefix rate height
                   (lw-euler-continuation-cutoff rate height error) request))
         (right (lw-complex-euler-dyadic-prefix rate height count request))
         (radius (* (lw-euler-dyadic-transport-cost rate height
                     (lw-euler-continuation-cutoff rate height error))
                    (+ (lw-euler-continuation-point-error rate height error) request)))
         (other-radius
          (+ (* (lw-euler-continuation-tail-cap rate height)
                (/ (- (lw-euler-continuation-cutoff rate height error) 1)))
             (* (lw-euler-dyadic-tail-rounding rate height count
                  (lw-euler-continuation-cutoff rate height error)) request))))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub (lw-complex-euler-continuation-value rate height error)
                                (lw-complex-euler-dyadic-prefix rate height count request)))
         (radius
          (+ (* (lw-euler-dyadic-transport-cost rate height
                 (lw-euler-continuation-cutoff rate height error))
                (+ (lw-euler-continuation-point-error rate height error) request))
             (* (lw-euler-continuation-tail-cap rate height)
                (/ (- (lw-euler-continuation-cutoff rate height error) 1)))
             (* (lw-euler-dyadic-tail-rounding rate height count
                 (lw-euler-continuation-cutoff rate height error)) request)))
         (cap (+ (/ error 4)
                 (* (lw-euler-continuation-comparison-cost rate height count error) request)))))
  :in-theory (union-theories
   '(lw-complex-euler-continuation-value lw-euler-continuation-comparison-cost
     lw-euler-continuation-tail-cap natp posp fix
     lw-ecv-left-commutes lw-ecv-left-distributes lw-ecv-fold-constants
     commutativity-of-* associativity-of-* commutativity-of-+
     commutativity-2-of-+ associativity-of-+ distributivity unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(defun lw-euler-continuation-common-cutoff (rate height left-error right-error)
 (max (lw-euler-continuation-cutoff rate height left-error)
      (lw-euler-continuation-cutoff rate height right-error)))

(local (in-theory (disable lw-euler-continuation-common-cutoff)))

(defthm lw-euler-continuation-common-cutoff-data
 (implies (and (rationalp rate) (< 0 rate) (rationalp height)
               (rationalp left-error) (< 0 left-error)
               (rationalp right-error) (< 0 right-error))
  (let ((count (lw-euler-continuation-common-cutoff rate height left-error right-error)))
   (and (natp count) (<= 2 count)
        (<= (lw-euler-continuation-cutoff rate height left-error) count)
        (<= (lw-euler-continuation-cutoff rate height right-error) count))))
 :hints (("Goal"
  :use ((:instance lw-euler-continuation-constructor-data (error left-error))
        (:instance lw-euler-continuation-constructor-data (error right-error)))
  :in-theory (union-theories '(lw-euler-continuation-common-cutoff max natp posp fix)
                             (theory 'minimal-theory))
  :do-not-induct t)))

(defun lw-euler-continuation-common-request (rate height left-error right-error)
 (let* ((count (lw-euler-continuation-common-cutoff rate height left-error right-error))
        (cost (+ (lw-euler-continuation-comparison-cost rate height count left-error)
                 (lw-euler-continuation-comparison-cost rate height count right-error))))
  (lw-euler-rounding-precision cost (/ (+ left-error right-error) 2))))

(local (in-theory (disable lw-euler-continuation-common-request)))

(defthm lw-euler-continuation-common-request-data
 (implies (and (rationalp rate) (< 0 rate) (rationalp height)
               (rationalp left-error) (< 0 left-error)
               (rationalp right-error) (< 0 right-error))
  (let ((count (lw-euler-continuation-common-cutoff rate height left-error right-error))
        (request (lw-euler-continuation-common-request rate height left-error right-error)))
   (and (rationalp request) (< 0 request) (<= request 1)
        (<= (* (+ (lw-euler-continuation-comparison-cost rate height count left-error)
                  (lw-euler-continuation-comparison-cost rate height count right-error)) request)
            (/ (+ left-error right-error) 4)))))
 :hints (("Goal"
  :use (lw-euler-continuation-common-cutoff-data
        (:instance lw-euler-continuation-comparison-cost-valid
         (count (lw-euler-continuation-common-cutoff rate height left-error right-error))
         (error left-error))
        (:instance lw-euler-continuation-comparison-cost-valid
         (count (lw-euler-continuation-common-cutoff rate height left-error right-error))
         (error right-error))
        (:instance lw-euler-rounding-precision-valid
         (cost (+ (lw-euler-continuation-comparison-cost rate height
                   (lw-euler-continuation-common-cutoff rate height left-error right-error) left-error)
                  (lw-euler-continuation-comparison-cost rate height
                   (lw-euler-continuation-common-cutoff rate height left-error right-error) right-error)))
         (error (/ (+ left-error right-error) 2))))
  :in-theory (union-theories
   '(lw-euler-continuation-common-request natp posp fix lw-ecv-left-commutes
     lw-ecv-fold-constants commutativity-of-* associativity-of-*
     commutativity-of-+ associativity-of-+ distributivity unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-complex-euler-continuation-value-cauchy
 (implies (and (rationalp rate) (< 0 rate) (rationalp height)
               (rationalp left-error) (< 0 left-error)
               (rationalp right-error) (< 0 right-error))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-euler-continuation-value rate height left-error)
                   (lw-complex-euler-continuation-value rate height right-error))
   (+ left-error right-error)))
 :hints (("Goal"
  :use (lw-euler-continuation-common-cutoff-data lw-euler-continuation-common-request-data
        (:instance lw-complex-euler-continuation-value-rational (error left-error))
        (:instance lw-complex-euler-continuation-value-rational (error right-error))
        (:instance lw-complex-euler-dyadic-prefix-rational
         (count (lw-euler-continuation-common-cutoff rate height left-error right-error))
         (error (lw-euler-continuation-common-request rate height left-error right-error)))
        (:instance lw-euler-continuation-comparison-cost-valid
         (count (lw-euler-continuation-common-cutoff rate height left-error right-error)) (error left-error))
        (:instance lw-euler-continuation-comparison-cost-valid
         (count (lw-euler-continuation-common-cutoff rate height left-error right-error)) (error right-error))
        (:instance lw-complex-euler-continuation-prefix-comparison
         (count (lw-euler-continuation-common-cutoff rate height left-error right-error))
         (request (lw-euler-continuation-common-request rate height left-error right-error))
         (error left-error))
        (:instance lw-complex-euler-continuation-prefix-comparison
         (count (lw-euler-continuation-common-cutoff rate height left-error right-error))
         (request (lw-euler-continuation-common-request rate height left-error right-error))
         (error right-error))
        (:instance lw-complex-difference-symmetric
         (left (lw-complex-euler-continuation-value rate height right-error))
         (right (lw-complex-euler-dyadic-prefix rate height
                  (lw-euler-continuation-common-cutoff rate height left-error right-error)
                  (lw-euler-continuation-common-request rate height left-error right-error)))
         (radius
          (+ (/ right-error 4)
             (* (lw-euler-continuation-comparison-cost rate height
                 (lw-euler-continuation-common-cutoff rate height left-error right-error) right-error)
                (lw-euler-continuation-common-request rate height left-error right-error)))))
        (:instance lw-complex-difference-triangle
         (left (lw-complex-euler-continuation-value rate height left-error))
         (middle (lw-complex-euler-dyadic-prefix rate height
                   (lw-euler-continuation-common-cutoff rate height left-error right-error)
                   (lw-euler-continuation-common-request rate height left-error right-error)))
         (right (lw-complex-euler-continuation-value rate height right-error))
         (radius
          (+ (/ left-error 4)
             (* (lw-euler-continuation-comparison-cost rate height
                 (lw-euler-continuation-common-cutoff rate height left-error right-error) left-error)
                (lw-euler-continuation-common-request rate height left-error right-error))))
         (other-radius
          (+ (/ right-error 4)
             (* (lw-euler-continuation-comparison-cost rate height
                 (lw-euler-continuation-common-cutoff rate height left-error right-error) right-error)
                (lw-euler-continuation-common-request rate height left-error right-error)))))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub (lw-complex-euler-continuation-value rate height left-error)
                                (lw-complex-euler-continuation-value rate height right-error)))
         (radius
          (+ (/ left-error 4) (/ right-error 4)
             (* (lw-euler-continuation-comparison-cost rate height
                 (lw-euler-continuation-common-cutoff rate height left-error right-error) left-error)
                (lw-euler-continuation-common-request rate height left-error right-error))
             (* (lw-euler-continuation-comparison-cost rate height
                 (lw-euler-continuation-common-cutoff rate height left-error right-error) right-error)
                (lw-euler-continuation-common-request rate height left-error right-error))))
         (cap (+ left-error right-error))))
  :in-theory (union-theories
   '(natp posp fix lw-ecv-left-commutes lw-ecv-left-distributes lw-ecv-fold-constants
     commutativity-of-* associativity-of-* commutativity-of-+ commutativity-2-of-+
     associativity-of-+ distributivity unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))


