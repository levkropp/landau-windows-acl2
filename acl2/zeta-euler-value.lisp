(in-package "ACL2")

(include-book "euler-zeta-agreement")

; A zeta Cauchy evaluator on the positive half-plane away from s=1.
; The reciprocal is exact rational arithmetic; its amplification is
; absorbed into the point request before calling the Euler evaluator.

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

(local (in-theory (disable lw-complex-euler-dirichlet-prefix
 lw-complex-euler-dirichlet-prefix-step lw-complex-euler-dirichlet-prefix-telescope
 lw-complex-euler-dyadic-prefix lw-complex-euler-continuation-value
 lw-complex-zeta-pole-removed-series-value lw-complex-zeta-series-value
 lw-euler-rounding-precision lw-complex-reciprocal-cancel-product
 lw-complex-euler-cell-segment-telescope lw-complex-euler-cell-segment-difference
 lw-complex-euler-dyadic-tail-telescope lw-complex-euler-dyadic-tail-difference)))

(local (defthm lw-zec-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-zec-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-zec-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-zec-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-zec-times-negative (a b) (b a)))
                 :in-theory (disable lw-zec-times-negative)))))

(local (defthm lw-zec-zero-times (equal (* 0 a) 0)))

(local (defthm lw-zec-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-zec-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-zec-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-zec-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-zec-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-zec-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-zec-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-zec-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-zec-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-zec-left-commutes)))))

(local (defthm lw-zec-size-data
 (implies (and (rationalp rate) (<= 0 rate) (rationalp height))
  (and (rationalp (abs height)) (<= 0 (abs height))
       (rationalp (+ rate (abs height))) (<= 0 (+ rate (abs height)))))
 :rule-classes nil))

(defun lw-zeta-euler-inverse-cap (rate height)
 (+ 1 (lw-complex-l1 (lw-complex-reciprocal (cons (- rate 1) height)))))

(local (in-theory (disable lw-zeta-euler-inverse-cap)))

(defthm lw-zeta-euler-inverse-cap-data
 (implies (and (rationalp rate) (rationalp height))
  (and (rationalp (lw-zeta-euler-inverse-cap rate height))
       (<= 1 (lw-zeta-euler-inverse-cap rate height))
       (lw-complexp (lw-complex-reciprocal (cons (- rate 1) height)))
       (lw-complex-diskp (lw-complex-reciprocal (cons (- rate 1) height))
                         (lw-zeta-euler-inverse-cap rate height))))
 :hints (("Goal"
  :use ((:instance lw-complex-reciprocal-rational (point (cons (- rate 1) height)))
        (:instance lw-complex-l1-bound (point (lw-complex-reciprocal (cons (- rate 1) height))))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-reciprocal (cons (- rate 1) height)))
         (radius (lw-complex-l1 (lw-complex-reciprocal (cons (- rate 1) height))))
         (cap (lw-zeta-euler-inverse-cap rate height))))
  :in-theory (union-theories
   '(lw-zeta-euler-inverse-cap lw-complexp lw-zec-left-commutes lw-zec-left-distributes lw-zec-fold-constants lw-zec-times-negative lw-zec-negative-times lw-zec-zero-times lw-zec-minus-one lw-zec-double-negative lw-zec-add-cancel lw-zec-double lw-zec-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t)))

(defun lw-zeta-euler-point-error (rate height error)
 (* error (/ (lw-zeta-euler-inverse-cap rate height))))

(local (in-theory (disable lw-zeta-euler-point-error)))

(defthm lw-zeta-euler-point-error-data
 (implies (and (rationalp rate) (rationalp height) (rationalp error) (< 0 error))
  (and (rationalp (lw-zeta-euler-point-error rate height error))
       (< 0 (lw-zeta-euler-point-error rate height error))
       (equal (* (lw-zeta-euler-inverse-cap rate height)
                 (lw-zeta-euler-point-error rate height error)) error)))
 :hints (("Goal"
  :use (lw-zeta-euler-inverse-cap-data
        (:instance lw-reciprocal-positive (value (lw-zeta-euler-inverse-cap rate height)))
        (:instance lw-zec-positive-product (a error) (b (/ (lw-zeta-euler-inverse-cap rate height))))
        (:instance lw-zec-inverse-factor (divisor (lw-zeta-euler-inverse-cap rate height)) (coefficient error)))
  :in-theory (union-theories
   '(lw-zeta-euler-point-error lw-zec-left-commutes lw-zec-left-distributes lw-zec-fold-constants lw-zec-times-negative lw-zec-negative-times lw-zec-zero-times lw-zec-minus-one lw-zec-double-negative lw-zec-add-cancel lw-zec-double lw-zec-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(defun lw-complex-zeta-euler-value (rate height error)
 (lw-complex-mul (lw-complex-reciprocal (cons (- rate 1) height))
  (lw-complex-euler-continuation-value rate height (lw-zeta-euler-point-error rate height error))))

(local (in-theory (disable lw-complex-zeta-euler-value)))

(defthm lw-complex-zeta-euler-value-rational
 (implies (and (rationalp rate) (< 0 rate) (rationalp height)
               (not (and (equal rate 1) (equal height 0)))
               (rationalp error) (< 0 error))
  (lw-complexp (lw-complex-zeta-euler-value rate height error)))
 :hints (("Goal"
  :use (lw-zeta-euler-point-error-data lw-zeta-euler-inverse-cap-data
        (:instance lw-complex-euler-continuation-value-rational
         (error (lw-zeta-euler-point-error rate height error)))
        (:instance lw-complex-operations-rational
         (left (lw-complex-reciprocal (cons (- rate 1) height)))
         (right (lw-complex-euler-continuation-value rate height (lw-zeta-euler-point-error rate height error)))
         (factor 1)))
  :in-theory (union-theories
   '(lw-complex-zeta-euler-value lw-zec-left-commutes lw-zec-left-distributes lw-zec-fold-constants lw-zec-times-negative lw-zec-negative-times lw-zec-zero-times lw-zec-minus-one lw-zec-double-negative lw-zec-add-cancel lw-zec-double lw-zec-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t)))

(local (defthm lw-zec-mul-difference
 (implies (and (lw-complexp point) (lw-complexp left) (lw-complexp right))
  (equal (lw-complex-sub (lw-complex-mul point left) (lw-complex-mul point right))
         (lw-complex-mul point (lw-complex-sub left right))))
 :hints (("Goal" :in-theory (enable lw-complexp lw-complex-sub lw-complex-mul)
                 :do-not-induct t)) :rule-classes nil))

(defthm lw-complex-zeta-euler-value-cauchy
 (implies (and (rationalp rate) (< 0 rate) (rationalp height)
               (not (and (equal rate 1) (equal height 0)))
               (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-zeta-euler-value rate height left-error)
                   (lw-complex-zeta-euler-value rate height right-error))
   (+ left-error right-error)))
 :hints (("Goal"
  :use (lw-zeta-euler-inverse-cap-data
        (:instance lw-zeta-euler-point-error-data (error left-error))
        (:instance lw-zeta-euler-point-error-data (error right-error))
        (:instance lw-complex-euler-continuation-value-rational
         (error (lw-zeta-euler-point-error rate height left-error)))
        (:instance lw-complex-euler-continuation-value-rational
         (error (lw-zeta-euler-point-error rate height right-error)))
        (:instance lw-complex-euler-continuation-value-cauchy
         (left-error (lw-zeta-euler-point-error rate height left-error))
         (right-error (lw-zeta-euler-point-error rate height right-error)))
        (:instance lw-zec-mul-difference
         (point (lw-complex-reciprocal (cons (- rate 1) height)))
         (left (lw-complex-euler-continuation-value rate height (lw-zeta-euler-point-error rate height left-error)))
         (right (lw-complex-euler-continuation-value rate height (lw-zeta-euler-point-error rate height right-error))))
        (:instance lw-complex-mul-disk
         (left (lw-complex-reciprocal (cons (- rate 1) height)))
         (right (lw-complex-sub
          (lw-complex-euler-continuation-value rate height (lw-zeta-euler-point-error rate height left-error))
          (lw-complex-euler-continuation-value rate height (lw-zeta-euler-point-error rate height right-error))))
         (radius (lw-zeta-euler-inverse-cap rate height))
         (other-radius (+ (lw-zeta-euler-point-error rate height left-error)
                          (lw-zeta-euler-point-error rate height right-error))))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub (lw-complex-zeta-euler-value rate height left-error)
                                (lw-complex-zeta-euler-value rate height right-error)))
         (radius (* (lw-zeta-euler-inverse-cap rate height)
                    (+ (lw-zeta-euler-point-error rate height left-error)
                       (lw-zeta-euler-point-error rate height right-error))))
         (cap (+ left-error right-error))))
  :in-theory (union-theories
   '(lw-complex-zeta-euler-value lw-zec-left-commutes lw-zec-left-distributes lw-zec-fold-constants lw-zec-times-negative lw-zec-negative-times lw-zec-zero-times lw-zec-minus-one lw-zec-double-negative lw-zec-add-cancel lw-zec-double lw-zec-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(local (defthm lw-zec-shifted-nonzero
 (implies (and (rationalp rate) (< 3 rate))
  (not (equal (cons (- rate 1) height) (cons 0 0))))))

(defthm lw-complex-zeta-euler-series-agreement
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (rationalp euler-error) (< 0 euler-error)
               (rationalp series-error) (< 0 series-error))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-zeta-euler-value rate height euler-error)
                   (lw-complex-zeta-series-value nil rate height series-error))
   (+ (* 1/4 euler-error)
      (* 3/8 (lw-zeta-euler-inverse-cap rate height) (+ rate (abs height) 1) series-error))))
 :hints (("Goal"
  :use (lw-zec-size-data lw-zec-shifted-nonzero lw-zeta-euler-inverse-cap-data
        (:instance lw-zeta-euler-point-error-data (error euler-error))
        (:instance lw-complex-euler-continuation-value-rational
         (error (lw-zeta-euler-point-error rate height euler-error)))
        (:instance lw-complex-zeta-series-value-rational (logp nil) (error series-error))
        (:instance lw-complex-zeta-pole-removed-series-rational (error series-error))
        (:instance lw-complex-euler-zeta-series-agreement
         (euler-error (lw-zeta-euler-point-error rate height euler-error)))
        (:instance lw-complex-reciprocal-cancel-product
         (a (cons (- rate 1) height)) (b (lw-complex-zeta-series-value nil rate height series-error)))
        (:instance lw-zec-mul-difference
         (point (lw-complex-reciprocal (cons (- rate 1) height)))
         (left (lw-complex-euler-continuation-value rate height (lw-zeta-euler-point-error rate height euler-error)))
         (right (lw-complex-zeta-pole-removed-series-value rate height series-error)))
        (:instance lw-complex-mul-disk
         (left (lw-complex-reciprocal (cons (- rate 1) height)))
         (right (lw-complex-sub
          (lw-complex-euler-continuation-value rate height (lw-zeta-euler-point-error rate height euler-error))
          (lw-complex-zeta-pole-removed-series-value rate height series-error)))
         (radius (lw-zeta-euler-inverse-cap rate height))
         (other-radius (+ (* 1/4 (lw-zeta-euler-point-error rate height euler-error))
                          (* 3/8 (+ rate (abs height) 1) series-error))))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub (lw-complex-zeta-euler-value rate height euler-error)
                                (lw-complex-zeta-series-value nil rate height series-error)))
         (radius (* (lw-zeta-euler-inverse-cap rate height)
                    (+ (* 1/4 (lw-zeta-euler-point-error rate height euler-error))
                       (* 3/8 (+ rate (abs height) 1) series-error))))
         (cap (+ (* 1/4 euler-error)
                 (* 3/8 (lw-zeta-euler-inverse-cap rate height) (+ rate (abs height) 1) series-error)))))
  :in-theory (union-theories
   '(lw-complex-zeta-euler-value lw-complex-zeta-pole-removed-series-value lw-complexp lw-zec-left-commutes lw-zec-left-distributes lw-zec-fold-constants lw-zec-times-negative lw-zec-negative-times lw-zec-zero-times lw-zec-minus-one lw-zec-double-negative lw-zec-add-cancel lw-zec-double lw-zec-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(defun lw-zeta-euler-series-precision (rate height error)
 (lw-euler-rounding-precision
  (+ 1/4 (* 3/8 (lw-zeta-euler-inverse-cap rate height) (+ rate (abs height) 1))) error))

(local (in-theory (disable lw-zeta-euler-series-precision)))

(defthm lw-zeta-euler-series-precision-valid
 (implies (and (rationalp rate) (< 3 rate) (rationalp height) (rationalp error) (< 0 error))
  (let ((request (lw-zeta-euler-series-precision rate height error)))
   (and (rationalp request) (< 0 request) (<= request 1)
        (<= (+ (* 1/4 request)
               (* 3/8 (lw-zeta-euler-inverse-cap rate height) (+ rate (abs height) 1) request)) error))))
 :hints (("Goal"
  :use (lw-zec-size-data lw-zeta-euler-inverse-cap-data
        (:instance lw-euler-rounding-precision-valid
         (cost (+ 1/4 (* 3/8 (lw-zeta-euler-inverse-cap rate height) (+ rate (abs height) 1))))))
  :in-theory (union-theories
   '(lw-zeta-euler-series-precision lw-zec-left-commutes lw-zec-left-distributes lw-zec-fold-constants lw-zec-times-negative lw-zec-negative-times lw-zec-zero-times lw-zec-minus-one lw-zec-double-negative lw-zec-add-cancel lw-zec-double lw-zec-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp t :do-not-induct t)))

(defthm lw-complex-zeta-euler-computed-series-agreement
 (implies (and (rationalp rate) (< 3 rate) (rationalp height) (rationalp error) (< 0 error))
  (let ((request (lw-zeta-euler-series-precision rate height error)))
   (lw-complex-diskp
    (lw-complex-sub (lw-complex-zeta-euler-value rate height request)
                    (lw-complex-zeta-series-value nil rate height request))
    error)))
 :hints (("Goal"
  :use (lw-zeta-euler-series-precision-valid
        (:instance lw-complex-zeta-euler-series-agreement
         (euler-error (lw-zeta-euler-series-precision rate height error))
         (series-error (lw-zeta-euler-series-precision rate height error)))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub
          (lw-complex-zeta-euler-value rate height (lw-zeta-euler-series-precision rate height error))
          (lw-complex-zeta-series-value nil rate height (lw-zeta-euler-series-precision rate height error))))
         (radius (+ (* 1/4 (lw-zeta-euler-series-precision rate height error))
                    (* 3/8 (lw-zeta-euler-inverse-cap rate height) (+ rate (abs height) 1)
                       (lw-zeta-euler-series-precision rate height error))))
         (cap error)))
  :in-theory (union-theories
   '( lw-zec-left-commutes lw-zec-left-distributes lw-zec-fold-constants lw-zec-times-negative lw-zec-negative-times lw-zec-zero-times lw-zec-minus-one lw-zec-double-negative lw-zec-add-cancel lw-zec-double lw-zec-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

