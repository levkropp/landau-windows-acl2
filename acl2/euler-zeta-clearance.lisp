(in-package "ACL2")

(include-book "euler-log-derivative")
(include-book "zeta-euler-clearance")

; Generate an actual Euler nonzero check throughout sigma>3.
; The already checked normalized zeta value supplies its lower bound.

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

(local (in-theory (disable lw-complex-euler-continuation-value
 lw-complex-zeta-euler-value lw-zeta-euler-point-error lw-zeta-euler-inverse-cap
 lw-euler-value-clearance-size lw-euler-value-clearance-lower
 lw-euler-value-clearance-check)))

(local (defthm lw-ezc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ezc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ezc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ezc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ezc-times-negative (a b) (b a)))
                 :in-theory (disable lw-ezc-times-negative)))))

(local (defthm lw-ezc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ezc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ezc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ezc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ezc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ezc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ezc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ezc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ezc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ezc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ezc-left-commutes)))))

(defun lw-euler-zeta-clearance-request (rate height)
 (lw-zeta-euler-point-error rate height 1/64))

(local (in-theory (disable lw-euler-zeta-clearance-request)))

(defthm lw-euler-zeta-clearance-request-data
 (implies (and (rationalp rate) (< 3 rate) (rationalp height))
  (and (rationalp (lw-euler-zeta-clearance-request rate height)) (< 0 (lw-euler-zeta-clearance-request rate height)) (<= (lw-euler-zeta-clearance-request rate height) 1/64)
       (equal (* (lw-zeta-euler-inverse-cap rate height) (lw-euler-zeta-clearance-request rate height)) 1/64)))
 :hints (("Goal"
  :use (lw-zeta-euler-inverse-cap-data
        (:instance lw-zeta-euler-point-error-data (error 1/64))
        (:instance lw-ezc-multiply-order (a 1) (b (lw-zeta-euler-inverse-cap rate height)) (factor (lw-euler-zeta-clearance-request rate height))))
  :in-theory (union-theories
 '(lw-euler-zeta-clearance-request lw-ezc-left-commutes lw-ezc-left-distributes lw-ezc-fold-constants lw-ezc-times-negative lw-ezc-negative-times lw-ezc-zero-times lw-ezc-minus-one lw-ezc-double-negative lw-ezc-add-cancel lw-ezc-double lw-ezc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(local (defthm lw-ezc-disk-radius-lower
 (implies (and (lw-complex-diskp point radius)
               (<= 1/16 (lw-complex-norm-square point)))
  (<= 1/4 radius))
 :hints (("Goal"
  :use (lw-complex-disk-data)
  :in-theory (union-theories
 '(lw-complex-diskp lw-diskp lw-complex-norm-square lw-ezc-left-commutes lw-ezc-left-distributes lw-ezc-fold-constants lw-ezc-times-negative lw-ezc-negative-times lw-ezc-zero-times lw-ezc-minus-one lw-ezc-double-negative lw-ezc-add-cancel lw-ezc-double lw-ezc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :nonlinearp t :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-ezc-check-scalar
 (implies (and (rationalp cap) (<= 1 cap)
               (rationalp request) (< 0 request)
               (equal (* cap request) 1/64)
               (rationalp size) (<= 0 size) (<= 1/4 (* cap size)))
  (and (< 0 size) (<= request (* 1/16 size))))
 :hints (("Goal" :in-theory (union-theories
 '( lw-ezc-left-commutes lw-ezc-left-distributes lw-ezc-fold-constants lw-ezc-times-negative lw-ezc-negative-times lw-ezc-zero-times lw-ezc-minus-one lw-ezc-double-negative lw-ezc-add-cancel lw-ezc-double lw-ezc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :nonlinearp t))
 :rule-classes nil))

(defthm lw-euler-zeta-clearance-check
 (implies (and (rationalp rate) (< 3 rate) (rationalp height))
  (lw-euler-value-clearance-check rate height (lw-euler-zeta-clearance-request rate height)))
 :hints (("Goal"
  :use (lw-euler-zeta-clearance-request-data lw-zeta-euler-inverse-cap-data
        (:instance lw-complex-euler-continuation-value-rational (error (lw-euler-zeta-clearance-request rate height)))
        (:instance lw-complex-l1-bound (point (lw-complex-euler-continuation-value rate height (lw-euler-zeta-clearance-request rate height))))
        (:instance lw-complex-zeta-euler-clearance (error 1/64))
        (:instance lw-complex-mul-disk
         (left (lw-complex-reciprocal (cons (- rate 1) height))) (right (lw-complex-euler-continuation-value rate height (lw-euler-zeta-clearance-request rate height)))
         (radius (lw-zeta-euler-inverse-cap rate height)) (other-radius (lw-euler-value-clearance-size rate height (lw-euler-zeta-clearance-request rate height))))
        (:instance lw-ezc-disk-radius-lower (point (lw-complex-zeta-euler-value rate height 1/64)) (radius (* (lw-zeta-euler-inverse-cap rate height) (lw-euler-value-clearance-size rate height (lw-euler-zeta-clearance-request rate height)))))
        (:instance lw-ezc-check-scalar (cap (lw-zeta-euler-inverse-cap rate height)) (request (lw-euler-zeta-clearance-request rate height)) (size (lw-euler-value-clearance-size rate height (lw-euler-zeta-clearance-request rate height)))))
  :in-theory (union-theories
 '(lw-euler-value-clearance-check lw-euler-value-clearance-size lw-complex-zeta-euler-value lw-euler-zeta-clearance-request lw-ezc-left-commutes lw-ezc-left-distributes lw-ezc-fold-constants lw-ezc-times-negative lw-ezc-negative-times lw-ezc-zero-times lw-ezc-minus-one lw-ezc-double-negative lw-ezc-add-cancel lw-ezc-double lw-ezc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

