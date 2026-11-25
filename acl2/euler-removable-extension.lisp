; The actual normalized Euler family, including its computed value at one.
(in-package "ACL2")
(include-book "euler-removable-agreement")
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

(local (in-theory (disable lw-euler-uniform-polynomial
 lw-complex-euler-continuation-value lw-polynomial-affine
 lw-polynomial-multiply-linear lw-polynomial-add-constant)))
(local (in-theory (disable lw-euler-removable-radius lw-euler-removable-value
 lw-euler-removable-model-value lw-mellin-euler-log-value lw-euler-value-clearance-check
 lw-euler-zeta-clearance-request lw-mellin-integral)))
(local (defthm lw-ere-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ere-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ere-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ere-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ere-times-negative (a b) (b a)))
                 :in-theory (disable lw-ere-times-negative)))))

(local (defthm lw-ere-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ere-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ere-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ere-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ere-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ere-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ere-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ere-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ere-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ere-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ere-left-commutes)))))

(defun lw-mellin-euler-log-extended-value (rate height radius anchor-error error)
 (if (and (equal rate 1) (equal height 0))
  (lw-euler-removable-value (cons 0 0) error)
  (lw-mellin-euler-log-value rate height radius anchor-error error)))

(local (in-theory (disable lw-mellin-euler-log-extended-value)))

(defthm lw-mellin-euler-log-extended-away
 (implies (not (and (equal rate 1) (equal height 0)))
 (equal (lw-mellin-euler-log-extended-value rate height radius anchor-error error) (lw-mellin-euler-log-value rate height radius anchor-error error)))
 :hints (("Goal" :in-theory (union-theories
 '(lw-mellin-euler-log-extended-value lw-ere-left-commutes lw-ere-left-distributes lw-ere-fold-constants lw-ere-times-negative lw-ere-negative-times lw-ere-zero-times lw-ere-minus-one lw-ere-double-negative lw-ere-add-cancel lw-ere-double lw-ere-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-mellin-euler-log-extended-at-one
 (equal (lw-mellin-euler-log-extended-value 1 0 radius anchor-error error)
        (lw-euler-removable-value (cons 0 0) error))
 :hints (("Goal" :in-theory (union-theories
 '(lw-mellin-euler-log-extended-value lw-ere-left-commutes lw-ere-left-distributes lw-ere-fold-constants lw-ere-times-negative lw-ere-negative-times lw-ere-zero-times lw-ere-minus-one lw-ere-double-negative lw-ere-add-cancel lw-ere-double lw-ere-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-mellin-euler-log-extended-value-rational
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp radius) (< 0 radius) (< radius rate) (rationalp error) (< 0 error))
 (lw-complexp (lw-mellin-euler-log-extended-value rate height radius anchor-error error)))
 :hints (("Goal"
 :cases ((and (equal rate 1) (equal height 0)))
 :use (lw-euler-value-clearance-data
       (:instance lw-euler-removable-value-rational (point (cons 0 0)))
       lw-mellin-euler-log-value-rational)
 :in-theory (union-theories
 '(lw-mellin-euler-log-extended-value (:executable-counterpart lw-complexp) lw-ere-left-commutes lw-ere-left-distributes lw-ere-fold-constants lw-ere-times-negative lw-ere-negative-times lw-ere-zero-times lw-ere-minus-one lw-ere-double-negative lw-ere-add-cancel lw-ere-double lw-ere-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-mellin-euler-log-extended-value-cauchy
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp radius) (< 0 radius) (< radius rate)
  (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
 (lw-complex-diskp
  (lw-complex-sub (lw-mellin-euler-log-extended-value rate height radius anchor-error left-error)
                  (lw-mellin-euler-log-extended-value rate height radius anchor-error right-error))
  (* 1/2 (+ left-error right-error))))
 :hints (("Goal"
 :cases ((and (equal rate 1) (equal height 0)))
 :use (lw-euler-value-clearance-data lw-euler-removable-neighborhood-data
       (:instance lw-complex-zero-disk (radius (* 1/2 (lw-euler-removable-radius))))
       (:instance lw-complex-euler-removable-value-cauchy (point (cons 0 0)))
       lw-mellin-euler-log-value-cauchy)
 :in-theory (union-theories
 '(lw-mellin-euler-log-extended-value lw-ere-left-commutes lw-ere-left-distributes lw-ere-fold-constants lw-ere-times-negative lw-ere-negative-times lw-ere-zero-times lw-ere-minus-one lw-ere-double-negative lw-ere-add-cancel lw-ere-double lw-ere-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-mellin-euler-log-extended-certificate-independence
 (implies (and (lw-euler-value-clearance-check rate height left-anchor)
  (lw-euler-value-clearance-check rate height right-anchor)
  (rationalp radius) (< 0 radius) (< radius rate)
  (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
 (lw-complex-diskp
  (lw-complex-sub (lw-mellin-euler-log-extended-value rate height radius left-anchor left-error)
                  (lw-mellin-euler-log-extended-value rate height radius right-anchor right-error))
  (* 1/2 (+ left-error right-error))))
 :hints (("Goal"
 :cases ((and (equal rate 1) (equal height 0)))
 :use ((:instance lw-euler-value-clearance-data (anchor-error left-anchor))
       lw-euler-removable-neighborhood-data
       (:instance lw-complex-zero-disk (radius (* 1/2 (lw-euler-removable-radius))))
       (:instance lw-complex-euler-removable-value-cauchy (point (cons 0 0)))
       lw-mellin-euler-log-certificate-independence)
 :in-theory (union-theories
 '(lw-mellin-euler-log-extended-value lw-ere-left-commutes lw-ere-left-distributes lw-ere-fold-constants lw-ere-times-negative lw-ere-negative-times lw-ere-zero-times lw-ere-minus-one lw-ere-double-negative lw-ere-add-cancel lw-ere-double lw-ere-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-complex-euler-removable-extended-model-comparison
 (implies (and (lw-complex-diskp point (* 1/2 (lw-euler-removable-radius))) (lw-euler-value-clearance-check (+ 1 (car point)) (cdr point) local-anchor)
 (rationalp coefficient-radius) (< 0 coefficient-radius) (< coefficient-radius (+ 1 (car point)))
 (natp target) (rationalp error) (< 0 error) (rationalp value-error) (< 0 value-error))
 (lw-complex-diskp
  (lw-complex-sub (lw-euler-removable-model-value point target error)
   (lw-mellin-euler-log-extended-value (+ 1 (car point)) (cdr point) coefficient-radius local-anchor value-error))
  (* 1/2 (+ error value-error))))
 :hints (("Goal"
 :cases ((equal point (cons 0 0)))
 :use (lw-euler-removable-denominator-clearance lw-euler-removable-neighborhood-data
       lw-euler-removable-point-data
       (:instance lw-complex-zero-disk (radius (* 1/2 (lw-euler-removable-radius))))
       (:instance lw-complex-euler-removable-model-value-cauchy
        (left-target target) (right-target 0) (left-error error) (right-error value-error))
       lw-complex-euler-removable-model-agreement)
 :in-theory (union-theories
 '(lw-mellin-euler-log-extended-value lw-euler-removable-value (:executable-counterpart lw-complexp) lw-ere-left-commutes lw-ere-left-distributes lw-ere-fold-constants lw-ere-times-negative lw-ere-negative-times lw-ere-zero-times lw-ere-minus-one lw-ere-double-negative lw-ere-add-cancel lw-ere-double lw-ere-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-mellin-euler-log-extended-right-comparison
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
  (rationalp radius) (< 0 radius) (< radius rate)
  (rationalp integral-error) (< 0 integral-error) (rationalp euler-error) (< 0 euler-error))
 (lw-complex-diskp
  (lw-complex-sub (lw-mellin-integral rate height 0 integral-error)
   (lw-mellin-euler-log-extended-value rate height radius
    (lw-euler-zeta-clearance-request rate height) euler-error))
  (+ (* 5 integral-error) (* 1/2 euler-error))))
 :hints (("Goal"
 :use (lw-mellin-euler-log-right-comparison)
 :in-theory (union-theories
 '(lw-mellin-euler-log-extended-value lw-ere-left-commutes lw-ere-left-distributes lw-ere-fold-constants lw-ere-times-negative lw-ere-negative-times lw-ere-zero-times lw-ere-minus-one lw-ere-double-negative lw-ere-add-cancel lw-ere-double lw-ere-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

