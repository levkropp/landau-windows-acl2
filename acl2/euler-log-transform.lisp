(in-package "ACL2")

(include-book "euler-zeta-log-derivative")
(include-book "dirichlet-transform")

; Normalize the actual Euler logarithmic derivative on the positive
; half-plane away from one, retaining explicit local amplification.

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

(local (in-theory (disable lw-dirichlet-transform lw-complex-quotient
 lw-zeta-euler-inverse-cap lw-complex-euler-log-derivative-value)))

(local (defthm lw-elt-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-elt-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-elt-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-elt-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-elt-times-negative (a b) (b a)))
                 :in-theory (disable lw-elt-times-negative)))))

(local (defthm lw-elt-zero-times (equal (* 0 a) 0)))

(local (defthm lw-elt-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-elt-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-elt-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-elt-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-elt-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-elt-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-elt-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-elt-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-elt-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-elt-left-commutes)))))

(local (defthm lw-elt-pair-equality
 (implies (equal left right)
  (and (equal (car left) (car right)) (equal (cdr left) (cdr right))))
 :rule-classes nil))

(local (defthm lw-elt-points
 (implies (and (rationalp rate) (< 0 rate) (rationalp height)
               (not (and (equal rate 1) (equal height 0))))
  (and (lw-complexp (cons (- rate 1) height)) (lw-complexp (cons rate height))
       (not (equal (cons (- rate 1) height) (cons 0 0))) (not (equal (cons rate height) (cons 0 0)))))
 :hints (("Goal"
  :use ((:instance lw-elt-pair-equality (left (cons (- rate 1) height)) (right (cons 0 0)))
        (:instance lw-elt-pair-equality (left (cons rate height)) (right (cons 0 0))))
  :in-theory (union-theories
 '(lw-complexp lw-elt-left-commutes lw-elt-left-distributes lw-elt-fold-constants lw-elt-times-negative lw-elt-negative-times lw-elt-zero-times lw-elt-minus-one lw-elt-double-negative lw-elt-add-cancel lw-elt-double lw-elt-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(defun lw-euler-log-transform-cost (rate height)
 (+ (* (lw-zeta-euler-inverse-cap (+ rate 1) height) (lw-zeta-euler-inverse-cap rate height)) (lw-zeta-euler-inverse-cap rate height)))

(local (in-theory (disable lw-euler-log-transform-cost)))

(defthm lw-euler-log-transform-cost-data
 (implies (and (rationalp rate) (< 0 rate) (rationalp height)
               (not (and (equal rate 1) (equal height 0))))
  (and (rationalp (lw-euler-log-transform-cost rate height)) (<= 2 (lw-euler-log-transform-cost rate height))
       (rationalp (lw-zeta-euler-inverse-cap (+ rate 1) height)) (<= 1 (lw-zeta-euler-inverse-cap (+ rate 1) height)) (rationalp (lw-zeta-euler-inverse-cap rate height)) (<= 1 (lw-zeta-euler-inverse-cap rate height))
       (lw-complexp (lw-complex-reciprocal (cons (- rate 1) height))) (lw-complexp (lw-complex-reciprocal (cons rate height))) (lw-complexp (lw-complex-reciprocal (lw-complex-mul (cons (- rate 1) height) (cons rate height))))
       (lw-complex-diskp (lw-complex-reciprocal (cons (- rate 1) height)) (lw-zeta-euler-inverse-cap rate height))
       (lw-complex-diskp (lw-complex-reciprocal (lw-complex-mul (cons (- rate 1) height) (cons rate height))) (* (lw-zeta-euler-inverse-cap (+ rate 1) height) (lw-zeta-euler-inverse-cap rate height)))))
 :hints (("Goal"
  :use (lw-elt-points lw-zeta-euler-inverse-cap-data
        (:instance lw-zeta-euler-inverse-cap-data (rate (+ rate 1)))
        (:instance lw-elt-multiply-order (a 1) (b (lw-zeta-euler-inverse-cap (+ rate 1) height)) (factor (lw-zeta-euler-inverse-cap rate height)))
        (:instance lw-complex-reciprocal-product (a (cons (- rate 1) height)) (b (cons rate height)))
        (:instance lw-complex-operations-rational (left (lw-complex-reciprocal (cons (- rate 1) height))) (right (lw-complex-reciprocal (cons rate height))) (factor 1))
        (:instance lw-complex-mul-disk (left (lw-complex-reciprocal (cons (- rate 1) height))) (right (lw-complex-reciprocal (cons rate height))) (radius (lw-zeta-euler-inverse-cap rate height)) (other-radius (lw-zeta-euler-inverse-cap (+ rate 1) height))))
  :in-theory (union-theories
 '(lw-euler-log-transform-cost lw-elt-left-commutes lw-elt-left-distributes lw-elt-fold-constants lw-elt-times-negative lw-elt-negative-times lw-elt-zero-times lw-elt-minus-one lw-elt-double-negative lw-elt-add-cancel lw-elt-double lw-elt-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(local (defthm lw-elt-transform-difference
 (implies (and (lw-complexp left) (lw-complexp right)
               (rationalp left-gamma) (rationalp right-gamma)
               (rationalp rate) (< 0 rate) (rationalp height)
               (not (and (equal rate 1) (equal height 0))))
  (equal
   (lw-complex-sub (lw-dirichlet-transform rate height left left-gamma)
                   (lw-dirichlet-transform rate height right right-gamma))
   (lw-complex-add (lw-complex-mul (lw-complex-sub left right) (lw-complex-reciprocal (lw-complex-mul (cons (- rate 1) height) (cons rate height))))
                   (lw-complex-scale (- left-gamma right-gamma) (lw-complex-reciprocal (cons (- rate 1) height))))))
 :hints (("Goal"
  :use (lw-euler-log-transform-cost-data)
  :in-theory (union-theories
 '(lw-dirichlet-transform lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale lw-elt-left-commutes lw-elt-left-distributes lw-elt-fold-constants lw-elt-times-negative lw-elt-negative-times lw-elt-zero-times lw-elt-minus-one lw-elt-double-negative lw-elt-add-cancel lw-elt-double lw-elt-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-elt-positive-transport
 (implies (and (rationalp rate) (< 0 rate) (rationalp height)
               (not (and (equal rate 1) (equal height 0)))
               (lw-complexp left) (lw-complexp right)
               (rationalp left-gamma) (rationalp right-gamma)
               (lw-complex-diskp (lw-complex-sub left right) log-error)
               (rationalp gamma-error) (<= 0 gamma-error)
               (<= (abs (- left-gamma right-gamma)) gamma-error))
  (lw-complex-diskp
   (lw-complex-sub (lw-dirichlet-transform rate height left left-gamma)
                   (lw-dirichlet-transform rate height right right-gamma))
   (+ (* (lw-zeta-euler-inverse-cap (+ rate 1) height) (lw-zeta-euler-inverse-cap rate height) log-error) (* (lw-zeta-euler-inverse-cap rate height) gamma-error))))
 :hints (("Goal"
  :use (lw-euler-log-transform-cost-data lw-elt-transform-difference
        (:instance lw-complex-disk-data (point (lw-complex-sub left right)) (radius log-error))
        (:instance lw-complex-mul-disk
         (left (lw-complex-sub left right)) (right (lw-complex-reciprocal (lw-complex-mul (cons (- rate 1) height) (cons rate height)))) (radius log-error) (other-radius (* (lw-zeta-euler-inverse-cap (+ rate 1) height) (lw-zeta-euler-inverse-cap rate height))))
        (:instance lw-complex-scale-disk (point (lw-complex-reciprocal (cons (- rate 1) height))) (factor (- left-gamma right-gamma)) (radius (lw-zeta-euler-inverse-cap rate height)))
        (:instance lw-elt-multiply-order
         (a (abs (- left-gamma right-gamma))) (b gamma-error) (factor (lw-zeta-euler-inverse-cap rate height)))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-scale (- left-gamma right-gamma) (lw-complex-reciprocal (cons (- rate 1) height))))
         (radius (* (abs (- left-gamma right-gamma)) (lw-zeta-euler-inverse-cap rate height))) (cap (* (lw-zeta-euler-inverse-cap rate height) gamma-error)))
        (:instance lw-complex-add-disk
         (left (lw-complex-mul (lw-complex-sub left right) (lw-complex-reciprocal (lw-complex-mul (cons (- rate 1) height) (cons rate height)))))
         (right (lw-complex-scale (- left-gamma right-gamma) (lw-complex-reciprocal (cons (- rate 1) height))))
         (radius (* (lw-zeta-euler-inverse-cap (+ rate 1) height) (lw-zeta-euler-inverse-cap rate height) log-error)) (other-radius (* (lw-zeta-euler-inverse-cap rate height) gamma-error))))
  :in-theory (union-theories
 '(abs lw-elt-left-commutes lw-elt-left-distributes lw-elt-fold-constants lw-elt-times-negative lw-elt-negative-times lw-elt-zero-times lw-elt-minus-one lw-elt-double-negative lw-elt-add-cancel lw-elt-double lw-elt-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))
 :rule-classes nil))

(defun lw-euler-log-transform (rate height log-value gamma-value)
 (lw-dirichlet-transform rate height (lw-complex-sub (lw-complex-reciprocal (cons (- rate 1) height)) log-value) gamma-value))

(local (in-theory (disable lw-euler-log-transform)))

(defthm lw-euler-log-transform-rational
 (implies (and (rationalp rate) (< 0 rate) (rationalp height)
               (not (and (equal rate 1) (equal height 0)))
               (lw-complexp log-value) (rationalp gamma-value))
  (lw-complexp (lw-euler-log-transform rate height log-value gamma-value)))
 :hints (("Goal"
  :use (lw-euler-log-transform-cost-data)
  :in-theory (union-theories
 '(lw-euler-log-transform lw-dirichlet-transform lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale lw-elt-left-commutes lw-elt-left-distributes lw-elt-fold-constants lw-elt-times-negative lw-elt-negative-times lw-elt-zero-times lw-elt-minus-one lw-elt-double-negative lw-elt-add-cancel lw-elt-double lw-elt-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(local (defthm lw-elt-complement-difference
 (implies (and (lw-complexp point) (lw-complexp left) (lw-complexp right))
  (equal (lw-complex-sub (lw-complex-sub point left) (lw-complex-sub point right))
         (lw-complex-scale -1 (lw-complex-sub left right))))
 :hints (("Goal"
  :in-theory (union-theories
 '(lw-complexp lw-complex-sub lw-complex-scale lw-elt-left-commutes lw-elt-left-distributes lw-elt-fold-constants lw-elt-times-negative lw-elt-negative-times lw-elt-zero-times lw-elt-minus-one lw-elt-double-negative lw-elt-add-cancel lw-elt-double lw-elt-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(defthm lw-euler-log-transform-transport
 (implies (and (rationalp rate) (< 0 rate) (rationalp height)
               (not (and (equal rate 1) (equal height 0)))
               (lw-complexp left) (lw-complexp right)
               (rationalp left-gamma) (rationalp right-gamma)
               (lw-complex-diskp (lw-complex-sub left right) log-error)
               (rationalp gamma-error) (<= 0 gamma-error)
               (<= (abs (- left-gamma right-gamma)) gamma-error))
  (lw-complex-diskp
   (lw-complex-sub (lw-euler-log-transform rate height left left-gamma)
                   (lw-euler-log-transform rate height right right-gamma))
   (+ (* (lw-zeta-euler-inverse-cap (+ rate 1) height) (lw-zeta-euler-inverse-cap rate height) log-error) (* (lw-zeta-euler-inverse-cap rate height) gamma-error))))
 :hints (("Goal"
  :use (lw-euler-log-transform-cost-data
        (:instance lw-complex-operations-rational (left (lw-complex-reciprocal (cons (- rate 1) height))) (right left) (factor 1))
        (:instance lw-complex-operations-rational (left (lw-complex-reciprocal (cons (- rate 1) height))) (right right) (factor 1))
        (:instance lw-complex-disk-data (point (lw-complex-sub left right)) (radius log-error))
        (:instance lw-complex-scale-disk (point (lw-complex-sub left right)) (radius log-error) (factor -1))
        (:instance lw-elt-positive-transport
         (left (lw-complex-sub (lw-complex-reciprocal (cons (- rate 1) height)) left)) (right (lw-complex-sub (lw-complex-reciprocal (cons (- rate 1) height)) right))))
  :in-theory (union-theories
 '(lw-euler-log-transform lw-elt-complement-difference (:executable-counterpart abs) lw-elt-left-commutes lw-elt-left-distributes lw-elt-fold-constants lw-elt-times-negative lw-elt-negative-times lw-elt-zero-times lw-elt-minus-one lw-elt-double-negative lw-elt-add-cancel lw-elt-double lw-elt-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))


(local (defthm lw-elt-unit-step
 (implies (and (rationalp rate) (rationalp height))
  (equal (lw-complex-sub (cons rate height) (cons (- rate 1) height)) (cons 1 0)))
 :hints (("Goal"
  :in-theory (union-theories
 '(lw-complex-sub lw-elt-left-commutes lw-elt-left-distributes lw-elt-fold-constants lw-elt-times-negative lw-elt-negative-times lw-elt-zero-times lw-elt-minus-one lw-elt-double-negative lw-elt-add-cancel lw-elt-double lw-elt-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(local (defthm lw-elt-inverse-identities
 (implies (and (rationalp rate) (< 0 rate) (rationalp height)
               (not (and (equal rate 1) (equal height 0))))
  (and (equal (lw-complex-reciprocal (lw-complex-mul (cons (- rate 1) height) (cons rate height))) (lw-complex-mul (lw-complex-reciprocal (cons (- rate 1) height)) (lw-complex-reciprocal (cons rate height))))
       (equal (lw-complex-reciprocal (lw-complex-mul (cons (- rate 1) height) (cons rate height))) (lw-complex-sub (lw-complex-reciprocal (cons (- rate 1) height)) (lw-complex-reciprocal (cons rate height))))
       (equal (lw-complex-mul (cons rate height) (lw-complex-reciprocal (lw-complex-mul (cons (- rate 1) height) (cons rate height)))) (lw-complex-reciprocal (cons (- rate 1) height)))))
 :hints (("Goal"
  :use (lw-elt-points lw-euler-log-transform-cost-data
        (:instance lw-complex-reciprocal-product (a (cons (- rate 1) height)) (b (cons rate height)))
        (:instance lw-complex-reciprocal-difference (a (cons (- rate 1) height)) (b (cons rate height)))
        (:instance lw-complex-reciprocal-cancel-product (a (cons rate height)) (b (lw-complex-reciprocal (cons (- rate 1) height))))
        (:instance lw-complex-mul-commutative (left (lw-complex-reciprocal (cons (- rate 1) height))) (right (lw-complex-reciprocal (cons rate height)))))
  :in-theory (union-theories
 '(lw-elt-unit-step lw-complex-mul-one lw-elt-left-commutes lw-elt-left-distributes lw-elt-fold-constants lw-elt-times-negative lw-elt-negative-times lw-elt-zero-times lw-elt-minus-one lw-elt-double-negative lw-elt-add-cancel lw-elt-double lw-elt-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-elt-base-normalization
 (implies (and (lw-complexp anchor) (lw-complexp origin) (lw-complexp joint)
               (equal joint (lw-complex-sub anchor origin))
               (equal joint (lw-complex-mul anchor origin)))
  (equal (lw-complex-add
          (lw-complex-sub (lw-complex-mul anchor joint) (lw-complex-mul anchor anchor)) anchor)
         origin))
 :hints (("Goal"
  :use ((:instance lw-complex-mul-subtract (a anchor) (b anchor) (c origin))
        (:instance lw-complex-operations-rational (left anchor) (right anchor) (factor 1)))
  :in-theory (union-theories
 '(lw-complexp lw-complex-add lw-complex-sub lw-elt-left-commutes lw-elt-left-distributes lw-elt-fold-constants lw-elt-times-negative lw-elt-negative-times lw-elt-zero-times lw-elt-minus-one lw-elt-double-negative lw-elt-add-cancel lw-elt-double lw-elt-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-elt-scaled-product
 (implies (and (lw-complexp point) (lw-complexp joint) (rationalp gamma))
  (equal (lw-complex-mul (lw-complex-scale gamma point) joint)
         (lw-complex-scale gamma (lw-complex-mul point joint))))
 :hints (("Goal"
  :in-theory (union-theories
 '(lw-complexp lw-complex-mul lw-complex-scale lw-elt-left-commutes lw-elt-left-distributes lw-elt-fold-constants lw-elt-times-negative lw-elt-negative-times lw-elt-zero-times lw-elt-minus-one lw-elt-double-negative lw-elt-add-cancel lw-elt-double lw-elt-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(local (defthm lw-elt-normalization-algebra
 (implies (and (lw-complexp point) (lw-complexp anchor) (lw-complexp origin)
               (lw-complexp joint) (lw-complexp value) (rationalp gamma)
               (equal joint (lw-complex-sub anchor origin))
               (equal joint (lw-complex-mul anchor origin))
               (equal (lw-complex-mul point joint) anchor))
  (equal
   (lw-complex-add
    (lw-complex-sub (lw-complex-mul (lw-complex-sub anchor value) joint)
                    (lw-complex-mul anchor anchor))
    (lw-complex-scale (+ 1 gamma) anchor))
   (lw-complex-sub origin
    (lw-complex-mul (lw-complex-sub value (lw-complex-scale gamma point)) joint))))
 :hints (("Goal"
  :use (lw-elt-base-normalization
        (:instance lw-elt-pair-equality
         (left (lw-complex-add (lw-complex-sub (lw-complex-mul anchor joint) (lw-complex-mul anchor anchor)) anchor))
         (right origin))
        (:instance lw-complex-operations-rational (left anchor) (right value) (factor gamma))
        (:instance lw-complex-operations-rational (left anchor) (right joint) (factor gamma))
        (:instance lw-complex-operations-rational (left anchor) (right anchor) (factor gamma))
        (:instance lw-complex-operations-rational (left value) (right joint) (factor gamma))
        (:instance lw-complex-operations-rational (left point) (right joint) (factor gamma))
        (:instance lw-complex-operations-rational (left value) (right (lw-complex-scale gamma point)) (factor gamma))
        (:instance lw-complex-mul-commutative (left (lw-complex-sub anchor value)) (right joint))
        (:instance lw-complex-mul-commutative (left (lw-complex-sub value (lw-complex-scale gamma point))) (right joint))
        (:instance lw-complex-mul-commutative (left joint) (right anchor))
        (:instance lw-complex-mul-commutative (left joint) (right value))
        (:instance lw-complex-mul-commutative (left joint) (right (lw-complex-scale gamma point)))
        (:instance lw-complex-mul-subtract (a joint) (b anchor) (c value))
        (:instance lw-complex-mul-subtract (a joint) (b value) (c (lw-complex-scale gamma point)))
        lw-elt-scaled-product)
  :in-theory (union-theories
 '(lw-complexp lw-complex-add lw-complex-sub lw-complex-scale lw-elt-left-commutes lw-elt-left-distributes lw-elt-fold-constants lw-elt-times-negative lw-elt-negative-times lw-elt-zero-times lw-elt-minus-one lw-elt-double-negative lw-elt-add-cancel lw-elt-double lw-elt-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))
 :rule-classes nil))

(defthm lw-euler-log-transform-normalized
 (implies (and (rationalp rate) (< 0 rate) (rationalp height)
               (not (and (equal rate 1) (equal height 0)))
               (lw-complexp log-value) (rationalp gamma-value))
  (equal
   (lw-euler-log-transform rate height log-value gamma-value)
   (lw-complex-sub (lw-complex-reciprocal (cons rate height))
    (lw-complex-quotient
     (lw-complex-sub log-value (lw-complex-scale gamma-value (cons rate height)))
     (lw-complex-mul (cons (- rate 1) height) (cons rate height))))))
 :hints (("Goal"
  :use (lw-euler-log-transform-cost-data lw-elt-inverse-identities
        (:instance lw-elt-normalization-algebra
         (point (cons rate height)) (anchor (lw-complex-reciprocal (cons (- rate 1) height))) (origin (lw-complex-reciprocal (cons rate height))) (joint (lw-complex-reciprocal (lw-complex-mul (cons (- rate 1) height) (cons rate height))))
         (value log-value) (gamma gamma-value)))
  :in-theory (union-theories
 '(lw-euler-log-transform lw-dirichlet-transform lw-complex-quotient lw-complexp lw-elt-left-commutes lw-elt-left-distributes lw-elt-fold-constants lw-elt-times-negative lw-elt-negative-times lw-elt-zero-times lw-elt-minus-one lw-elt-double-negative lw-elt-add-cancel lw-elt-double lw-elt-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))


