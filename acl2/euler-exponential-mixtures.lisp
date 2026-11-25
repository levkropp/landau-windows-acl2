(in-package "ACL2")

(include-book "euler-disk-bounds")
(include-book "exp-mixture-precision")

; Freeze the actual lower logarithms into valid exponential mixtures.
; Their common-precision values are exactly the existing Euler prefix.

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

(local (in-theory (disable lw-exp-mixturep lw-exp-mixture-mass lw-exp-mixture-common-value
 lw-complex-common-dirichlet-prefix lw-common-dirichlet-coefficient
 lw-zeta-dirichlet-weight lw-dirichlet-sample lw-complex-euler-dirichlet-prefix
 lw-complex-euler-dirichlet-prefix-step lw-complex-euler-dirichlet-prefix-telescope
 lw-complex-euler-cell-segment-telescope lw-complex-euler-cell-segment-difference
 lw-complex-euler-dyadic-tail-telescope lw-complex-euler-dyadic-tail-difference)))

(local (defthm lw-emx-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-emx-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-emx-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-emx-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-emx-times-negative (a b) (b a)))
                 :in-theory (disable lw-emx-times-negative)))))

(local (defthm lw-emx-zero-times (equal (* 0 a) 0)))

(local (defthm lw-emx-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-emx-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-emx-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-emx-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-emx-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-emx-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-emx-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-emx-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-emx-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-emx-left-commutes)))))

(defun lw-euler-dirichlet-nodes (count log-error)
 (declare (xargs :measure (nfix count)))
 (if (or (zp count) (equal count 1)) nil
  (cons (cons (car (lw-log-bounds count log-error)) (cons 1 0))
        (lw-euler-dirichlet-nodes (- count 1) log-error))))

(local (in-theory (disable lw-euler-dirichlet-nodes)))

(defthm lw-euler-dirichlet-nodes-valid
 (implies (and (natp count) (rationalp log-error) (< 0 log-error))
  (and (lw-exp-mixturep (lw-euler-dirichlet-nodes count log-error))
       (equal (len (lw-euler-dirichlet-nodes count log-error)) (if (zp count) 0 (- count 1)))))
 :hints (("Goal" :induct (lw-euler-dirichlet-nodes count log-error)
                 :in-theory (union-theories
   '(lw-euler-dirichlet-nodes lw-exp-mixturep lw-complexp len lw-intervalp lw-emx-left-commutes lw-emx-left-distributes lw-emx-fold-constants lw-emx-times-negative lw-emx-negative-times lw-emx-zero-times lw-emx-minus-one lw-emx-double-negative lw-emx-add-cancel lw-emx-double lw-emx-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory)))
         (and stable-under-simplificationp
          '(:use ((:instance lw-log-bounds-interval (value count) (epsilon log-error))
                  (:instance lw-log-bounds-nonnegative (point count)))
            :do-not-induct t))))

(defthm lw-euler-dirichlet-nodes-mass
 (implies (natp count)
  (equal (lw-exp-mixture-mass (lw-euler-dirichlet-nodes count log-error))
         (if (zp count) 0 (- count 1))))
 :hints (("Goal" :induct (lw-euler-dirichlet-nodes count log-error)
                 :in-theory (enable lw-euler-dirichlet-nodes lw-exp-mixture-mass lw-complex-l1))))

(local (defthm lw-emx-prefix-one
 (equal (lw-complex-common-dirichlet-prefix nil nil rate height 1 request) (cons 1 0))
 :hints (("Goal" :expand ((lw-complex-common-dirichlet-prefix nil nil rate height 1 request))))))

(local (defthm lw-emx-nodes-one
 (equal (lw-euler-dirichlet-nodes 1 request) nil)
 :hints (("Goal" :expand ((lw-euler-dirichlet-nodes 1 request))))))

(local (defthm lw-emx-common-empty
 (equal (lw-exp-mixture-common-value nil point request) (cons 0 0))
 :hints (("Goal" :expand ((lw-exp-mixture-common-value nil point request))))))

(local (defthm lw-emx-point-rational
 (implies (and (rationalp rate) (rationalp height))
  (lw-complexp (lw-complex-laplace-point rate height)))
 :hints (("Goal" :in-theory (enable lw-complex-laplace-point lw-complexp)))
 :rule-classes nil))

(local (defthm lw-emx-add-swap-left
 (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c))
  (equal (lw-complex-add a (lw-complex-add b c)) (lw-complex-add b (lw-complex-add a c))))
 :hints (("Goal" :in-theory (enable lw-complexp lw-complex-add)))))

(local (defthm lw-emx-prefix-step
 (implies (and (rationalp rate) (rationalp height) (natp count) (< 1 count)
               (rationalp request) (< 0 request))
  (equal (lw-complex-common-dirichlet-prefix nil nil rate height count request)
   (lw-complex-add (lw-complex-log-ramp-independent-exp rate height count request request)
    (lw-complex-common-dirichlet-prefix nil nil rate height (- count 1) request))))
 :hints (("Goal"
  :expand ((lw-complex-common-dirichlet-prefix nil nil rate height count request))
  :use ((:instance lw-complex-log-ramp-independent-exp-rational
         (index count) (log-error request) (delta request)))
  :in-theory (union-theories
   '(lw-common-dirichlet-coefficient lw-zeta-dirichlet-weight lw-dirichlet-sample lw-complex-scale-one lw-emx-left-commutes lw-emx-left-distributes lw-emx-fold-constants lw-emx-times-negative lw-emx-negative-times lw-emx-zero-times lw-emx-minus-one lw-emx-double-negative lw-emx-add-cancel lw-emx-double lw-emx-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t))))

(local (defthm lw-emx-mixture-step
 (implies (and (rationalp rate) (rationalp height) (natp count) (< 1 count)
               (rationalp request) (< 0 request))
  (equal
   (lw-exp-mixture-common-value (lw-euler-dirichlet-nodes count request)
                               (lw-complex-laplace-point rate height) request)
   (lw-complex-add (lw-complex-log-ramp-independent-exp rate height count request request)
    (lw-exp-mixture-common-value (lw-euler-dirichlet-nodes (- count 1) request)
                                (lw-complex-laplace-point rate height) request))))
 :hints (("Goal"
  :expand ((lw-euler-dirichlet-nodes count request)
           (lw-exp-mixture-common-value
            (cons (cons (car (lw-log-bounds count request)) (cons 1 0))
                  (lw-euler-dirichlet-nodes (- count 1) request))
            (lw-complex-laplace-point rate height) request))
  :use ((:instance lw-complex-log-ramp-independent-exp-rational
         (index count) (log-error request) (delta request)))
  :in-theory (union-theories
   '(lw-complex-log-ramp-independent-exp lw-complex-log-ramp-start lw-complex-mul-one lw-emx-left-commutes lw-emx-left-distributes lw-emx-fold-constants lw-emx-times-negative lw-emx-negative-times lw-emx-zero-times lw-emx-minus-one lw-emx-double-negative lw-emx-add-cancel lw-emx-double lw-emx-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t))))

(defthm lw-euler-dirichlet-nodes-prefix
 (implies (and (rationalp rate) (rationalp height) (posp count) (rationalp request) (< 0 request))
  (equal (lw-complex-common-dirichlet-prefix nil nil rate height count request)
   (lw-complex-add (cons 1 0)
    (lw-exp-mixture-common-value (lw-euler-dirichlet-nodes count request)
                                (lw-complex-laplace-point rate height) request))))
 :hints (("Goal"
  :induct (lw-euler-dirichlet-nodes count request)
  :in-theory (union-theories
   '((:induction lw-euler-dirichlet-nodes) lw-emx-prefix-step lw-emx-mixture-step lw-emx-prefix-one lw-emx-nodes-one lw-emx-common-empty lw-complex-add-zero lw-emx-add-swap-left (:executable-counterpart lw-complexp) lw-emx-left-commutes lw-emx-left-distributes lw-emx-fold-constants lw-emx-times-negative lw-emx-negative-times lw-emx-zero-times lw-emx-minus-one lw-emx-double-negative lw-emx-add-cancel lw-emx-double lw-emx-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory)))
         (and stable-under-simplificationp
          '(:use (lw-emx-point-rational (:instance lw-complex-log-ramp-independent-exp-rational
                   (index count) (log-error request) (delta request))
                  (:instance lw-euler-dirichlet-nodes-valid (count (- count 1)) (log-error request))
                  (:instance lw-exp-mixture-common-value-rational
                   (nodes (lw-euler-dirichlet-nodes (- count 1) request))
                   (point (lw-complex-laplace-point rate height))))
            :do-not-induct t))))

(defun lw-euler-boundary-nodes (index log-error)
 (list (cons (car (lw-log-bounds index log-error)) (cons index 0))))

(local (in-theory (disable lw-euler-boundary-nodes)))

(defthm lw-euler-boundary-nodes-valid
 (implies (and (rationalp index) (< 1 index) (rationalp log-error) (< 0 log-error))
  (and (lw-exp-mixturep (lw-euler-boundary-nodes index log-error))
       (equal (len (lw-euler-boundary-nodes index log-error)) 1)
       (equal (lw-exp-mixture-mass (lw-euler-boundary-nodes index log-error)) index)))
 :hints (("Goal"
  :use ((:instance lw-log-bounds-interval (value index) (epsilon log-error))
        (:instance lw-log-bounds-nonnegative (point index)))
  :in-theory (e/d (lw-euler-boundary-nodes lw-exp-mixturep lw-complexp lw-exp-mixture-mass lw-complex-l1 lw-intervalp)
                  (lw-log-bounds-interval lw-log-bounds-nonnegative))
  :do-not-induct t)))

(defthm lw-euler-boundary-nodes-value
 (implies (and (rationalp rate) (rationalp height) (rationalp index) (< 1 index)
               (rationalp request) (< 0 request))
  (equal
   (lw-exp-mixture-common-value (lw-euler-boundary-nodes index request)
                               (lw-complex-laplace-point rate height) request)
   (lw-complex-scale index (lw-complex-log-ramp-independent-exp rate height index request request))))
 :hints (("Goal"
  :use ((:instance lw-complex-log-ramp-independent-exp-rational (log-error request) (delta request)))
  :in-theory (enable lw-euler-boundary-nodes lw-exp-mixture-common-value
   lw-complex-log-ramp-independent-exp lw-complex-log-ramp-start
   lw-complex-laplace-point lw-complexp lw-complex-mul lw-complex-add lw-complex-scale)
  :do-not-induct t)))

(defthm lw-complex-euler-prefix-mixture-identity
 (implies (and (rationalp rate) (rationalp height) (posp count) (rationalp request) (< 0 request))
  (equal (lw-complex-euler-dirichlet-prefix rate height count request)
   (lw-complex-add
    (lw-complex-mul (cons (- rate 1) height)
     (lw-complex-add (cons 1 0)
      (lw-exp-mixture-common-value (lw-euler-dirichlet-nodes count request)
                                  (lw-complex-laplace-point rate height) request)))
    (lw-exp-mixture-common-value (lw-euler-boundary-nodes (+ 1 count) request)
                                (lw-complex-laplace-point rate height) request))))
 :hints (("Goal"
  :use (lw-euler-dirichlet-nodes-prefix
        (:instance lw-euler-boundary-nodes-value (index (+ 1 count))))
  :in-theory (union-theories
   '(lw-complex-euler-dirichlet-prefix lw-dirichlet-sample lw-emx-left-commutes lw-emx-left-distributes lw-emx-fold-constants lw-emx-times-negative lw-emx-negative-times lw-emx-zero-times lw-emx-minus-one lw-emx-double-negative lw-emx-add-cancel lw-emx-double lw-emx-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t)))

