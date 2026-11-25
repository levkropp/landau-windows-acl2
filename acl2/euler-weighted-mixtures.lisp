(in-package "ACL2")

(include-book "euler-exponential-mixtures")
(include-book "exp-mixture-derivative-bounds")

; The derivative mixtures use exactly the native frozen lower logarithms.
; Coarse masses are uniform in the common precision request.

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

(local (in-theory (disable lw-euler-dirichlet-nodes)))

(local (in-theory (disable lw-euler-boundary-nodes)))
(local (in-theory (disable lw-exp-mixture-derivative-nodes)))

(local (defthm lw-ewm-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ewm-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ewm-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ewm-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ewm-times-negative (a b) (b a)))
                 :in-theory (disable lw-ewm-times-negative)))))

(local (defthm lw-ewm-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ewm-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ewm-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ewm-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ewm-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ewm-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ewm-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ewm-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ewm-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ewm-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ewm-left-commutes)))))

(local (defthm lw-ewm-point-rational
 (implies (and (rationalp rate) (rationalp height))
  (lw-complexp (lw-complex-laplace-point rate height)))
 :hints (("Goal" :in-theory (enable lw-complex-laplace-point lw-complexp)))
 :rule-classes nil))

(local (defthm lw-ewm-prefix-one
 (equal (lw-complex-common-dirichlet-prefix nil t rate height 1 request) (cons 0 0))
 :hints (("Goal" :expand ((lw-complex-common-dirichlet-prefix nil t rate height 1 request))))))

(local (defthm lw-ewm-nodes-one
 (equal (lw-exp-mixture-derivative-nodes (lw-euler-dirichlet-nodes 1 request)) nil)
 :hints (("Goal" :in-theory (enable lw-euler-dirichlet-nodes lw-exp-mixture-derivative-nodes)))))

(local (defthm lw-ewm-common-empty
 (equal (lw-exp-mixture-common-value nil point request) (cons 0 0))
 :hints (("Goal" :expand ((lw-exp-mixture-common-value nil point request))))))

(local (defthm lw-ewm-prefix-step
 (implies (and (rationalp rate) (rationalp height) (natp count) (< 1 count)
               (rationalp request) (< 0 request))
  (equal (lw-complex-common-dirichlet-prefix nil t rate height count request)
   (lw-complex-add
    (lw-complex-scale (car (lw-log-bounds count request))
     (lw-complex-log-ramp-independent-exp rate height count request request))
    (lw-complex-common-dirichlet-prefix nil t rate height (- count 1) request))))
 :hints (("Goal"
  :expand ((lw-complex-common-dirichlet-prefix nil t rate height count request))
  :in-theory (union-theories
 '(lw-common-dirichlet-coefficient lw-zeta-dirichlet-weight lw-dirichlet-sample lw-ewm-left-commutes lw-ewm-left-distributes lw-ewm-fold-constants lw-ewm-times-negative lw-ewm-negative-times lw-ewm-zero-times lw-ewm-minus-one lw-ewm-double-negative lw-ewm-add-cancel lw-ewm-double lw-ewm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(local (defthm lw-ewm-mixture-step
 (implies (and (rationalp rate) (rationalp height) (natp count) (< 1 count)
               (rationalp request) (< 0 request))
  (equal
   (lw-exp-mixture-common-value
    (lw-exp-mixture-derivative-nodes (lw-euler-dirichlet-nodes count request))
    (lw-complex-laplace-point rate height) request)
   (lw-complex-add
    (lw-complex-scale (car (lw-log-bounds count request))
     (lw-complex-log-ramp-independent-exp rate height count request request))
    (lw-exp-mixture-common-value
     (lw-exp-mixture-derivative-nodes (lw-euler-dirichlet-nodes (- count 1) request))
     (lw-complex-laplace-point rate height) request))))
 :hints (("Goal"
  :expand ((lw-euler-dirichlet-nodes count request))
  :use ((:instance lw-log-bounds-interval (value count) (epsilon request))
        (:instance lw-complex-log-ramp-independent-exp-rational
         (index count) (log-error request) (delta request)))
  :in-theory (union-theories
 '(lw-exp-mixture-derivative-nodes lw-exp-mixture-common-value lw-complex-log-ramp-independent-exp lw-complex-log-ramp-start lw-complexp lw-complex-mul lw-complex-scale lw-intervalp lw-ewm-left-commutes lw-ewm-left-distributes lw-ewm-fold-constants lw-ewm-times-negative lw-ewm-negative-times lw-ewm-zero-times lw-ewm-minus-one lw-ewm-double-negative lw-ewm-add-cancel lw-ewm-double lw-ewm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(defthm lw-euler-weighted-dirichlet-nodes-prefix
 (implies (and (rationalp rate) (rationalp height) (posp count)
               (rationalp request) (< 0 request))
  (equal
   (lw-exp-mixture-common-value
    (lw-exp-mixture-derivative-nodes (lw-euler-dirichlet-nodes count request))
    (lw-complex-laplace-point rate height) request)
   (lw-complex-common-dirichlet-prefix nil t rate height count request)))
 :hints (("Goal"
  :induct (lw-euler-dirichlet-nodes count request)
  :in-theory (union-theories
 '((:induction lw-euler-dirichlet-nodes) lw-ewm-prefix-step lw-ewm-mixture-step lw-ewm-prefix-one lw-ewm-nodes-one lw-ewm-common-empty lw-ewm-left-commutes lw-ewm-left-distributes lw-ewm-fold-constants lw-ewm-times-negative lw-ewm-negative-times lw-ewm-zero-times lw-ewm-minus-one lw-ewm-double-negative lw-ewm-add-cancel lw-ewm-double lw-ewm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not '(generalize))))

(local (defthm lw-ewm-mass-step
 (implies (and (natp count) (< 1 count) (rationalp request) (< 0 request))
  (equal
   (lw-exp-mixture-mass
    (lw-exp-mixture-derivative-nodes (lw-euler-dirichlet-nodes count request)))
   (+ (car (lw-log-bounds count request))
      (lw-exp-mixture-mass
       (lw-exp-mixture-derivative-nodes (lw-euler-dirichlet-nodes (- count 1) request))))))
 :hints (("Goal"
  :expand ((lw-euler-dirichlet-nodes count request))
  :use ((:instance lw-log-bounds-interval (value count) (epsilon request))
        (:instance lw-log-bounds-nonnegative (point count) (log-error request)))
  :in-theory (union-theories
 '(lw-exp-mixture-derivative-nodes lw-exp-mixture-mass lw-complex-l1 lw-complex-scale lw-intervalp abs lw-ewm-left-commutes lw-ewm-left-distributes lw-ewm-fold-constants lw-ewm-times-negative lw-ewm-negative-times lw-ewm-zero-times lw-ewm-minus-one lw-ewm-double-negative lw-ewm-add-cancel lw-ewm-double lw-ewm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(local (defthm lw-ewm-nodes-zero
 (implies (zp count)
  (equal (lw-exp-mixture-derivative-nodes (lw-euler-dirichlet-nodes count request)) nil))
 :hints (("Goal" :in-theory (enable lw-euler-dirichlet-nodes lw-exp-mixture-derivative-nodes)))))

(local (defthm lw-ewm-mass-empty
 (equal (lw-exp-mixture-mass nil) 0)
 :hints (("Goal" :expand ((lw-exp-mixture-mass nil))))))

(defthm lw-euler-weighted-dirichlet-nodes-mass
 (implies (and (natp count) (rationalp request) (< 0 request))
  (and
   (rationalp (lw-exp-mixture-mass
    (lw-exp-mixture-derivative-nodes (lw-euler-dirichlet-nodes count request))))
   (<= 0 (lw-exp-mixture-mass
    (lw-exp-mixture-derivative-nodes (lw-euler-dirichlet-nodes count request))))
   (<= (lw-exp-mixture-mass
    (lw-exp-mixture-derivative-nodes (lw-euler-dirichlet-nodes count request))) (* count count))))
 :hints (("Goal"
  :induct (lw-euler-dirichlet-nodes count request)
  :in-theory (union-theories
 '((:induction lw-euler-dirichlet-nodes) lw-ewm-mass-step lw-ewm-nodes-one lw-ewm-nodes-zero lw-ewm-mass-empty lw-ewm-left-commutes lw-ewm-left-distributes lw-ewm-fold-constants lw-ewm-times-negative lw-ewm-negative-times lw-ewm-zero-times lw-ewm-minus-one lw-ewm-double-negative lw-ewm-add-cancel lw-ewm-double lw-ewm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :nonlinearp t)
  (and stable-under-simplificationp
   '(:use ((:instance lw-log-bounds-unit-envelopes (value count) (error request))
           (:instance lw-log-bounds-interval (value count) (epsilon request))
           (:instance lw-log-bounds-nonnegative (point count) (log-error request)))
     :in-theory (union-theories
 '(lw-intervalp (:induction lw-euler-dirichlet-nodes) lw-ewm-mass-step lw-ewm-nodes-one lw-ewm-nodes-zero lw-ewm-mass-empty lw-ewm-left-commutes lw-ewm-left-distributes lw-ewm-fold-constants lw-ewm-times-negative lw-ewm-negative-times lw-ewm-zero-times lw-ewm-minus-one lw-ewm-double-negative lw-ewm-add-cancel lw-ewm-double lw-ewm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :nonlinearp t :do-not-induct t))))

(defthm lw-euler-weighted-boundary-nodes-data
 (implies (and (rationalp index) (< 1 index) (rationalp request) (< 0 request))
  (and
   (lw-exp-mixturep (lw-exp-mixture-derivative-nodes (lw-euler-boundary-nodes index request)))
   (equal (lw-exp-mixture-mass (lw-exp-mixture-derivative-nodes (lw-euler-boundary-nodes index request)))
          (* index (car (lw-log-bounds index request))))
   (<= 0 (lw-exp-mixture-mass (lw-exp-mixture-derivative-nodes (lw-euler-boundary-nodes index request))))
   (<= (lw-exp-mixture-mass (lw-exp-mixture-derivative-nodes (lw-euler-boundary-nodes index request))) (* index index))))
 :hints (("Goal"
  :use ((:instance lw-log-bounds-unit-envelopes (value index) (error request))
        (:instance lw-log-bounds-interval (value index) (epsilon request))
        (:instance lw-log-bounds-nonnegative (point index) (log-error request)))
  :in-theory (union-theories
 '(lw-euler-boundary-nodes lw-exp-mixture-derivative-nodes lw-exp-mixturep lw-exp-mixture-mass lw-complex-l1 lw-complex-scale lw-complexp lw-intervalp abs lw-ewm-left-commutes lw-ewm-left-distributes lw-ewm-fold-constants lw-ewm-times-negative lw-ewm-negative-times lw-ewm-zero-times lw-ewm-minus-one lw-ewm-double-negative lw-ewm-add-cancel lw-ewm-double lw-ewm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :nonlinearp t :do-not-induct t)))

(defthm lw-euler-weighted-boundary-nodes-value
 (implies (and (rationalp rate) (rationalp height) (rationalp index) (< 1 index)
               (rationalp request) (< 0 request))
  (equal
   (lw-exp-mixture-common-value
    (lw-exp-mixture-derivative-nodes (lw-euler-boundary-nodes index request))
    (lw-complex-laplace-point rate height) request)
   (lw-complex-scale (* index (car (lw-log-bounds index request)))
    (lw-complex-log-ramp-independent-exp rate height index request request))))
 :hints (("Goal"
  :use ((:instance lw-log-bounds-interval (value index) (epsilon request))
        (:instance lw-complex-log-ramp-independent-exp-rational (log-error request) (delta request)))
  :in-theory (union-theories
 '(lw-euler-boundary-nodes lw-exp-mixture-derivative-nodes lw-exp-mixture-common-value lw-complex-log-ramp-independent-exp lw-complex-log-ramp-start lw-complex-laplace-point lw-complexp lw-complex-mul lw-complex-scale lw-complex-add lw-intervalp lw-ewm-left-commutes lw-ewm-left-distributes lw-ewm-fold-constants lw-ewm-times-negative lw-ewm-negative-times lw-ewm-zero-times lw-ewm-minus-one lw-ewm-double-negative lw-ewm-add-cancel lw-ewm-double lw-ewm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

