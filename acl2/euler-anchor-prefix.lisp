(in-package "ACL2")

(include-book "euler-anchor-value")
(include-book "euler-prefix-derivatives")
(include-book "euler-continuity")

; At rate one the finite derivative is a harmonic/logarithm enclosure.
; All finite-node errors retain their computed common precision.

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

(local (in-theory (disable lw-dirichlet-sample lw-complex-common-dirichlet-prefix
 lw-complex-euler-prefix-derivative lw-harmonic lw-euler-from-log lw-euler-bounds)))

(local (defthm lw-eap-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-eap-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-eap-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-eap-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-eap-times-negative (a b) (b a)))
                 :in-theory (disable lw-eap-times-negative)))))

(local (defthm lw-eap-zero-times (equal (* 0 a) 0)))

(local (defthm lw-eap-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-eap-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-eap-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-eap-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-eap-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-eap-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-eap-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-eap-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-eap-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-eap-left-commutes)))))

(local (defthm lw-eap-inverse-data
 (implies (and (rationalp index) (< 1 index))
  (and (rationalp (/ index)) (< 0 (/ index)) (<= (/ index) 1)))
 :hints (("Goal" :nonlinearp t))
 :rule-classes nil))

(local (defthm lw-eap-node-identity
 (implies (and (lw-complexp point) (rationalp index) (not (equal index 0)))
  (equal
   (lw-complex-scale (/ index) (lw-complex-sub (lw-complex-scale index point) (cons 1 0)))
   (lw-complex-sub point (cons (/ index) 0))))
 :hints (("Goal"
  :use ((:instance lw-eap-inverse-factor (divisor index) (coefficient (car point)))
        (:instance lw-eap-inverse-factor (divisor index) (coefficient (cdr point))))
  :in-theory (union-theories
 '(lw-complexp lw-complex-scale lw-complex-sub lw-eap-left-commutes lw-eap-left-distributes lw-eap-fold-constants lw-eap-times-negative lw-eap-negative-times lw-eap-zero-times lw-eap-minus-one lw-eap-double-negative lw-eap-add-cancel lw-eap-double lw-eap-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(defthm lw-euler-anchor-node
 (implies (and (rationalp index) (< 1 index)
               (rationalp request) (< 0 request) (<= request 1))
  (lw-complex-diskp
   (lw-complex-sub (lw-dirichlet-sample 1 0 index request request) (cons (/ index) 0))
   (* (lw-euler-anchor-node-cost index) request)))
 :hints (("Goal"
  :use (lw-euler-anchor-node-cost-valid lw-euler-anchor-endpoint lw-eap-inverse-data
        (:instance lw-dirichlet-sample-rational (rate 1) (height 0) (log-error request) (node-error request))
        (:instance lw-eap-node-identity (point (lw-dirichlet-sample 1 0 index request request)))
        (:instance lw-complex-scale-disk
         (point (lw-complex-sub (lw-complex-scale index (lw-dirichlet-sample 1 0 index request request)) (cons 1 0)))
         (radius (* (lw-euler-anchor-node-cost index) request)) (factor (/ index)))
        (:instance lw-eap-positive-product (a (lw-euler-anchor-node-cost index)) (b request))
        (:instance lw-eap-multiply-order (a (/ index)) (b 1) (factor (* (lw-euler-anchor-node-cost index) request)))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub (lw-dirichlet-sample 1 0 index request request) (cons (/ index) 0)))
         (radius (* (abs (/ index)) (* (lw-euler-anchor-node-cost index) request)))
         (cap (* (lw-euler-anchor-node-cost index) request))))
  :in-theory (union-theories
 '(abs lw-eap-left-commutes lw-eap-left-distributes lw-eap-fold-constants lw-eap-times-negative lw-eap-negative-times lw-eap-zero-times lw-eap-minus-one lw-eap-double-negative lw-eap-add-cancel lw-eap-double lw-eap-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(local (defthm lw-eap-weighted-identity
 (implies (and (lw-complexp point) (rationalp index) (rationalp weight))
  (equal
   (lw-complex-scale weight (lw-complex-sub (lw-complex-scale index point) (cons 1 0)))
   (lw-complex-sub (lw-complex-scale (* index weight) point) (cons weight 0))))
 :hints (("Goal"
  :in-theory (union-theories
 '(lw-complexp lw-complex-scale lw-complex-sub lw-eap-left-commutes lw-eap-left-distributes lw-eap-fold-constants lw-eap-times-negative lw-eap-negative-times lw-eap-zero-times lw-eap-minus-one lw-eap-double-negative lw-eap-add-cancel lw-eap-double lw-eap-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(defthm lw-euler-anchor-log-endpoint
 (implies (and (rationalp index) (< 1 index)
               (rationalp request) (< 0 request) (<= request 1))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-complex-scale (* index (car (lw-log-bounds index request)))
     (lw-dirichlet-sample 1 0 index request request))
    (cons (car (lw-log-bounds index request)) 0))
   (* index (lw-euler-anchor-node-cost index) request)))
 :hints (("Goal"
  :use (lw-euler-anchor-node-cost-valid lw-euler-anchor-endpoint
        (:instance lw-log-bounds-interval (value index) (epsilon request))
        (:instance lw-log-bounds-lower-coarse (value index) (epsilon request))
        (:instance lw-dirichlet-sample-rational (rate 1) (height 0) (log-error request) (node-error request))
        (:instance lw-eap-weighted-identity
         (point (lw-dirichlet-sample 1 0 index request request)) (weight (car (lw-log-bounds index request))))
        (:instance lw-complex-scale-disk
         (point (lw-complex-sub (lw-complex-scale index (lw-dirichlet-sample 1 0 index request request)) (cons 1 0)))
         (radius (* (lw-euler-anchor-node-cost index) request)) (factor (car (lw-log-bounds index request))))
        (:instance lw-eap-positive-product (a (lw-euler-anchor-node-cost index)) (b request))
        (:instance lw-eap-multiply-order (a (car (lw-log-bounds index request))) (b index)
         (factor (* (lw-euler-anchor-node-cost index) request)))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub
          (lw-complex-scale (* index (car (lw-log-bounds index request))) (lw-dirichlet-sample 1 0 index request request))
          (cons (car (lw-log-bounds index request)) 0)))
         (radius (* (abs (car (lw-log-bounds index request))) (* (lw-euler-anchor-node-cost index) request)))
         (cap (* index (lw-euler-anchor-node-cost index) request))))
  :in-theory (union-theories
 '(abs lw-intervalp lw-eap-left-commutes lw-eap-left-distributes lw-eap-fold-constants lw-eap-times-negative lw-eap-negative-times lw-eap-zero-times lw-eap-minus-one lw-eap-double-negative lw-eap-add-cancel lw-eap-double lw-eap-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))


(defun lw-euler-anchor-prefix-cost (count)
 (declare (xargs :measure (nfix count)))
 (if (or (zp count) (equal count 1)) 0
  (+ (lw-euler-anchor-node-cost count) (lw-euler-anchor-prefix-cost (- count 1)))))

(local (in-theory (disable lw-euler-anchor-prefix-cost)))

(defthm lw-euler-anchor-prefix-cost-valid
 (implies (natp count)
  (and (rationalp (lw-euler-anchor-prefix-cost count))
       (<= 0 (lw-euler-anchor-prefix-cost count))))
 :hints (("Goal"
  :induct (lw-euler-anchor-prefix-cost count)
  :in-theory (union-theories
 '(lw-euler-anchor-prefix-cost lw-eap-left-commutes lw-eap-left-distributes lw-eap-fold-constants lw-eap-times-negative lw-eap-negative-times lw-eap-zero-times lw-eap-minus-one lw-eap-double-negative lw-eap-add-cancel lw-eap-double lw-eap-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
  (and stable-under-simplificationp
       '(:use ((:instance lw-euler-anchor-node-cost-valid (index count)))))))

(local (defthm lw-eap-add-errors
 (implies
  (and (lw-complexp a) (lw-complexp b) (rationalp a0) (rationalp b0)
       (lw-complex-diskp (lw-complex-sub a (cons a0 0)) ra)
       (lw-complex-diskp (lw-complex-sub b (cons b0 0)) rb))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-add a b) (cons (+ a0 b0) 0))
   (+ ra rb)))
 :hints (("Goal"
  :use ((:instance lw-complex-add-disk
         (left (lw-complex-sub a (cons a0 0))) (right (lw-complex-sub b (cons b0 0)))
         (radius ra) (other-radius rb)))
  :in-theory (union-theories
 '(lw-complexp lw-complex-add lw-complex-sub lw-eap-left-commutes lw-eap-left-distributes lw-eap-fold-constants lw-eap-times-negative lw-eap-negative-times lw-eap-zero-times lw-eap-minus-one lw-eap-double-negative lw-eap-add-cancel lw-eap-double lw-eap-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-eap-prefix-step
 (implies (and (natp count) (< 1 count)
               (rationalp request) (< 0 request) (<= request 1)
               (lw-complex-diskp
                (lw-complex-sub
                 (lw-complex-common-dirichlet-prefix nil nil 1 0 (- count 1) request)
                 (cons (lw-harmonic (- count 1)) 0))
                (* (lw-euler-anchor-prefix-cost (- count 1)) request)))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-complex-common-dirichlet-prefix nil nil 1 0 count request)
    (cons (lw-harmonic count) 0))
   (* (lw-euler-anchor-prefix-cost count) request)))
 :hints (("Goal"
  :use ((:instance lw-euler-anchor-node (index count))
        (:instance lw-dirichlet-sample-rational
         (rate 1) (height 0) (index count) (log-error request) (node-error request))
        (:instance lw-complex-common-dirichlet-prefix-rational
         (mangoldtp nil) (logp nil) (rate 1) (height 0) (count (- count 1)) (error request))
        (:instance lw-harmonic-rational (count (- count 1)))
        (:instance lw-eap-add-errors
         (a (lw-dirichlet-sample 1 0 count request request))
         (b (lw-complex-common-dirichlet-prefix nil nil 1 0 (- count 1) request))
         (a0 (/ count)) (b0 (lw-harmonic (- count 1)))
         (ra (* (lw-euler-anchor-node-cost count) request))
         (rb (* (lw-euler-anchor-prefix-cost (- count 1)) request))))
  :expand ((lw-complex-common-dirichlet-prefix nil nil 1 0 count request)
           (lw-euler-anchor-prefix-cost count) (lw-harmonic count))
  :in-theory (union-theories
 '(lw-common-dirichlet-coefficient lw-zeta-dirichlet-weight lw-complex-scale lw-complex-add lw-complexp lw-eap-left-commutes lw-eap-left-distributes lw-eap-fold-constants lw-eap-times-negative lw-eap-negative-times lw-eap-zero-times lw-eap-minus-one lw-eap-double-negative lw-eap-add-cancel lw-eap-double lw-eap-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(defthm lw-euler-anchor-ordinary-prefix
 (implies (and (natp count) (rationalp request) (< 0 request) (<= request 1))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-common-dirichlet-prefix nil nil 1 0 count request) (cons (lw-harmonic count) 0))
   (* (lw-euler-anchor-prefix-cost count) request)))
 :hints (("Goal"
  :induct (lw-euler-anchor-prefix-cost count)
  :in-theory (union-theories
 '(lw-eap-prefix-step (:induction lw-euler-anchor-prefix-cost) lw-eap-left-commutes lw-eap-left-distributes lw-eap-fold-constants lw-eap-times-negative lw-eap-negative-times lw-eap-zero-times lw-eap-minus-one lw-eap-double-negative lw-eap-add-cancel lw-eap-double lw-eap-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
  ("Subgoal *1/2" :use (lw-eap-prefix-step))
  ("Subgoal *1/1"
   :in-theory (union-theories
 '(lw-euler-anchor-prefix-cost lw-complex-common-dirichlet-prefix lw-harmonic lw-complex-sub lw-complex-diskp lw-complexp lw-diskp lw-eap-left-commutes lw-eap-left-distributes lw-eap-fold-constants lw-eap-times-negative lw-eap-negative-times lw-eap-zero-times lw-eap-minus-one lw-eap-double-negative lw-eap-add-cancel lw-eap-double lw-eap-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))


(local (defthm lw-eap-sub-errors
 (implies
  (and (lw-complexp a) (lw-complexp b) (rationalp a0) (rationalp b0)
       (lw-complex-diskp (lw-complex-sub a (cons a0 0)) ra)
       (lw-complex-diskp (lw-complex-sub b (cons b0 0)) rb))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-sub a b) (cons (- a0 b0) 0))
   (+ ra rb)))
 :hints (("Goal"
  :use ((:instance lw-complex-disk-data (point (lw-complex-sub b (cons b0 0))) (radius rb))
        (:instance lw-complex-disk-data (point (lw-complex-sub a (cons a0 0))) (radius ra))
        (:instance lw-complex-scale-disk
         (point (lw-complex-sub b (cons b0 0))) (radius rb) (factor -1))
        (:instance lw-complex-add-disk
         (left (lw-complex-sub a (cons a0 0)))
         (right (lw-complex-scale -1 (lw-complex-sub b (cons b0 0))))
         (radius ra) (other-radius rb)))
  :in-theory (union-theories
 '(lw-complexp lw-complex-add lw-complex-sub lw-complex-scale abs lw-eap-left-commutes lw-eap-left-distributes lw-eap-fold-constants lw-eap-times-negative lw-eap-negative-times lw-eap-zero-times lw-eap-minus-one lw-eap-double-negative lw-eap-add-cancel lw-eap-double lw-eap-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))
 :rule-classes nil))

(defun lw-euler-anchor-derivative-cost (count)
 (+ (lw-euler-anchor-prefix-cost count)
    (* (+ 1 count) (lw-euler-anchor-node-cost (+ 1 count)))))

(local (in-theory (disable lw-euler-anchor-derivative-cost)))

(defthm lw-euler-anchor-derivative-cost-valid
 (implies (posp count)
  (and (rationalp (lw-euler-anchor-derivative-cost count))
       (< 0 (lw-euler-anchor-derivative-cost count))))
 :hints (("Goal"
  :use (lw-euler-anchor-prefix-cost-valid
        (:instance lw-euler-anchor-node-cost-valid (index (+ 1 count)))
        (:instance lw-eap-positive-product (a (+ 1 count)) (b (lw-euler-anchor-node-cost (+ 1 count)))))
  :in-theory (union-theories
 '(lw-euler-anchor-derivative-cost lw-eap-left-commutes lw-eap-left-distributes lw-eap-fold-constants lw-eap-times-negative lw-eap-negative-times lw-eap-zero-times lw-eap-minus-one lw-eap-double-negative lw-eap-add-cancel lw-eap-double lw-eap-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-euler-anchor-prefix-derivative
 (implies (and (posp count) (rationalp request) (< 0 request) (<= request 1))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-euler-prefix-derivative 1 0 count request)
    (cons (- (lw-harmonic count) (car (lw-log-bounds (+ 1 count) request))) 0))
   (* (lw-euler-anchor-derivative-cost count) request)))
 :hints (("Goal"
  :use (lw-euler-anchor-ordinary-prefix lw-euler-anchor-prefix-cost-valid
        (:instance lw-euler-anchor-node-cost-valid (index (+ 1 count)))
        (:instance lw-euler-anchor-log-endpoint (index (+ 1 count)))
        (:instance lw-complex-common-dirichlet-prefix-rational
         (mangoldtp nil) (logp nil) (rate 1) (height 0) (error request))
        (:instance lw-dirichlet-sample-rational
         (rate 1) (height 0) (index (+ 1 count)) (log-error request) (node-error request))
        (:instance lw-log-bounds-interval (value (+ 1 count)) (epsilon request))
        lw-harmonic-rational
        (:instance lw-eap-sub-errors
         (a (lw-complex-common-dirichlet-prefix nil nil 1 0 count request))
         (b (lw-complex-scale (* (+ 1 count) (car (lw-log-bounds (+ 1 count) request)))
             (lw-dirichlet-sample 1 0 (+ 1 count) request request)))
         (a0 (lw-harmonic count)) (b0 (car (lw-log-bounds (+ 1 count) request)))
         (ra (* (lw-euler-anchor-prefix-cost count) request))
         (rb (* (+ 1 count) (lw-euler-anchor-node-cost (+ 1 count)) request))))
  :in-theory (union-theories
 '(lw-complex-euler-prefix-derivative lw-dirichlet-sample lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale lw-intervalp lw-euler-anchor-derivative-cost lw-eap-left-commutes lw-eap-left-distributes lw-eap-fold-constants lw-eap-times-negative lw-eap-negative-times lw-eap-zero-times lw-eap-minus-one lw-eap-double-negative lw-eap-add-cancel lw-eap-double lw-eap-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-euler-anchor-harmonic-gamma
 (implies (and (posp count) (rationalp request) (< 0 request)
               (rationalp gamma-error) (< 0 gamma-error))
  (<=
   (abs (- (- (lw-harmonic count) (car (lw-log-bounds (+ 1 count) request)))
           (car (lw-euler-bounds gamma-error))))
   (+ request (/ (+ 1 count)) gamma-error)))
 :hints (("Goal"
  :use ((:instance lw-harmonic-successor)
        (:instance lw-harmonic-rational)
        (:instance lw-euler-count-positive (epsilon gamma-error))
        (:instance lw-euler-count-at-least-three (epsilon gamma-error))
        (:instance lw-euler-bounds-interval (epsilon gamma-error))
        (:instance lw-euler-bounds-width (epsilon gamma-error))
        (:instance lw-log-bounds-interval (value (+ 1 count)) (epsilon request))
        (:instance lw-log-bounds-width (value (+ 1 count)) (epsilon request))
        (:instance lw-euler-log-enclosures-overlap
         (left-count (+ 1 count)) (left-error request)
         (right-count (lw-euler-count gamma-error)) (right-error (/ gamma-error 2)))
        (:instance lw-euler-log-enclosures-overlap
         (right-count (+ 1 count)) (right-error request)
         (left-count (lw-euler-count gamma-error)) (left-error (/ gamma-error 2))))
  :in-theory (union-theories
 '(lw-euler-bounds lw-euler-from-log lw-intervalp abs lw-eap-left-commutes lw-eap-left-distributes lw-eap-fold-constants lw-eap-times-negative lw-eap-negative-times lw-eap-zero-times lw-eap-minus-one lw-eap-double-negative lw-eap-add-cancel lw-eap-double lw-eap-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))


(local (defthm lw-eap-real-difference-disk
         (implies (and (rationalp a) (rationalp b) (rationalp error) (<= (abs (- a b)) error))
                  (lw-complex-diskp (lw-complex-sub (cons a 0) (cons b 0)) error))
         :hints (("Goal" :in-theory (union-theories
 '(lw-complex-diskp lw-complex-sub lw-complexp lw-diskp abs lw-eap-left-commutes lw-eap-left-distributes lw-eap-fold-constants lw-eap-times-negative lw-eap-negative-times lw-eap-zero-times lw-eap-minus-one lw-eap-double-negative lw-eap-add-cancel lw-eap-double lw-eap-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
                         :cases ((<= a b)) :nonlinearp t))
         :rule-classes nil))

(defthm lw-euler-anchor-prefix-derivative-rational
 (implies (and (posp count) (rationalp request) (< 0 request))
  (lw-complexp (lw-complex-euler-prefix-derivative 1 0 count request)))
 :hints (("Goal"
  :use ((:instance lw-complex-common-dirichlet-prefix-rational
         (mangoldtp nil) (logp nil) (rate 1) (height 0) (error request))
        (:instance lw-dirichlet-sample-rational
         (rate 1) (height 0) (index (+ 1 count)) (log-error request) (node-error request))
        (:instance lw-log-bounds-interval (value (+ 1 count)) (epsilon request)))
  :in-theory (union-theories
 '(lw-complex-euler-prefix-derivative lw-dirichlet-sample lw-complexp lw-complex-add lw-complex-mul lw-complex-scale lw-intervalp lw-eap-left-commutes lw-eap-left-distributes lw-eap-fold-constants lw-eap-times-negative lw-eap-negative-times lw-eap-zero-times lw-eap-minus-one lw-eap-double-negative lw-eap-add-cancel lw-eap-double lw-eap-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-euler-anchor-prefix-gamma
 (implies (and (posp count) (rationalp request) (< 0 request) (<= request 1)
               (rationalp gamma-error) (< 0 gamma-error))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-euler-prefix-derivative 1 0 count request)
    (cons (car (lw-euler-bounds gamma-error)) 0))
   (+ (* (+ 1 (lw-euler-anchor-derivative-cost count)) request)
      (/ (+ 1 count)) gamma-error)))
 :hints (("Goal"
  :use (lw-euler-anchor-prefix-derivative lw-euler-anchor-harmonic-gamma
        lw-euler-anchor-prefix-derivative-rational lw-euler-anchor-derivative-cost-valid
        lw-harmonic-rational
        (:instance lw-log-bounds-interval (value (+ 1 count)) (epsilon request))
        (:instance lw-euler-bounds-interval (epsilon gamma-error))
        (:instance lw-eap-real-difference-disk
         (a (- (lw-harmonic count) (car (lw-log-bounds (+ 1 count) request))))
         (b (car (lw-euler-bounds gamma-error)))
         (error (+ request (/ (+ 1 count)) gamma-error)))
        (:instance lw-complex-difference-triangle
         (left (lw-complex-euler-prefix-derivative 1 0 count request))
         (middle (cons (- (lw-harmonic count) (car (lw-log-bounds (+ 1 count) request))) 0))
         (right (cons (car (lw-euler-bounds gamma-error)) 0))
         (radius (* (lw-euler-anchor-derivative-cost count) request))
         (other-radius (+ request (/ (+ 1 count)) gamma-error)))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub (lw-complex-euler-prefix-derivative 1 0 count request)
                 (cons (car (lw-euler-bounds gamma-error)) 0)))
         (radius (+ (* (lw-euler-anchor-derivative-cost count) request) request (/ (+ 1 count)) gamma-error))
         (cap (+ (* (+ 1 (lw-euler-anchor-derivative-cost count)) request) (/ (+ 1 count)) gamma-error))))
  :in-theory (union-theories
 '(lw-complexp lw-intervalp lw-eap-left-commutes lw-eap-left-distributes lw-eap-fold-constants lw-eap-times-negative lw-eap-negative-times lw-eap-zero-times lw-eap-minus-one lw-eap-double-negative lw-eap-add-cancel lw-eap-double lw-eap-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))




