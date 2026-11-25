(in-package "ACL2")

(include-book "euler-circle-count-stability")

(defun lw-euler-circle-count-value-error (radius)
  (* 1/16 (/ (+ 1 radius))))

(defun lw-euler-circle-count-budget (radius gap anchor cost request)
  (min request
       (min (* 1/4 anchor)
            (min (* anchor (/ (+ 1 gap)))
                 (* (lw-euler-circle-count-value-error radius) (/ (+ 1 cost)))))))

; One tolerance serves the value polynomial and its approximate factorization.
(defun lw-euler-circle-count-request (center radius plus-arcs minus-arcs request)
  (lw-euler-circle-count-budget radius (lw-euler-circle-outer-gap center radius) (lw-euler-circle-anchor-min plus-arcs minus-arcs)
    (+ (lw-euler-circle-global-quotient-cost center radius plus-arcs minus-arcs) (lw-disk-factor-quotient-cost
      (- (lw-euler-circle-outer-radius center radius) radius)
      (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs))
      (lw-euler-circle-global-derivative-cap center radius)))
    request))

(local (in-theory (disable lw-euler-circle-count-request lw-euler-circle-count-budget lw-euler-circle-count-value-error)))

(local (defthm lw-eccr-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-eccr-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-eccr-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-eccr-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-eccr-times-negative (a b) (b a)))
                 :in-theory (disable lw-eccr-times-negative)))))

(local (defthm lw-eccr-zero-times (equal (* 0 a) 0)))

(local (defthm lw-eccr-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-eccr-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-eccr-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-eccr-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-eccr-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-eccr-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))


(local (defthm lw-eccr-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-reciprocal-positive lw-eccr-left-commutes lw-eccr-left-distributes lw-eccr-fold-constants lw-eccr-times-negative lw-eccr-negative-times lw-eccr-zero-times lw-eccr-minus-one lw-eccr-double-negative lw-eccr-add-cancel lw-eccr-double lw-eccr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :nonlinearp t)) :rule-classes nil))

(local (defthm lw-eccr-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-reciprocal-positive lw-eccr-left-commutes lw-eccr-left-distributes lw-eccr-fold-constants lw-eccr-times-negative lw-eccr-negative-times lw-eccr-zero-times lw-eccr-minus-one lw-eccr-double-negative lw-eccr-add-cancel lw-eccr-double lw-eccr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :nonlinearp t)) :rule-classes nil))

(local (defthm lw-eccr-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-eccr-left-commutes)))))

(local
 (defthm lw-eccr-product-bound
   (implies (and (rationalp request) (rationalp cost) (<= 0 cost)
                 (rationalp budget) (<= 0 budget)
                 (<= request (* budget (/ (+ 1 cost)))))
            (<= (* cost request) budget))
    :hints (("Goal"
            :use ((:instance lw-eccr-multiply-order (a request) (b (* budget (/ (+ 1 cost)))) (factor cost))
                  (:instance lw-eccr-multiply-order (a cost) (b (+ 1 cost)) (factor (* (/ (+ 1 cost)) budget)))
                  (:instance lw-eccr-inverse-factor (divisor (+ 1 cost)) (coefficient budget)))
            :in-theory (union-theories
 '(fold-consts-in-+ lw-reciprocal-positive lw-eccr-left-commutes lw-eccr-left-distributes lw-eccr-fold-constants lw-eccr-times-negative lw-eccr-negative-times lw-eccr-zero-times lw-eccr-minus-one lw-eccr-double-negative lw-eccr-add-cancel lw-eccr-double lw-eccr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :nonlinearp t))
   :rule-classes nil))

(local
 (defthm lw-eccr-value-budget
   (implies (and (rationalp radius) (< 0 radius))
            (and (rationalp (lw-euler-circle-count-value-error radius)) (< 0 (lw-euler-circle-count-value-error radius)) (<= (* radius (lw-euler-circle-count-value-error radius)) 1/16)))
   :hints (("Goal"
            :use ((:instance lw-eccr-product-bound (cost radius) (request (lw-euler-circle-count-value-error radius)) (budget 1/16))
                  (:instance lw-reciprocal-positive (value (+ 1 radius))))
            :in-theory (union-theories
 '(fold-consts-in-+ lw-reciprocal-positive lw-euler-circle-count-value-error lw-eccr-left-commutes lw-eccr-left-distributes lw-eccr-fold-constants lw-eccr-times-negative lw-eccr-negative-times lw-eccr-zero-times lw-eccr-minus-one lw-eccr-double-negative lw-eccr-add-cancel lw-eccr-double lw-eccr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defthm lw-eccr-model-budget
   (implies (and (rationalp radius) (< 0 radius)
                 (rationalp left) (<= 0 left) (rationalp right) (<= 0 right)
                 (rationalp delta) (rationalp value-error) (< 0 value-error)
                 (<= (* radius value-error) 1/16)
                 (<= delta (* value-error (/ (+ 1 (+ left right))))))
            (<= (* radius (+ (* left delta) (* right delta) value-error)) 1/8))
   :hints (("Goal"
            :use ((:instance lw-eccr-product-bound
                    (cost (+ left right)) (request delta) (budget value-error)))
            :in-theory (union-theories
 '(fold-consts-in-+ lw-reciprocal-positive lw-eccr-left-commutes lw-eccr-left-distributes lw-eccr-fold-constants lw-eccr-times-negative lw-eccr-negative-times lw-eccr-zero-times lw-eccr-minus-one lw-eccr-double-negative lw-eccr-add-cancel lw-eccr-double lw-eccr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :nonlinearp t))
   :rule-classes nil))

(local
 (defthm lw-eccr-request-data
   (implies (and (rationalp radius) (< 0 radius)
                 (rationalp gap) (< 0 gap)
                 (rationalp anchor) (< 0 anchor) (<= anchor 1)
                 (rationalp cost) (<= 0 cost) (rationalp request) (< 0 request))
            (and (rationalp (lw-euler-circle-count-budget radius gap anchor cost request))
                 (< 0 (lw-euler-circle-count-budget radius gap anchor cost request))
                 (<= (lw-euler-circle-count-budget radius gap anchor cost request) request)
                 (<= (lw-euler-circle-count-budget radius gap anchor cost request) 1)
                 (<= (lw-euler-circle-count-budget radius gap anchor cost request) (* 1/4 anchor))
                 (<= (* gap (lw-euler-circle-count-budget radius gap anchor cost request)) anchor)
                 (<= (lw-euler-circle-count-budget radius gap anchor cost request) (* (lw-euler-circle-count-value-error radius) (/ (+ 1 cost))))))
   :hints (("Goal"
            :use (lw-eccr-value-budget
                  (:instance lw-reciprocal-positive (value (+ 1 gap)))
                  (:instance lw-reciprocal-positive (value (+ 1 cost)))
                  (:instance lw-eccr-product-bound (cost gap) (budget anchor)
                    (request (lw-euler-circle-count-budget radius gap anchor cost request))))
            :in-theory (union-theories
 '(fold-consts-in-+ lw-reciprocal-positive lw-euler-circle-count-budget min lw-eccr-left-commutes lw-eccr-left-distributes lw-eccr-fold-constants lw-eccr-times-negative lw-eccr-negative-times lw-eccr-zero-times lw-eccr-minus-one lw-eccr-double-negative lw-eccr-add-cancel lw-eccr-double lw-eccr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :nonlinearp t))
   :rule-classes nil))

(local
 (defthm lw-eccr-cost-positive
   (implies (and (rationalp gap) (< 0 gap)
                 (rationalp clearance) (< 0 clearance)
                 (rationalp cap) (< 0 cap))
            (and (rationalp (lw-disk-factor-quotient-cost gap clearance cap))
                 (<= 0 (lw-disk-factor-quotient-cost gap clearance cap))))
   :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-reciprocal-positive lw-disk-factor-quotient-cost lw-eccr-left-commutes lw-eccr-left-distributes lw-eccr-fold-constants lw-eccr-times-negative lw-eccr-negative-times lw-eccr-zero-times lw-eccr-minus-one lw-eccr-double-negative lw-eccr-add-cancel lw-eccr-double lw-eccr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
                   :nonlinearp t))
   :rule-classes nil))

(defthm lw-euler-circle-count-request-adequate
  (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
                (natp target) (rationalp request) (< 0 request))
           (and
            (<= (lw-euler-circle-count-request center radius plus-arcs minus-arcs request) request)
            (lw-euler-circle-count-modelp center radius plus-arcs minus-arcs target (lw-euler-circle-count-request center radius plus-arcs minus-arcs request) (lw-euler-circle-count-request center radius plus-arcs minus-arcs request) (lw-euler-circle-count-value-error radius))))
  :hints (("Goal"
           :use (lw-eccr-value-budget lw-euler-circle-outer-data
                 lw-euler-circle-global-quotient-cost-data
                 (:instance lw-eccr-cost-positive
                   (gap (- (lw-euler-circle-outer-radius center radius) radius))
                   (clearance (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs))) (cap (lw-euler-circle-global-derivative-cap center radius)))
                 (:instance lw-eccr-request-data (gap (lw-euler-circle-outer-gap center radius)) (anchor (lw-euler-circle-anchor-min plus-arcs minus-arcs)) (cost (+ (lw-euler-circle-global-quotient-cost center radius plus-arcs minus-arcs) (lw-disk-factor-quotient-cost
      (- (lw-euler-circle-outer-radius center radius) radius)
      (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs))
      (lw-euler-circle-global-derivative-cap center radius)))))
                 (:instance lw-eccr-model-budget (left (lw-disk-factor-quotient-cost
      (- (lw-euler-circle-outer-radius center radius) radius)
      (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs))
      (lw-euler-circle-global-derivative-cap center radius))) (right (lw-euler-circle-global-quotient-cost center radius plus-arcs minus-arcs)) (delta (lw-euler-circle-count-request center radius plus-arcs minus-arcs request)) (value-error (lw-euler-circle-count-value-error radius))))
           :in-theory (union-theories
 '(fold-consts-in-+ lw-euler-circle-count-request lw-euler-circle-count-modelp lw-euler-circle-count-quotient-error lw-eccr-left-commutes lw-eccr-left-distributes lw-eccr-fold-constants lw-eccr-times-negative lw-eccr-negative-times lw-eccr-zero-times lw-eccr-minus-one lw-eccr-double-negative lw-eccr-add-cancel lw-eccr-double lw-eccr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(defun lw-euler-circle-interior-count (center radius plus-arcs minus-arcs)
  (len (lw-circle-pole-roots (lw-euler-circle-factor-roots center radius 0 (lw-euler-circle-count-request center radius plus-arcs minus-arcs 1) (lw-euler-circle-count-request center radius plus-arcs minus-arcs 1)) radius)))

(defthm lw-euler-circle-request-count-exact
  (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
                (natp target) (rationalp request) (< 0 request))
           (equal (len (lw-circle-pole-roots (lw-euler-circle-factor-roots center radius target (lw-euler-circle-count-request center radius plus-arcs minus-arcs request) (lw-euler-circle-count-request center radius plus-arcs minus-arcs request)) radius))
                  (lw-euler-circle-interior-count center radius plus-arcs minus-arcs)))
  :hints (("Goal"
           :use (lw-euler-circle-count-request-adequate
                 (:instance lw-euler-circle-count-request-adequate (target 0) (request 1))
                 (:instance lw-euler-circle-interior-count-stable
                   (left-target target) (left-error (lw-euler-circle-count-request center radius plus-arcs minus-arcs request)) (left-epsilon (lw-euler-circle-count-request center radius plus-arcs minus-arcs request))
                   (right-target 0) (right-error (lw-euler-circle-count-request center radius plus-arcs minus-arcs 1)) (right-epsilon (lw-euler-circle-count-request center radius plus-arcs minus-arcs 1))
                   (value-error (lw-euler-circle-count-value-error radius))))
           :in-theory (union-theories
 '(fold-consts-in-+ lw-euler-circle-interior-count lw-eccr-left-commutes lw-eccr-left-distributes lw-eccr-fold-constants lw-eccr-times-negative lw-eccr-negative-times lw-eccr-zero-times lw-eccr-minus-one lw-eccr-double-negative lw-eccr-add-cancel lw-eccr-double lw-eccr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
