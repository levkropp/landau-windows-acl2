(in-package "ACL2")

(include-book "euler-circle-empty-log-model")
(include-book "euler-circle-log-at-one")
(include-book "polynomial-coefficient-maps")
(include-book "polynomial-geometric-bounds")

(defun lw-euler-circle-reflected-log-polynomial (center radius plus-arcs minus-arcs anchor-error request approximation-error)
  (lw-polynomial-rescale (lw-euler-circle-empty-log-polynomial center radius plus-arcs minus-arcs anchor-error request approximation-error) (- (/ radius)) 0))

(defun lw-euler-circle-reflected-log-cap (center radius plus-arcs minus-arcs inner)
  (* (+ 1 (lw-euler-circle-factor-sum-cap center radius plus-arcs minus-arcs)) (lw-geometric-disk-gain (/ inner radius))))

(local (defthm lw-ecrl-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ecrl-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ecrl-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ecrl-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ecrl-times-negative (a b) (b a)))
                 :in-theory (disable lw-ecrl-times-negative)))))

(local (defthm lw-ecrl-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ecrl-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ecrl-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ecrl-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ecrl-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ecrl-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ecrl-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ecrl-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecrl-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecrl-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ecrl-left-commutes)))))

(local
 (defthm lw-ecrl-scale-opposite
   (implies (and (rationalp radius) (< 0 radius))
            (equal (* radius (- (/ radius))) -1))
   :hints (("Goal"
            :use ((:instance inverse-of-* (x radius)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-reciprocal-positive
              lw-ecrl-left-commutes lw-ecrl-left-distributes lw-ecrl-fold-constants
              lw-ecrl-times-negative lw-ecrl-negative-times lw-ecrl-zero-times
              lw-ecrl-minus-one lw-ecrl-double-negative lw-ecrl-add-cancel lw-ecrl-double lw-ecrl-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defthm lw-ecrl-unit-shift-data
   (implies (and (rationalp radius) (< 0 radius) (lw-complex-diskp point radius))
            (and (lw-complex-diskp (lw-complex-scale (- (/ radius)) point) 1)
                 (equal (lw-complex-scale radius (lw-complex-scale (- (/ radius)) point)) (lw-complex-scale -1 point))))
   :hints (("Goal"
            :use (lw-complex-disk-data
                  (:instance lw-complex-scale-disk (factor (- (/ radius))))
                  (:instance lw-complex-scale-compose (left radius) (right (- (/ radius))))
                  lw-ecrl-scale-opposite
                  (:instance inverse-of-* (x radius)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              abs lw-reciprocal-positive
              lw-ecrl-left-commutes lw-ecrl-left-distributes lw-ecrl-fold-constants
              lw-ecrl-times-negative lw-ecrl-negative-times lw-ecrl-zero-times
              lw-ecrl-minus-one lw-ecrl-double-negative lw-ecrl-add-cancel lw-ecrl-double lw-ecrl-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-euler-circle-reflected-log-comparison
  (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
                (lw-euler-value-clearance-check (car center) (cdr center) anchor-error)
                (equal (lw-euler-circle-interior-count center radius plus-arcs minus-arcs) 0)
                (rationalp request) (< 0 request)
                (rationalp approximation-error) (< 0 approximation-error) (lw-complex-diskp point radius))
           (and (lw-complex-coefficientsp (lw-euler-circle-reflected-log-polynomial center radius plus-arcs minus-arcs anchor-error request approximation-error))
                (lw-complex-diskp (lw-complex-sub (lw-polynomial-factor-log-sum (lw-euler-circle-factor-roots center radius 0 (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)) (lw-complex-scale -1 point)) (lw-complex-polynomial (lw-euler-circle-reflected-log-polynomial center radius plus-arcs minus-arcs anchor-error request approximation-error) point 0)) approximation-error)))
  :hints (("Goal"
           :use (lw-euler-circle-outer-data lw-ecrl-unit-shift-data
                 (:instance lw-complex-disk-data (radius radius))
                 (:instance lw-euler-circle-empty-log-polynomial-comparison (point (lw-complex-scale (- (/ radius)) point)))
                 (:instance lw-polynomial-rescale-valid (coefficients (lw-euler-circle-empty-log-polynomial center radius plus-arcs minus-arcs anchor-error request approximation-error)) (factor (- (/ radius))) (offset 0))
                 (:instance lw-polynomial-rescale-evaluation (coefficients (lw-euler-circle-empty-log-polynomial center radius plus-arcs minus-arcs anchor-error request approximation-error)) (factor (- (/ radius))) (offset 0)))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-circle-reflected-log-polynomial
              lw-ecrl-left-commutes lw-ecrl-left-distributes lw-ecrl-fold-constants
              lw-ecrl-times-negative lw-ecrl-negative-times lw-ecrl-zero-times
              lw-ecrl-minus-one lw-ecrl-double-negative lw-ecrl-add-cancel lw-ecrl-double lw-ecrl-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm lw-ecrl-inner-unit-data
   (implies (and (rationalp radius) (rationalp inner) (<= 0 inner) (< inner radius)
                 (lw-complex-diskp point inner))
            (and (rationalp (/ inner radius)) (<= 0 (/ inner radius)) (< (/ inner radius) 1)
                 (lw-complex-diskp (lw-complex-scale (- (/ radius)) point) (/ inner radius))))
   :hints (("Goal"
            :use ((:instance lw-complex-scale-disk (factor (- (/ radius))) (radius inner))
                  (:instance lw-ecrl-multiply-order (a 0) (b inner) (factor (/ radius)))
                  (:instance lw-ecrl-multiply-order (a inner) (b radius) (factor (/ radius)))
                  (:instance lw-ecrl-positive-product (a (- radius inner)) (b (/ radius)))
                  (:instance inverse-of-* (x radius)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              abs lw-reciprocal-positive
              lw-ecrl-left-commutes lw-ecrl-left-distributes lw-ecrl-fold-constants
              lw-ecrl-times-negative lw-ecrl-negative-times lw-ecrl-zero-times
              lw-ecrl-minus-one lw-ecrl-double-negative lw-ecrl-add-cancel lw-ecrl-double lw-ecrl-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-euler-circle-reflected-log-bound
  (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
                (lw-euler-value-clearance-check (car center) (cdr center) anchor-error)
                (equal (lw-euler-circle-interior-count center radius plus-arcs minus-arcs) 0)
                (rationalp request) (< 0 request)
                (rationalp approximation-error) (< 0 approximation-error) (<= approximation-error 1)
                (rationalp inner) (<= 0 inner) (< inner radius)
                (lw-complex-diskp point inner))
           (lw-complex-diskp (lw-complex-polynomial (lw-euler-circle-reflected-log-polynomial center radius plus-arcs minus-arcs anchor-error request approximation-error) point 0) (lw-euler-circle-reflected-log-cap center radius plus-arcs minus-arcs inner)))
  :hints (("Goal"
           :use (lw-euler-circle-empty-log-polynomial-caps lw-ecrl-inner-unit-data lw-euler-circle-outer-data
                 lw-euler-circle-factor-sum-cap-data
                 (:instance lw-geometric-disk-gain-data (radius (/ inner radius)))
                 (:instance lw-complex-disk-data (radius inner))
                 (:instance lw-complex-polynomial-geometric-tail-bound
                   (coefficients (lw-euler-circle-empty-log-polynomial center radius plus-arcs minus-arcs anchor-error request approximation-error)) (point (lw-complex-scale (- (/ radius)) point))
                   (radius (/ inner radius)) (cap (+ 1 (lw-euler-circle-factor-sum-cap center radius plus-arcs minus-arcs))) (offset 0))
                 (:instance lw-polynomial-rescale-evaluation (coefficients (lw-euler-circle-empty-log-polynomial center radius plus-arcs minus-arcs anchor-error request approximation-error)) (factor (- (/ radius))) (offset 0)))
           :expand ((lw-rational-power (/ inner radius) 0))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-circle-reflected-log-polynomial lw-euler-circle-reflected-log-cap
              lw-ecrl-left-commutes lw-ecrl-left-distributes lw-ecrl-fold-constants
              lw-ecrl-times-negative lw-ecrl-negative-times lw-ecrl-zero-times
              lw-ecrl-minus-one lw-ecrl-double-negative lw-ecrl-add-cancel lw-ecrl-double lw-ecrl-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm lw-ecrl-real-pair
   (implies (rationalp value) (lw-complexp (cons value 0)))
   :hints (("Goal" :in-theory
             (union-theories '(lw-complexp car-cons cdr-cons)
                             (theory 'minimal-theory))))))

(local
 (defthm lw-ecrl-anchor-shift
   (implies (and (rationalp rate) (< 1 rate) (rationalp radius) (<= (- rate 1) radius))
            (and (lw-complex-diskp (cons (- rate 1) 0) radius)
                 (equal (lw-complex-scale -1 (cons (- rate 1) 0)) (cons (- 1 rate) 0))))
   :hints (("Goal"
            :use ((:instance lw-complex-disk-norm-square (point (cons (- rate 1) 0)))
                  (:instance lw-ecrl-multiply-order (a (- rate 1)) (b radius) (factor radius))
                  (:instance lw-ecrl-multiply-order (a (- rate 1)) (b radius) (factor (- rate 1))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complexp lw-complex-norm-square lw-complex-scale
              lw-ecrl-left-commutes lw-ecrl-left-distributes lw-ecrl-fold-constants
              lw-ecrl-times-negative lw-ecrl-negative-times lw-ecrl-zero-times
              lw-ecrl-minus-one lw-ecrl-double-negative lw-ecrl-add-cancel lw-ecrl-double lw-ecrl-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-euler-circle-reflected-log-at-one
  (implies (and (lw-euler-circle-coverp (cons rate 0) radius plus-arcs minus-arcs)
                (lw-euler-value-clearance-check rate 0 anchor-error)
                (equal (lw-euler-circle-interior-count (cons rate 0) radius plus-arcs minus-arcs) 0)
                (rationalp request) (< 0 request)
                (rationalp approximation-error) (< 0 approximation-error)
                (rationalp rate) (< 1 rate) (<= (- rate 1) radius)
                (rationalp value-error) (< 0 value-error) (<= value-error 1/4))
           (lw-complex-diskp (lw-complex-sub (lw-complex-polynomial (lw-euler-circle-reflected-log-polynomial (cons rate 0) radius plus-arcs minus-arcs anchor-error request approximation-error) (cons (- rate 1) 0) 0) (cons (car (lw-euler-bounds value-error)) 0))
                             (+ approximation-error
                                (lw-euler-circle-at-one-log-error rate radius (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request) value-error))))
  :hints (("Goal"
           :use (lw-ecrl-anchor-shift
                 (:instance lw-euler-circle-outer-data (center (cons rate 0)))
                 (:instance lw-euler-circle-global-polynomials-valid
                   (center (cons rate 0)) (target 0) (error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)))
                 (:instance lw-euler-bounds-interval (epsilon value-error))
                 (:instance lw-euler-circle-reflected-log-comparison (center (cons rate 0)) (point (cons (- rate 1) 0)))
                 (:instance lw-euler-circle-joint-request-adequate (center (cons rate 0)) (target 0))
                 (:instance lw-euler-circle-anchor-min-data (center (cons rate 0)) (point (cons 1 0)))
                 (:instance lw-euler-circle-factor-log-at-one (target 0) (error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) (epsilon (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)))
                 (:instance lw-complex-polynomial-rational
                   (coefficients (lw-euler-circle-reflected-log-polynomial (cons rate 0) radius plus-arcs minus-arcs anchor-error request approximation-error))
                   (point (cons (- rate 1) 0)) (offset 0))
                 (:instance lw-polynomial-disk-factor-data (coefficients (lw-euler-circle-global-polynomial (cons rate 0) radius 0 (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request))) (outer-radius (lw-euler-circle-outer-radius (cons rate 0) radius)) (epsilon (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)))
                 (:instance lw-polynomial-factor-log-sum-rational
                   (roots (lw-euler-circle-factor-roots (cons rate 0) radius 0 (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request))) (point (cons (- 1 rate) 0)))
                 (:instance lw-complex-difference-symmetric
                   (left (lw-polynomial-factor-log-sum (lw-euler-circle-factor-roots (cons rate 0) radius 0 (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) (cons (- 1 rate) 0))) (right (lw-complex-polynomial (lw-euler-circle-reflected-log-polynomial (cons rate 0) radius plus-arcs minus-arcs anchor-error request approximation-error) (cons (- rate 1) 0) 0)) (radius approximation-error))
                 (:instance lw-complex-difference-triangle
                   (left (lw-complex-polynomial (lw-euler-circle-reflected-log-polynomial (cons rate 0) radius plus-arcs minus-arcs anchor-error request approximation-error) (cons (- rate 1) 0) 0)) (middle (lw-polynomial-factor-log-sum (lw-euler-circle-factor-roots (cons rate 0) radius 0 (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) (cons (- 1 rate) 0))) (right (cons (car (lw-euler-bounds value-error)) 0))
                   (radius approximation-error)
                   (other-radius (lw-euler-circle-at-one-log-error rate radius (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request) value-error))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-circle-center-modelp lw-euler-circle-factor-roots
              lw-intervalp lw-ecrl-real-pair (:executable-counterpart lw-complex-diskp)
              (:executable-counterpart lw-complex-norm-square)
              lw-ecrl-left-commutes lw-ecrl-left-distributes lw-ecrl-fold-constants
              lw-ecrl-times-negative lw-ecrl-negative-times lw-ecrl-zero-times
              lw-ecrl-minus-one lw-ecrl-double-negative lw-ecrl-add-cancel lw-ecrl-double lw-ecrl-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
