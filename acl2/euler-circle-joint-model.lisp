(in-package "ACL2")

(include-book "circle-interior-pole-power-sums")
(include-book "euler-circle-center-clearance")

; One model request meets the outer contour, collar and center budgets.
(defun lw-euler-circle-joint-input-request (center radius plus-arcs minus-arcs anchor-error request)
  (min request
       (min (lw-euler-circle-center-margin-size center anchor-error)
            (min (* anchor-error (/ (+ 1 (lw-euler-circle-outer-gap center radius))))
                 (* 1/8 (lw-euler-circle-anchor-min plus-arcs minus-arcs) (/ (+ 1 (lw-euler-circle-outer-gap center radius))))))))

(defun lw-euler-circle-joint-request (center radius plus-arcs minus-arcs anchor-error request)
  (lw-euler-circle-count-request center radius plus-arcs minus-arcs (lw-euler-circle-joint-input-request center radius plus-arcs minus-arcs anchor-error request)))

(local (defthm lw-ecjm-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ecjm-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ecjm-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ecjm-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ecjm-times-negative (a b) (b a)))
                 :in-theory (disable lw-ecjm-times-negative)))))

(local (defthm lw-ecjm-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ecjm-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ecjm-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ecjm-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ecjm-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ecjm-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ecjm-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ecjm-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecjm-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecjm-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ecjm-left-commutes)))))
(local
 (defthm lw-ecjm-cost-budget
   (implies (and (rationalp gap) (< 0 gap) (rationalp cap) (< 0 cap)
                 (rationalp delta) (< 0 delta)
                 (<= delta (* cap (/ (+ 1 gap)))))
            (and (<= delta cap) (<= (* gap delta) cap)))
   :hints (("Goal"
            :use ((:instance lw-ecjm-multiply-order
                    (a delta) (b (* cap (/ (+ 1 gap)))) (factor gap))
                  (:instance lw-ecjm-multiply-order
                    (a gap) (b (+ 1 gap)) (factor (* (/ (+ 1 gap)) cap)))
                  (:instance lw-ecjm-multiply-order
                    (a 1) (b (+ 1 gap)) (factor (* (/ (+ 1 gap)) cap)))
                  (:instance lw-ecjm-inverse-factor (divisor (+ 1 gap)) (coefficient cap)))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-reciprocal-positive lw-ecjm-left-commutes lw-ecjm-left-distributes lw-ecjm-fold-constants lw-ecjm-times-negative lw-ecjm-negative-times lw-ecjm-zero-times lw-ecjm-minus-one lw-ecjm-double-negative lw-ecjm-add-cancel lw-ecjm-double lw-ecjm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :nonlinearp t :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-ecjm-input-data
   (implies (and (rationalp gap) (< 0 gap)
                 (rationalp cap) (< 0 cap)
                 (rationalp anchor) (< 0 anchor)
                 (rationalp margin) (< 0 margin)
                 (rationalp request) (< 0 request))
            (let ((budget (min request (min margin (min (* cap (/ (+ 1 gap))) (* 1/8 anchor (/ (+ 1 gap))))))))
              (and (rationalp budget) (< 0 budget)
                   (<= budget request) (<= budget margin)
                   (<= budget (* cap (/ (+ 1 gap))))
                   (<= budget (* 1/8 anchor (/ (+ 1 gap)))))))
   :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) min lw-reciprocal-positive lw-ecjm-left-commutes lw-ecjm-left-distributes lw-ecjm-fold-constants lw-ecjm-times-negative lw-ecjm-negative-times lw-ecjm-zero-times lw-ecjm-minus-one lw-ecjm-double-negative lw-ecjm-add-cancel lw-ecjm-double lw-ecjm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
                   :nonlinearp t :do-not-induct t))
   :rule-classes nil))

(defthm lw-euler-circle-joint-request-adequate
  (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
                (lw-euler-value-clearance-check (car center) (cdr center) anchor-error)
                (natp target) (rationalp request) (< 0 request))
           (and (rationalp (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)) (< 0 (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)) (<= (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request) request)
                (<= (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request) anchor-error)
                (lw-euler-circle-center-modelp center radius plus-arcs minus-arcs target (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request) anchor-error)
                (<= (* (lw-euler-circle-outer-gap center radius) (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)) (* 1/8 (lw-euler-circle-anchor-min plus-arcs minus-arcs)))
                (<= (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request) (* 1/8 (lw-euler-circle-anchor-min plus-arcs minus-arcs)))
                (equal (len (lw-circle-pole-roots (lw-euler-circle-factor-roots center radius target (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)) radius)) (lw-euler-circle-interior-count center radius plus-arcs minus-arcs))))
  :hints (("Goal"
           :use (lw-euler-circle-outer-data
                 (:instance lw-euler-neighborhood-data (rate (car center)) (height (cdr center)) (outer-radius (lw-euler-circle-outer-radius center radius)))
                 (:instance lw-euler-circle-anchor-min-data (point (cons 1 0)))
                 (:instance lw-ecjm-input-data (gap (lw-euler-circle-outer-gap center radius)) (cap anchor-error) (anchor (lw-euler-circle-anchor-min plus-arcs minus-arcs)) (margin (lw-euler-circle-center-margin-size center anchor-error)))
                 (:instance lw-euler-circle-count-request-adequate (request (lw-euler-circle-joint-input-request center radius plus-arcs minus-arcs anchor-error request)))
                 (:instance lw-euler-circle-request-count-exact (request (lw-euler-circle-joint-input-request center radius plus-arcs minus-arcs anchor-error request)))
                 (:instance lw-ecjm-cost-budget (gap (lw-euler-circle-outer-gap center radius)) (cap anchor-error) (delta (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)))
                 (:instance lw-ecjm-cost-budget (gap (lw-euler-circle-outer-gap center radius)) (cap (* 1/8 (lw-euler-circle-anchor-min plus-arcs minus-arcs))) (delta (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request))))
           :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-euler-circle-joint-input-request lw-euler-circle-joint-request lw-euler-circle-center-modelp lw-euler-circle-count-modelp lw-euler-circle-center-margin-size (:executable-counterpart lw-complex-norm-square) lw-ecjm-left-commutes lw-ecjm-left-distributes lw-ecjm-fold-constants lw-ecjm-times-negative lw-ecjm-negative-times lw-ecjm-zero-times lw-ecjm-minus-one lw-ecjm-double-negative lw-ecjm-add-cancel lw-ecjm-double lw-ecjm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm lw-ecjm-square-nonnegative
   (implies (rationalp value) (<= 0 (* value value)))
   :hints (("Goal"
            :cases ((< value 0))
            :use ((:instance lw-ecjm-multiply-order (a 0) (b value) (factor value))
                  (:instance lw-ecjm-multiply-order (a 0) (b (- value)) (factor (- value))))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) consp lw-ecjm-left-commutes lw-ecjm-left-distributes lw-ecjm-fold-constants lw-ecjm-times-negative lw-ecjm-negative-times lw-ecjm-zero-times lw-ecjm-minus-one lw-ecjm-double-negative lw-ecjm-add-cancel lw-ecjm-double lw-ecjm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes :linear))

(local
 (defthm lw-ecjm-selected-nonzero
   (implies (and (lw-circle-exterior-rootsp roots inner-radius)
                 (rationalp inner-radius))
            (lw-circle-exterior-rootsp (lw-circle-pole-roots roots radius) 0))
   :hints (("Goal" :induct (lw-circle-pole-roots roots radius)
                   :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-circle-pole-roots lw-circle-exterior-rootsp endp lw-ecjm-square-nonnegative lw-ecjm-left-commutes lw-ecjm-left-distributes lw-ecjm-fold-constants lw-ecjm-times-negative lw-ecjm-negative-times lw-ecjm-zero-times lw-ecjm-minus-one lw-ecjm-double-negative lw-ecjm-add-cancel lw-ecjm-double lw-ecjm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
                   :do-not '(generalize fertilize)))))

(defthm lw-euler-circle-joint-root-data
  (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
                (lw-euler-value-clearance-check (car center) (cdr center) anchor-error)
                (natp target) (rationalp request) (< 0 request))
           (and (rationalp (- radius (lw-euler-circle-collar-width center radius plus-arcs minus-arcs))) (< 0 (- radius (lw-euler-circle-collar-width center radius plus-arcs minus-arcs))) (< (- radius (lw-euler-circle-collar-width center radius plus-arcs minus-arcs)) radius)
                (lw-circle-interior-rootsp (lw-circle-pole-roots (lw-euler-circle-factor-roots center radius target (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)) radius) (- radius (lw-euler-circle-collar-width center radius plus-arcs minus-arcs)))
                (lw-circle-exterior-rootsp (lw-circle-pole-roots (lw-euler-circle-factor-roots center radius target (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)) radius) 0)
                (equal (len (lw-circle-pole-roots (lw-euler-circle-factor-roots center radius target (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)) radius)) (lw-euler-circle-interior-count center radius plus-arcs minus-arcs))))
  :hints (("Goal"
           :use (lw-euler-circle-joint-request-adequate
                 (:instance lw-euler-circle-interior-collar (error (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)) (epsilon (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)))
                 (:instance lw-euler-circle-center-model-data (error (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)) (epsilon (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)))
                 (:instance lw-euler-circle-center-roots-exterior (error (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)) (epsilon (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)))
                 (:instance lw-ecjm-selected-nonzero (roots (lw-euler-circle-factor-roots center radius target (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request))) (inner-radius (lw-euler-circle-center-radius center radius anchor-error))))
           :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) consp lw-ecjm-left-commutes lw-ecjm-left-distributes lw-ecjm-fold-constants lw-ecjm-times-negative lw-ecjm-negative-times lw-ecjm-zero-times lw-ecjm-minus-one lw-ecjm-double-negative lw-ecjm-add-cancel lw-ecjm-double lw-ecjm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(defthm lw-euler-circle-joint-large-index-data
  (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
                (lw-euler-value-clearance-check (car center) (cdr center) anchor-error)
                (natp target) (rationalp request) (< 0 request) (< 0 (lw-euler-circle-interior-count center radius plus-arcs minus-arcs)) (natp start))
           (and (natp (lw-circle-interior-pole-large-index (lw-circle-pole-roots (lw-euler-circle-factor-roots center radius target (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)) radius) (- radius (lw-euler-circle-collar-width center radius plus-arcs minus-arcs)) start)) (<= start (lw-circle-interior-pole-large-index (lw-circle-pole-roots (lw-euler-circle-factor-roots center radius target (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)) radius) (- radius (lw-euler-circle-collar-width center radius plus-arcs minus-arcs)) start)) (< (lw-circle-interior-pole-large-index (lw-circle-pole-roots (lw-euler-circle-factor-roots center radius target (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)) radius) (- radius (lw-euler-circle-collar-width center radius plus-arcs minus-arcs)) start) (+ start (lw-euler-circle-interior-count center radius plus-arcs minus-arcs)))
                (not (lw-complex-diskp
                  (lw-circle-exterior-coefficient (lw-circle-pole-roots (lw-euler-circle-factor-roots center radius target (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)) radius) -1 (lw-circle-interior-pole-large-index (lw-circle-pole-roots (lw-euler-circle-factor-roots center radius target (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)) radius) (- radius (lw-euler-circle-collar-width center radius plus-arcs minus-arcs)) start))
                  (* (lw-power-large-term-cap (lw-circle-interior-pole-power-system (lw-circle-pole-roots (lw-euler-circle-factor-roots center radius target (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)) radius) (- radius (lw-euler-circle-collar-width center radius plus-arcs minus-arcs))) start)
                     (/ (lw-rational-power (- radius (lw-euler-circle-collar-width center radius plus-arcs minus-arcs)) (+ 1 (lw-circle-interior-pole-large-index (lw-circle-pole-roots (lw-euler-circle-factor-roots center radius target (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)) radius) (- radius (lw-euler-circle-collar-width center radius plus-arcs minus-arcs)) start)))))))))
  :hints (("Goal"
           :use (lw-euler-circle-joint-root-data
                 (:instance lw-circle-interior-pole-large-index-data (roots (lw-circle-pole-roots (lw-euler-circle-factor-roots center radius target (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)) radius)) (radius (- radius (lw-euler-circle-collar-width center radius plus-arcs minus-arcs)))))
           :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) len lw-ecjm-left-commutes lw-ecjm-left-distributes lw-ecjm-fold-constants lw-ecjm-times-negative lw-ecjm-negative-times lw-ecjm-zero-times lw-ecjm-minus-one lw-ecjm-double-negative lw-ecjm-add-cancel lw-ecjm-double lw-ecjm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
