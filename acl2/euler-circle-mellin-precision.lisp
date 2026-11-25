(in-package "ACL2")

(include-book "euler-circle-mellin-coefficients")
(include-book "euler-circle-joint-model")

(defun lw-euler-circle-mellin-coefficient-gain (center radius anchor-error index)
  (lw-euler-circle-mellin-coefficient-error center radius anchor-error
               1 1 index 1 1 1 1))

(defun lw-euler-circle-mellin-block-gain (center radius anchor-error start count)
  (declare (xargs :measure (nfix count)
                  :hints (("Goal" :in-theory (theory 'ground-zero)))))
  (if (zp count) 0
    (max (abs (lw-euler-circle-mellin-coefficient-gain center radius anchor-error start))
         (lw-euler-circle-mellin-block-gain center radius anchor-error (+ 1 start) (- count 1)))))

(defun lw-euler-circle-mellin-precision (center radius anchor-error start count tolerance)
  (min 1 (/ tolerance (+ 1 (lw-euler-circle-mellin-block-gain center radius anchor-error start count)))))

(local (defthm lw-ecmp-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ecmp-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ecmp-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ecmp-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ecmp-times-negative (a b) (b a)))
                 :in-theory (disable lw-ecmp-times-negative)))))

(local (defthm lw-ecmp-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ecmp-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ecmp-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ecmp-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ecmp-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ecmp-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ecmp-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ecmp-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecmp-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ecmp-left-commutes)))))

(local
 (defthm lw-ecmp-rounding-scales
   (implies (and (rationalp cost) (<= 0 cost) (rationalp error)
                 (< 0 error) (<= error 1))
            (and (<= (lw-euler-rounding-precision cost error) error)
                 (equal (lw-euler-rounding-precision cost error)
                        (* error (lw-euler-rounding-precision cost 1)))))
   :hints (("Goal"
            :use ((:instance lw-positive-division-bound
                    (numerator error) (divisor (+ 2 (* 2 cost))) (bound error))
                  (:instance lw-positive-division-bound
                    (numerator 1) (divisor (+ 2 (* 2 cost))) (bound 1))
                  (:instance lw-ecmp-multiply-order
                    (a 1) (b (+ 2 (* 2 cost))) (factor error)))
            :in-theory
            (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-rounding-precision min
              lw-ecmp-left-commutes lw-ecmp-left-distributes lw-ecmp-fold-constants
              lw-ecmp-times-negative lw-ecmp-negative-times lw-ecmp-zero-times
              lw-ecmp-minus-one lw-ecmp-double-negative lw-ecmp-add-cancel lw-ecmp-double lw-ecmp-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :nonlinearp t
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-ecmp-nested-request-scales
   (implies (and (rationalp norm-cost) (<= 0 norm-cost)
                 (rationalp log-cost) (<= 0 log-cost)
                 (rationalp error) (< 0 error) (<= error 1))
            (let ((request (lw-euler-rounding-precision norm-cost error))
                  (unit-request (lw-euler-rounding-precision norm-cost 1)))
              (and (equal request (* error unit-request))
                   (equal (lw-euler-rounding-precision log-cost request)
                          (* error (lw-euler-rounding-precision log-cost unit-request))))))
   :hints (("Goal"
            :use ((:instance lw-euler-rounding-precision-valid
                    (cost norm-cost))
                  (:instance lw-euler-rounding-precision-valid
                    (cost norm-cost) (error 1))
                  (:instance lw-ecmp-rounding-scales (cost norm-cost))
                  (:instance lw-ecmp-rounding-scales
                    (cost log-cost) (error (lw-euler-rounding-precision norm-cost error)))
                  (:instance lw-ecmp-rounding-scales
                    (cost log-cost) (error (lw-euler-rounding-precision norm-cost 1))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              
              lw-ecmp-left-commutes lw-ecmp-left-distributes lw-ecmp-fold-constants
              lw-ecmp-times-negative lw-ecmp-negative-times lw-ecmp-zero-times
              lw-ecmp-minus-one lw-ecmp-double-negative lw-ecmp-add-cancel lw-ecmp-double lw-ecmp-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-euler-circle-native-requests-scale
   (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
                (lw-euler-value-clearance-check (car center) (cdr center) anchor-error)
                (< 3 (car center))
                 (rationalp error) (< 0 error) (<= error 1))
            (and (equal (lw-euler-normalized-request (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error error) (* error (lw-euler-normalized-request (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error 1)))
                 (equal (lw-euler-uniform-log-request (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error (lw-euler-normalized-request (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error error)) (* error (lw-euler-uniform-log-request (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error (lw-euler-normalized-request (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error 1))))))
   :hints (("Goal"
            :use (lw-euler-circle-outer-data
                  (:instance lw-euler-normalized-disk-data
                     (rate (car center)) (height (cdr center)) (outer-radius (lw-euler-circle-outer-radius center radius)))
                  (:instance lw-euler-uniform-log-model-data
                     (rate (car center)) (height (cdr center)) (outer-radius (lw-euler-circle-outer-radius center radius)) (error 1))
                  (:instance lw-ecmp-nested-request-scales (norm-cost (lw-euler-normalized-total-cost (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error)) (log-cost (lw-euler-uniform-log-model-cost (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-normalized-request lw-euler-uniform-log-request
              lw-ecmp-left-commutes lw-ecmp-left-distributes lw-ecmp-fold-constants
              lw-ecmp-times-negative lw-ecmp-negative-times lw-ecmp-zero-times
              lw-ecmp-minus-one lw-ecmp-double-negative lw-ecmp-add-cancel lw-ecmp-double lw-ecmp-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
  :rule-classes nil)

(defthm lw-euler-circle-mellin-coefficient-error-scales
  (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
                (lw-euler-value-clearance-check (car center) (cdr center) anchor-error)
                (< 3 (car center))
                (natp index) (rationalp error) (< 0 error) (<= error 1))
           (equal (lw-euler-circle-mellin-coefficient-error center radius anchor-error
               error error index error error error error) (* error (lw-euler-circle-mellin-coefficient-gain center radius anchor-error index))))
  :hints (("Goal"
           :use (lw-euler-circle-native-requests-scale lw-euler-circle-outer-data)
           :in-theory
           (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-circle-mellin-coefficient-gain lw-euler-circle-mellin-coefficient-error
              lw-euler-mellin-quadratic-log-error lw-euler-mellin-quadratic-transport-error
              lw-euler-circle-center-coefficient-error lw-euler-circle-center-native-quotient-error
              lw-rational-power-rational
              lw-ecmp-left-commutes lw-ecmp-left-distributes lw-ecmp-fold-constants
              lw-ecmp-times-negative lw-ecmp-negative-times lw-ecmp-zero-times
              lw-ecmp-minus-one lw-ecmp-double-negative lw-ecmp-add-cancel lw-ecmp-double lw-ecmp-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm lw-ecmp-model-gain-number
   (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
                (lw-euler-value-clearance-check (car center) (cdr center) anchor-error)
                (< 3 (car center)) (natp index))
            (rationalp (lw-euler-circle-mellin-coefficient-gain center radius anchor-error index)))
   :hints (("Goal"
            :use (lw-euler-circle-outer-data
                  (:instance lw-zeta-residue-denominator-rational (zero (cons (car center) (cdr center))))
                  (:instance lw-euler-circle-joint-request-adequate (request 1) (target 0))
                  (:instance lw-euler-circle-center-model-data
                    (target 0) (error (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error 1)) (epsilon (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error 1)))
                  lw-euler-circle-global-derivative-cap-data
                  (:instance lw-euler-local-normalized-data
                     (rate (car center)) (height (cdr center)) (outer-radius (lw-euler-circle-outer-radius center radius)))
                  (:instance lw-euler-normalized-disk-data
                     (rate (car center)) (height (cdr center)) (outer-radius (lw-euler-circle-outer-radius center radius)))
                  (:instance lw-euler-normalized-request-data
                     (rate (car center)) (height (cdr center)) (outer-radius (lw-euler-circle-outer-radius center radius)) (error 1))
                  (:instance lw-euler-uniform-log-model-data
                     (rate (car center)) (height (cdr center)) (outer-radius (lw-euler-circle-outer-radius center radius)) (error (lw-euler-normalized-request (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error 1))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-circle-mellin-coefficient-gain lw-euler-circle-mellin-coefficient-error
              lw-euler-mellin-quadratic-log-error lw-euler-mellin-quadratic-transport-error
              lw-euler-circle-center-coefficient-error lw-euler-circle-center-native-quotient-error
              lw-disk-factor-quotient-cost lw-mellin-quadratic-cap lw-normalized-local-point-cap
              lw-complex-l1 lw-complex-sub lw-complex-scale lw-complex-mul lw-complexp lw-zeta-residue-denominator
              abs lw-rational-power-rational
              lw-ecmp-left-commutes lw-ecmp-left-distributes lw-ecmp-fold-constants
              lw-ecmp-times-negative lw-ecmp-negative-times lw-ecmp-zero-times
              lw-ecmp-minus-one lw-ecmp-double-negative lw-ecmp-add-cancel lw-ecmp-double lw-ecmp-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-ecmp-block-gain-data
   (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
                (lw-euler-value-clearance-check (car center) (cdr center) anchor-error)
                (< 3 (car center)) (natp start) (natp count))
            (and (rationalp (lw-euler-circle-mellin-block-gain center radius anchor-error start count)) (<= 0 (lw-euler-circle-mellin-block-gain center radius anchor-error start count))
                 (implies (and (natp index) (<= start index) (< index (+ start count)))
                          (<= (lw-euler-circle-mellin-coefficient-gain center radius anchor-error index) (lw-euler-circle-mellin-block-gain center radius anchor-error start count)))))
   :hints (("Goal"
            :induct (lw-euler-circle-mellin-block-gain center radius anchor-error start count)
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-circle-mellin-block-gain max abs
              lw-ecmp-left-commutes lw-ecmp-left-distributes lw-ecmp-fold-constants
              lw-ecmp-times-negative lw-ecmp-negative-times lw-ecmp-zero-times
              lw-ecmp-minus-one lw-ecmp-double-negative lw-ecmp-add-cancel lw-ecmp-double lw-ecmp-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory)))
           (and stable-under-simplificationp
                '(:use ((:instance lw-ecmp-model-gain-number (index start))
                        lw-ecmp-model-gain-number)
                  :do-not-induct t)))
   :rule-classes nil))

(defthm lw-euler-circle-mellin-block-precision-adequate
  (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
                (lw-euler-value-clearance-check (car center) (cdr center) anchor-error)
                (< 3 (car center))
                (natp start) (natp count) (natp index)
                (<= start index) (< index (+ start count))
                (rationalp tolerance) (< 0 tolerance))
           (let ((error (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error (lw-euler-circle-mellin-precision center radius anchor-error start count tolerance))))
             (and (rationalp (lw-euler-circle-mellin-precision center radius anchor-error start count tolerance))
                  (< 0 (lw-euler-circle-mellin-precision center radius anchor-error start count tolerance))
                  (rationalp error) (< 0 error) (<= error 1) (<= error tolerance)
                  (<= (lw-euler-circle-mellin-coefficient-error center radius anchor-error
               error error index error error error error) tolerance))))
  :hints (("Goal"
           :use (lw-ecmp-block-gain-data lw-ecmp-model-gain-number
                 (:instance lw-euler-circle-joint-request-adequate (request (lw-euler-circle-mellin-precision center radius anchor-error start count tolerance)) (target 0))
                 (:instance lw-euler-circle-mellin-coefficient-error-scales (error (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error (lw-euler-circle-mellin-precision center radius anchor-error start count tolerance))))
                 (:instance lw-ecmp-multiply-order
                   (a (lw-euler-circle-mellin-coefficient-gain center radius anchor-error index)) (b (lw-euler-circle-mellin-block-gain center radius anchor-error start count)) (factor (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error (lw-euler-circle-mellin-precision center radius anchor-error start count tolerance))))
                 (:instance lw-ecmp-multiply-order
                   (a (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error (lw-euler-circle-mellin-precision center radius anchor-error start count tolerance))) (b (/ tolerance (+ 1 (lw-euler-circle-mellin-block-gain center radius anchor-error start count)))) (factor (lw-euler-circle-mellin-block-gain center radius anchor-error start count)))
                 (:instance lw-ecmp-multiply-order
                   (a (lw-euler-circle-mellin-block-gain center radius anchor-error start count)) (b (+ 1 (lw-euler-circle-mellin-block-gain center radius anchor-error start count))) (factor (/ tolerance (+ 1 (lw-euler-circle-mellin-block-gain center radius anchor-error start count)))))
                 (:instance lw-ecmp-multiply-order
                   (a 1) (b (+ 1 (lw-euler-circle-mellin-block-gain center radius anchor-error start count))) (factor (/ tolerance (+ 1 (lw-euler-circle-mellin-block-gain center radius anchor-error start count)))))
                 (:instance lw-ecmp-inverse-factor (divisor (+ 1 (lw-euler-circle-mellin-block-gain center radius anchor-error start count))) (coefficient tolerance)))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-circle-mellin-precision min lw-reciprocal-positive
              lw-ecmp-left-commutes lw-ecmp-left-distributes lw-ecmp-fold-constants
              lw-ecmp-times-negative lw-ecmp-negative-times lw-ecmp-zero-times
              lw-ecmp-minus-one lw-ecmp-double-negative lw-ecmp-add-cancel lw-ecmp-double lw-ecmp-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
