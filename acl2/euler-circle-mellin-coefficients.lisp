(in-package "ACL2")

(include-book "euler-circle-center-split-coefficients")
(include-book "euler-mellin-quadratic-model")

(defun lw-euler-circle-mellin-coefficient-error (center radius anchor-error error epsilon index extraction-error coefficient-error model-error value-error)
  (+ (lw-euler-mellin-quadratic-log-error (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error index coefficient-error model-error) (* (lw-euler-circle-center-coefficient-error center radius anchor-error error epsilon extraction-error (lw-euler-normalized-request (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error model-error) value-error)
              (/ (lw-rational-power (lw-euler-circle-center-radius center radius anchor-error) (+ 2 index))))))

(local (defthm lw-ecmc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ecmc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ecmc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ecmc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ecmc-times-negative (a b) (b a)))
                 :in-theory (disable lw-ecmc-times-negative)))))

(local (defthm lw-ecmc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ecmc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ecmc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ecmc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ecmc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ecmc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ecmc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))


(local
 (defthm lw-ecmc-add-difference
   (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp value))
            (equal (lw-complex-add (lw-complex-sub a (lw-complex-scale -1 value))
                                   (lw-complex-sub b value))
                   (lw-complex-add a b)))
   :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-complexp lw-complex-sub lw-complex-add lw-complex-scale consp lw-ecmc-left-commutes lw-ecmc-left-distributes lw-ecmc-fold-constants lw-ecmc-times-negative lw-ecmc-negative-times lw-ecmc-zero-times lw-ecmc-minus-one lw-ecmc-double-negative lw-ecmc-add-cancel lw-ecmc-double lw-ecmc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local
 (defthm lw-ecmc-logs-agree
   (equal (lw-euler-circle-center-reflected-log-coefficient center radius anchor-error (+ 2 index)
                (lw-euler-normalized-request (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error model-error)) (lw-euler-mellin-quadratic-log-model (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error (+ 2 index) (+ 2 index) model-error))
   :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-euler-circle-center-reflected-log-coefficient lw-euler-mellin-quadratic-log-model lw-ecmc-left-commutes lw-ecmc-left-distributes lw-ecmc-fold-constants lw-ecmc-times-negative lw-ecmc-negative-times lw-ecmc-zero-times lw-ecmc-minus-one lw-ecmc-double-negative lw-ecmc-add-cancel lw-ecmc-double lw-ecmc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
                   :do-not-induct t))))

(local
 (defthm lw-ecmc-native-data
   (implies (and (lw-euler-circle-center-modelp center radius plus-arcs minus-arcs target error epsilon anchor-error) (< 3 (car center)) (natp index)
                (rationalp extraction-error) (< 0 extraction-error)
                (rationalp coefficient-error) (< 0 coefficient-error)
                (rationalp model-error) (< 0 model-error)
                (rationalp value-error) (< 0 value-error) (<= value-error anchor-error))
            (and (lw-complexp (lw-euler-mellin-quadratic-coefficient-value (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error index coefficient-error)) (lw-complexp (lw-euler-mellin-quadratic-log-model (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error (+ 2 index) (+ 2 index) model-error))))
   :hints (("Goal"
            :use (lw-euler-circle-outer-data
                  (:instance lw-euler-normalized-request-data
                    (rate (car center)) (height (cdr center)) (outer-radius (lw-euler-circle-outer-radius center radius)) (error model-error))
                  (:instance lw-euler-uniform-log-polynomial-valid
                    (rate (car center)) (height (cdr center)) (outer-radius (lw-euler-circle-outer-radius center radius)) (target (+ 2 index)) (error (lw-euler-normalized-request (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error model-error)))
                  (:instance lw-complex-euler-mellin-coefficient-rational
                    (rate (car center)) (height (cdr center)) (outer-radius (lw-euler-circle-outer-radius center radius)) (error coefficient-error))
                  (:instance lw-complex-euler-mellin-coefficient-rational
                    (rate (car center)) (height (cdr center)) (outer-radius (lw-euler-circle-outer-radius center radius)) (error coefficient-error) (index (+ 1 index)))
                  (:instance lw-complex-euler-mellin-coefficient-rational
                    (rate (car center)) (height (cdr center)) (outer-radius (lw-euler-circle-outer-radius center radius)) (error coefficient-error) (index (+ 2 index))))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-euler-circle-center-modelp lw-euler-mellin-quadratic-coefficient-value lw-euler-mellin-quadratic-log-model lw-pole-quadratic-coefficient lw-complex-ring-rational lw-zeta-residue-denominator-rational lw-complex-coefficient-at-rational lw-rational-power-rational lw-complex-scale-rational cons-car-cdr lw-ecmc-left-commutes lw-ecmc-left-distributes lw-ecmc-fold-constants lw-ecmc-times-negative lw-ecmc-negative-times lw-ecmc-zero-times lw-ecmc-minus-one lw-ecmc-double-negative lw-ecmc-add-cancel lw-ecmc-double lw-ecmc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-euler-circle-mellin-split-comparison
  (implies (and (lw-euler-circle-center-modelp center radius plus-arcs minus-arcs target error epsilon anchor-error) (< 3 (car center)) (natp index)
                (rationalp extraction-error) (< 0 extraction-error)
                (rationalp coefficient-error) (< 0 coefficient-error)
                (rationalp model-error) (< 0 model-error)
                (rationalp value-error) (< 0 value-error) (<= value-error anchor-error))
           (lw-complex-diskp (lw-complex-add (lw-euler-mellin-quadratic-coefficient-value (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error index coefficient-error) (lw-complex-add (lw-circle-exterior-coefficient (lw-circle-pole-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius) -1 (+ 2 index)) (lw-circle-exterior-coefficient (lw-circle-exterior-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius) -1 (+ 2 index)))) (lw-euler-circle-mellin-coefficient-error center radius anchor-error error epsilon index extraction-error coefficient-error model-error value-error)))
  :hints (("Goal"
           :use (lw-euler-circle-outer-data lw-euler-circle-center-model-data lw-ecmc-native-data
                 (:instance lw-euler-normalized-request-data
                   (rate (car center)) (height (cdr center)) (outer-radius (lw-euler-circle-outer-radius center radius)) (error model-error))
                 (:instance lw-euler-mellin-quadratic-log-comparison
                   (rate (car center)) (height (cdr center)) (outer-radius (lw-euler-circle-outer-radius center radius)) (target (+ 2 index)))
                 (:instance lw-euler-circle-center-split-coefficient-comparison
                   (index (+ 2 index)) (native-error (lw-euler-normalized-request (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error model-error)))
                 (:instance lw-complex-disk-data
                   (point (lw-complex-sub (lw-euler-mellin-quadratic-coefficient-value (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error index coefficient-error) (lw-complex-scale -1 (lw-euler-mellin-quadratic-log-model (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error (+ 2 index) (+ 2 index) model-error)))) (radius (lw-euler-mellin-quadratic-log-error (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error index coefficient-error model-error)))
                 (:instance lw-complex-disk-data
                   (point (lw-complex-sub (lw-complex-add (lw-circle-exterior-coefficient (lw-circle-pole-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius) -1 (+ 2 index)) (lw-circle-exterior-coefficient (lw-circle-exterior-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius) -1 (+ 2 index))) (lw-euler-circle-center-reflected-log-coefficient center radius anchor-error (+ 2 index)
                (lw-euler-normalized-request (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error model-error)))) (radius (* (lw-euler-circle-center-coefficient-error center radius anchor-error error epsilon extraction-error (lw-euler-normalized-request (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error model-error) value-error)
              (/ (lw-rational-power (lw-euler-circle-center-radius center radius anchor-error) (+ 2 index))))))
                 (:instance lw-complex-add-disk
                   (left (lw-complex-sub (lw-euler-mellin-quadratic-coefficient-value (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error index coefficient-error) (lw-complex-scale -1 (lw-euler-mellin-quadratic-log-model (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error (+ 2 index) (+ 2 index) model-error)))) (radius (lw-euler-mellin-quadratic-log-error (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error index coefficient-error model-error))
                   (right (lw-complex-sub (lw-complex-add (lw-circle-exterior-coefficient (lw-circle-pole-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius) -1 (+ 2 index)) (lw-circle-exterior-coefficient (lw-circle-exterior-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius) -1 (+ 2 index))) (lw-euler-circle-center-reflected-log-coefficient center radius anchor-error (+ 2 index)
                (lw-euler-normalized-request (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error model-error)))) (other-radius (* (lw-euler-circle-center-coefficient-error center radius anchor-error error epsilon extraction-error (lw-euler-normalized-request (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error model-error) value-error)
              (/ (lw-rational-power (lw-euler-circle-center-radius center radius anchor-error) (+ 2 index)))))))
           :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-euler-circle-center-modelp lw-euler-circle-mellin-coefficient-error lw-ecmc-logs-agree lw-ecmc-add-difference lw-circle-pole-split-valid lw-circle-factor-coefficient-rational lw-complex-ring-rational lw-ecmc-left-commutes lw-ecmc-left-distributes lw-ecmc-fold-constants lw-ecmc-times-negative lw-ecmc-negative-times lw-ecmc-zero-times lw-ecmc-minus-one lw-ecmc-double-negative lw-ecmc-add-cancel lw-ecmc-double lw-ecmc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm lw-ecmc-remove-exterior
   (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp exterior))
            (equal (lw-complex-sub (lw-complex-add a (lw-complex-add b exterior)) exterior)
                   (lw-complex-add a b)))
   :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-complexp lw-complex-sub lw-complex-add consp lw-ecmc-left-commutes lw-ecmc-left-distributes lw-ecmc-fold-constants lw-ecmc-times-negative lw-ecmc-negative-times lw-ecmc-zero-times lw-ecmc-minus-one lw-ecmc-double-negative lw-ecmc-add-cancel lw-ecmc-double lw-ecmc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-euler-circle-mellin-pole-comparison
  (implies (and (lw-euler-circle-center-modelp center radius plus-arcs minus-arcs target error epsilon anchor-error) (< 3 (car center)) (natp index)
                (rationalp extraction-error) (< 0 extraction-error)
                (rationalp coefficient-error) (< 0 coefficient-error)
                (rationalp model-error) (< 0 model-error)
                (rationalp value-error) (< 0 value-error) (<= value-error anchor-error)
                (<= (* (lw-euler-circle-outer-gap center radius) error) (lw-euler-circle-anchor-min plus-arcs minus-arcs))
                (<= epsilon (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs))))
           (lw-complex-diskp (lw-complex-add (lw-euler-mellin-quadratic-coefficient-value (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error index coefficient-error) (lw-circle-exterior-coefficient (lw-circle-pole-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius) -1 (+ 2 index))) (+ (lw-euler-circle-mellin-coefficient-error center radius anchor-error error epsilon index extraction-error coefficient-error model-error value-error) (* (lw-euler-circle-factor-sum-cap center radius plus-arcs minus-arcs) (/ (lw-rational-power radius (+ 2 index)))))))
  :hints (("Goal"
           :use (lw-euler-circle-mellin-split-comparison lw-ecmc-native-data lw-euler-circle-center-model-data
                 (:instance lw-euler-circle-reflected-exterior-coefficient-cap (index (+ 2 index)))
                 (:instance lw-complex-disk-data (point (lw-complex-add (lw-euler-mellin-quadratic-coefficient-value (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error index coefficient-error) (lw-complex-add (lw-circle-exterior-coefficient (lw-circle-pole-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius) -1 (+ 2 index)) (lw-circle-exterior-coefficient (lw-circle-exterior-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius) -1 (+ 2 index))))) (radius (lw-euler-circle-mellin-coefficient-error center radius anchor-error error epsilon index extraction-error coefficient-error model-error value-error)))
                 (:instance lw-complex-sub-disk
                   (left (lw-complex-add (lw-euler-mellin-quadratic-coefficient-value (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error index coefficient-error) (lw-complex-add (lw-circle-exterior-coefficient (lw-circle-pole-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius) -1 (+ 2 index)) (lw-circle-exterior-coefficient (lw-circle-exterior-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius) -1 (+ 2 index))))) (radius (lw-euler-circle-mellin-coefficient-error center radius anchor-error error epsilon index extraction-error coefficient-error model-error value-error))
                   (right (lw-circle-exterior-coefficient (lw-circle-exterior-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius) -1 (+ 2 index))) (other-radius (* (lw-euler-circle-factor-sum-cap center radius plus-arcs minus-arcs) (/ (lw-rational-power radius (+ 2 index)))))))
           :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-euler-circle-center-modelp lw-ecmc-remove-exterior lw-circle-factor-coefficient-rational lw-circle-pole-split-valid lw-complex-ring-rational lw-ecmc-left-commutes lw-ecmc-left-distributes lw-ecmc-fold-constants lw-ecmc-times-negative lw-ecmc-negative-times lw-ecmc-zero-times lw-ecmc-minus-one lw-ecmc-double-negative lw-ecmc-add-cancel lw-ecmc-double lw-ecmc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
