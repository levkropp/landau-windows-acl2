(in-package "ACL2")

(include-book "euler-circle-center-coefficients")
(include-book "circle-factor-coefficient-split")
(include-book "euler-circle-exterior-uniform")

; Reflect the local offset so that the Taylor variable is c-s, as in
; the Mellin coefficient search.
(defun lw-euler-circle-center-reflected-log-coefficient (center radius anchor-error index native-error)
  (lw-complex-scale (lw-rational-power -1 index) (lw-complex-coefficient-at (lw-euler-uniform-log-polynomial (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error index native-error) index 0)))

(local (defthm lw-ecsc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ecsc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ecsc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ecsc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ecsc-times-negative (a b) (b a)))
                 :in-theory (disable lw-ecsc-times-negative)))))

(local (defthm lw-ecsc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ecsc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ecsc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ecsc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ecsc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ecsc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ecsc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))


(local
 (defthm lw-ecsc-log-model-data
   (implies (and (lw-euler-circle-center-modelp center radius plus-arcs minus-arcs target error epsilon anchor-error) (natp index) (rationalp native-error) (< 0 native-error))
            (and (lw-complex-coefficientsp (lw-euler-uniform-log-polynomial (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error index native-error))
                 (lw-complexp (lw-complex-coefficient-at (lw-euler-uniform-log-polynomial (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error index native-error) index 0))))
   :hints (("Goal"
            :use (lw-euler-circle-outer-data lw-euler-circle-center-model-data
                  (:instance lw-euler-uniform-log-polynomial-valid
                    (rate (car center)) (height (cdr center)) (outer-radius (lw-euler-circle-outer-radius center radius))
                    (target index) (error native-error)))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-euler-circle-center-modelp lw-complex-coefficient-at-rational lw-ecsc-left-commutes lw-ecsc-left-distributes lw-ecsc-fold-constants lw-ecsc-times-negative lw-ecsc-negative-times lw-ecsc-zero-times lw-ecsc-minus-one lw-ecsc-double-negative lw-ecsc-add-cancel lw-ecsc-double lw-ecsc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-ecsc-scaled-comparison
   (implies (and (lw-euler-circle-center-modelp center radius plus-arcs minus-arcs target error epsilon anchor-error)
                (natp index) (rationalp extraction-error) (< 0 extraction-error)
                (rationalp native-error) (< 0 native-error)
                (rationalp value-error) (< 0 value-error) (<= value-error anchor-error))
            (and (lw-complexp (lw-complex-sub (lw-complex-add (lw-circle-exterior-coefficient (lw-circle-pole-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius) -1 index) (lw-circle-exterior-coefficient (lw-circle-exterior-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius) -1 index)) (lw-euler-circle-center-reflected-log-coefficient center radius anchor-error index native-error)))
                 (lw-complex-diskp (lw-complex-scale (lw-rational-power (- (lw-euler-circle-center-radius center radius anchor-error)) index) (lw-complex-sub (lw-complex-add (lw-circle-exterior-coefficient (lw-circle-pole-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius) -1 index) (lw-circle-exterior-coefficient (lw-circle-exterior-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius) -1 index)) (lw-euler-circle-center-reflected-log-coefficient center radius anchor-error index native-error))) (lw-euler-circle-center-coefficient-error center radius anchor-error error epsilon extraction-error native-error value-error))))
   :hints (("Goal"
            :use (lw-euler-circle-center-model-data lw-ecsc-log-model-data
                  lw-euler-circle-center-coefficient-comparison
                  (:instance lw-circle-factor-coefficient-reflected-scaling (roots (lw-euler-circle-factor-roots center radius target error epsilon)) (radius (lw-euler-circle-center-radius center radius anchor-error)))
                  (:instance lw-circle-factor-coefficient-split (roots (lw-euler-circle-factor-roots center radius target error epsilon)) (radius -1) (split-radius radius))
                  (:instance lw-complex-sub-scales (factor (lw-rational-power (- (lw-euler-circle-center-radius center radius anchor-error)) index)) (a (lw-complex-add (lw-circle-exterior-coefficient (lw-circle-pole-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius) -1 index) (lw-circle-exterior-coefficient (lw-circle-exterior-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius) -1 index))) (b (lw-euler-circle-center-reflected-log-coefficient center radius anchor-error index native-error)))
                  (:instance lw-circle-factor-reflected-scale-compose (radius (lw-euler-circle-center-radius center radius anchor-error)) (point (lw-complex-coefficient-at (lw-euler-uniform-log-polynomial (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error index native-error) index 0))))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-euler-circle-center-reflected-log-coefficient lw-circle-pole-split-valid lw-circle-factor-coefficient-rational lw-polynomial-rescale-coefficient lw-complex-ring-rational lw-complex-scale-rational lw-rational-power-rational lw-ecsc-left-commutes lw-ecsc-left-distributes lw-ecsc-fold-constants lw-ecsc-times-negative lw-ecsc-negative-times lw-ecsc-zero-times lw-ecsc-minus-one lw-ecsc-double-negative lw-ecsc-add-cancel lw-ecsc-double lw-ecsc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-euler-circle-center-split-coefficient-comparison
  (implies (and (lw-euler-circle-center-modelp center radius plus-arcs minus-arcs target error epsilon anchor-error)
                (natp index) (rationalp extraction-error) (< 0 extraction-error)
                (rationalp native-error) (< 0 native-error)
                (rationalp value-error) (< 0 value-error) (<= value-error anchor-error))
           (lw-complex-diskp (lw-complex-sub (lw-complex-add (lw-circle-exterior-coefficient (lw-circle-pole-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius) -1 index) (lw-circle-exterior-coefficient (lw-circle-exterior-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius) -1 index)) (lw-euler-circle-center-reflected-log-coefficient center radius anchor-error index native-error)) (* (lw-euler-circle-center-coefficient-error center radius anchor-error error epsilon extraction-error native-error value-error) (/ (lw-rational-power (lw-euler-circle-center-radius center radius anchor-error) index)))))
  :hints (("Goal"
           :use (lw-euler-circle-center-model-data lw-ecsc-scaled-comparison
                 (:instance lw-circle-factor-reflected-scale-inverse
                   (point (lw-complex-sub (lw-complex-add (lw-circle-exterior-coefficient (lw-circle-pole-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius) -1 index) (lw-circle-exterior-coefficient (lw-circle-exterior-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius) -1 index)) (lw-euler-circle-center-reflected-log-coefficient center radius anchor-error index native-error))) (radius (lw-euler-circle-center-radius center radius anchor-error)) (cap (lw-euler-circle-center-coefficient-error center radius anchor-error error epsilon extraction-error native-error value-error))))
           :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-rational-power-rational lw-ecsc-left-commutes lw-ecsc-left-distributes lw-ecsc-fold-constants lw-ecsc-times-negative lw-ecsc-negative-times lw-ecsc-zero-times lw-ecsc-minus-one lw-ecsc-double-negative lw-ecsc-add-cancel lw-ecsc-double lw-ecsc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(defthm lw-euler-circle-reflected-exterior-coefficient-cap
  (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
                (natp target) (rationalp error) (< 0 error) (<= error 1)
                (<= (* (lw-euler-circle-outer-gap center radius) error) (lw-euler-circle-anchor-min plus-arcs minus-arcs))
                (rationalp epsilon) (< 0 epsilon) (<= epsilon (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs))) (natp index))
           (lw-complex-diskp (lw-circle-exterior-coefficient (lw-circle-exterior-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius) -1 index) (* (lw-euler-circle-factor-sum-cap center radius plus-arcs minus-arcs) (/ (lw-rational-power radius index)))))
  :hints (("Goal"
           :use (lw-euler-circle-outer-data lw-euler-circle-exterior-roots-data lw-euler-circle-exterior-uniform-cap
                 (:instance lw-circle-factor-coefficient-reflected-scaling (roots (lw-circle-exterior-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius)))
                 (:instance lw-circle-factor-reflected-scale-inverse
                   (point (lw-circle-exterior-coefficient (lw-circle-exterior-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius) -1 index)) (cap (lw-euler-circle-factor-sum-cap center radius plus-arcs minus-arcs))))
           :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-circle-exterior-roots-typed lw-circle-factor-coefficient-rational lw-ecsc-left-commutes lw-ecsc-left-distributes lw-ecsc-fold-constants lw-ecsc-times-negative lw-ecsc-negative-times lw-ecsc-zero-times lw-ecsc-minus-one lw-ecsc-double-negative lw-ecsc-add-cancel lw-ecsc-double lw-ecsc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
