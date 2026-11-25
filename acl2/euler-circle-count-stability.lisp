(in-package "ACL2")

(include-book "euler-circle-pole-split")
(include-book "circle-count-comparison")

; Both models approximate the same native value at every contour sample.
; A radius-weighted error of at most 1/8 per model suffices for exact counts.
(defun lw-euler-circle-count-quotient-error (center radius plus-arcs minus-arcs error epsilon value-error)
  (+ (* (lw-disk-factor-quotient-cost
          (- (lw-euler-circle-outer-radius center radius) radius)
          (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs))
          (lw-euler-circle-global-derivative-cap center radius))
        epsilon)
     (+ (* (lw-euler-circle-global-quotient-cost center radius plus-arcs minus-arcs) error)
        value-error)))

(defun lw-euler-circle-count-modelp (center radius plus-arcs minus-arcs target error epsilon value-error)
  (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
       (natp target)
       (rationalp error) (< 0 error) (<= error 1)
       (<= (* (lw-euler-circle-outer-gap center radius) error)
           (lw-euler-circle-anchor-min plus-arcs minus-arcs))
       (rationalp epsilon) (< 0 epsilon)
       (<= epsilon (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs)))
       (rationalp value-error) (< 0 value-error)
       (<= (* radius (lw-euler-circle-count-quotient-error center radius plus-arcs minus-arcs error epsilon value-error)) 1/8)))

(local (in-theory (disable lw-euler-circle-count-modelp lw-euler-circle-count-quotient-error)))

(local (defthm lw-eccs-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-eccs-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-eccs-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-eccs-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-eccs-times-negative (a b) (b a)))
                 :in-theory (disable lw-eccs-times-negative)))))

(local (defthm lw-eccs-zero-times (equal (* 0 a) 0)))

(local (defthm lw-eccs-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-eccs-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-eccs-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-eccs-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-eccs-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-eccs-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))


(local
 (defthm lw-eccs-model-data
   (implies (lw-euler-circle-count-modelp center radius plus-arcs minus-arcs target error epsilon value-error)
            (and (rationalp radius) (< 0 radius)
                 (lw-ray-pointsp (lw-euler-circle-factor-roots center radius target error epsilon))
                 (not (lw-circle-boundary-root (lw-euler-circle-factor-roots center radius target error epsilon) radius))))
   :hints (("Goal"
            :use (lw-euler-circle-outer-data lw-euler-circle-global-polynomials-valid
                  lw-euler-circle-boundary-root-excluded
                  (:instance lw-polynomial-disk-factor-data
                    (coefficients (lw-euler-circle-global-polynomial center radius target error))
                    (outer-radius (lw-euler-circle-outer-radius center radius))))
            :in-theory (union-theories
 '(fold-consts-in-+ lw-euler-circle-count-modelp lw-euler-circle-factor-roots lw-eccs-left-commutes lw-eccs-left-distributes lw-eccs-fold-constants lw-eccs-times-negative lw-eccs-negative-times lw-eccs-zero-times lw-eccs-minus-one lw-eccs-double-negative lw-eccs-add-cancel lw-eccs-double lw-eccs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))))

(local
 (defthm lw-eccs-real-coordinate
   (implies (lw-complexp point) (rationalp (car point)))
   :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complexp consp lw-eccs-left-commutes lw-eccs-left-distributes lw-eccs-fold-constants lw-eccs-times-negative lw-eccs-negative-times lw-eccs-zero-times lw-eccs-minus-one lw-eccs-double-negative lw-eccs-add-cancel lw-eccs-double lw-eccs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm lw-eccs-real-subtract-car
   (implies (and (lw-complexp a) (lw-complexp b))
            (equal (car (lw-complex-sub a b)) (- (car a) (car b))))
   :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complexp lw-complex-sub consp lw-eccs-left-commutes lw-eccs-left-distributes lw-eccs-fold-constants lw-eccs-times-negative lw-eccs-negative-times lw-eccs-zero-times lw-eccs-minus-one lw-eccs-double-negative lw-eccs-add-cancel lw-eccs-double lw-eccs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local
 (defthm lw-eccs-weighted-error
   (implies (and (lw-euler-circle-count-modelp center radius plus-arcs minus-arcs target error epsilon value-error)
                 (lw-complexp point) (equal (lw-complex-norm-square point) 1))
            (lw-complex-diskp
             (lw-complex-sub (lw-complex-mul (lw-complex-scale radius point) (lw-polynomial-factor-log-sum (lw-euler-circle-factor-roots center radius target error epsilon) (lw-complex-scale radius point))) (lw-complex-mul (lw-complex-scale radius point) (lw-euler-circle-log-value center radius plus-arcs minus-arcs point value-error))) 1/8))
   :hints (("Goal"
            :use (lw-eccs-model-data lw-euler-circle-global-shift-data
                  lw-euler-circle-log-value-rational
                  lw-euler-circle-native-factor-pole-sum-error
                  (:instance lw-complex-left-product-error
                    (factor (lw-complex-scale radius point)) (cap radius) (a (lw-polynomial-factor-log-sum (lw-euler-circle-factor-roots center radius target error epsilon) (lw-complex-scale radius point))) (b (lw-euler-circle-log-value center radius plus-arcs minus-arcs point value-error)) (error (lw-euler-circle-count-quotient-error center radius plus-arcs minus-arcs error epsilon value-error)))
                  (:instance lw-complex-disk-enlarge
                    (point (lw-complex-sub (lw-complex-mul (lw-complex-scale radius point) (lw-polynomial-factor-log-sum (lw-euler-circle-factor-roots center radius target error epsilon) (lw-complex-scale radius point))) (lw-complex-mul (lw-complex-scale radius point) (lw-euler-circle-log-value center radius plus-arcs minus-arcs point value-error))))
                    (radius (* radius (lw-euler-circle-count-quotient-error center radius plus-arcs minus-arcs error epsilon value-error))) (cap 1/8)))
            :in-theory (union-theories
 '(fold-consts-in-+ lw-euler-circle-count-modelp lw-euler-circle-count-quotient-error lw-polynomial-factor-log-sum-rational lw-eccs-left-commutes lw-eccs-left-distributes lw-eccs-fold-constants lw-eccs-times-negative lw-eccs-negative-times lw-eccs-zero-times lw-eccs-minus-one lw-eccs-double-negative lw-eccs-add-cancel lw-eccs-double lw-eccs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-eccs-real-close
   (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp value)
                 (lw-complex-diskp (lw-complex-sub a value) 1/8)
                 (lw-complex-diskp (lw-complex-sub b value) 1/8))
            (<= (abs (- (car a) (car b))) 1/4))
   :hints (("Goal"
            :use ((:instance lw-complex-disk-coordinates (point (lw-complex-sub a value)) (radius 1/8))
                  (:instance lw-complex-disk-coordinates (point (lw-complex-sub b value)) (radius 1/8)))
            :in-theory (union-theories
 '(fold-consts-in-+ abs lw-eccs-real-coordinate lw-eccs-real-subtract-car lw-eccs-left-commutes lw-eccs-left-distributes lw-eccs-fold-constants lw-eccs-times-negative lw-eccs-negative-times lw-eccs-zero-times lw-eccs-minus-one lw-eccs-double-negative lw-eccs-add-cancel lw-eccs-double lw-eccs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-eccs-point-bound
   (implies (and (lw-euler-circle-count-modelp center radius plus-arcs minus-arcs left-target left-error left-epsilon value-error)
                (lw-euler-circle-count-modelp center radius plus-arcs minus-arcs right-target right-error right-epsilon value-error)
                 (lw-complexp point) (equal (lw-complex-norm-square point) 1))
            (<= (abs (car (lw-complex-polynomial (lw-circle-count-difference (lw-euler-circle-factor-roots center radius left-target left-error left-epsilon) (lw-euler-circle-factor-roots center radius right-target right-error right-epsilon) radius) point 0))) 3/8))
   :hints (("Goal"
            :use ((:instance lw-eccs-model-data (target left-target) (error left-error) (epsilon left-epsilon))
                  (:instance lw-eccs-model-data (target right-target) (error right-error) (epsilon right-epsilon))
                  (:instance lw-eccs-weighted-error (target left-target) (error left-error) (epsilon left-epsilon))
                  (:instance lw-eccs-weighted-error (target right-target) (error right-error) (epsilon right-epsilon))
                  lw-euler-circle-global-shift-data lw-euler-circle-log-value-rational
                  (:instance lw-eccs-real-close (a (lw-complex-mul (lw-complex-scale radius point) (lw-polynomial-factor-log-sum (lw-euler-circle-factor-roots center radius left-target left-error left-epsilon) (lw-complex-scale radius point)))) (b (lw-complex-mul (lw-complex-scale radius point) (lw-polynomial-factor-log-sum (lw-euler-circle-factor-roots center radius right-target right-error right-epsilon) (lw-complex-scale radius point)))) (value (lw-complex-mul (lw-complex-scale radius point) (lw-euler-circle-log-value center radius plus-arcs minus-arcs point value-error))))
                  (:instance lw-circle-count-difference-point-bound (left (lw-euler-circle-factor-roots center radius left-target left-error left-epsilon)) (right (lw-euler-circle-factor-roots center radius right-target right-error right-epsilon))))
            :in-theory (union-theories
 '(fold-consts-in-+ lw-euler-circle-count-modelp lw-polynomial-factor-log-sum-rational lw-complex-ring-rational lw-eccs-left-commutes lw-eccs-left-distributes lw-eccs-fold-constants lw-eccs-times-negative lw-eccs-negative-times lw-eccs-zero-times lw-eccs-minus-one lw-eccs-double-negative lw-eccs-add-cancel lw-eccs-double lw-eccs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))))

(local
 (defthm lw-eccs-samples-pass
   (implies (and (lw-euler-circle-count-modelp center radius plus-arcs minus-arcs left-target left-error left-epsilon value-error)
                (lw-euler-circle-count-modelp center radius plus-arcs minus-arcs right-target right-error right-epsilon value-error)
                 (natp degree) (natp count))
            (lw-cauchy-real-boundary-check (lw-circle-count-difference (lw-euler-circle-factor-roots center radius left-target left-error left-epsilon) (lw-euler-circle-factor-roots center radius right-target right-error right-epsilon) radius) (lw-cauchy-orbit-rotation degree) count 3/8))
   :hints (("Goal" :induct (lw-cauchy-real-boundary-check (lw-circle-count-difference (lw-euler-circle-factor-roots center radius left-target left-error left-epsilon) (lw-euler-circle-factor-roots center radius right-target right-error right-epsilon) radius) (lw-cauchy-orbit-rotation degree) count 3/8)
                   :in-theory (union-theories
 '(fold-consts-in-+ lw-cauchy-real-boundary-check lw-eccs-point-bound lw-complex-power-rational lw-cauchy-orbit-data lw-cauchy-orbit-power-norm-one lw-eccs-left-commutes lw-eccs-left-distributes lw-eccs-fold-constants lw-eccs-times-negative lw-eccs-negative-times lw-eccs-zero-times lw-eccs-minus-one lw-eccs-double-negative lw-eccs-add-cancel lw-eccs-double lw-eccs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
                   :do-not '(generalize fertilize)))))

(local (defthm lw-eccs-length-natural
         (natp (len coefficients))
         :rule-classes (:rewrite :type-prescription)))

(defthm lw-euler-circle-interior-count-stable
  (implies (and (lw-euler-circle-count-modelp center radius plus-arcs minus-arcs left-target left-error left-epsilon value-error)
                (lw-euler-circle-count-modelp center radius plus-arcs minus-arcs right-target right-error right-epsilon value-error))
           (equal (len (lw-circle-pole-roots (lw-euler-circle-factor-roots center radius left-target left-error left-epsilon) radius))
                  (len (lw-circle-pole-roots (lw-euler-circle-factor-roots center radius right-target right-error right-epsilon) radius))))
  :hints (("Goal"
           :use ((:instance lw-circle-interior-count-from-comparison (left (lw-euler-circle-factor-roots center radius left-target left-error left-epsilon)) (right (lw-euler-circle-factor-roots center radius right-target right-error right-epsilon)))
                 (:instance lw-eccs-samples-pass
                   (degree (len (lw-circle-count-difference (lw-euler-circle-factor-roots center radius left-target left-error left-epsilon) (lw-euler-circle-factor-roots center radius right-target right-error right-epsilon) radius)))
                   (count (lw-cauchy-coefficient-count (lw-circle-count-difference (lw-euler-circle-factor-roots center radius left-target left-error left-epsilon) (lw-euler-circle-factor-roots center radius right-target right-error right-epsilon) radius) (len (lw-circle-count-difference (lw-euler-circle-factor-roots center radius left-target left-error left-epsilon) (lw-euler-circle-factor-roots center radius right-target right-error right-epsilon) radius)) 1/8))))
           :in-theory (union-theories
 '(fold-consts-in-+ lw-eccs-model-data lw-eccs-length-natural lw-cauchy-coefficient-count-natural lw-eccs-left-commutes lw-eccs-left-distributes lw-eccs-fold-constants lw-eccs-times-negative lw-eccs-negative-times lw-eccs-zero-times lw-eccs-minus-one lw-eccs-double-negative lw-eccs-add-cancel lw-eccs-double lw-eccs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
