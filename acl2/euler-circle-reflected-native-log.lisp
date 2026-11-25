(in-package "ACL2")

(include-book "euler-circle-reflected-log-model")
(include-book "euler-circle-center-coefficients")
(include-book "euler-normalized-disk")

(local (defthm lw-ecrn-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ecrn-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ecrn-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ecrn-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ecrn-times-negative (a b) (b a)))
                 :in-theory (disable lw-ecrn-times-negative)))))

(local (defthm lw-ecrn-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ecrn-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ecrn-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ecrn-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ecrn-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ecrn-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ecrn-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ecrn-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecrn-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecrn-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ecrn-left-commutes)))))

(defthm lw-euler-normalized-request-upper
  (implies (and (lw-euler-value-clearance-check rate height anchor-error)
                (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
                (not (and (equal rate 1) (equal height 0)))
                (rationalp error) (< 0 error))
           (<= (lw-euler-normalized-request rate height outer-radius anchor-error error) error))
  :hints (("Goal"
           :use (lw-euler-normalized-disk-data
                 (:instance lw-ecrn-multiply-order (a 1)
                   (b (+ 2 (* 2 (lw-euler-normalized-total-cost rate height outer-radius anchor-error))))
                   (factor error))
                 (:instance lw-positive-division-bound (numerator error)
                   (divisor (+ 2 (* 2 (lw-euler-normalized-total-cost rate height outer-radius anchor-error))))
                   (bound error)))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-normalized-request lw-euler-rounding-precision min
              lw-ecrn-left-commutes lw-ecrn-left-distributes lw-ecrn-fold-constants
              lw-ecrn-times-negative lw-ecrn-negative-times lw-ecrn-zero-times
              lw-ecrn-minus-one lw-ecrn-double-negative lw-ecrn-add-cancel lw-ecrn-double lw-ecrn-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(defthm lw-euler-circle-reflected-native-log-comparison
  (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
                (lw-euler-value-clearance-check (car center) (cdr center) anchor-error)
                (equal (lw-euler-circle-interior-count center radius plus-arcs minus-arcs) 0)
                (rationalp request) (< 0 request)
                (rationalp approximation-error) (< 0 approximation-error)
                (natp target) (rationalp native-error) (< 0 native-error)
                (lw-complex-diskp point (lw-euler-circle-center-radius center radius anchor-error)))
           (and (lw-complexp (lw-complex-polynomial (lw-euler-circle-reflected-log-polynomial center radius plus-arcs minus-arcs anchor-error request approximation-error) point 0)) (lw-complexp (lw-complex-polynomial (lw-euler-uniform-log-polynomial (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error target native-error) (lw-complex-scale -1 point) 0))
                (lw-complex-diskp (lw-complex-sub (lw-complex-polynomial (lw-euler-circle-reflected-log-polynomial center radius plus-arcs minus-arcs anchor-error request approximation-error) point 0) (lw-complex-polynomial (lw-euler-uniform-log-polynomial (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error target native-error) (lw-complex-scale -1 point) 0)) (lw-euler-circle-center-coefficient-error center radius anchor-error (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request) approximation-error native-error (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)))))
  :hints (("Goal"
           :use (lw-euler-circle-outer-data
                 (:instance lw-euler-neighborhood-data
                   (rate (car center)) (height (cdr center)) (outer-radius (lw-euler-circle-outer-radius center radius)))
                 (:instance lw-euler-circle-joint-request-adequate (target 0))
                 (:instance lw-euler-circle-center-model-data (target 0) (error (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)) (epsilon (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)))
                 (:instance lw-complex-disk-data (radius (lw-euler-circle-center-radius center radius anchor-error)))
                 (:instance lw-complex-scale-disk (factor -1) (radius (lw-euler-circle-center-radius center radius anchor-error)))
                 (:instance lw-complex-disk-enlarge (radius (lw-euler-circle-center-radius center radius anchor-error)) (cap radius))
                 (:instance lw-complex-disk-enlarge (point (lw-complex-scale -1 point)) (radius (lw-euler-circle-center-radius center radius anchor-error)) (cap (lw-euler-neighborhood-radius (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error)))
                 (:instance lw-euler-disk-point-data (rate (car center)) (height (cdr center)) (radius (lw-euler-circle-center-radius center radius anchor-error)) (offset (lw-complex-scale -1 point)))
                 lw-euler-circle-reflected-log-comparison
                 (:instance lw-euler-circle-center-native-quotient-comparison (target 0) (point (lw-complex-scale -1 point))
                   (value-error (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)) (error (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)) (epsilon (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)))
                 (:instance lw-euler-circle-center-native-factor-error (target 0) (point (lw-complex-scale -1 point))
                   (value-error (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)) (error (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)) (epsilon (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)))
                 (:instance lw-complex-euler-uniform-log-node-comparison
                   (rate (car center)) (height (cdr center)) (outer-radius (lw-euler-circle-outer-radius center radius)) (point (lw-complex-scale -1 point))
                   (coefficient-radius (* 1/2 (+ (car center) (car (lw-complex-scale -1 point))))) (error native-error) (request (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)))
                 (:instance lw-euler-uniform-log-polynomial-valid
                   (rate (car center)) (height (cdr center)) (outer-radius (lw-euler-circle-outer-radius center radius)) (error native-error))
                 (:instance lw-complex-polynomial-rational (coefficients (lw-euler-circle-reflected-log-polynomial center radius plus-arcs minus-arcs anchor-error request approximation-error)) (offset 0))
                 (:instance lw-complex-polynomial-rational (coefficients (lw-euler-uniform-log-polynomial (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error target native-error)) (point (lw-complex-scale -1 point)) (offset 0))
                 (:instance lw-polynomial-factor-log-sum-rational (roots (lw-euler-circle-factor-roots center radius 0 (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request))) (point (lw-complex-scale -1 point)))
                 (:instance lw-complex-difference-symmetric (left (lw-polynomial-factor-log-sum (lw-euler-circle-factor-roots center radius 0 (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)) (lw-complex-scale -1 point))) (right (lw-complex-polynomial (lw-euler-circle-reflected-log-polynomial center radius plus-arcs minus-arcs anchor-error request approximation-error) point 0)) (radius approximation-error))
                 (:instance lw-complex-difference-triangle
                   (left (lw-complex-polynomial (lw-euler-circle-reflected-log-polynomial center radius plus-arcs minus-arcs anchor-error request approximation-error) point 0)) (middle (lw-polynomial-factor-log-sum (lw-euler-circle-factor-roots center radius 0 (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)) (lw-complex-scale -1 point))) (right (lw-euler-circle-center-native-quotient center (lw-complex-scale -1 point) (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)))
                   (radius approximation-error) (other-radius (+ (* (lw-disk-factor-quotient-cost (- (lw-euler-circle-outer-radius center radius) (lw-euler-circle-center-radius center radius anchor-error)) (lw-euler-circle-center-margin-size center anchor-error) (lw-euler-circle-global-derivative-cap center radius)) (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)) (lw-euler-circle-center-native-quotient-error center radius anchor-error (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)))))
                 (:instance lw-complex-difference-triangle
                   (left (lw-complex-polynomial (lw-euler-circle-reflected-log-polynomial center radius plus-arcs minus-arcs anchor-error request approximation-error) point 0)) (middle (lw-euler-circle-center-native-quotient center (lw-complex-scale -1 point) (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request))) (right (lw-complex-polynomial (lw-euler-uniform-log-polynomial (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error target native-error) (lw-complex-scale -1 point) 0))
                   (radius (+ approximation-error (+ (* (lw-disk-factor-quotient-cost (- (lw-euler-circle-outer-radius center radius) (lw-euler-circle-center-radius center radius anchor-error)) (lw-euler-circle-center-margin-size center anchor-error) (lw-euler-circle-global-derivative-cap center radius)) (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)) (lw-euler-circle-center-native-quotient-error center radius anchor-error (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request))))) (other-radius (+ (* (lw-euler-uniform-log-model-cost (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error)
            (lw-euler-uniform-log-request (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error native-error))
          (* (lw-euler-uniform-log-node-cost (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error) (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request))))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-circle-center-native-quotient lw-euler-circle-center-coefficient-error
              abs lw-complex-scale-rational
              lw-ecrn-left-commutes lw-ecrn-left-distributes lw-ecrn-fold-constants
              lw-ecrn-times-negative lw-ecrn-negative-times lw-ecrn-zero-times
              lw-ecrn-minus-one lw-ecrn-double-negative lw-ecrn-add-cancel lw-ecrn-double lw-ecrn-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
