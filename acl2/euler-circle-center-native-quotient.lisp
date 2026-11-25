(in-package "ACL2")

(include-book "euler-circle-center-clearance")

(defun lw-euler-circle-center-native-quotient (center point value-error)
  (lw-complex-quotient (lw-complex-euler-local-coefficient-value (+ (car center) (car point)) (+ (cdr center) (cdr point)) (* 1/2 (+ (car center) (car point))) 1 value-error) (lw-complex-euler-continuation-value (+ (car center) (car point)) (+ (cdr center) (cdr point)) value-error)))

(defun lw-euler-circle-center-native-quotient-error (center radius anchor-error error value-error)
  (let ((margin (lw-euler-circle-center-margin-size center anchor-error)))
    (+ (* (/ margin) (+ error value-error))
       (* (lw-euler-circle-global-derivative-cap center radius) (+ (* (lw-euler-circle-outer-gap center radius) error) (* 1/4 value-error)) (/ margin) (/ margin)))))

(local (defthm lw-ecq-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ecq-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ecq-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ecq-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ecq-times-negative (a b) (b a)))
                 :in-theory (disable lw-ecq-times-negative)))))

(local (defthm lw-ecq-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ecq-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ecq-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ecq-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ecq-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ecq-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ecq-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))


(local
 (defthm lw-ecq-margin-comparison
   (implies (and (rationalp size) (< 0 size))
            (<= (* 1/16 size 1/16 size) (* 1/16 size size)))
   :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-complex-norm-square-valid consp lw-ecq-left-commutes lw-ecq-left-distributes lw-ecq-fold-constants lw-ecq-times-negative lw-ecq-negative-times lw-ecq-zero-times lw-ecq-minus-one lw-ecq-double-negative lw-ecq-add-cancel lw-ecq-double lw-ecq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :nonlinearp t))
   :rule-classes nil))

(local
 (defthm lw-ecq-norm-margin
   (implies (and (lw-complexp point) (rationalp margin) (< 0 margin)
                 (not (lw-complex-diskp point (* 2 margin))))
            (<= (* margin margin) (lw-complex-norm-square point)))
   :hints (("Goal"
            :use ((:instance lw-complex-disk-norm-square (radius (* 2 margin))))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) consp lw-ecq-left-commutes lw-ecq-left-distributes lw-ecq-fold-constants lw-ecq-times-negative lw-ecq-negative-times lw-ecq-zero-times lw-ecq-minus-one lw-ecq-double-negative lw-ecq-add-cancel lw-ecq-double lw-ecq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :nonlinearp t))
   :rule-classes nil))

(local
 (defthm lw-ecq-denominator-data
   (implies (and (lw-euler-circle-center-modelp center radius plus-arcs minus-arcs target error epsilon anchor-error) (lw-complex-diskp point (lw-euler-circle-center-radius center radius anchor-error))
                (rationalp value-error) (< 0 value-error) (<= value-error anchor-error))
            (and (lw-complexp (lw-complex-polynomial (lw-euler-circle-global-polynomial center radius target error) point 0)) (lw-complexp (lw-complex-euler-continuation-value (+ (car center) (car point)) (+ (cdr center) (cdr point)) value-error))
                 (<= (* (lw-euler-circle-center-margin-size center anchor-error) (lw-euler-circle-center-margin-size center anchor-error)) (lw-complex-norm-square (lw-complex-polynomial (lw-euler-circle-global-polynomial center radius target error) point 0)))
                 (<= (* (lw-euler-circle-center-margin-size center anchor-error) (lw-euler-circle-center-margin-size center anchor-error)) (lw-complex-norm-square (lw-complex-euler-continuation-value (+ (car center) (car point)) (+ (cdr center) (cdr point)) value-error)))
                 (lw-complex-diskp (lw-complex-sub (lw-complex-euler-continuation-value (+ (car center) (car point)) (+ (cdr center) (cdr point)) value-error) (lw-complex-polynomial (lw-euler-circle-global-polynomial center radius target error) point 0)) (+ (* (lw-euler-circle-outer-gap center radius) error) (* 1/4 value-error)))))
   :hints (("Goal"
            :use (lw-euler-circle-center-model-data lw-euler-circle-outer-data lw-euler-circle-center-polynomial-margin
                  (:instance lw-complex-disk-data (radius (lw-euler-circle-center-radius center radius anchor-error)))
                  (:instance lw-complex-disk-enlarge (radius (lw-euler-circle-center-radius center radius anchor-error)) (cap (lw-euler-circle-outer-radius center radius)))
                  (:instance lw-complex-disk-enlarge (radius (lw-euler-circle-center-radius center radius anchor-error)) (cap (lw-euler-neighborhood-radius (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error)))
                  (:instance lw-euler-neighborhood-data (rate (car center)) (height (cdr center)) (outer-radius (lw-euler-circle-outer-radius center radius)))
                  (:instance lw-complex-euler-neighborhood-value-clearance
                    (rate (car center)) (height (cdr center)) (outer-radius (lw-euler-circle-outer-radius center radius)) (error value-error))
                  (:instance lw-complex-euler-uniform-polynomial-comparison
                    (rate (car center)) (height (cdr center)) (radius (lw-euler-circle-outer-radius center radius)) (error (* (lw-euler-circle-outer-gap center radius) error)))
                  (:instance lw-complex-difference-symmetric (left (lw-complex-polynomial (lw-euler-circle-global-polynomial center radius target error) point 0)) (right (lw-complex-euler-continuation-value (+ (car center) (car point)) (+ (cdr center) (cdr point)) value-error)) (radius (+ (* (lw-euler-circle-outer-gap center radius) error) (* 1/4 value-error))))
                  (:instance lw-ecq-margin-comparison (size (lw-euler-value-clearance-size (car center) (cdr center) anchor-error)))
                  (:instance lw-ecq-norm-margin (point (lw-complex-polynomial (lw-euler-circle-global-polynomial center radius target error) point 0)) (margin (lw-euler-circle-center-margin-size center anchor-error))))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-euler-circle-center-modelp lw-euler-circle-global-polynomial lw-euler-circle-center-margin-size lw-complex-polynomial-rational lw-ecq-left-commutes lw-ecq-left-distributes lw-ecq-fold-constants lw-ecq-times-negative lw-ecq-negative-times lw-ecq-zero-times lw-ecq-minus-one lw-ecq-double-negative lw-ecq-add-cancel lw-ecq-double lw-ecq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :nonlinearp t :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-ecq-numerator-data
   (implies (and (lw-euler-circle-center-modelp center radius plus-arcs minus-arcs target error epsilon anchor-error) (lw-complex-diskp point (lw-euler-circle-center-radius center radius anchor-error))
                (rationalp value-error) (< 0 value-error) (<= value-error anchor-error))
            (and (lw-complexp (lw-complex-euler-local-coefficient-value (+ (car center) (car point)) (+ (cdr center) (cdr point)) (* 1/2 (+ (car center) (car point))) 1 value-error)) (lw-complexp (lw-complex-polynomial-derivative (lw-euler-circle-global-polynomial center radius target error) point))
                 (lw-complex-diskp (lw-complex-polynomial-derivative (lw-euler-circle-global-polynomial center radius target error) point) (lw-euler-circle-global-derivative-cap center radius))
                 (lw-complex-diskp (lw-complex-sub (lw-complex-euler-local-coefficient-value (+ (car center) (car point)) (+ (cdr center) (cdr point)) (* 1/2 (+ (car center) (car point))) 1 value-error) (lw-complex-polynomial-derivative (lw-euler-circle-global-polynomial center radius target error) point)) (+ error value-error))))
   :hints (("Goal"
            :use (lw-euler-circle-center-model-data lw-euler-circle-outer-data
                  lw-euler-circle-center-derivative-bound lw-euler-circle-global-derivative-identity
                  (:instance lw-complex-disk-data (radius (lw-euler-circle-center-radius center radius anchor-error)))
                  (:instance lw-complex-disk-data (point (lw-complex-polynomial-derivative (lw-euler-circle-global-polynomial center radius target error) point)) (radius (lw-euler-circle-global-derivative-cap center radius)))
                  (:instance lw-complex-disk-enlarge (radius (lw-euler-circle-center-radius center radius anchor-error)) (cap radius))
                  (:instance lw-euler-disk-point-data (rate (car center)) (height (cdr center)) (offset point))
                  (:instance lw-polynomial-derivative-coefficients-evaluation (coefficients (lw-euler-circle-global-polynomial center radius target error)))
                  (:instance lw-complex-euler-uniform-derivative-comparison
                    (rate (car center)) (height (cdr center)) (outer-radius (lw-euler-circle-outer-radius center radius)) (inner-radius radius)
                    (center point) (coefficient-radius (* 1/2 (+ (car center) (car point)))) (coefficient-error value-error))
                  (:instance lw-complex-euler-local-coefficient-rational
                    (rate (+ (car center) (car point))) (height (+ (cdr center) (cdr point))) (radius (* 1/2 (+ (car center) (car point)))) (index 1) (error value-error))
                  (:instance lw-complex-difference-symmetric (left (lw-complex-polynomial-derivative (lw-euler-circle-global-polynomial center radius target error) point)) (right (lw-complex-euler-local-coefficient-value (+ (car center) (car point)) (+ (cdr center) (cdr point)) (* 1/2 (+ (car center) (car point))) 1 value-error)) (radius (+ error value-error))))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-euler-circle-center-modelp lw-euler-circle-global-derivative lw-ecq-left-commutes lw-ecq-left-distributes lw-ecq-fold-constants lw-ecq-times-negative lw-ecq-negative-times lw-ecq-zero-times lw-ecq-minus-one lw-ecq-double-negative lw-ecq-add-cancel lw-ecq-double lw-ecq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-euler-circle-center-native-quotient-comparison
  (implies (and (lw-euler-circle-center-modelp center radius plus-arcs minus-arcs target error epsilon anchor-error) (lw-complex-diskp point (lw-euler-circle-center-radius center radius anchor-error))
                (rationalp value-error) (< 0 value-error) (<= value-error anchor-error))
           (and (lw-complexp (lw-euler-circle-center-native-quotient center point value-error)) (lw-complexp (lw-euler-circle-center-quotient center radius point target error))
                (lw-complex-diskp (lw-complex-sub (lw-euler-circle-center-native-quotient center point value-error) (lw-euler-circle-center-quotient center radius point target error)) (lw-euler-circle-center-native-quotient-error center radius anchor-error error value-error))))
  :hints (("Goal"
           :use (lw-euler-circle-center-model-data
                 lw-ecq-denominator-data lw-ecq-numerator-data
                 (:instance lw-complex-quotient-difference-bound
                   (numerator (lw-complex-euler-local-coefficient-value (+ (car center) (car point)) (+ (cdr center) (cdr point)) (* 1/2 (+ (car center) (car point))) 1 value-error)) (denominator (lw-complex-euler-continuation-value (+ (car center) (car point)) (+ (cdr center) (cdr point)) value-error))
                   (approximate-numerator (lw-complex-polynomial-derivative (lw-euler-circle-global-polynomial center radius target error) point)) (approximate-denominator (lw-complex-polynomial (lw-euler-circle-global-polynomial center radius target error) point 0))
                   (left-clearance (lw-euler-circle-center-margin-size center anchor-error)) (right-clearance (lw-euler-circle-center-margin-size center anchor-error))
                   (numerator-cap (lw-euler-circle-global-derivative-cap center radius)) (numerator-error (+ error value-error)) (denominator-error (+ (* (lw-euler-circle-outer-gap center radius) error) (* 1/4 value-error)))))
           :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-euler-circle-center-quotient lw-euler-circle-center-native-quotient lw-euler-circle-center-native-quotient-error lw-complex-quotient-rational lw-ecq-left-commutes lw-ecq-left-distributes lw-ecq-fold-constants lw-ecq-times-negative lw-ecq-negative-times lw-ecq-zero-times lw-ecq-minus-one lw-ecq-double-negative lw-ecq-add-cancel lw-ecq-double lw-ecq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(defthm lw-euler-circle-center-native-factor-error
  (implies (and (lw-euler-circle-center-modelp center radius plus-arcs minus-arcs target error epsilon anchor-error) (lw-complex-diskp point (lw-euler-circle-center-radius center radius anchor-error))
                (rationalp value-error) (< 0 value-error) (<= value-error anchor-error))
           (lw-complex-diskp (lw-complex-sub (lw-polynomial-factor-log-sum (lw-euler-circle-factor-roots center radius target error epsilon) point) (lw-euler-circle-center-native-quotient center point value-error))
                             (+ (* (lw-disk-factor-quotient-cost (- (lw-euler-circle-outer-radius center radius) (lw-euler-circle-center-radius center radius anchor-error)) (lw-euler-circle-center-margin-size center anchor-error) (lw-euler-circle-global-derivative-cap center radius)) epsilon) (lw-euler-circle-center-native-quotient-error center radius anchor-error error value-error))))
  :hints (("Goal"
           :use (lw-euler-circle-center-model-data lw-euler-circle-center-native-quotient-comparison
                 lw-euler-circle-center-factor-quotient-error
                 (:instance lw-complex-disk-data (radius (lw-euler-circle-center-radius center radius anchor-error)))
                 (:instance lw-complex-difference-symmetric (left (lw-euler-circle-center-native-quotient center point value-error)) (right (lw-euler-circle-center-quotient center radius point target error)) (radius (lw-euler-circle-center-native-quotient-error center radius anchor-error error value-error)))
                 (:instance lw-complex-difference-triangle (left (lw-polynomial-factor-log-sum (lw-euler-circle-factor-roots center radius target error epsilon) point)) (middle (lw-euler-circle-center-quotient center radius point target error)) (right (lw-euler-circle-center-native-quotient center point value-error))
                   (radius (* (lw-disk-factor-quotient-cost (- (lw-euler-circle-outer-radius center radius) (lw-euler-circle-center-radius center radius anchor-error)) (lw-euler-circle-center-margin-size center anchor-error) (lw-euler-circle-global-derivative-cap center radius)) epsilon)) (other-radius (lw-euler-circle-center-native-quotient-error center radius anchor-error error value-error))))
           :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-polynomial-factor-log-sum-rational lw-ecq-left-commutes lw-ecq-left-distributes lw-ecq-fold-constants lw-ecq-times-negative lw-ecq-negative-times lw-ecq-zero-times lw-ecq-minus-one lw-ecq-double-negative lw-ecq-add-cancel lw-ecq-double lw-ecq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
