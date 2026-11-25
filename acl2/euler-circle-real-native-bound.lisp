(in-package "ACL2")

(include-book "euler-circle-real-native-coefficients")
(include-book "euler-mellin-native-coefficients")
(include-book "euler-normalized-physical-comparison")

(defun lw-euler-circle-real-native-coefficient-gain (rate radius inner plus-arcs minus-arcs anchor-error index)
  (+ 1 (* 1/2 (/ (lw-rational-power (lw-euler-local-normalized-radius rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error) index))) (* (lw-euler-circle-real-native-error-at rate radius inner plus-arcs minus-arcs anchor-error 1) (/ (lw-rational-power (lw-euler-circle-real-native-radius rate radius inner anchor-error) index)))))

(defun lw-euler-circle-real-native-coefficient-request (rate radius inner plus-arcs minus-arcs anchor-error index coefficient-error)
  (min 1/4 (/ (* 1/2 coefficient-error) (+ 1 (lw-euler-circle-real-native-coefficient-gain rate radius inner plus-arcs minus-arcs anchor-error index)))))

(local (defthm lw-ernf-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ernf-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ernf-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ernf-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ernf-times-negative (a b) (b a)))
                 :in-theory (disable lw-ernf-times-negative)))))

(local (defthm lw-ernf-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ernf-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ernf-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ernf-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ernf-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ernf-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ernf-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ernf-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ernf-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ernf-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ernf-left-commutes)))))

(local
 (defthm lw-ernf-native-chart-polynomial
   (implies (and (lw-euler-circle-coverp (cons rate 0) radius plus-arcs minus-arcs)
                (lw-euler-value-clearance-check rate 0 anchor-error)
                (equal (lw-euler-circle-interior-count (cons rate 0) radius plus-arcs minus-arcs) 0)
                (rationalp rate) (< 3 rate) (rationalp inner)
                (< (- rate 1) inner) (< inner radius)
                (rationalp request) (< 0 request) (<= request 1/4) (natp target) (natp index))
            (and (lw-complexp (lw-complex-euler-mellin-coefficient-value rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error index (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)))
                 (lw-complex-diskp (lw-complex-sub (lw-complex-euler-mellin-coefficient-value rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error index (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) (lw-complex-coefficient-at (lw-euler-circle-real-native-polynomial rate radius anchor-error target (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) index 0)) (+ (* 1/2 (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) (* 1/2 (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request) (/ (lw-rational-power (lw-euler-local-normalized-radius rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error) index)))))))
   :hints (("Goal"
            :use ((:instance lw-euler-circle-outer-data (center (cons rate 0)))
                  (:instance lw-euler-circle-joint-request-adequate (center (cons rate 0)) (target 0))
                  lw-euler-circle-real-native-model-data lw-euler-mellin-sign-data
                  (:instance lw-complex-euler-mellin-coefficient-rational (height 0) (outer-radius (lw-euler-circle-outer-radius (cons rate 0) radius)) (error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)))
                  (:instance lw-complex-euler-normalized-physical-coefficient-rational (height 0) (outer-radius (lw-euler-circle-outer-radius (cons rate 0) radius)) (error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)))
                  (:instance lw-euler-local-normalized-polynomial-valid (height 0) (outer-radius (lw-euler-circle-outer-radius (cons rate 0) radius)) (error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)))
                  (:instance lw-complex-coefficient-at-rational (coefficients (lw-euler-local-normalized-polynomial rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error target (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request))) (target index) (offset 0))
                  (:instance lw-complex-euler-normalized-physical-polynomial-comparison (height 0) (outer-radius (lw-euler-circle-outer-radius (cons rate 0) radius))
                    (coefficient-error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) (polynomial-error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)))
                  (:instance lw-polynomial-rescale-coefficient (coefficients (lw-euler-local-normalized-polynomial rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error target (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request))) (factor -1) (target index) (offset 0))
                  (:instance lw-complex-sub-scales (factor (lw-rational-power -1 index)) (a (lw-complex-euler-normalized-physical-coefficient-value rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error index (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request))) (b (lw-complex-coefficient-at (lw-euler-local-normalized-polynomial rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error target (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) index 0)))
                  (:instance lw-complex-scale-disk (factor (lw-rational-power -1 index))
                    (point (lw-complex-sub (lw-complex-euler-normalized-physical-coefficient-value rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error index (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) (lw-complex-coefficient-at (lw-euler-local-normalized-polynomial rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error target (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) index 0))) (radius (+ (* 1/2 (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) (* 1/2 (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request) (/ (lw-rational-power (lw-euler-local-normalized-radius rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error) index)))))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complex-euler-mellin-coefficient-value lw-euler-circle-real-native-polynomial
              lw-euler-local-normalized-polynomial
              lw-ernf-left-commutes lw-ernf-left-distributes lw-ernf-fold-constants
              lw-ernf-times-negative lw-ernf-negative-times lw-ernf-zero-times
              lw-ernf-minus-one lw-ernf-double-negative lw-ernf-add-cancel lw-ernf-double lw-ernf-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-ernf-coefficient-bound-with-request
   (implies (and (lw-euler-circle-coverp (cons rate 0) radius plus-arcs minus-arcs)
                (lw-euler-value-clearance-check rate 0 anchor-error)
                (equal (lw-euler-circle-interior-count (cons rate 0) radius plus-arcs minus-arcs) 0)
                (rationalp rate) (< 3 rate) (rationalp inner)
                (< (- rate 1) inner) (< inner radius)
                (rationalp request) (< 0 request) (<= request 1/4)
                 (natp target) (natp index)
                 (rationalp coefficient-error) (< 0 coefficient-error))
            (lw-complex-diskp (lw-complex-mellin-euler-coefficient-value rate 0 index coefficient-error) (+ (* (lw-euler-circle-real-normalized-cap rate radius inner plus-arcs minus-arcs) (/ (lw-rational-power inner index))) (+ (* 1/2 (+ (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request) coefficient-error)) (+ (* 1/2 (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) (* 1/2 (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request) (/ (lw-rational-power (lw-euler-local-normalized-radius rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error) index)))) (* (lw-euler-circle-real-native-model-error rate radius inner plus-arcs minus-arcs anchor-error request) (/ (lw-rational-power (lw-euler-circle-real-native-radius rate radius inner anchor-error) index)))))))
   :hints (("Goal"
            :use ((:instance lw-euler-circle-outer-data (center (cons rate 0)))
                  (:instance lw-euler-circle-joint-request-adequate (center (cons rate 0)) (target 0))
                  lw-euler-circle-real-native-model-data lw-euler-circle-real-native-coefficient-comparison
                  lw-ernf-native-chart-polynomial
                  (:instance lw-complex-mellin-euler-coefficient-rational (height 0) (error coefficient-error))
                  (:instance lw-mellin-euler-native-coefficient-agreement
                    (height 0) (outer-radius (lw-euler-circle-outer-radius (cons rate 0) radius)) (left-error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) (right-error coefficient-error))
                  (:instance lw-euler-circle-real-normalized-coefficient-bound (approximation-error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)))
                  (:instance lw-complex-difference-symmetric (left (lw-complex-euler-mellin-coefficient-value rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error index (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request))) (right (lw-complex-mellin-euler-coefficient-value rate 0 index coefficient-error)) (radius (* 1/2 (+ (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request) coefficient-error))))
                  (:instance lw-complex-difference-triangle (left (lw-complex-mellin-euler-coefficient-value rate 0 index coefficient-error)) (middle (lw-complex-euler-mellin-coefficient-value rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error index (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request))) (right (lw-complex-coefficient-at (lw-euler-circle-real-native-polynomial rate radius anchor-error target (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) index 0))
                    (radius (* 1/2 (+ (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request) coefficient-error))) (other-radius (+ (* 1/2 (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) (* 1/2 (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request) (/ (lw-rational-power (lw-euler-local-normalized-radius rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error) index))))))
                  (:instance lw-complex-difference-triangle (left (lw-complex-mellin-euler-coefficient-value rate 0 index coefficient-error)) (middle (lw-complex-coefficient-at (lw-euler-circle-real-native-polynomial rate radius anchor-error target (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) index 0)) (right (lw-complex-coefficient-at (lw-euler-circle-real-normalized-polynomial rate radius inner plus-arcs minus-arcs anchor-error request (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) index 0))
                    (radius (+ (* 1/2 (+ (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request) coefficient-error)) (+ (* 1/2 (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) (* 1/2 (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request) (/ (lw-rational-power (lw-euler-local-normalized-radius rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error) index)))))) (other-radius (* (lw-euler-circle-real-native-model-error rate radius inner plus-arcs minus-arcs anchor-error request) (/ (lw-rational-power (lw-euler-circle-real-native-radius rate radius inner anchor-error) index)))))
                  (:instance lw-complex-difference-triangle (left (lw-complex-mellin-euler-coefficient-value rate 0 index coefficient-error)) (middle (lw-complex-coefficient-at (lw-euler-circle-real-normalized-polynomial rate radius inner plus-arcs minus-arcs anchor-error request (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) index 0)) (right (cons 0 0))
                    (radius (+ (* 1/2 (+ (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request) coefficient-error)) (+ (* 1/2 (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) (* 1/2 (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request) (/ (lw-rational-power (lw-euler-local-normalized-radius rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error) index)))) (* (lw-euler-circle-real-native-model-error rate radius inner plus-arcs minus-arcs anchor-error request) (/ (lw-rational-power (lw-euler-circle-real-native-radius rate radius inner anchor-error) index))))) (other-radius (* (lw-euler-circle-real-normalized-cap rate radius inner plus-arcs minus-arcs) (/ (lw-rational-power inner index))))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complex-sub-zero
              lw-ernf-left-commutes lw-ernf-left-distributes lw-ernf-fold-constants
              lw-ernf-times-negative lw-ernf-negative-times lw-ernf-zero-times
              lw-ernf-minus-one lw-ernf-double-negative lw-ernf-add-cancel lw-ernf-double lw-ernf-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-euler-circle-real-native-cap-data
  (implies (and (lw-euler-circle-coverp (cons rate 0) radius plus-arcs minus-arcs)
                (lw-euler-value-clearance-check rate 0 anchor-error)
                (equal (lw-euler-circle-interior-count (cons rate 0) radius plus-arcs minus-arcs) 0)
                (rationalp rate) (< 3 rate) (rationalp inner)
                (< (- rate 1) inner) (< inner radius))
           (and (rationalp (lw-euler-circle-real-normalized-cap rate radius inner plus-arcs minus-arcs)) (<= 0 (lw-euler-circle-real-normalized-cap rate radius inner plus-arcs minus-arcs))))
  :hints (("Goal"
           :use ((:instance lw-euler-circle-joint-request-adequate (center (cons rate 0)) (target 0) (request 1/4))
                 (:instance lw-euler-circle-real-normalized-boundary
                   (point (cons inner 0)) (request 1/4) (approximation-error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error 1/4)))
                 (:instance lw-complex-disk-data
                   (point (lw-complex-polynomial (lw-euler-circle-real-normalized-polynomial rate radius inner plus-arcs minus-arcs anchor-error 1/4 (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error 1/4)) (cons inner 0) 0))
                   (radius (lw-euler-circle-real-normalized-cap rate radius inner plus-arcs minus-arcs))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complexp lw-complex-norm-square
              lw-ernf-left-commutes lw-ernf-left-distributes lw-ernf-fold-constants
              lw-ernf-times-negative lw-ernf-negative-times lw-ernf-zero-times
              lw-ernf-minus-one lw-ernf-double-negative lw-ernf-add-cancel lw-ernf-double lw-ernf-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm lw-ernf-unscale-nonnegative
   (implies (and (rationalp factor) (< 0 factor) (acl2-numberp gain)
                 (rationalp (* factor gain)) (<= 0 (* factor gain)))
            (and (rationalp gain) (<= 0 gain)))
   :hints (("Goal"
            :use ((:instance inverse-of-* (x factor))
                  (:instance associativity-of-* (x (/ factor)) (y factor) (z gain))
                  (:instance commutativity-of-* (x (/ factor)) (y factor))
                  (:instance commutativity-of-* (x (* factor gain)) (y (/ factor)))
                  (:instance lw-reciprocal-positive (value factor))
                  (:instance lw-ernf-multiply-order (a 0) (b (* factor gain)) (factor (/ factor))))
            :in-theory (set-difference-theories (theory 'ground-zero)
                          '(associativity-of-* commutativity-of-* inverse-of-*))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-ernf-gain-data
   (implies (and (lw-euler-circle-coverp (cons rate 0) radius plus-arcs minus-arcs)
                (lw-euler-value-clearance-check rate 0 anchor-error)
                (equal (lw-euler-circle-interior-count (cons rate 0) radius plus-arcs minus-arcs) 0)
                (rationalp rate) (< 3 rate) (rationalp inner)
                (< (- rate 1) inner) (< inner radius) (natp index))
            (and (rationalp (lw-euler-circle-real-native-coefficient-gain rate radius inner plus-arcs minus-arcs anchor-error index)) (<= 0 (lw-euler-circle-real-native-coefficient-gain rate radius inner plus-arcs minus-arcs anchor-error index))))
   :hints (("Goal"
            :use ((:instance lw-euler-circle-outer-data (center (cons rate 0)))
                  (:instance lw-euler-circle-joint-request-adequate (center (cons rate 0)) (target 0) (request 1/4))
                  (:instance lw-euler-circle-real-native-model-data (target 0) (request 1/4))
                  (:instance lw-euler-circle-real-native-error-scales (error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error 1/4)))
                  (:instance lw-ernf-unscale-nonnegative (factor (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error 1/4)) (gain (lw-euler-circle-real-native-error-at rate radius inner plus-arcs minus-arcs anchor-error 1)))
                  (:instance lw-euler-local-normalized-data (height 0) (outer-radius (lw-euler-circle-outer-radius (cons rate 0) radius)))
                  (:instance lw-rational-power-positive (base (lw-euler-local-normalized-radius rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error)) (exponent index))
                  (:instance lw-rational-power-positive (base (lw-euler-circle-real-native-radius rate radius inner anchor-error)) (exponent index))
                  (:instance lw-ernf-multiply-order (a 0) (b (lw-euler-circle-real-native-error-at rate radius inner plus-arcs minus-arcs anchor-error 1)) (factor (/ (lw-rational-power (lw-euler-circle-real-native-radius rate radius inner anchor-error) index)))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-circle-real-native-coefficient-gain lw-euler-circle-real-native-model-error
              (:type-prescription lw-euler-circle-real-native-error-at)
              lw-rational-power-rational lw-reciprocal-positive
              lw-ernf-left-commutes lw-ernf-left-distributes lw-ernf-fold-constants
              lw-ernf-times-negative lw-ernf-negative-times lw-ernf-zero-times
              lw-ernf-minus-one lw-ernf-double-negative lw-ernf-add-cancel lw-ernf-double lw-ernf-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-ernf-scaled-request
   (implies (and (rationalp coefficient-error) (< 0 coefficient-error)
                 (rationalp gain) (<= 0 gain))
            (let ((request (min 1/4 (/ (* 1/2 coefficient-error) (+ 1 gain)))))
              (and (rationalp request) (< 0 request) (<= request 1/4)
                   (<= (* gain request) (* 1/2 coefficient-error)))))
   :hints (("Goal"
            :use ((:instance lw-ernf-multiply-order (a gain) (b (+ 1 gain))
                    (factor (/ (* 1/2 coefficient-error) (+ 1 gain))))
                  (:instance lw-ernf-multiply-order (a (min 1/4 (/ (* 1/2 coefficient-error) (+ 1 gain))))
                    (b (/ (* 1/2 coefficient-error) (+ 1 gain))) (factor gain))
                  (:instance lw-ernf-inverse-factor (divisor (+ 1 gain)) (coefficient (* 1/2 coefficient-error))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              min lw-reciprocal-positive
              lw-ernf-left-commutes lw-ernf-left-distributes lw-ernf-fold-constants
              lw-ernf-times-negative lw-ernf-negative-times lw-ernf-zero-times
              lw-ernf-minus-one lw-ernf-double-negative lw-ernf-add-cancel lw-ernf-double lw-ernf-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-euler-circle-real-native-coefficient-bound
  (implies (and (lw-euler-circle-coverp (cons rate 0) radius plus-arcs minus-arcs)
                (lw-euler-value-clearance-check rate 0 anchor-error)
                (equal (lw-euler-circle-interior-count (cons rate 0) radius plus-arcs minus-arcs) 0)
                (rationalp rate) (< 3 rate) (rationalp inner)
                (< (- rate 1) inner) (< inner radius)
                (natp index) (rationalp coefficient-error) (< 0 coefficient-error))
           (lw-complex-diskp (lw-complex-mellin-euler-coefficient-value rate 0 index coefficient-error) (+ (* (lw-euler-circle-real-normalized-cap rate radius inner plus-arcs minus-arcs) (/ (lw-rational-power inner index))) coefficient-error)))
  :hints (("Goal"
           :use (lw-ernf-gain-data lw-euler-circle-real-native-cap-data
                 (:instance lw-ernf-scaled-request (gain (lw-euler-circle-real-native-coefficient-gain rate radius inner plus-arcs minus-arcs anchor-error index)))
                 (:instance lw-euler-circle-joint-request-adequate (center (cons rate 0)) (target 0) (request (lw-euler-circle-real-native-coefficient-request rate radius inner plus-arcs minus-arcs anchor-error index coefficient-error)))
                 (:instance lw-ernf-coefficient-bound-with-request (target 0) (request (lw-euler-circle-real-native-coefficient-request rate radius inner plus-arcs minus-arcs anchor-error index coefficient-error)))
                 (:instance lw-euler-circle-real-native-error-scales (error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error (lw-euler-circle-real-native-coefficient-request rate radius inner plus-arcs minus-arcs anchor-error index coefficient-error))))
                 (:instance lw-ernf-multiply-order (a (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error (lw-euler-circle-real-native-coefficient-request rate radius inner plus-arcs minus-arcs anchor-error index coefficient-error))) (b (lw-euler-circle-real-native-coefficient-request rate radius inner plus-arcs minus-arcs anchor-error index coefficient-error)) (factor (lw-euler-circle-real-native-coefficient-gain rate radius inner plus-arcs minus-arcs anchor-error index)))
                 (:instance lw-complex-disk-enlarge (point (lw-complex-mellin-euler-coefficient-value rate 0 index coefficient-error))
                   (radius (+ (* (lw-euler-circle-real-normalized-cap rate radius inner plus-arcs minus-arcs) (/ (lw-rational-power inner index))) (+ (* 1/2 (+ (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error (lw-euler-circle-real-native-coefficient-request rate radius inner plus-arcs minus-arcs anchor-error index coefficient-error)) coefficient-error)) (+ (* 1/2 (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error (lw-euler-circle-real-native-coefficient-request rate radius inner plus-arcs minus-arcs anchor-error index coefficient-error))) (* 1/2 (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error (lw-euler-circle-real-native-coefficient-request rate radius inner plus-arcs minus-arcs anchor-error index coefficient-error)) (/ (lw-rational-power (lw-euler-local-normalized-radius rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error) index)))) (* (lw-euler-circle-real-native-model-error rate radius inner plus-arcs minus-arcs anchor-error (lw-euler-circle-real-native-coefficient-request rate radius inner plus-arcs minus-arcs anchor-error index coefficient-error)) (/ (lw-rational-power (lw-euler-circle-real-native-radius rate radius inner anchor-error) index)))))) (cap (+ (* (lw-euler-circle-real-normalized-cap rate radius inner plus-arcs minus-arcs) (/ (lw-rational-power inner index))) coefficient-error))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-circle-real-native-model-error lw-euler-circle-real-native-coefficient-request
              lw-euler-circle-real-native-coefficient-gain
              lw-rational-power-rational lw-reciprocal-positive
              lw-ernf-left-commutes lw-ernf-left-distributes lw-ernf-fold-constants
              lw-ernf-times-negative lw-ernf-negative-times lw-ernf-zero-times
              lw-ernf-minus-one lw-ernf-double-negative lw-ernf-add-cancel lw-ernf-double lw-ernf-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(defthm lw-euler-circle-real-native-negative-part-bound
  (implies (and (lw-euler-circle-coverp (cons rate 0) radius plus-arcs minus-arcs)
                (lw-euler-value-clearance-check rate 0 anchor-error)
                (equal (lw-euler-circle-interior-count (cons rate 0) radius plus-arcs minus-arcs) 0)
                (rationalp rate) (< 3 rate) (rationalp inner)
                (< (- rate 1) inner) (< inner radius)
                (natp index) (rationalp coefficient-error) (< 0 coefficient-error))
           (<= (- (car (lw-complex-mellin-euler-coefficient-value rate 0 index coefficient-error))) (+ (* (lw-euler-circle-real-normalized-cap rate radius inner plus-arcs minus-arcs) (/ (lw-rational-power inner index))) coefficient-error)))
  :hints (("Goal"
           :use (lw-euler-circle-real-native-coefficient-bound
                 (:instance lw-complex-disk-data (point (lw-complex-mellin-euler-coefficient-value rate 0 index coefficient-error)) (radius (+ (* (lw-euler-circle-real-normalized-cap rate radius inner plus-arcs minus-arcs) (/ (lw-rational-power inner index))) coefficient-error)))
                 (:instance lw-complex-disk-coordinates (point (lw-complex-mellin-euler-coefficient-value rate 0 index coefficient-error)) (radius (+ (* (lw-euler-circle-real-normalized-cap rate radius inner plus-arcs minus-arcs) (/ (lw-rational-power inner index))) coefficient-error))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complexp abs
              lw-ernf-left-commutes lw-ernf-left-distributes lw-ernf-fold-constants
              lw-ernf-times-negative lw-ernf-negative-times lw-ernf-zero-times
              lw-ernf-minus-one lw-ernf-double-negative lw-ernf-add-cancel lw-ernf-double lw-ernf-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
