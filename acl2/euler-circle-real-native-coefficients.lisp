(in-package "ACL2")

(include-book "euler-circle-real-native-model")
(include-book "polynomial-cauchy-caps")
(include-book "polynomial-capped-coefficients")

(defun lw-euler-circle-real-native-difference (rate radius inner plus-arcs minus-arcs anchor-error target request)
  (let ((native (lw-euler-circle-real-native-polynomial rate radius anchor-error target (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)))
        (real-model (lw-euler-circle-real-normalized-polynomial rate radius inner plus-arcs minus-arcs anchor-error request (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request))))
    (lw-polynomial-disk-difference native real-model (lw-euler-circle-real-native-radius rate radius inner anchor-error) (+ (len native) (len real-model)))))

(local (defthm lw-ernc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ernc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ernc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ernc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ernc-times-negative (a b) (b a)))
                 :in-theory (disable lw-ernc-times-negative)))))

(local (defthm lw-ernc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ernc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ernc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ernc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ernc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ernc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ernc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ernc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ernc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ernc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ernc-left-commutes)))))

(local (defthm lw-ernc-length-natural
         (natp (len coefficients))
         :rule-classes (:rewrite :type-prescription)))

(local
 (defthm lw-ernc-difference-data
   (implies (and (lw-euler-circle-coverp (cons rate 0) radius plus-arcs minus-arcs)
                (lw-euler-value-clearance-check rate 0 anchor-error)
                (equal (lw-euler-circle-interior-count (cons rate 0) radius plus-arcs minus-arcs) 0)
                (rationalp rate) (< 3 rate) (rationalp inner)
                (< (- rate 1) inner) (< inner radius)
                (rationalp request) (< 0 request) (<= request 1/4) (natp target))
            (lw-complex-coefficientsp (lw-euler-circle-real-native-difference rate radius inner plus-arcs minus-arcs anchor-error target request)))
   :hints (("Goal"
            :use (lw-euler-circle-real-native-model-data
                  (:instance lw-polynomial-disk-difference-valid
                    (left (lw-euler-circle-real-native-polynomial rate radius anchor-error target (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request))) (right (lw-euler-circle-real-normalized-polynomial rate radius inner plus-arcs minus-arcs anchor-error request (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request))) (radius (lw-euler-circle-real-native-radius rate radius inner anchor-error)) (count (+ (len (lw-euler-circle-real-native-polynomial rate radius anchor-error target (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request))) (len (lw-euler-circle-real-normalized-polynomial rate radius inner plus-arcs minus-arcs anchor-error request (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)))))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-circle-real-native-difference lw-ernc-length-natural
              lw-ernc-left-commutes lw-ernc-left-distributes lw-ernc-fold-constants
              lw-ernc-times-negative lw-ernc-negative-times lw-ernc-zero-times
              lw-ernc-minus-one lw-ernc-double-negative lw-ernc-add-cancel lw-ernc-double lw-ernc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-ernc-difference-point-bound
   (implies (and (lw-euler-circle-coverp (cons rate 0) radius plus-arcs minus-arcs)
                (lw-euler-value-clearance-check rate 0 anchor-error)
                (equal (lw-euler-circle-interior-count (cons rate 0) radius plus-arcs minus-arcs) 0)
                (rationalp rate) (< 3 rate) (rationalp inner)
                (< (- rate 1) inner) (< inner radius)
                (rationalp request) (< 0 request) (<= request 1/4) (natp target) (lw-complex-diskp point 1))
            (lw-complex-diskp (lw-complex-polynomial (lw-euler-circle-real-native-difference rate radius inner plus-arcs minus-arcs anchor-error target request) point 0) (lw-euler-circle-real-native-model-error rate radius inner plus-arcs minus-arcs anchor-error request)))
   :hints (("Goal"
            :use (lw-euler-circle-real-native-model-data
                  (:instance lw-complex-disk-data (radius 1))
                  (:instance lw-complex-scale-disk (factor (lw-euler-circle-real-native-radius rate radius inner anchor-error)) (radius 1))
                  (:instance lw-euler-circle-real-native-polynomial-comparison (point (lw-complex-scale (lw-euler-circle-real-native-radius rate radius inner anchor-error) point)))
                  (:instance lw-polynomial-disk-difference-evaluation
                    (left (lw-euler-circle-real-native-polynomial rate radius anchor-error target (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request))) (right (lw-euler-circle-real-normalized-polynomial rate radius inner plus-arcs minus-arcs anchor-error request (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request))) (radius (lw-euler-circle-real-native-radius rate radius inner anchor-error)) (count (+ (len (lw-euler-circle-real-native-polynomial rate radius anchor-error target (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request))) (len (lw-euler-circle-real-normalized-polynomial rate radius inner plus-arcs minus-arcs anchor-error request (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)))))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              abs lw-euler-circle-real-native-difference lw-ernc-length-natural
              lw-ernc-left-commutes lw-ernc-left-distributes lw-ernc-fold-constants
              lw-ernc-times-negative lw-ernc-negative-times lw-ernc-zero-times
              lw-ernc-minus-one lw-ernc-double-negative lw-ernc-add-cancel lw-ernc-double lw-ernc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-ernc-difference-boundary-check
   (implies (and (lw-euler-circle-coverp (cons rate 0) radius plus-arcs minus-arcs)
                (lw-euler-value-clearance-check rate 0 anchor-error)
                (equal (lw-euler-circle-interior-count (cons rate 0) radius plus-arcs minus-arcs) 0)
                (rationalp rate) (< 3 rate) (rationalp inner)
                (< (- rate 1) inner) (< inner radius)
                (rationalp request) (< 0 request) (<= request 1/4) (natp target) (natp degree) (natp count))
            (lw-cauchy-boundary-check (lw-euler-circle-real-native-difference rate radius inner plus-arcs minus-arcs anchor-error target request) (lw-cauchy-orbit-rotation degree) 0 count (lw-euler-circle-real-native-model-error rate radius inner plus-arcs minus-arcs anchor-error request)))
   :hints (("Goal" :induct (lw-cauchy-boundary-check (lw-euler-circle-real-native-difference rate radius inner plus-arcs minus-arcs anchor-error target request) (lw-cauchy-orbit-rotation degree) 0 count (lw-euler-circle-real-native-model-error rate radius inner plus-arcs minus-arcs anchor-error request))
                   :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-cauchy-boundary-check
              lw-ernc-left-commutes lw-ernc-left-distributes lw-ernc-fold-constants
              lw-ernc-times-negative lw-ernc-negative-times lw-ernc-zero-times
              lw-ernc-minus-one lw-ernc-double-negative lw-ernc-add-cancel lw-ernc-double lw-ernc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory)))
           (and stable-under-simplificationp
                '(:use (lw-cauchy-orbit-data
                        (:instance lw-complex-unit-power (point (lw-cauchy-orbit-rotation degree)) (index (- count 1)))
                        (:instance lw-ernc-difference-point-bound
                          (point (lw-complex-power (lw-cauchy-orbit-rotation degree) (- count 1)))))
                  :do-not-induct t)))
   :rule-classes nil))

(local
 (defthm lw-ernc-difference-caps
   (implies (and (lw-euler-circle-coverp (cons rate 0) radius plus-arcs minus-arcs)
                (lw-euler-value-clearance-check rate 0 anchor-error)
                (equal (lw-euler-circle-interior-count (cons rate 0) radius plus-arcs minus-arcs) 0)
                (rationalp rate) (< 3 rate) (rationalp inner)
                (< (- rate 1) inner) (< inner radius)
                (rationalp request) (< 0 request) (<= request 1/4) (natp target))
            (lw-polynomial-coefficient-caps (lw-euler-circle-real-native-difference rate radius inner plus-arcs minus-arcs anchor-error target request) (lw-euler-circle-real-native-model-error rate radius inner plus-arcs minus-arcs anchor-error request)))
   :hints (("Goal"
            :use (lw-euler-circle-real-native-model-data lw-ernc-difference-data
                  (:instance lw-polynomial-cauchy-cap-data (coefficients (lw-euler-circle-real-native-difference rate radius inner plus-arcs minus-arcs anchor-error target request)) (cap (lw-euler-circle-real-native-model-error rate radius inner plus-arcs minus-arcs anchor-error request)))
                  (:instance lw-ernc-difference-boundary-check
                    (degree (len (lw-euler-circle-real-native-difference rate radius inner plus-arcs minus-arcs anchor-error target request)))
                    (count (lw-cauchy-coefficient-count (lw-euler-circle-real-native-difference rate radius inner plus-arcs minus-arcs anchor-error target request) (len (lw-euler-circle-real-native-difference rate radius inner plus-arcs minus-arcs anchor-error target request))
                             (lw-polynomial-cap-test-error (lw-euler-circle-real-native-difference rate radius inner plus-arcs minus-arcs anchor-error target request) (lw-euler-circle-real-native-model-error rate radius inner plus-arcs minus-arcs anchor-error request)))))
                  (:instance lw-polynomial-cauchy-cap-check-sound (coefficients (lw-euler-circle-real-native-difference rate radius inner plus-arcs minus-arcs anchor-error target request)) (cap (lw-euler-circle-real-native-model-error rate radius inner plus-arcs minus-arcs anchor-error request))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-polynomial-cauchy-cap-check
              lw-ernc-left-commutes lw-ernc-left-distributes lw-ernc-fold-constants
              lw-ernc-times-negative lw-ernc-negative-times lw-ernc-zero-times
              lw-ernc-minus-one lw-ernc-double-negative lw-ernc-add-cancel lw-ernc-double lw-ernc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-euler-circle-real-native-coefficient-comparison
  (implies (and (lw-euler-circle-coverp (cons rate 0) radius plus-arcs minus-arcs)
                (lw-euler-value-clearance-check rate 0 anchor-error)
                (equal (lw-euler-circle-interior-count (cons rate 0) radius plus-arcs minus-arcs) 0)
                (rationalp rate) (< 3 rate) (rationalp inner)
                (< (- rate 1) inner) (< inner radius)
                (rationalp request) (< 0 request) (<= request 1/4) (natp target) (natp index))
           (and (lw-complexp (lw-complex-coefficient-at (lw-euler-circle-real-native-polynomial rate radius anchor-error target (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) index 0)) (lw-complexp (lw-complex-coefficient-at (lw-euler-circle-real-normalized-polynomial rate radius inner plus-arcs minus-arcs anchor-error request (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) index 0))
                (lw-complex-diskp (lw-complex-sub (lw-complex-coefficient-at (lw-euler-circle-real-native-polynomial rate radius anchor-error target (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) index 0) (lw-complex-coefficient-at (lw-euler-circle-real-normalized-polynomial rate radius inner plus-arcs minus-arcs anchor-error request (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) index 0)) (* (lw-euler-circle-real-native-model-error rate radius inner plus-arcs minus-arcs anchor-error request) (/ (lw-rational-power (lw-euler-circle-real-native-radius rate radius inner anchor-error) index))))))
  :hints (("Goal"
           :use (lw-euler-circle-real-native-model-data lw-ernc-difference-caps
                 (:instance lw-polynomial-disk-difference-capped-coefficient
                   (left (lw-euler-circle-real-native-polynomial rate radius anchor-error target (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request))) (right (lw-euler-circle-real-normalized-polynomial rate radius inner plus-arcs minus-arcs anchor-error request (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request))) (radius (lw-euler-circle-real-native-radius rate radius inner anchor-error)) (count (+ (len (lw-euler-circle-real-native-polynomial rate radius anchor-error target (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request))) (len (lw-euler-circle-real-normalized-polynomial rate radius inner plus-arcs minus-arcs anchor-error request (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request))))) (cap (lw-euler-circle-real-native-model-error rate radius inner plus-arcs minus-arcs anchor-error request)))
                 (:instance lw-complex-coefficient-at-rational (coefficients (lw-euler-circle-real-native-polynomial rate radius anchor-error target (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request))) (target index) (offset 0))
                 (:instance lw-complex-coefficient-at-rational (coefficients (lw-euler-circle-real-normalized-polynomial rate radius inner plus-arcs minus-arcs anchor-error request (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request))) (target index) (offset 0))
                 (:instance lw-polynomial-rescale-coefficient (coefficients (lw-euler-circle-real-native-polynomial rate radius anchor-error target (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request))) (factor (lw-euler-circle-real-native-radius rate radius inner anchor-error)) (target index) (offset 0))
                 (:instance lw-polynomial-rescale-coefficient (coefficients (lw-euler-circle-real-normalized-polynomial rate radius inner plus-arcs minus-arcs anchor-error request (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request))) (factor (lw-euler-circle-real-native-radius rate radius inner anchor-error)) (target index) (offset 0))
                 (:instance lw-complex-sub-scales (a (lw-complex-coefficient-at (lw-euler-circle-real-native-polynomial rate radius anchor-error target (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) index 0)) (b (lw-complex-coefficient-at (lw-euler-circle-real-normalized-polynomial rate radius inner plus-arcs minus-arcs anchor-error request (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) index 0)) (factor (lw-rational-power (lw-euler-circle-real-native-radius rate radius inner anchor-error) index)))
                 (:instance lw-rational-power-positive (base (lw-euler-circle-real-native-radius rate radius inner anchor-error)) (exponent index))
                 (:instance lw-complex-scale-disk (point (lw-complex-scale (lw-rational-power (lw-euler-circle-real-native-radius rate radius inner anchor-error) index) (lw-complex-sub (lw-complex-coefficient-at (lw-euler-circle-real-native-polynomial rate radius anchor-error target (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) index 0) (lw-complex-coefficient-at (lw-euler-circle-real-normalized-polynomial rate radius inner plus-arcs minus-arcs anchor-error request (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) index 0)))) (radius (lw-euler-circle-real-native-model-error rate radius inner plus-arcs minus-arcs anchor-error request)) (factor (/ (lw-rational-power (lw-euler-circle-real-native-radius rate radius inner anchor-error) index))))
                 (:instance lw-complex-scale-compose (point (lw-complex-sub (lw-complex-coefficient-at (lw-euler-circle-real-native-polynomial rate radius anchor-error target (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) index 0) (lw-complex-coefficient-at (lw-euler-circle-real-normalized-polynomial rate radius inner plus-arcs minus-arcs anchor-error request (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) index 0))) (left (/ (lw-rational-power (lw-euler-circle-real-native-radius rate radius inner anchor-error) index))) (right (lw-rational-power (lw-euler-circle-real-native-radius rate radius inner anchor-error) index)))
                 (:instance inverse-of-* (x (lw-rational-power (lw-euler-circle-real-native-radius rate radius inner anchor-error) index))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-circle-real-native-difference lw-ernc-length-natural
              lw-rational-power-rational lw-reciprocal-positive lw-complex-ring-rational
              lw-complex-scale-one abs
              lw-ernc-left-commutes lw-ernc-left-distributes lw-ernc-fold-constants
              lw-ernc-times-negative lw-ernc-negative-times lw-ernc-zero-times
              lw-ernc-minus-one lw-ernc-double-negative lw-ernc-add-cancel lw-ernc-double lw-ernc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
