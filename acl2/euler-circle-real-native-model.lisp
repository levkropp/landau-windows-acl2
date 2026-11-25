(in-package "ACL2")

(include-book "euler-circle-real-normalized-comparison")
(include-book "euler-circle-reflected-native-log")
(include-book "euler-normalized-polynomial")
(include-book "euler-circle-mellin-precision")

(defun lw-euler-circle-real-native-radius (rate radius inner anchor-error)
  (min inner (min (lw-euler-circle-center-radius (cons rate 0) radius anchor-error) (lw-euler-normalized-disk-radius rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error))))

(defun lw-euler-circle-real-native-polynomial (rate radius anchor-error target error)
  (lw-polynomial-rescale
   (lw-euler-normalized-polynomial rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error target error) -1 0))

(defun lw-euler-circle-real-native-error-at
    (rate radius inner plus-arcs minus-arcs anchor-error error)
  (let* ((outer-radius (lw-euler-circle-outer-radius (cons rate 0) radius))
         (native-request (lw-euler-normalized-request rate 0 outer-radius anchor-error error))
         (local-radius (lw-euler-circle-real-native-radius rate radius inner anchor-error)))
    (+ (* (lw-normalized-local-inverse-cost (cons rate 0)
          (lw-euler-normalized-disk-radius rate 0 outer-radius anchor-error)
          (lw-euler-uniform-log-cap rate 0 outer-radius anchor-error)) native-request)
       (* (/ (* 1/4 (lw-complex-l1 (cons rate 0)))) (/ (* 1/4 (lw-complex-l1 (lw-complex-sub (cons rate 0) (cons 1 0)))))
          (+ (lw-euler-circle-center-coefficient-error (cons rate 0) radius anchor-error error error error native-request error)
             (* (lw-normalized-local-point-cap (cons rate 0) local-radius)
                (+ error (lw-euler-circle-at-one-log-error rate radius error error native-request)))))
       (* (lw-euler-circle-real-anchor-numerator-cap rate radius inner plus-arcs minus-arcs local-radius) error))))

(defun lw-euler-circle-real-native-model-error (rate radius inner plus-arcs minus-arcs anchor-error request)
  (lw-euler-circle-real-native-error-at rate radius inner plus-arcs minus-arcs anchor-error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)))

(local (defthm lw-ernb-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ernb-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ernb-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ernb-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ernb-times-negative (a b) (b a)))
                 :in-theory (disable lw-ernb-times-negative)))))

(local (defthm lw-ernb-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ernb-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ernb-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ernb-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ernb-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ernb-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ernb-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ernb-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ernb-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ernb-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ernb-left-commutes)))))

(local
 (defthm lw-ernb-anchor-disk
   (implies (and (rationalp rate) (<= 1 rate) (rationalp radius)
                 (<= (- rate 1) radius))
            (lw-complex-diskp (cons (- rate 1) 0) radius))
   :hints (("Goal"
            :use ((:instance lw-complex-disk-norm-square (point (cons (- rate 1) 0)))
                  (:instance lw-ernb-multiply-order (a (- rate 1)) (b radius) (factor radius))
                  (:instance lw-ernb-multiply-order (a (- rate 1)) (b radius) (factor (- rate 1))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complexp lw-complex-norm-square
              lw-ernb-left-commutes lw-ernb-left-distributes lw-ernb-fold-constants
              lw-ernb-times-negative lw-ernb-negative-times lw-ernb-zero-times
              lw-ernb-minus-one lw-ernb-double-negative lw-ernb-add-cancel lw-ernb-double lw-ernb-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-ernb-radius-data
   (implies (and (lw-euler-circle-coverp (cons rate 0) radius plus-arcs minus-arcs)
                (lw-euler-value-clearance-check rate 0 anchor-error)
                (equal (lw-euler-circle-interior-count (cons rate 0) radius plus-arcs minus-arcs) 0)
                (rationalp rate) (< 3 rate) (rationalp inner)
                (< (- rate 1) inner) (< inner radius)
                (rationalp request) (< 0 request) (<= request 1/4))
            (and (rationalp (lw-euler-circle-real-native-radius rate radius inner anchor-error)) (< 0 (lw-euler-circle-real-native-radius rate radius inner anchor-error))
                 (rationalp (lw-euler-circle-center-radius (cons rate 0) radius anchor-error)) (rationalp (lw-euler-normalized-disk-radius rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error))
                 (<= (lw-euler-circle-real-native-radius rate radius inner anchor-error) inner) (<= (lw-euler-circle-real-native-radius rate radius inner anchor-error) (lw-euler-circle-center-radius (cons rate 0) radius anchor-error))
                 (<= (lw-euler-circle-real-native-radius rate radius inner anchor-error) (lw-euler-normalized-disk-radius rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error))
                 (<= (lw-euler-circle-real-native-radius rate radius inner anchor-error) (* 1/4 (lw-complex-l1 (cons rate 0))))
                 (<= (lw-euler-circle-real-native-radius rate radius inner anchor-error) (* 1/4 (lw-complex-l1 (lw-complex-sub (cons rate 0) (cons 1 0)))))))
   :hints (("Goal"
            :use ((:instance lw-euler-circle-outer-data (center (cons rate 0)))
                  (:instance lw-euler-circle-joint-request-adequate (center (cons rate 0)) (target 0))
                  (:instance lw-euler-circle-center-model-data (center (cons rate 0)) (target 0) (error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) (epsilon (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)))
                  (:instance lw-euler-normalized-disk-data (height 0) (outer-radius (lw-euler-circle-outer-radius (cons rate 0) radius))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-circle-real-native-radius min
              lw-ernb-left-commutes lw-ernb-left-distributes lw-ernb-fold-constants
              lw-ernb-times-negative lw-ernb-negative-times lw-ernb-zero-times
              lw-ernb-minus-one lw-ernb-double-negative lw-ernb-add-cancel lw-ernb-double lw-ernb-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-ernb-alignment-data
   (implies (and (lw-euler-circle-coverp (cons rate 0) radius plus-arcs minus-arcs)
                (lw-euler-value-clearance-check rate 0 anchor-error)
                (equal (lw-euler-circle-interior-count (cons rate 0) radius plus-arcs minus-arcs) 0)
                (rationalp rate) (< 3 rate) (rationalp inner)
                (< (- rate 1) inner) (< inner radius)
                (rationalp request) (< 0 request) (<= request 1/4) (lw-complex-diskp point (lw-euler-circle-real-native-radius rate radius inner anchor-error)))
            (and (rationalp (lw-euler-circle-outer-radius (cons rate 0) radius)) (< 0 (lw-euler-circle-outer-radius (cons rate 0) radius)) (< (lw-euler-circle-outer-radius (cons rate 0) radius) rate)
                 (rationalp (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) (< 0 (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) (<= (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request) 1/4)
                 (rationalp (lw-euler-normalized-request rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request))) (< 0 (lw-euler-normalized-request rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request))) (<= (lw-euler-normalized-request rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) 1/4)
                 (rationalp (lw-euler-normalized-gamma rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)))
                 (lw-complexp point) (lw-complexp (lw-complex-scale -1 point))
                 (lw-complex-diskp point (lw-euler-circle-center-radius (cons rate 0) radius anchor-error)) (lw-complex-diskp (lw-complex-scale -1 point) (lw-euler-normalized-disk-radius rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error))
                 (lw-complex-diskp (cons (- rate 1) 0) inner)
                 (lw-complexp (lw-complex-sub (lw-complex-sub (cons rate 0) point) (cons 1 0))) (lw-complexp (lw-complex-sub (cons rate 0) point))
                 (not (equal (lw-complex-sub (lw-complex-sub (cons rate 0) point) (cons 1 0)) (cons 0 0))) (not (equal (lw-complex-sub (cons rate 0) point) (cons 0 0)))
                 (equal (lw-complex-add (cons 1 0) (lw-complex-sub (lw-complex-sub (cons rate 0) point) (cons 1 0))) (lw-complex-sub (cons rate 0) point))
                 (equal (lw-complex-add (cons rate 0) (lw-complex-scale -1 point)) (lw-complex-sub (cons rate 0) point))
                 (equal (lw-complex-add (lw-complex-sub (cons rate 0) (cons 1 0)) (lw-complex-scale -1 point)) (lw-complex-sub (lw-complex-sub (cons rate 0) point) (cons 1 0)))
                 (lw-complex-diskp (lw-complex-sub (cons rate 0) point) (lw-normalized-local-point-cap (cons rate 0) (lw-euler-circle-real-native-radius rate radius inner anchor-error)))
                 (lw-complex-diskp (lw-complex-reciprocal (lw-complex-mul (lw-complex-sub (cons rate 0) point) (lw-complex-sub (lw-complex-sub (cons rate 0) point) (cons 1 0)))) (* (/ (* 1/4 (lw-complex-l1 (cons rate 0)))) (/ (* 1/4 (lw-complex-l1 (lw-complex-sub (cons rate 0) (cons 1 0)))))))))
   :hints (("Goal"
            :use (lw-ernb-radius-data
                  (:instance lw-ernb-anchor-disk (radius inner))
                  (:instance lw-euler-circle-outer-data (center (cons rate 0)))
                  (:instance lw-complex-disk-data (radius (lw-euler-circle-real-native-radius rate radius inner anchor-error)))
                  (:instance lw-complex-scale-disk (factor -1) (radius (lw-euler-circle-real-native-radius rate radius inner anchor-error)))
                  (:instance lw-complex-scale-rational (factor -1))
                  (:instance lw-complex-disk-enlarge (radius (lw-euler-circle-real-native-radius rate radius inner anchor-error)) (cap (lw-euler-circle-center-radius (cons rate 0) radius anchor-error)))
                  (:instance lw-complex-disk-enlarge (point (lw-complex-scale -1 point)) (radius (lw-euler-circle-real-native-radius rate radius inner anchor-error)) (cap (lw-euler-normalized-disk-radius rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error)))
                  (:instance lw-euler-circle-joint-request-adequate (center (cons rate 0)) (target 0))
                  (:instance lw-euler-normalized-disk-data (height 0) (outer-radius (lw-euler-circle-outer-radius (cons rate 0) radius)))
                  (:instance lw-euler-normalized-request-data (height 0) (outer-radius (lw-euler-circle-outer-radius (cons rate 0) radius)) (error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)))
                  (:instance lw-euler-normalized-request-upper (height 0) (outer-radius (lw-euler-circle-outer-radius (cons rate 0) radius)) (error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)))
                  (:instance lw-euler-circle-real-normalized-point-data (local-radius (lw-euler-circle-real-native-radius rate radius inner anchor-error))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              abs
              lw-ernb-left-commutes lw-ernb-left-distributes lw-ernb-fold-constants
              lw-ernb-times-negative lw-ernb-negative-times lw-ernb-zero-times
              lw-ernb-minus-one lw-ernb-double-negative lw-ernb-add-cancel lw-ernb-double lw-ernb-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-ernb-native-model-value
   (implies (and (lw-euler-circle-coverp (cons rate 0) radius plus-arcs minus-arcs)
                (lw-euler-value-clearance-check rate 0 anchor-error)
                (equal (lw-euler-circle-interior-count (cons rate 0) radius plus-arcs minus-arcs) 0)
                (rationalp rate) (< 3 rate) (rationalp inner)
                (< (- rate 1) inner) (< inner radius)
                (rationalp request) (< 0 request) (<= request 1/4)
                (natp target) (lw-complex-diskp point (lw-euler-circle-real-native-radius rate radius inner anchor-error)))
            (and (lw-complex-coefficientsp (lw-euler-circle-real-native-polynomial rate radius anchor-error target (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request))) (lw-complexp (lw-complex-polynomial (lw-euler-circle-real-native-polynomial rate radius anchor-error target (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) point 0)) (lw-complexp (lw-complex-normalized-euler (lw-complex-sub (lw-complex-sub (cons rate 0) point) (cons 1 0)) (lw-complex-polynomial (lw-euler-uniform-log-polynomial rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error target (lw-euler-normalized-request rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request))) (lw-complex-scale -1 point) 0) (cons (lw-euler-normalized-gamma rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) 0)))
                 (lw-complex-diskp (lw-complex-sub (lw-complex-polynomial (lw-euler-circle-real-native-polynomial rate radius anchor-error target (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) point 0) (lw-complex-normalized-euler (lw-complex-sub (lw-complex-sub (cons rate 0) point) (cons 1 0)) (lw-complex-polynomial (lw-euler-uniform-log-polynomial rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error target (lw-euler-normalized-request rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request))) (lw-complex-scale -1 point) 0) (cons (lw-euler-normalized-gamma rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) 0))) (* (lw-normalized-local-inverse-cost (cons rate 0) (lw-euler-normalized-disk-radius rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error) (lw-euler-uniform-log-cap rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error)) (lw-euler-normalized-request rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request))))))
   :hints (("Goal"
            :use (lw-ernb-alignment-data
                  (:instance lw-euler-normalized-polynomial-valid (height 0) (outer-radius (lw-euler-circle-outer-radius (cons rate 0) radius)) (error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)))
                  (:instance lw-complex-euler-normalized-polynomial-model-error (height 0) (outer-radius (lw-euler-circle-outer-radius (cons rate 0) radius)) (point (lw-complex-scale -1 point)) (error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)))
                  (:instance lw-euler-uniform-log-polynomial-valid (height 0) (outer-radius (lw-euler-circle-outer-radius (cons rate 0) radius)) (error (lw-euler-normalized-request rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request))))
                  (:instance lw-complex-polynomial-rational
                    (coefficients (lw-euler-uniform-log-polynomial rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error target (lw-euler-normalized-request rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)))) (point (lw-complex-scale -1 point)) (offset 0))
                  (:instance lw-complex-local-normalization-normalized (anchor (cons rate 0)) (point (lw-complex-scale -1 point)) (value (lw-complex-polynomial (lw-euler-uniform-log-polynomial rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error target (lw-euler-normalized-request rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request))) (lw-complex-scale -1 point) 0)) (gamma (lw-euler-normalized-gamma rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request))))
                  (:instance lw-polynomial-rescale-valid (coefficients (lw-euler-normalized-polynomial rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error target (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request))) (factor -1) (offset 0))
                  (:instance lw-polynomial-rescale-evaluation (coefficients (lw-euler-normalized-polynomial rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error target (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request))) (factor -1) (offset 0))
                  (:instance lw-complex-polynomial-rational (coefficients (lw-euler-normalized-polynomial rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error target (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request))) (point (lw-complex-scale -1 point)) (offset 0))
                  (:instance lw-complex-normalized-euler-rational (point (lw-complex-sub (lw-complex-sub (cons rate 0) point) (cons 1 0))) (value (lw-complex-polynomial (lw-euler-uniform-log-polynomial rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error target (lw-euler-normalized-request rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request))) (lw-complex-scale -1 point) 0)) (anchor (cons (lw-euler-normalized-gamma rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) 0)))
                  (:instance lw-complex-difference-symmetric (left (lw-complex-local-normalization (cons rate 0) (lw-complex-scale -1 point) (lw-complex-polynomial (lw-euler-uniform-log-polynomial rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error target (lw-euler-normalized-request rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request))) (lw-complex-scale -1 point) 0) (lw-euler-normalized-gamma rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)))) (right (lw-complex-polynomial (lw-euler-normalized-polynomial rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error target (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) (lw-complex-scale -1 point) 0)) (radius (* (lw-normalized-local-inverse-cost (cons rate 0) (lw-euler-normalized-disk-radius rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error) (lw-euler-uniform-log-cap rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error)) (lw-euler-normalized-request rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request))))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-circle-real-native-polynomial lw-complexp
              lw-ernb-left-commutes lw-ernb-left-distributes lw-ernb-fold-constants
              lw-ernb-times-negative lw-ernb-negative-times lw-ernb-zero-times
              lw-ernb-minus-one lw-ernb-double-negative lw-ernb-add-cancel lw-ernb-double lw-ernb-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-ernb-transport
   (implies (and (lw-euler-circle-coverp (cons rate 0) radius plus-arcs minus-arcs)
                (lw-euler-value-clearance-check rate 0 anchor-error)
                (equal (lw-euler-circle-interior-count (cons rate 0) radius plus-arcs minus-arcs) 0)
                (rationalp rate) (< 3 rate) (rationalp inner)
                (< (- rate 1) inner) (< inner radius)
                (rationalp request) (< 0 request) (<= request 1/4)
                (natp target) (lw-complex-diskp point (lw-euler-circle-real-native-radius rate radius inner anchor-error)))
            (lw-complex-diskp (lw-complex-sub (lw-complex-normalized-euler (lw-complex-sub (lw-complex-sub (cons rate 0) point) (cons 1 0)) (lw-complex-polynomial (lw-euler-uniform-log-polynomial rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error target (lw-euler-normalized-request rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request))) (lw-complex-scale -1 point) 0) (cons (lw-euler-normalized-gamma rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) 0)) (lw-complex-normalized-euler (lw-complex-sub (lw-complex-sub (cons rate 0) point) (cons 1 0)) (lw-complex-polynomial (lw-euler-circle-reflected-log-polynomial (cons rate 0) radius plus-arcs minus-arcs anchor-error request (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) point 0) (lw-complex-polynomial (lw-euler-circle-reflected-log-polynomial (cons rate 0) radius plus-arcs minus-arcs anchor-error request (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) (cons (- rate 1) 0) 0))) (* (/ (* 1/4 (lw-complex-l1 (cons rate 0)))) (/ (* 1/4 (lw-complex-l1 (lw-complex-sub (cons rate 0) (cons 1 0))))) (+ (lw-euler-circle-center-coefficient-error (cons rate 0) radius anchor-error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request) (lw-euler-normalized-request rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) (* (lw-normalized-local-point-cap (cons rate 0) (lw-euler-circle-real-native-radius rate radius inner anchor-error)) (+ (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-at-one-log-error rate radius (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request) (lw-euler-normalized-request rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)))))))))
   :hints (("Goal"
            :use (lw-ernb-alignment-data
                  (:instance lw-euler-circle-reflected-native-log-comparison (center (cons rate 0)) (native-error (lw-euler-normalized-request rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request))) (approximation-error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)))
                  (:instance lw-euler-circle-reflected-log-at-one (value-error (lw-euler-normalized-request rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request))) (approximation-error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)))
                  (:instance lw-euler-circle-reflected-log-bound (center (cons rate 0)) (point (cons (- rate 1) 0)) (approximation-error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)))
                  (:instance lw-complex-disk-data (point (lw-complex-polynomial (lw-euler-circle-reflected-log-polynomial (cons rate 0) radius plus-arcs minus-arcs anchor-error request (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) (cons (- rate 1) 0) 0)) (radius (lw-euler-circle-reflected-log-cap (cons rate 0) radius plus-arcs minus-arcs inner)))
                  (:instance lw-complex-difference-symmetric (left (lw-complex-polynomial (lw-euler-circle-reflected-log-polynomial (cons rate 0) radius plus-arcs minus-arcs anchor-error request (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) point 0)) (right (lw-complex-polynomial (lw-euler-uniform-log-polynomial rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error target (lw-euler-normalized-request rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request))) (lw-complex-scale -1 point) 0)) (radius (lw-euler-circle-center-coefficient-error (cons rate 0) radius anchor-error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request) (lw-euler-normalized-request rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request))))
                  (:instance lw-complex-difference-symmetric (left (lw-complex-polynomial (lw-euler-circle-reflected-log-polynomial (cons rate 0) radius plus-arcs minus-arcs anchor-error request (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) (cons (- rate 1) 0) 0)) (right (cons (lw-euler-normalized-gamma rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) 0)) (radius (+ (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-at-one-log-error rate radius (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request) (lw-euler-normalized-request rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request))))))
                  (:instance lw-complex-normalized-euler-transport (point (lw-complex-sub (lw-complex-sub (cons rate 0) point) (cons 1 0)))
                    (value (lw-complex-polynomial (lw-euler-uniform-log-polynomial rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error target (lw-euler-normalized-request rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request))) (lw-complex-scale -1 point) 0)) (other-value (lw-complex-polynomial (lw-euler-circle-reflected-log-polynomial (cons rate 0) radius plus-arcs minus-arcs anchor-error request (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) point 0)) (anchor (cons (lw-euler-normalized-gamma rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) 0)) (other-anchor (lw-complex-polynomial (lw-euler-circle-reflected-log-polynomial (cons rate 0) radius plus-arcs minus-arcs anchor-error request (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) (cons (- rate 1) 0) 0))
                    (point-cap (lw-normalized-local-point-cap (cons rate 0) (lw-euler-circle-real-native-radius rate radius inner anchor-error))) (inverse-cap (* (/ (* 1/4 (lw-complex-l1 (cons rate 0)))) (/ (* 1/4 (lw-complex-l1 (lw-complex-sub (cons rate 0) (cons 1 0)))))))
                    (value-error (lw-euler-circle-center-coefficient-error (cons rate 0) radius anchor-error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request) (lw-euler-normalized-request rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request))) (anchor-error (+ (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-at-one-log-error rate radius (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request) (lw-euler-normalized-request rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)))))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-normalized-gamma lw-complexp
              lw-ernb-left-commutes lw-ernb-left-distributes lw-ernb-fold-constants
              lw-ernb-times-negative lw-ernb-negative-times lw-ernb-zero-times
              lw-ernb-minus-one lw-ernb-double-negative lw-ernb-add-cancel lw-ernb-double lw-ernb-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-euler-circle-real-native-polynomial-comparison
  (implies (and (lw-euler-circle-coverp (cons rate 0) radius plus-arcs minus-arcs)
                (lw-euler-value-clearance-check rate 0 anchor-error)
                (equal (lw-euler-circle-interior-count (cons rate 0) radius plus-arcs minus-arcs) 0)
                (rationalp rate) (< 3 rate) (rationalp inner)
                (< (- rate 1) inner) (< inner radius)
                (rationalp request) (< 0 request) (<= request 1/4)
                (natp target) (lw-complex-diskp point (lw-euler-circle-real-native-radius rate radius inner anchor-error)))
           (and (lw-complex-coefficientsp (lw-euler-circle-real-native-polynomial rate radius anchor-error target (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)))
                (lw-complex-diskp (lw-complex-sub (lw-complex-polynomial (lw-euler-circle-real-native-polynomial rate radius anchor-error target (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) point 0) (lw-complex-polynomial (lw-euler-circle-real-normalized-polynomial rate radius inner plus-arcs minus-arcs anchor-error request (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) point 0)) (lw-euler-circle-real-native-model-error rate radius inner plus-arcs minus-arcs anchor-error request))))
  :hints (("Goal"
           :use (lw-ernb-radius-data lw-ernb-alignment-data lw-ernb-native-model-value lw-ernb-transport
                 (:instance lw-euler-circle-real-normalized-model-comparison (local-radius (lw-euler-circle-real-native-radius rate radius inner anchor-error)) (approximation-error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)))
                 (:instance lw-complex-difference-triangle (left (lw-complex-polynomial (lw-euler-circle-real-native-polynomial rate radius anchor-error target (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) point 0)) (middle (lw-complex-normalized-euler (lw-complex-sub (lw-complex-sub (cons rate 0) point) (cons 1 0)) (lw-complex-polynomial (lw-euler-uniform-log-polynomial rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error target (lw-euler-normalized-request rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request))) (lw-complex-scale -1 point) 0) (cons (lw-euler-normalized-gamma rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) 0))) (right (lw-complex-normalized-euler (lw-complex-sub (lw-complex-sub (cons rate 0) point) (cons 1 0)) (lw-complex-polynomial (lw-euler-circle-reflected-log-polynomial (cons rate 0) radius plus-arcs minus-arcs anchor-error request (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) point 0) (lw-complex-polynomial (lw-euler-circle-reflected-log-polynomial (cons rate 0) radius plus-arcs minus-arcs anchor-error request (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) (cons (- rate 1) 0) 0)))
                   (radius (* (lw-normalized-local-inverse-cost (cons rate 0) (lw-euler-normalized-disk-radius rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error) (lw-euler-uniform-log-cap rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error)) (lw-euler-normalized-request rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)))) (other-radius (* (/ (* 1/4 (lw-complex-l1 (cons rate 0)))) (/ (* 1/4 (lw-complex-l1 (lw-complex-sub (cons rate 0) (cons 1 0))))) (+ (lw-euler-circle-center-coefficient-error (cons rate 0) radius anchor-error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request) (lw-euler-normalized-request rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) (* (lw-normalized-local-point-cap (cons rate 0) (lw-euler-circle-real-native-radius rate radius inner anchor-error)) (+ (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-at-one-log-error rate radius (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request) (lw-euler-normalized-request rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)))))))))
                 (:instance lw-complex-difference-triangle (left (lw-complex-polynomial (lw-euler-circle-real-native-polynomial rate radius anchor-error target (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) point 0)) (middle (lw-complex-normalized-euler (lw-complex-sub (lw-complex-sub (cons rate 0) point) (cons 1 0)) (lw-complex-polynomial (lw-euler-circle-reflected-log-polynomial (cons rate 0) radius plus-arcs minus-arcs anchor-error request (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) point 0) (lw-complex-polynomial (lw-euler-circle-reflected-log-polynomial (cons rate 0) radius plus-arcs minus-arcs anchor-error request (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) (cons (- rate 1) 0) 0))) (right (lw-complex-polynomial (lw-euler-circle-real-normalized-polynomial rate radius inner plus-arcs minus-arcs anchor-error request (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) point 0))
                   (radius (+ (* (lw-normalized-local-inverse-cost (cons rate 0) (lw-euler-normalized-disk-radius rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error) (lw-euler-uniform-log-cap rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error)) (lw-euler-normalized-request rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request))) (* (/ (* 1/4 (lw-complex-l1 (cons rate 0)))) (/ (* 1/4 (lw-complex-l1 (lw-complex-sub (cons rate 0) (cons 1 0))))) (+ (lw-euler-circle-center-coefficient-error (cons rate 0) radius anchor-error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request) (lw-euler-normalized-request rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) (* (lw-normalized-local-point-cap (cons rate 0) (lw-euler-circle-real-native-radius rate radius inner anchor-error)) (+ (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-at-one-log-error rate radius (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request) (lw-euler-normalized-request rate 0 (lw-euler-circle-outer-radius (cons rate 0) radius) anchor-error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request))))))))) (other-radius (* (lw-euler-circle-real-anchor-numerator-cap rate radius inner plus-arcs minus-arcs (lw-euler-circle-real-native-radius rate radius inner anchor-error)) (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-circle-real-native-model-error lw-euler-circle-real-native-error-at
              lw-ernb-left-commutes lw-ernb-left-distributes lw-ernb-fold-constants
              lw-ernb-times-negative lw-ernb-negative-times lw-ernb-zero-times
              lw-ernb-minus-one lw-ernb-double-negative lw-ernb-add-cancel lw-ernb-double lw-ernb-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
(defthm lw-euler-circle-real-native-error-scales
  (implies (and (lw-euler-circle-coverp (cons rate 0) radius plus-arcs minus-arcs)
                (lw-euler-value-clearance-check rate 0 anchor-error)
                (rationalp rate) (< 3 rate)
                (rationalp error) (< 0 error) (<= error 1))
           (equal (lw-euler-circle-real-native-error-at rate radius inner plus-arcs minus-arcs anchor-error error) (* error (lw-euler-circle-real-native-error-at rate radius inner plus-arcs minus-arcs anchor-error 1))))
  :hints (("Goal"
           :use ((:instance lw-euler-circle-native-requests-scale (center (cons rate 0))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-circle-real-native-error-at
              lw-euler-circle-at-one-log-error lw-euler-circle-at-one-value-error
              lw-euler-circle-at-one-derivative-error lw-euler-circle-center-coefficient-error
              lw-euler-circle-center-native-quotient-error
              lw-ernb-left-commutes lw-ernb-left-distributes lw-ernb-fold-constants
              lw-ernb-times-negative lw-ernb-negative-times lw-ernb-zero-times
              lw-ernb-minus-one lw-ernb-double-negative lw-ernb-add-cancel lw-ernb-double lw-ernb-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(defthm lw-euler-circle-real-native-model-data
  (implies (and (lw-euler-circle-coverp (cons rate 0) radius plus-arcs minus-arcs)
                (lw-euler-value-clearance-check rate 0 anchor-error)
                (equal (lw-euler-circle-interior-count (cons rate 0) radius plus-arcs minus-arcs) 0)
                (rationalp rate) (< 3 rate) (rationalp inner)
                (< (- rate 1) inner) (< inner radius)
                (rationalp request) (< 0 request) (<= request 1/4) (natp target))
           (and (rationalp (lw-euler-circle-real-native-radius rate radius inner anchor-error)) (< 0 (lw-euler-circle-real-native-radius rate radius inner anchor-error))
                (lw-complex-coefficientsp (lw-euler-circle-real-native-polynomial rate radius anchor-error target (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request))) (lw-complex-coefficientsp (lw-euler-circle-real-normalized-polynomial rate radius inner plus-arcs minus-arcs anchor-error request (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)))
                (rationalp (lw-euler-circle-real-native-model-error rate radius inner plus-arcs minus-arcs anchor-error request)) (<= 0 (lw-euler-circle-real-native-model-error rate radius inner plus-arcs minus-arcs anchor-error request))))
  :hints (("Goal"
           :use (lw-ernb-radius-data
                 (:instance lw-euler-circle-joint-request-adequate (center (cons rate 0)) (target 0))
                 (:instance lw-euler-circle-real-native-polynomial-comparison (point (cons 0 0)))
                 (:instance lw-euler-circle-real-normalized-boundary
                   (point (cons inner 0)) (approximation-error (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)))
                 (:instance lw-complex-zero-disk (radius (lw-euler-circle-real-native-radius rate radius inner anchor-error)))
                 (:instance lw-complex-disk-data
                   (point (lw-complex-sub (lw-complex-polynomial (lw-euler-circle-real-native-polynomial rate radius anchor-error target (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) (cons 0 0) 0) (lw-complex-polynomial (lw-euler-circle-real-normalized-polynomial rate radius inner plus-arcs minus-arcs anchor-error request (lw-euler-circle-joint-request (cons rate 0) radius plus-arcs minus-arcs anchor-error request)) (cons 0 0) 0)))
                   (radius (lw-euler-circle-real-native-model-error rate radius inner plus-arcs minus-arcs anchor-error request))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complexp lw-complex-norm-square
              lw-ernb-left-commutes lw-ernb-left-distributes lw-ernb-fold-constants
              lw-ernb-times-negative lw-ernb-negative-times lw-ernb-zero-times
              lw-ernb-minus-one lw-ernb-double-negative lw-ernb-add-cancel lw-ernb-double lw-ernb-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
