(in-package "ACL2")

(include-book "euler-circle-reflected-log-model")
(include-book "polynomial-real-anchor-normalization")
(include-book "polynomial-wide-linear-inverse")
(include-book "polynomial-product")
(include-book "polynomial-cauchy-caps")
(include-book "polynomial-capped-coefficients")

(defun lw-euler-circle-real-normalized-polynomial (rate radius inner plus-arcs minus-arcs anchor-error request approximation-error)
  (lw-polynomial-product (lw-polynomial-real-anchor-numerator (lw-euler-circle-reflected-log-polynomial (cons rate 0) radius plus-arcs minus-arcs anchor-error request approximation-error) rate) (lw-polynomial-wide-linear-inverse rate inner 0 approximation-error)))

(defun lw-euler-circle-real-normalized-cap (rate radius inner plus-arcs minus-arcs)
  (* (lw-polynomial-real-anchor-cap rate inner (lw-euler-circle-reflected-log-cap (cons rate 0) radius plus-arcs minus-arcs inner)) (+ 1 (/ (- rate inner)))))

(local (defthm lw-ernm-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ernm-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ernm-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ernm-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ernm-times-negative (a b) (b a)))
                 :in-theory (disable lw-ernm-times-negative)))))

(local (defthm lw-ernm-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ernm-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ernm-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ernm-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ernm-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ernm-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ernm-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ernm-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ernm-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ernm-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ernm-left-commutes)))))

(local
 (defthm lw-ernm-anchor-disk
   (implies (and (rationalp rate) (<= 1 rate) (rationalp inner)
                 (<= (- rate 1) inner))
            (lw-complex-diskp (cons (- rate 1) 0) inner))
   :hints (("Goal"
            :use ((:instance lw-complex-disk-norm-square (point (cons (- rate 1) 0)) (radius inner))
                  (:instance lw-ernm-multiply-order (a (- rate 1)) (b inner) (factor inner))
                  (:instance lw-ernm-multiply-order (a (- rate 1)) (b inner) (factor (- rate 1))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complexp lw-complex-norm-square
              lw-ernm-left-commutes lw-ernm-left-distributes lw-ernm-fold-constants
              lw-ernm-times-negative lw-ernm-negative-times lw-ernm-zero-times
              lw-ernm-minus-one lw-ernm-double-negative lw-ernm-add-cancel lw-ernm-double lw-ernm-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-euler-circle-real-normalized-boundary
  (implies (and (lw-euler-circle-coverp (cons rate 0) radius plus-arcs minus-arcs)
                (lw-euler-value-clearance-check rate 0 anchor-error)
                (equal (lw-euler-circle-interior-count (cons rate 0) radius plus-arcs minus-arcs) 0)
                (rationalp request) (< 0 request)
                (rationalp approximation-error) (< 0 approximation-error)
                (<= approximation-error 1)
                (rationalp rate) (< 1 rate) (rationalp inner)
                (< (- rate 1) inner) (< inner radius) (lw-complexp point)
                (equal (lw-complex-norm-square point) (* inner inner)))
           (and (lw-complex-coefficientsp (lw-euler-circle-real-normalized-polynomial rate radius inner plus-arcs minus-arcs anchor-error request approximation-error)) (lw-complex-diskp (lw-complex-polynomial (lw-euler-circle-real-normalized-polynomial rate radius inner plus-arcs minus-arcs anchor-error request approximation-error) point 0) (lw-euler-circle-real-normalized-cap rate radius inner plus-arcs minus-arcs))))
  :hints (("Goal"
           :use ((:instance lw-euler-circle-outer-data (center (cons rate 0)))
                 (:instance lw-complex-disk-norm-square (radius inner))
                 lw-ernm-anchor-disk
                 (:instance lw-complex-disk-enlarge (radius inner) (cap radius))
                 (:instance lw-euler-circle-reflected-log-comparison (center (cons rate 0)))
                 (:instance lw-euler-circle-reflected-log-bound (center (cons rate 0)))
                 (:instance lw-euler-circle-reflected-log-bound (center (cons rate 0)) (point (cons (- rate 1) 0)))
                 (:instance lw-polynomial-real-anchor-numerator-identity (coefficients (lw-euler-circle-reflected-log-polynomial (cons rate 0) radius plus-arcs minus-arcs anchor-error request approximation-error)))
                 (:instance lw-polynomial-real-anchor-numerator-bound (coefficients (lw-euler-circle-reflected-log-polynomial (cons rate 0) radius plus-arcs minus-arcs anchor-error request approximation-error)) (radius inner) (cap (lw-euler-circle-reflected-log-cap (cons rate 0) radius plus-arcs minus-arcs inner)))
                 (:instance lw-polynomial-wide-linear-inverse-data (radius inner) (target 0) (error approximation-error))
                 (:instance lw-complex-disk-enlarge (point (lw-complex-polynomial (lw-polynomial-wide-linear-inverse rate inner 0 approximation-error) point 0))
                   (radius (+ (/ (- rate inner)) approximation-error)) (cap (+ 1 (/ (- rate inner)))))
                 (:instance lw-polynomial-product-valid (left (lw-polynomial-real-anchor-numerator (lw-euler-circle-reflected-log-polynomial (cons rate 0) radius plus-arcs minus-arcs anchor-error request approximation-error) rate)) (right (lw-polynomial-wide-linear-inverse rate inner 0 approximation-error)))
                 (:instance lw-polynomial-product-evaluation (left (lw-polynomial-real-anchor-numerator (lw-euler-circle-reflected-log-polynomial (cons rate 0) radius plus-arcs minus-arcs anchor-error request approximation-error) rate)) (right (lw-polynomial-wide-linear-inverse rate inner 0 approximation-error)))
                 (:instance lw-complex-mul-disk (left (lw-complex-polynomial (lw-polynomial-real-anchor-numerator (lw-euler-circle-reflected-log-polynomial (cons rate 0) radius plus-arcs minus-arcs anchor-error request approximation-error) rate) point 0)) (right (lw-complex-polynomial (lw-polynomial-wide-linear-inverse rate inner 0 approximation-error) point 0)) (radius (lw-polynomial-real-anchor-cap rate inner (lw-euler-circle-reflected-log-cap (cons rate 0) radius plus-arcs minus-arcs inner))) (other-radius (+ 1 (/ (- rate inner))))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-circle-real-normalized-polynomial lw-euler-circle-real-normalized-cap lw-reciprocal-positive
              lw-ernm-left-commutes lw-ernm-left-distributes lw-ernm-fold-constants
              lw-ernm-times-negative lw-ernm-negative-times lw-ernm-zero-times
              lw-ernm-minus-one lw-ernm-double-negative lw-ernm-add-cancel lw-ernm-double lw-ernm-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm lw-ernm-complex-real-multiply
   (implies (and (rationalp inner) (lw-complexp point))
            (and (equal (lw-complex-mul (cons inner 0) point) (lw-complex-scale inner point))
                 (equal (lw-complex-norm-square (cons inner 0)) (* inner inner))
                 (lw-complexp (cons inner 0))))
   :hints (("Goal" :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complexp lw-complex-mul lw-complex-scale lw-complex-norm-square
              lw-ernm-left-commutes lw-ernm-left-distributes lw-ernm-fold-constants
              lw-ernm-times-negative lw-ernm-negative-times lw-ernm-zero-times
              lw-ernm-minus-one lw-ernm-double-negative lw-ernm-add-cancel lw-ernm-double lw-ernm-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defthm lw-ernm-radial-sample
   (implies (and (rationalp inner) (lw-complexp point)
                 (equal (lw-complex-norm-square point) 1))
            (and (lw-complexp (lw-complex-scale inner point))
                 (equal (lw-complex-norm-square (lw-complex-scale inner point)) (* inner inner))))
   :hints (("Goal"
            :use (lw-ernm-complex-real-multiply
                  (:instance lw-complex-scale-rational (factor inner))
                  (:instance lw-complex-norm-square-product (left (cons inner 0)) (right point)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              
              lw-ernm-left-commutes lw-ernm-left-distributes lw-ernm-fold-constants
              lw-ernm-times-negative lw-ernm-negative-times lw-ernm-zero-times
              lw-ernm-minus-one lw-ernm-double-negative lw-ernm-add-cancel lw-ernm-double lw-ernm-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defthm lw-ernm-scaled-boundary
   (implies (and (lw-euler-circle-coverp (cons rate 0) radius plus-arcs minus-arcs)
                (lw-euler-value-clearance-check rate 0 anchor-error)
                (equal (lw-euler-circle-interior-count (cons rate 0) radius plus-arcs minus-arcs) 0)
                (rationalp request) (< 0 request)
                (rationalp approximation-error) (< 0 approximation-error)
                (<= approximation-error 1)
                (rationalp rate) (< 1 rate) (rationalp inner)
                (< (- rate 1) inner) (< inner radius) (lw-complexp point)
                 (equal (lw-complex-norm-square point) 1))
            (and (lw-complex-coefficientsp (lw-polynomial-rescale (lw-euler-circle-real-normalized-polynomial rate radius inner plus-arcs minus-arcs anchor-error request approximation-error) inner 0)) (lw-complex-diskp (lw-complex-polynomial (lw-polynomial-rescale (lw-euler-circle-real-normalized-polynomial rate radius inner plus-arcs minus-arcs anchor-error request approximation-error) inner 0) point 0) (lw-euler-circle-real-normalized-cap rate radius inner plus-arcs minus-arcs))))
   :hints (("Goal"
            :use (lw-ernm-radial-sample
                  (:instance lw-euler-circle-real-normalized-boundary (point (lw-complex-scale inner point)))
                  (:instance lw-polynomial-rescale-valid (coefficients (lw-euler-circle-real-normalized-polynomial rate radius inner plus-arcs minus-arcs anchor-error request approximation-error)) (factor inner) (offset 0))
                  (:instance lw-polynomial-rescale-evaluation (coefficients (lw-euler-circle-real-normalized-polynomial rate radius inner plus-arcs minus-arcs anchor-error request approximation-error)) (factor inner) (offset 0)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              
              lw-ernm-left-commutes lw-ernm-left-distributes lw-ernm-fold-constants
              lw-ernm-times-negative lw-ernm-negative-times lw-ernm-zero-times
              lw-ernm-minus-one lw-ernm-double-negative lw-ernm-add-cancel lw-ernm-double lw-ernm-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-ernm-scaled-check
   (implies (and (lw-euler-circle-coverp (cons rate 0) radius plus-arcs minus-arcs)
                (lw-euler-value-clearance-check rate 0 anchor-error)
                (equal (lw-euler-circle-interior-count (cons rate 0) radius plus-arcs minus-arcs) 0)
                (rationalp request) (< 0 request)
                (rationalp approximation-error) (< 0 approximation-error)
                (<= approximation-error 1)
                (rationalp rate) (< 1 rate) (rationalp inner)
                (< (- rate 1) inner) (< inner radius) (natp degree) (natp count))
            (lw-cauchy-boundary-check (lw-polynomial-rescale (lw-euler-circle-real-normalized-polynomial rate radius inner plus-arcs minus-arcs anchor-error request approximation-error) inner 0) (lw-cauchy-orbit-rotation degree) 0 count (lw-euler-circle-real-normalized-cap rate radius inner plus-arcs minus-arcs)))
   :hints (("Goal" :induct (lw-cauchy-boundary-check (lw-polynomial-rescale (lw-euler-circle-real-normalized-polynomial rate radius inner plus-arcs minus-arcs anchor-error request approximation-error) inner 0) (lw-cauchy-orbit-rotation degree) 0 count (lw-euler-circle-real-normalized-cap rate radius inner plus-arcs minus-arcs))
                   :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-cauchy-boundary-check
              lw-ernm-left-commutes lw-ernm-left-distributes lw-ernm-fold-constants
              lw-ernm-times-negative lw-ernm-negative-times lw-ernm-zero-times
              lw-ernm-minus-one lw-ernm-double-negative lw-ernm-add-cancel lw-ernm-double lw-ernm-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory)))
           (and stable-under-simplificationp
                '(:use (lw-cauchy-orbit-data
                        (:instance lw-cauchy-orbit-power-norm-one (index (- count 1)))
                        (:instance lw-complex-power-rational (point (lw-cauchy-orbit-rotation degree)) (index (- count 1)))
                        (:instance lw-ernm-scaled-boundary (point (lw-complex-power (lw-cauchy-orbit-rotation degree) (- count 1)))))
                  :do-not-induct t)))
   :rule-classes nil))

(local
 (defthm lw-ernm-scaled-caps
   (implies (and (lw-euler-circle-coverp (cons rate 0) radius plus-arcs minus-arcs)
                (lw-euler-value-clearance-check rate 0 anchor-error)
                (equal (lw-euler-circle-interior-count (cons rate 0) radius plus-arcs minus-arcs) 0)
                (rationalp request) (< 0 request)
                (rationalp approximation-error) (< 0 approximation-error)
                (<= approximation-error 1)
                (rationalp rate) (< 1 rate) (rationalp inner)
                (< (- rate 1) inner) (< inner radius))
            (and (lw-complex-coefficientsp (lw-euler-circle-real-normalized-polynomial rate radius inner plus-arcs minus-arcs anchor-error request approximation-error))
                 (lw-complex-coefficientsp (lw-polynomial-rescale (lw-euler-circle-real-normalized-polynomial rate radius inner plus-arcs minus-arcs anchor-error request approximation-error) inner 0))
                 (rationalp (lw-euler-circle-real-normalized-cap rate radius inner plus-arcs minus-arcs)) (<= 0 (lw-euler-circle-real-normalized-cap rate radius inner plus-arcs minus-arcs))
                 (lw-polynomial-coefficient-caps (lw-polynomial-rescale (lw-euler-circle-real-normalized-polynomial rate radius inner plus-arcs minus-arcs anchor-error request approximation-error) inner 0) (lw-euler-circle-real-normalized-cap rate radius inner plus-arcs minus-arcs))))
   :hints (("Goal"
            :use ((:instance lw-ernm-radial-sample (point (cons 1 0)))
                  (:instance lw-euler-circle-real-normalized-boundary (point (lw-complex-scale inner (cons 1 0))))
                  (:instance lw-ernm-scaled-boundary (point (cons 1 0)))
                  (:instance lw-complex-disk-data (point (lw-complex-polynomial (lw-polynomial-rescale (lw-euler-circle-real-normalized-polynomial rate radius inner plus-arcs minus-arcs anchor-error request approximation-error) inner 0) (cons 1 0) 0)) (radius (lw-euler-circle-real-normalized-cap rate radius inner plus-arcs minus-arcs)))
                  (:instance lw-polynomial-cauchy-cap-data (coefficients (lw-polynomial-rescale (lw-euler-circle-real-normalized-polynomial rate radius inner plus-arcs minus-arcs anchor-error request approximation-error) inner 0)) (cap (lw-euler-circle-real-normalized-cap rate radius inner plus-arcs minus-arcs)))
                  (:instance lw-ernm-scaled-check (degree (len (lw-polynomial-rescale (lw-euler-circle-real-normalized-polynomial rate radius inner plus-arcs minus-arcs anchor-error request approximation-error) inner 0)))
                    (count (lw-cauchy-coefficient-count (lw-polynomial-rescale (lw-euler-circle-real-normalized-polynomial rate radius inner plus-arcs minus-arcs anchor-error request approximation-error) inner 0) (len (lw-polynomial-rescale (lw-euler-circle-real-normalized-polynomial rate radius inner plus-arcs minus-arcs anchor-error request approximation-error) inner 0)) (lw-polynomial-cap-test-error (lw-polynomial-rescale (lw-euler-circle-real-normalized-polynomial rate radius inner plus-arcs minus-arcs anchor-error request approximation-error) inner 0) (lw-euler-circle-real-normalized-cap rate radius inner plus-arcs minus-arcs)))))
                  (:instance lw-polynomial-cauchy-cap-check-sound (coefficients (lw-polynomial-rescale (lw-euler-circle-real-normalized-polynomial rate radius inner plus-arcs minus-arcs anchor-error request approximation-error) inner 0)) (cap (lw-euler-circle-real-normalized-cap rate radius inner plus-arcs minus-arcs))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-polynomial-cauchy-cap-check (:executable-counterpart lw-complex-norm-square)
              lw-ernm-left-commutes lw-ernm-left-distributes lw-ernm-fold-constants
              lw-ernm-times-negative lw-ernm-negative-times lw-ernm-zero-times
              lw-ernm-minus-one lw-ernm-double-negative lw-ernm-add-cancel lw-ernm-double lw-ernm-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-euler-circle-real-normalized-coefficient-bound
  (implies (and (lw-euler-circle-coverp (cons rate 0) radius plus-arcs minus-arcs)
                (lw-euler-value-clearance-check rate 0 anchor-error)
                (equal (lw-euler-circle-interior-count (cons rate 0) radius plus-arcs minus-arcs) 0)
                (rationalp request) (< 0 request)
                (rationalp approximation-error) (< 0 approximation-error)
                (<= approximation-error 1)
                (rationalp rate) (< 1 rate) (rationalp inner)
                (< (- rate 1) inner) (< inner radius) (natp index))
           (lw-complex-diskp (lw-complex-coefficient-at (lw-euler-circle-real-normalized-polynomial rate radius inner plus-arcs minus-arcs anchor-error request approximation-error) index 0) (* (lw-euler-circle-real-normalized-cap rate radius inner plus-arcs minus-arcs) (/ (lw-rational-power inner index)))))
  :hints (("Goal"
           :use (lw-ernm-scaled-caps
                 (:instance lw-polynomial-capped-coefficient-at (coefficients (lw-polynomial-rescale (lw-euler-circle-real-normalized-polynomial rate radius inner plus-arcs minus-arcs anchor-error request approximation-error) inner 0)) (cap (lw-euler-circle-real-normalized-cap rate radius inner plus-arcs minus-arcs))
                   (target index) (offset 0))
                 (:instance lw-polynomial-rescale-coefficient (coefficients (lw-euler-circle-real-normalized-polynomial rate radius inner plus-arcs minus-arcs anchor-error request approximation-error)) (factor inner) (target index) (offset 0))
                 (:instance lw-rational-power-positive (base inner) (exponent index))
                 (:instance lw-complex-coefficient-at-rational (coefficients (lw-euler-circle-real-normalized-polynomial rate radius inner plus-arcs minus-arcs anchor-error request approximation-error)) (target index) (offset 0))
                 (:instance lw-complex-scale-disk (point (lw-complex-scale (lw-rational-power inner index) (lw-complex-coefficient-at (lw-euler-circle-real-normalized-polynomial rate radius inner plus-arcs minus-arcs anchor-error request approximation-error) index 0))) (radius (lw-euler-circle-real-normalized-cap rate radius inner plus-arcs minus-arcs))
                   (factor (/ (lw-rational-power inner index))))
                 (:instance lw-complex-scale-compose (left (/ (lw-rational-power inner index))) (right (lw-rational-power inner index)) (point (lw-complex-coefficient-at (lw-euler-circle-real-normalized-polynomial rate radius inner plus-arcs minus-arcs anchor-error request approximation-error) index 0)))
                 (:instance inverse-of-* (x (lw-rational-power inner index))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-rational-power-rational lw-reciprocal-positive abs lw-complex-scale-one
              lw-ernm-left-commutes lw-ernm-left-distributes lw-ernm-fold-constants
              lw-ernm-times-negative lw-ernm-negative-times lw-ernm-zero-times
              lw-ernm-minus-one lw-ernm-double-negative lw-ernm-add-cancel lw-ernm-double lw-ernm-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
