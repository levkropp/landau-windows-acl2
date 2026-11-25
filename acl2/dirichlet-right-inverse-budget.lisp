(in-package "ACL2")

(include-book "dirichlet-right-inverse")
(include-book "dirichlet-right-mass-cap")
(include-book "euler-dirichlet-tail-budget")

; Select the dyadic square cutoff and a shared primitive request.
; The coefficients of the error budget are rational and nonnegative.

(local (defthm lw-drib-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-drib-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-drib-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-drib-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-drib-times-negative (a b) (b a)))
                 :in-theory (disable lw-drib-times-negative)))))

(local (defthm lw-drib-zero-times (equal (* 0 a) 0)))

(local (defthm lw-drib-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-drib-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-drib-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-drib-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-drib-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-drib-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-drib-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-drib-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-drib-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-drib-left-commutes)))))

(local (deftheory lw-drib-arithmetic (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-drib-left-commutes lw-drib-left-distributes lw-drib-fold-constants
              lw-drib-times-negative lw-drib-negative-times lw-drib-zero-times
              lw-drib-minus-one lw-drib-double-negative lw-drib-add-cancel lw-drib-double lw-drib-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))

(defun lw-dirichlet-right-inverse-block (rate)
  (+ 2 (lw-precision-fuel (lw-dirichlet-right-tail-majorant rate)
                          (* 1/16 (/ (lw-dirichlet-right-mass-cap rate))))))

(defun lw-dirichlet-right-inverse-cost (rate height lower upper)
  (let ((count (- (lw-rational-power 2 upper) 1)))
    (+ (lw-dirichlet-right-dyadic-cost rate height 2 upper)
       (* 2 (lw-dirichlet-right-mass-cap rate)
          (lw-dirichlet-right-dyadic-cost rate height lower upper))
       (lw-dirichlet-hyperbola-cost rate height count count count))))

(defun lw-dirichlet-right-inverse-request (rate height lower upper)
  (lw-euler-rounding-precision (lw-dirichlet-right-inverse-cost rate height lower upper) 1/16))

(defthm lw-dirichlet-right-inverse-block-data
  (implies (and (rationalp rate) (< 1 rate))
           (let* ((block (lw-dirichlet-right-inverse-block rate))
                  (cap (lw-dirichlet-right-mass-cap rate))
                  (majorant (lw-dirichlet-right-tail-majorant rate)))
             (and (natp block) (<= 2 block)
                  (<= (* majorant (/ (- block 1))) (* 1/16 (/ cap))))))
  :hints (("Goal"
           :use (lw-dirichlet-right-mass-cap-data
                 (:instance lw-precision-fuel-adequate (width (lw-dirichlet-right-tail-majorant rate))
                            (epsilon (* 1/16 (/ (lw-dirichlet-right-mass-cap rate)))))
                 (:instance lw-reciprocal-positive (value (lw-dirichlet-right-mass-cap rate)))
                 (:instance lw-positive-division-bound
                            (numerator (lw-dirichlet-right-tail-majorant rate))
                            (divisor (- (lw-dirichlet-right-inverse-block rate) 1))
                            (bound (* 1/16 (/ (lw-dirichlet-right-mass-cap rate))))))
           :in-theory (union-theories '(lw-dirichlet-right-inverse-block (:type-prescription lw-precision-fuel))
                                       (theory 'lw-drib-arithmetic))
           :do-not-induct t))
  :rule-classes nil)

(defthm lw-dirichlet-right-square-cutoff-data
  (implies (and (natp lower) (<= 2 lower) (natp upper) (<= (* 2 lower) upper))
           (let ((start (- (lw-rational-power 2 lower) 1))
                 (count (- (lw-rational-power 2 upper) 1)))
             (and (posp start) (posp count) (<= (* start start) count))))
  :hints (("Goal"
           :use ((:instance lw-rational-power-natural (base 2) (exponent lower))
                 (:instance lw-rational-power-natural (base 2) (exponent upper))
                 (:instance lw-rational-power-monotone-exponent (base 2) (small 2) (large lower))
                 (:instance lw-rational-power-monotone-exponent (base 2) (small (* 2 lower)) (large upper))
                 (:instance lw-rational-power-add-exponents (base 2) (left lower) (right lower)))
           :in-theory (union-theories '((:executable-counterpart lw-rational-power)) (theory 'lw-drib-arithmetic))
           :nonlinearp t
           :do-not-induct t))
  :rule-classes nil)

(defthm lw-dirichlet-right-inverse-cost-data
  (implies (and (rationalp rate) (< 1 rate) (rationalp height)
                (natp lower) (<= 2 lower) (natp upper) (<= (* 2 lower) upper))
           (and (rationalp (lw-dirichlet-right-inverse-cost rate height lower upper))
                (<= 0 (lw-dirichlet-right-inverse-cost rate height lower upper))))
  :hints (("Goal"
           :use (lw-dirichlet-right-mass-cap-data lw-dirichlet-right-square-cutoff-data
                 (:instance lw-dirichlet-right-dyadic-mass-bound (lower 2) (error 1))
                 (:instance lw-dirichlet-right-dyadic-mass-bound (error 1))
                 (:instance lw-dirichlet-hyperbola-cost-valid (left (- (lw-rational-power 2 upper) 1))
                            (bound (- (lw-rational-power 2 upper) 1)) (limit (- (lw-rational-power 2 upper) 1)))
                 (:instance lw-drib-multiply-order (a 0) (b (lw-dirichlet-right-dyadic-cost rate height lower upper))
                            (factor (* 2 (lw-dirichlet-right-mass-cap rate)))))
           :in-theory (union-theories '(lw-dirichlet-right-inverse-cost) (theory 'lw-drib-arithmetic))
           :do-not-induct t))
  :rule-classes nil)

(defthm lw-dirichlet-right-inverse-request-data
  (implies (and (rationalp rate) (< 1 rate) (rationalp height)
                (natp lower) (<= 2 lower) (natp upper) (<= (* 2 lower) upper))
           (let ((budget (lw-dirichlet-right-inverse-request rate height lower upper))
                 (cost (lw-dirichlet-right-inverse-cost rate height lower upper)))
             (and (rationalp budget) (< 0 budget) (<= budget 1) (<= (* cost budget) 1/32))))
  :hints (("Goal"
           :use (lw-dirichlet-right-inverse-cost-data
                 (:instance lw-euler-rounding-precision-valid
                   (cost (lw-dirichlet-right-inverse-cost rate height lower upper)) (error 1/16)))
           :in-theory (union-theories '(lw-dirichlet-right-inverse-request) (theory 'lw-drib-arithmetic))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm lw-drib-rounding-parts
   (implies (and (rationalp first) (<= 0 first) (rationalp tail) (<= 0 tail)
                 (rationalp hyperbola) (<= 0 hyperbola) (rationalp cap) (< 0 cap)
                 (rationalp request) (< 0 request)
                 (<= (* (+ first (* 2 cap tail) hyperbola) request) 1/32))
            (and (<= (* first request) 1)
                 (<= (+ (* 2 cap tail request) (* hyperbola request)) 1/32)))
   :hints (("Goal"
            :use ((:instance lw-drib-multiply-order (a 0) (b first) (factor request))
                  (:instance lw-drib-multiply-order (a 0) (b tail) (factor (* 2 cap request)))
                  (:instance lw-drib-multiply-order (a 0) (b hyperbola) (factor request))
                  (:instance lw-drib-positive-product (a cap) (b request)))
            :in-theory (theory 'lw-drib-arithmetic)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-drib-error-bounds
   (implies (and (rationalp cap) (< 0 cap)
                 (rationalp mass) (<= mass cap)
                 (rationalp tail) (<= 0 tail)
                 (rationalp decay) (<= decay (* 1/16 (/ cap)))
                 (rationalp noise) (<= tail (+ decay noise))
                 (rationalp rounding) (<= (+ (* 2 cap noise) rounding) 1/32))
            (<= (+ (* 2 mass tail) rounding) 1/2))
   :hints (("Goal"
            :use ((:instance lw-drib-multiply-order (a mass) (b cap) (factor (* 2 tail)))
                  (:instance lw-drib-multiply-order (a tail) (b (+ decay noise)) (factor (* 2 cap)))
                  (:instance lw-drib-multiply-order (a decay) (b (* 1/16 (/ cap))) (factor (* 2 cap)))
                  (:instance inverse-of-* (x cap)))
            :in-theory (theory 'lw-drib-arithmetic)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-drib-dyadic-certificate-budget
   (implies (and (rationalp rate) (< 1 rate) (rationalp height)
                 (equal lower (lw-dirichlet-right-inverse-block rate)) (natp upper) (<= (* 2 lower) upper)
                 (rationalp request) (< 0 request) (<= request (lw-dirichlet-right-inverse-request rate height lower upper)))
            (and (posp (- (lw-rational-power 2 upper) 1)) (posp (- (lw-rational-power 2 lower) 1)) (<= (* (- (lw-rational-power 2 lower) 1) (- (lw-rational-power 2 lower) 1)) (- (lw-rational-power 2 upper) 1))
                 (<= (lw-dirichlet-node-mass (- (lw-rational-power 2 upper) 1) 0 (lw-dirichlet-sample-table rate height (- (lw-rational-power 2 upper) 1) request request)) (lw-dirichlet-right-mass-cap rate))
                 (<= (+ (* 2 (lw-dirichlet-node-mass (- (lw-rational-power 2 upper) 1) 0 (lw-dirichlet-sample-table rate height (- (lw-rational-power 2 upper) 1) request request)) (lw-dirichlet-node-mass (- (lw-rational-power 2 upper) 1) (- (lw-rational-power 2 lower) 1) (lw-dirichlet-sample-table rate height (- (lw-rational-power 2 upper) 1) request request))) (* (lw-dirichlet-hyperbola-cost rate height (- (lw-rational-power 2 upper) 1) (- (lw-rational-power 2 upper) 1) (- (lw-rational-power 2 upper) 1)) request)) 1/2)))
   :hints (("Goal"
            :use (lw-dirichlet-right-inverse-block-data lw-dirichlet-right-square-cutoff-data
                  lw-dirichlet-right-mass-cap-data lw-dirichlet-right-inverse-cost-data lw-dirichlet-right-inverse-request-data
                  (:instance lw-drib-multiply-order (a request) (b (lw-dirichlet-right-inverse-request rate height lower upper)) (factor (lw-dirichlet-right-inverse-cost rate height lower upper)))
                  (:instance lw-dirichlet-right-dyadic-mass-bound (lower 2) (error 1))
                  (:instance lw-dirichlet-right-dyadic-mass-bound (error 1))
                  (:instance lw-dirichlet-hyperbola-cost-valid (left (- (lw-rational-power 2 upper) 1)) (bound (- (lw-rational-power 2 upper) 1)) (limit (- (lw-rational-power 2 upper) 1)))
                  (:instance lw-drib-rounding-parts (first (lw-dirichlet-right-dyadic-cost rate height 2 upper)) (tail (lw-dirichlet-right-dyadic-cost rate height lower upper)) (hyperbola (lw-dirichlet-hyperbola-cost rate height (- (lw-rational-power 2 upper) 1) (- (lw-rational-power 2 upper) 1) (- (lw-rational-power 2 upper) 1))) (cap (lw-dirichlet-right-mass-cap rate)))
                  (:instance lw-dirichlet-right-dyadic-table-cap (block upper))
                  lw-dirichlet-right-dyadic-table-tail
                  (:instance lw-dirichlet-node-mass-data (upper (- (lw-rational-power 2 upper) 1)) (lower 0) (nodes (lw-dirichlet-sample-table rate height (- (lw-rational-power 2 upper) 1) request request)))
                  (:instance lw-dirichlet-node-mass-data (upper (- (lw-rational-power 2 upper) 1)) (lower (- (lw-rational-power 2 lower) 1)) (nodes (lw-dirichlet-sample-table rate height (- (lw-rational-power 2 upper) 1) request request)))
                  (:instance lw-drib-error-bounds (cap (lw-dirichlet-right-mass-cap rate)) (mass (lw-dirichlet-node-mass (- (lw-rational-power 2 upper) 1) 0 (lw-dirichlet-sample-table rate height (- (lw-rational-power 2 upper) 1) request request))) (tail (lw-dirichlet-node-mass (- (lw-rational-power 2 upper) 1) (- (lw-rational-power 2 lower) 1) (lw-dirichlet-sample-table rate height (- (lw-rational-power 2 upper) 1) request request)))
                    (decay (* (lw-dirichlet-right-tail-majorant rate) (/ (- lower 1))))
                    (noise (* (lw-dirichlet-right-dyadic-cost rate height lower upper) request)) (rounding (* (lw-dirichlet-hyperbola-cost rate height (- (lw-rational-power 2 upper) 1) (- (lw-rational-power 2 upper) 1) (- (lw-rational-power 2 upper) 1)) request))))
            :in-theory (union-theories '(lw-dirichlet-right-inverse-cost) (theory 'lw-drib-arithmetic))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-complex-dirichlet-right-dyadic-clearance
  (implies
   (and (rationalp rate) (< 1 rate) (rationalp height)
        (natp upper) (<= (* 2 (lw-dirichlet-right-inverse-block rate)) upper)
        (rationalp request) (< 0 request) (<= request (lw-dirichlet-right-inverse-request rate height (lw-dirichlet-right-inverse-block rate) upper)))
   (not (lw-complex-diskp (lw-complex-common-dirichlet-prefix nil nil rate height (- (lw-rational-power 2 upper) 1) request)
                           (* 1/4 (/ (lw-dirichlet-right-mass-cap rate))))))
  :hints (("Goal"
           :use (lw-dirichlet-right-mass-cap-data
                 (:instance lw-drib-dyadic-certificate-budget (lower (lw-dirichlet-right-inverse-block rate)))
                 (:instance lw-dirichlet-prefix-clearance-from-mobius (count (- (lw-rational-power 2 upper) 1)) (start (- (lw-rational-power 2 (lw-dirichlet-right-inverse-block rate)) 1)) (cap (lw-dirichlet-right-mass-cap rate)))
                 (:instance lw-ordinary-table-common-prefix (count (- (lw-rational-power 2 upper) 1)) (total (- (lw-rational-power 2 upper) 1)) (error request)))
           :in-theory (theory 'lw-drib-arithmetic)
           :do-not-induct t))
  :rule-classes nil)
