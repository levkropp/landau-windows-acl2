(in-package "ACL2")

(include-book "dirichlet-right-inverse-budget")
(include-book "euler-fixed-truncation")

; A dyadic prefix proves nonvanishing of the native evaluator when its
; Möbius inverse, truncation, and terminal term share this request.

(local (defthm lw-ercb-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ercb-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ercb-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ercb-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ercb-times-negative (a b) (b a)))
                 :in-theory (disable lw-ercb-times-negative)))))

(local (defthm lw-ercb-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ercb-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ercb-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ercb-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ercb-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ercb-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ercb-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ercb-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ercb-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ercb-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ercb-left-commutes)))))

(local (deftheory lw-ercb-arithmetic (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-ercb-left-commutes lw-ercb-left-distributes lw-ercb-fold-constants
              lw-ercb-times-negative lw-ercb-negative-times lw-ercb-zero-times
              lw-ercb-minus-one lw-ercb-double-negative lw-ercb-add-cancel lw-ercb-double lw-ercb-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))

(defun lw-euler-right-floor (rate)
  (* 1/32 (- rate 1) (/ (lw-dirichlet-right-mass-cap rate))))

(defun lw-euler-right-proof-block (rate height)
  (max (* 2 (lw-dirichlet-right-inverse-block rate))
       (max (lw-euler-continuation-block-cutoff rate height (lw-euler-right-floor rate))
            (+ 2 (lw-precision-fuel (lw-dirichlet-right-tail-majorant rate) (lw-euler-right-floor rate))))))

(defun lw-euler-right-proof-request (rate height block)
  (min (lw-dirichlet-right-inverse-request rate height (lw-dirichlet-right-inverse-block rate) block)
       (min (lw-euler-rounding-precision (lw-euler-dyadic-transport-cost rate height block) (lw-euler-right-floor rate))
            (lw-euler-rounding-precision (lw-dirichlet-right-node-cost rate height (lw-rational-power 2 block)) (lw-euler-right-floor rate)))))

(defthm lw-euler-right-floor-data
  (implies (and (rationalp rate) (< 1 rate))
           (and (rationalp (lw-euler-right-floor rate)) (< 0 (lw-euler-right-floor rate))))
  :hints (("Goal"
           :use (lw-dirichlet-right-mass-cap-data
                 (:instance lw-reciprocal-positive (value (lw-dirichlet-right-mass-cap rate)))
                 (:instance lw-ercb-positive-product (a (- rate 1)) (b (/ (lw-dirichlet-right-mass-cap rate)))))
           :in-theory (union-theories '(lw-euler-right-floor) (theory 'lw-ercb-arithmetic))
           :do-not-induct t))
  :rule-classes nil)

(defthm lw-euler-right-proof-block-data
  (implies (and (rationalp rate) (< 1 rate) (rationalp height))
           (and (natp (lw-euler-right-proof-block rate height)) (<= 2 (lw-euler-right-proof-block rate height))
                (<= (* 2 (lw-dirichlet-right-inverse-block rate)) (lw-euler-right-proof-block rate height))
                (<= (lw-euler-continuation-block-cutoff rate height (lw-euler-right-floor rate)) (lw-euler-right-proof-block rate height))
                (<= (+ 2 (lw-precision-fuel (lw-dirichlet-right-tail-majorant rate) (lw-euler-right-floor rate))) (lw-euler-right-proof-block rate height))))
  :hints (("Goal"
           :use (lw-dirichlet-right-inverse-block-data
                 (:instance lw-euler-continuation-block-cutoff-natural (error (lw-euler-right-floor rate))))
           :in-theory (union-theories '(lw-euler-right-proof-block max (:type-prescription lw-precision-fuel))
                                       (theory 'lw-ercb-arithmetic))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm lw-ercb-endpoint-estimate
   (implies (and (rationalp rate) (< 1 rate) (natp block) (<= 2 block)
                 (<= (+ 2 (lw-precision-fuel (lw-dirichlet-right-tail-majorant rate) (lw-euler-right-floor rate))) block))
            (<= (lw-dirichlet-right-block-decay rate block) (* 1/2 (lw-euler-right-floor rate))))
   :hints (("Goal"
            :use (lw-euler-right-floor-data lw-dirichlet-right-mass-cap-data
                  (:instance lw-precision-fuel-adequate (width (lw-dirichlet-right-tail-majorant rate)) (epsilon (lw-euler-right-floor rate)))
                  (:instance lw-ercb-multiply-order
                    (a (+ 1 (lw-precision-fuel (lw-dirichlet-right-tail-majorant rate) (lw-euler-right-floor rate)))) (b block) (factor (lw-euler-right-floor rate)))
                  (:instance lw-positive-division-bound (numerator (lw-dirichlet-right-tail-majorant rate)) (divisor block) (bound (lw-euler-right-floor rate)))
                  (:instance lw-reciprocal-positive (value block))
                  (:instance lw-reciprocal-antitone (left 1) (right block))
                  (:instance lw-ercb-multiply-order (a (/ block)) (b 1) (factor (* (lw-dirichlet-right-tail-majorant rate) (/ block))))
                  (:instance lw-ercb-positive-product (a (lw-dirichlet-right-tail-majorant rate)) (b (/ block))))
            :in-theory (union-theories '(lw-dirichlet-right-block-decay lw-dirichlet-right-tail-majorant
                                        (:type-prescription lw-precision-fuel))
                                       (theory 'lw-ercb-arithmetic))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-euler-right-proof-request-data
  (implies (and (rationalp rate) (< 1 rate) (rationalp height)
                (natp block) (<= 2 block) (<= (* 2 (lw-dirichlet-right-inverse-block rate)) block)
                (<= (+ 2 (lw-precision-fuel (lw-dirichlet-right-tail-majorant rate) (lw-euler-right-floor rate))) block))
           (and (rationalp (lw-euler-right-proof-request rate height block)) (< 0 (lw-euler-right-proof-request rate height block)) (<= (lw-euler-right-proof-request rate height block) 1)
                (<= (lw-euler-right-proof-request rate height block) (lw-dirichlet-right-inverse-request rate height (lw-dirichlet-right-inverse-block rate) block))
                (<= (lw-euler-right-proof-request rate height block) (lw-euler-rounding-precision (lw-euler-dyadic-transport-cost rate height block) (lw-euler-right-floor rate)))
                (<= (+ (lw-dirichlet-right-block-decay rate block) (* (lw-dirichlet-right-node-cost rate height (lw-rational-power 2 block)) (lw-euler-right-proof-request rate height block))) (lw-euler-right-floor rate))))
  :hints (("Goal"
           :use (lw-euler-right-floor-data lw-dirichlet-right-inverse-block-data
                 (:instance lw-dirichlet-right-inverse-request-data (lower (lw-dirichlet-right-inverse-block rate)) (upper block))
                 lw-ercb-endpoint-estimate
                 (:instance lw-euler-dyadic-transport-cost-valid (count block))
                 (:instance lw-rational-power-monotone-exponent (base 2) (small 2) (large block))
                 (:instance lw-rational-power-rational (base 2) (exponent block))
                 (:instance lw-dirichlet-right-node-cost-data (index (lw-rational-power 2 block)))
                 (:instance lw-euler-rounding-precision-valid (cost (lw-euler-dyadic-transport-cost rate height block)) (error (lw-euler-right-floor rate)))
                 (:instance lw-euler-rounding-precision-valid (cost (lw-dirichlet-right-node-cost rate height (lw-rational-power 2 block))) (error (lw-euler-right-floor rate)))
                 (:instance lw-ercb-multiply-order (a (lw-euler-right-proof-request rate height block)) (b (lw-euler-rounding-precision (lw-dirichlet-right-node-cost rate height (lw-rational-power 2 block)) (lw-euler-right-floor rate))) (factor (lw-dirichlet-right-node-cost rate height (lw-rational-power 2 block)))))
           :in-theory (union-theories '(lw-euler-right-proof-request min
                                       (:executable-counterpart lw-rational-power)
                                       (:type-prescription lw-precision-fuel)) (theory 'lw-ercb-arithmetic))
           :do-not-induct t))
  :rule-classes nil)
