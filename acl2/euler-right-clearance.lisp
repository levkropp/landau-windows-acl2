(in-package "ACL2")

(include-book "euler-right-clearance-budget")

; Transfer the finite Dirichlet separation to the native pole-removed
; evaluator. The separation is uniform in height for each right strip.

(local (defthm lw-erc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-erc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-erc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-erc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-erc-times-negative (a b) (b a)))
                 :in-theory (disable lw-erc-times-negative)))))

(local (defthm lw-erc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-erc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-erc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-erc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-erc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-erc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-erc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-erc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-erc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-erc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-erc-left-commutes)))))

(local (deftheory lw-erc-arithmetic (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-erc-left-commutes lw-erc-left-distributes lw-erc-fold-constants
              lw-erc-times-negative lw-erc-negative-times lw-erc-zero-times
              lw-erc-minus-one lw-erc-double-negative lw-erc-add-cancel lw-erc-double lw-erc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))

(local
 (defthm lw-erc-nonnegative-square
   (implies (rationalp a) (<= 0 (* a a)))
   :hints (("Goal" :nonlinearp t))
   :rule-classes nil))

(local
 (defthm lw-erc-square-lower
   (implies (and (rationalp real) (rationalp imag))
            (<= (* real real) (lw-complex-norm-square (cons real imag))))
   :hints (("Goal"
            :use ((:instance lw-erc-nonnegative-square (a imag)))
            :in-theory (union-theories '(lw-complex-norm-square) (theory 'lw-erc-arithmetic))
            :nonlinearp t))
   :rule-classes nil))

(local
 (defthm lw-erc-strict-product
   (implies (and (rationalp a) (rationalp b) (< a b)
                 (rationalp factor) (< 0 factor))
            (< (* a factor) (* b factor)))
   :hints (("Goal" :nonlinearp t))
   :rule-classes nil))

(local
 (defthm lw-erc-multiplied-clearance
   (implies (and (rationalp real) (< 0 real) (rationalp imag)
                 (rationalp floor) (< 0 floor) (lw-complexp prefix)
                 (not (lw-complex-diskp prefix floor)))
            (not (lw-complex-diskp (lw-complex-mul (cons real imag) prefix) (* real floor))))
   :hints (("Goal"
            :use (lw-erc-square-lower
                  (:instance lw-complex-norm-square-valid (point prefix))
                  (:instance lw-complex-disk-norm-square (point prefix) (radius floor))
                  (:instance lw-complex-norm-square-product (left (cons real imag)) (right prefix))
                  (:instance lw-complex-disk-norm-square (point (lw-complex-mul (cons real imag) prefix)) (radius (* real floor)))
                  (:instance lw-erc-strict-product (a (* floor floor)) (b (lw-complex-norm-square prefix)) (factor (* real real)))
                  (:instance lw-erc-multiply-order (a (* real real)) (b (lw-complex-norm-square (cons real imag))) (factor (lw-complex-norm-square prefix)))
                  (:instance lw-complex-norm-square-valid (point (cons real imag)))
                  (:instance lw-erc-positive-product (a real) (b real)))
            :in-theory (union-theories '(lw-complexp) (theory 'lw-erc-arithmetic))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-erc-additive-transport
   (implies (and (lw-complexp total) (lw-complexp main) (lw-complexp endpoint) (lw-complexp sample)
                 (equal total (lw-complex-add main endpoint))
                 (rationalp floor) (< 0 floor) (rationalp error) (< 0 error) (<= error floor)
                 (lw-complex-diskp endpoint floor)
                 (lw-complex-diskp (lw-complex-sub sample total) (+ (* 1/4 error) floor))
                 (lw-complex-diskp sample floor))
            (lw-complex-diskp main (* 8 floor)))
   :hints (("Goal"
            :use ((:instance lw-complex-sub-add-cancel (a main) (b endpoint))
                  (:instance lw-complex-difference-symmetric (left total) (right main) (radius floor))
                  (:instance lw-complex-difference-symmetric (left sample) (right total) (radius (+ (* 1/4 error) floor)))
                  (:instance lw-complex-difference-triangle (left main) (middle total) (right sample)
                    (radius floor) (other-radius (+ (* 1/4 error) floor)))
                  (:instance lw-complex-difference-triangle (left main) (middle sample) (right (cons 0 0))
                    (radius (+ floor (* 1/4 error) floor)) (other-radius floor))
                  (:instance lw-complex-disk-enlarge (point main) (radius (+ floor (* 1/4 error) floor floor)) (cap (* 8 floor))))
            :in-theory (union-theories '(lw-complex-sub-zero (:executable-counterpart lw-complexp)) (theory 'lw-erc-arithmetic))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-erc-dyadic-transfer
   (implies
    (and (rationalp rate) (< 1 rate) (rationalp height)
         (natp block) (<= 2 block) (<= (* 2 (lw-dirichlet-right-inverse-block rate)) block)
         (<= (lw-euler-continuation-block-cutoff rate height (lw-euler-right-floor rate)) block)
         (rationalp request) (< 0 request) (<= request 1)
         (<= request (lw-dirichlet-right-inverse-request rate height (lw-dirichlet-right-inverse-block rate) block))
         (<= request (lw-euler-rounding-precision (lw-euler-dyadic-transport-cost rate height block) (lw-euler-right-floor rate)))
         (<= (+ (lw-dirichlet-right-block-decay rate block) (* (lw-dirichlet-right-node-cost rate height (lw-rational-power 2 block)) request)) (lw-euler-right-floor rate))
         (rationalp error) (< 0 error) (<= error (lw-euler-right-floor rate)))
    (not (lw-complex-diskp (lw-complex-euler-continuation-value rate height error) (lw-euler-right-floor rate))))
   :hints (("Goal"
            :use (lw-dirichlet-right-mass-cap-data lw-euler-right-floor-data
                  (:instance lw-reciprocal-positive (value (lw-dirichlet-right-mass-cap rate)))
                  (:instance lw-rational-power-monotone-exponent (base 2) (small 2) (large block))
                  (:instance lw-rational-power-rational (base 2) (exponent block))
                  (:instance lw-complex-dirichlet-right-dyadic-clearance (upper block))
                  (:instance lw-complex-common-dirichlet-prefix-rational (count (- (lw-rational-power 2 block) 1))
                    (mangoldtp nil) (logp nil) (error request))
                  (:instance lw-dirichlet-sample-rational (index (lw-rational-power 2 block)) (log-error request) (node-error request))
                  (:instance lw-dirichlet-right-scaled-sample-bound (index (lw-rational-power 2 block)) (error request))
                  (:instance lw-complex-euler-fixed-truncation-computed (target-error (lw-euler-right-floor rate)))
                  (:instance lw-complex-disk-enlarge (point (lw-complex-scale (lw-rational-power 2 block) (lw-dirichlet-sample rate height (lw-rational-power 2 block) request request))) (cap (lw-euler-right-floor rate))
                    (radius (+ (lw-dirichlet-right-block-decay rate block) (* (lw-dirichlet-right-node-cost rate height (lw-rational-power 2 block)) request))))
                  (:instance lw-erc-multiplied-clearance (real (- rate 1)) (imag height)
                    (floor (* 1/4 (/ (lw-dirichlet-right-mass-cap rate)))) (prefix (lw-complex-common-dirichlet-prefix nil nil rate height (- (lw-rational-power 2 block) 1) request)))
                  (:instance lw-erc-additive-transport (floor (lw-euler-right-floor rate)) (total (lw-complex-euler-dyadic-prefix rate height block request))
                    (main (lw-complex-mul (cons (- rate 1) height) (lw-complex-common-dirichlet-prefix nil nil rate height (- (lw-rational-power 2 block) 1) request))) (endpoint (lw-complex-scale (lw-rational-power 2 block) (lw-dirichlet-sample rate height (lw-rational-power 2 block) request request))) (sample (lw-complex-euler-continuation-value rate height error)))
                  lw-complex-euler-continuation-value-rational)
            :in-theory (union-theories '(lw-euler-right-floor lw-complex-euler-dyadic-prefix
                  lw-complex-euler-dirichlet-prefix lw-complexp lw-complex-ring-rational lw-complex-scale-rational
                  (:executable-counterpart lw-rational-power)) (theory 'lw-erc-arithmetic))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-complex-euler-right-clearance
  (implies (and (rationalp rate) (< 1 rate) (rationalp height)
                (rationalp error) (< 0 error) (<= error (lw-euler-right-floor rate)))
           (not (lw-complex-diskp (lw-complex-euler-continuation-value rate height error) (lw-euler-right-floor rate))))
  :hints (("Goal"
           :use (lw-euler-right-proof-block-data
                 (:instance lw-euler-right-proof-request-data (block (lw-euler-right-proof-block rate height)))
                 (:instance lw-erc-dyadic-transfer (block (lw-euler-right-proof-block rate height))
                   (request (lw-euler-right-proof-request rate height (lw-euler-right-proof-block rate height)))))
           :in-theory (theory 'lw-erc-arithmetic)
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm lw-erc-mass-cap-antitone
   (implies (and (rationalp lower) (< 1 lower) (rationalp rate) (<= lower rate))
            (<= (lw-dirichlet-right-mass-cap rate) (lw-dirichlet-right-mass-cap lower)))
   :hints (("Goal"
            :use ((:instance lw-reciprocal-positive (value (- rate 1)))
                  (:instance lw-reciprocal-positive (value (- lower 1)))
                  (:instance lw-reciprocal-antitone (left (- lower 1)) (right (- rate 1)))
                  (:instance lw-erc-multiply-order (a (/ (- rate 1))) (b (/ (- lower 1)))
                    (factor (* 64 (/ (- rate 1)))))
                  (:instance lw-erc-multiply-order (a (/ (- rate 1))) (b (/ (- lower 1)))
                    (factor (* 64 (/ (- lower 1))))))
            :in-theory (union-theories '(lw-dirichlet-right-tail-majorant lw-dirichlet-right-mass-cap)
                                        (theory 'lw-erc-arithmetic))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-euler-right-floor-monotone
  (implies (and (rationalp lower) (< 1 lower) (rationalp rate) (<= lower rate))
           (<= (lw-euler-right-floor lower) (lw-euler-right-floor rate)))
  :hints (("Goal"
           :use (lw-erc-mass-cap-antitone lw-dirichlet-right-mass-cap-data
                 (:instance lw-dirichlet-right-mass-cap-data (rate lower))
                 (:instance lw-reciprocal-positive (value (lw-dirichlet-right-mass-cap lower)))
                 (:instance lw-reciprocal-antitone (left (lw-dirichlet-right-mass-cap rate)) (right (lw-dirichlet-right-mass-cap lower)))
                 (:instance lw-erc-multiply-order (a (- lower 1)) (b (- rate 1))
                   (factor (* 1/32 (/ (lw-dirichlet-right-mass-cap lower)))))
                 (:instance lw-erc-multiply-order (a (/ (lw-dirichlet-right-mass-cap lower))) (b (/ (lw-dirichlet-right-mass-cap rate)))
                   (factor (* 1/32 (- rate 1)))))
           :in-theory (union-theories '(lw-euler-right-floor) (theory 'lw-erc-arithmetic))
           :do-not-induct t))
  :rule-classes nil)

(defthm lw-complex-euler-right-uniform-clearance
  (implies (and (rationalp lower) (< 1 lower) (rationalp rate) (<= lower rate) (rationalp height)
                (rationalp error) (< 0 error) (<= error (lw-euler-right-floor lower)))
           (not (lw-complex-diskp (lw-complex-euler-continuation-value rate height error)
                                  (lw-euler-right-floor lower))))
  :hints (("Goal"
           :use (lw-euler-right-floor-monotone lw-euler-right-floor-data lw-complex-euler-right-clearance
                 (:instance lw-complex-disk-enlarge
                   (point (lw-complex-euler-continuation-value rate height error))
                   (radius (lw-euler-right-floor lower)) (cap (lw-euler-right-floor rate))))
           :in-theory (theory 'lw-erc-arithmetic)
           :do-not-induct t))
  :rule-classes nil)
