(in-package "ACL2")

(include-book "euler-real-eta-comparison")

; Fix a truncation and a single finite request from the first-pair gap.

(local (defthm lw-ereb-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ereb-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ereb-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ereb-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ereb-times-negative (a b) (b a)))
                 :in-theory (disable lw-ereb-times-negative)))))

(local (defthm lw-ereb-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ereb-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ereb-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ereb-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ereb-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ereb-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ereb-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ereb-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ereb-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ereb-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ereb-left-commutes)))))

(local (deftheory lw-ereb-arithmetic (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              
              lw-ereb-left-commutes lw-ereb-left-distributes lw-ereb-fold-constants
              lw-ereb-times-negative lw-ereb-negative-times lw-ereb-zero-times
              lw-ereb-minus-one lw-ereb-double-negative lw-ereb-add-cancel lw-ereb-double lw-ereb-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))

(defun lw-real-euler-eta-lower-strength (rate)
  (* (abs (- rate 1)) (lw-real-dirichlet-first-gap rate)))

(defun lw-real-euler-eta-proof-block (rate)
  (lw-euler-continuation-block-cutoff rate 0 (* 1/64 (lw-real-euler-eta-lower-strength rate))))

(defun lw-real-euler-eta-proof-request (rate block)
  (min (min (lw-euler-rounding-precision (lw-euler-dyadic-transport-cost rate 0 block) (* 1/64 (lw-real-euler-eta-lower-strength rate))) (lw-euler-rounding-precision (lw-euler-dyadic-transport-cost rate 0 (+ 1 block)) (* 1/64 (lw-real-euler-eta-lower-strength rate))))
       (min (lw-euler-rounding-precision (lw-real-euler-eta-cancellation-cost rate (lw-real-euler-eta-prefix-count block)) (* 1/64 (lw-real-euler-eta-lower-strength rate))) (lw-euler-rounding-precision (* (+ 1 (lw-real-euler-eta-prefix-count block)) (lw-real-dirichlet-order-gain rate (+ 1 (* 2 (lw-real-euler-eta-prefix-count block))))) (lw-real-dirichlet-first-gap rate)))))

(defthm lw-real-euler-eta-lower-strength-data
  (implies (and (rationalp rate) (< 0 rate) (not (equal rate 1)))
           (and (rationalp (lw-real-euler-eta-lower-strength rate)) (< 0 (lw-real-euler-eta-lower-strength rate))))
  :hints (("Goal"
           :use (lw-real-dirichlet-first-gap-positive
                 (:instance lw-ereb-positive-product (a (abs (- rate 1))) (b (lw-real-dirichlet-first-gap rate))))
           :in-theory (union-theories '(lw-real-euler-eta-lower-strength abs) (theory 'lw-ereb-arithmetic))
           :do-not-induct t))
  :rule-classes nil)

(defthm lw-real-euler-eta-proof-block-data
  (and (natp (lw-real-euler-eta-proof-block rate)) (<= 2 (lw-real-euler-eta-proof-block rate))
       (equal (lw-real-euler-eta-proof-block rate) (lw-euler-continuation-block-cutoff rate 0 (* 1/64 (lw-real-euler-eta-lower-strength rate)))))
  :hints (("Goal"
           :in-theory (union-theories '(lw-real-euler-eta-proof-block lw-euler-continuation-block-cutoff-natural) (theory 'lw-ereb-arithmetic))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm lw-ereb-cost-data
   (implies (and (rationalp rate) (< 0 rate) (not (equal rate 1)) (natp block) (<= 2 block))
            (and (rationalp (lw-euler-dyadic-transport-cost rate 0 block)) (<= 0 (lw-euler-dyadic-transport-cost rate 0 block))
                 (rationalp (lw-euler-dyadic-transport-cost rate 0 (+ 1 block))) (<= 0 (lw-euler-dyadic-transport-cost rate 0 (+ 1 block)))
                 (rationalp (lw-real-euler-eta-cancellation-cost rate (lw-real-euler-eta-prefix-count block))) (<= 0 (lw-real-euler-eta-cancellation-cost rate (lw-real-euler-eta-prefix-count block)))
                 (rationalp (* (+ 1 (lw-real-euler-eta-prefix-count block)) (lw-real-dirichlet-order-gain rate (+ 1 (* 2 (lw-real-euler-eta-prefix-count block)))))) (<= 0 (* (+ 1 (lw-real-euler-eta-prefix-count block)) (lw-real-dirichlet-order-gain rate (+ 1 (* 2 (lw-real-euler-eta-prefix-count block))))))))
   :hints (("Goal"
            :use (lw-real-euler-eta-prefix-count-data
                  (:instance lw-euler-dyadic-transport-cost-valid (height 0) (count block))
                  (:instance lw-euler-dyadic-transport-cost-valid (height 0) (count (+ 1 block)))
                  (:instance lw-real-euler-eta-cancellation-cost-data (count (lw-real-euler-eta-prefix-count block)))
                  (:instance lw-real-dirichlet-order-gain-data (limit (+ 1 (* 2 (lw-real-euler-eta-prefix-count block)))))
                  (:instance lw-ereb-positive-product (a (+ 1 (lw-real-euler-eta-prefix-count block))) (b (lw-real-dirichlet-order-gain rate (+ 1 (* 2 (lw-real-euler-eta-prefix-count block)))))))
            :in-theory (theory 'lw-ereb-arithmetic)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-ereb-common-rounding-data
   (implies (and (rationalp first) (<= 0 first) (rationalp second) (<= 0 second)
                 (rationalp third) (<= 0 third) (rationalp fourth) (<= 0 fourth)
                 (rationalp budget) (< 0 budget) (rationalp gap) (< 0 gap))
            (let* ((a (lw-euler-rounding-precision first budget))
                   (b (lw-euler-rounding-precision second budget))
                   (c (lw-euler-rounding-precision third budget))
                   (d (lw-euler-rounding-precision fourth gap))
                   (request (min (min a b) (min c d))))
              (and (rationalp request) (< 0 request) (<= request 1)
                   (<= request a) (<= request b)
                   (<= (* third request) (/ budget 2))
                   (<= (* fourth request) (/ gap 2)))))
   :hints (("Goal"
            :use ((:instance lw-euler-rounding-precision-valid (cost first) (error budget))
                  (:instance lw-euler-rounding-precision-valid (cost second) (error budget))
                  (:instance lw-euler-rounding-precision-valid (cost third) (error budget))
                  (:instance lw-euler-rounding-precision-valid (cost fourth) (error gap))
                  (:instance lw-ereb-multiply-order
                    (a (min (min (lw-euler-rounding-precision first budget) (lw-euler-rounding-precision second budget))
                            (min (lw-euler-rounding-precision third budget) (lw-euler-rounding-precision fourth gap))))
                    (b (lw-euler-rounding-precision third budget)) (factor third))
                  (:instance lw-ereb-multiply-order
                    (a (min (min (lw-euler-rounding-precision first budget) (lw-euler-rounding-precision second budget))
                            (min (lw-euler-rounding-precision third budget) (lw-euler-rounding-precision fourth gap))))
                    (b (lw-euler-rounding-precision fourth gap)) (factor fourth)))
            :in-theory (union-theories '(min) (theory 'lw-ereb-arithmetic))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-real-euler-eta-proof-request-data
  (implies (and (rationalp rate) (< 0 rate) (not (equal rate 1)) (natp block) (<= 2 block))
           (and (rationalp (lw-real-euler-eta-proof-request rate block)) (< 0 (lw-real-euler-eta-proof-request rate block)) (<= (lw-real-euler-eta-proof-request rate block) 1)
                (<= (lw-real-euler-eta-proof-request rate block) (lw-euler-rounding-precision (lw-euler-dyadic-transport-cost rate 0 block) (* 1/64 (lw-real-euler-eta-lower-strength rate)))) (<= (lw-real-euler-eta-proof-request rate block) (lw-euler-rounding-precision (lw-euler-dyadic-transport-cost rate 0 (+ 1 block)) (* 1/64 (lw-real-euler-eta-lower-strength rate))))
                (<= (* (lw-real-euler-eta-cancellation-cost rate (lw-real-euler-eta-prefix-count block)) (lw-real-euler-eta-proof-request rate block)) (* 1/64 (lw-real-euler-eta-lower-strength rate)))
                (<= (* (* (+ 1 (lw-real-euler-eta-prefix-count block)) (lw-real-dirichlet-order-gain rate (+ 1 (* 2 (lw-real-euler-eta-prefix-count block))))) (lw-real-euler-eta-proof-request rate block)) (* 1/2 (lw-real-dirichlet-first-gap rate)))))
  :hints (("Goal"
           :use (lw-ereb-cost-data lw-real-euler-eta-lower-strength-data lw-real-dirichlet-first-gap-positive
                 (:instance lw-ereb-common-rounding-data
                   (first (lw-euler-dyadic-transport-cost rate 0 block)) (second (lw-euler-dyadic-transport-cost rate 0 (+ 1 block))) (third (lw-real-euler-eta-cancellation-cost rate (lw-real-euler-eta-prefix-count block))) (fourth (* (+ 1 (lw-real-euler-eta-prefix-count block)) (lw-real-dirichlet-order-gain rate (+ 1 (* 2 (lw-real-euler-eta-prefix-count block)))))) (budget (* 1/64 (lw-real-euler-eta-lower-strength rate))) (gap (lw-real-dirichlet-first-gap rate))))
           :in-theory (union-theories '(lw-real-euler-eta-proof-request) (theory 'lw-ereb-arithmetic))
           :do-not-induct t))
  :rule-classes nil)
