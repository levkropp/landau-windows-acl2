(in-package "ACL2")

(include-book "real-dirichlet-parity")
(include-book "dirichlet-hyperbola-product")

; Pull the factor of two out of the even-indexed finite sum.

(local (defthm lw-rdet-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-rdet-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-rdet-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-rdet-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-rdet-times-negative (a b) (b a)))
                 :in-theory (disable lw-rdet-times-negative)))))

(local (defthm lw-rdet-zero-times (equal (* 0 a) 0)))

(local (defthm lw-rdet-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-rdet-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-rdet-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-rdet-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-rdet-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-rdet-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-rdet-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-rdet-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-rdet-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-rdet-left-commutes)))))

(local (deftheory lw-rdet-arithmetic (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              
              lw-rdet-left-commutes lw-rdet-left-distributes lw-rdet-fold-constants
              lw-rdet-times-negative lw-rdet-negative-times lw-rdet-zero-times
              lw-rdet-minus-one lw-rdet-double-negative lw-rdet-add-cancel lw-rdet-double lw-rdet-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))

(defun lw-real-dirichlet-even-transport-cost (rate count)
  (declare (xargs :measure (nfix count) :hints (("Goal" :in-theory (theory 'ground-zero)))))
  (if (zp count) 0
    (+ (lw-dirichlet-pair-cost rate 0 2 count) (lw-real-dirichlet-even-transport-cost rate (- count 1)))))

(defthm lw-real-dirichlet-even-transport-cost-data
  (implies (and (rationalp rate) (<= 0 rate) (natp count))
           (and (rationalp (lw-real-dirichlet-even-transport-cost rate count)) (<= 0 (lw-real-dirichlet-even-transport-cost rate count))))
  :hints (("Goal"
           :induct (lw-real-dirichlet-even-transport-cost rate count)
           :in-theory (union-theories '(lw-real-dirichlet-even-transport-cost) (theory 'lw-rdet-arithmetic))
           :do-not '(generalize fertilize))
          (and stable-under-simplificationp
               '(:use ((:instance lw-dirichlet-pair-cost-valid (height 0) (left 2) (right count))))))
  :rule-classes nil)

(local
 (defthm lw-rdet-difference-step
   (implies (and (rationalp rate) (<= 0 rate) (natp count) (rationalp error) (< 0 error) (< 0 count))
            (equal (lw-complex-sub (lw-complex-mul (lw-dirichlet-sample rate 0 2 error error) (lw-complex-common-dirichlet-prefix nil nil rate 0 count error)) (lw-real-dirichlet-even-prefix rate count error)) (lw-complex-add (lw-complex-sub (lw-complex-mul (lw-dirichlet-sample rate 0 2 error error) (lw-dirichlet-sample rate 0 count error error)) (lw-dirichlet-sample rate 0 (* 2 count) error error)) (lw-complex-sub (lw-complex-mul (lw-dirichlet-sample rate 0 2 error error) (lw-complex-common-dirichlet-prefix nil nil rate 0 (- count 1) error)) (lw-real-dirichlet-even-prefix rate (- count 1) error)))))
   :hints (("Goal"
            :use (lw-ordinary-dirichlet-real-prefix-step
                  (:instance lw-dirichlet-sample-rational (height 0) (index 2) (log-error error) (node-error error))
                  (:instance lw-dirichlet-sample-rational (height 0) (index count) (log-error error) (node-error error))
                  (:instance lw-dirichlet-sample-rational (height 0) (index (* 2 count)) (log-error error) (node-error error))
                  (:instance lw-complex-common-dirichlet-prefix-rational (mangoldtp nil) (logp nil) (height 0) (count (- count 1)))
                  (:instance lw-real-dirichlet-even-prefix-rational (count (- count 1)))
                  (:instance lw-complex-mul-distribute
                    (a (lw-dirichlet-sample rate 0 2 error error)) (b (lw-dirichlet-sample rate 0 count error error)) (c (lw-complex-common-dirichlet-prefix nil nil rate 0 (- count 1) error)))
                  (:instance lw-complex-ring-rational (left (lw-dirichlet-sample rate 0 2 error error)) (right (lw-dirichlet-sample rate 0 count error error)))
                  (:instance lw-complex-ring-rational (left (lw-dirichlet-sample rate 0 2 error error)) (right (lw-complex-common-dirichlet-prefix nil nil rate 0 (- count 1) error)))
                  (:instance lw-complex-sub-add
                    (a (lw-complex-mul (lw-dirichlet-sample rate 0 2 error error) (lw-dirichlet-sample rate 0 count error error))) (b (lw-complex-mul (lw-dirichlet-sample rate 0 2 error error) (lw-complex-common-dirichlet-prefix nil nil rate 0 (- count 1) error)))
                    (c (lw-dirichlet-sample rate 0 (* 2 count) error error)) (d (lw-real-dirichlet-even-prefix rate (- count 1) error))))
            :expand ((lw-real-dirichlet-even-prefix rate count error))
            :in-theory (theory 'lw-rdet-arithmetic)
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-real-dirichlet-even-prefix-transport
  (implies
   (and (rationalp rate) (<= 0 rate) (natp count) (rationalp error) (< 0 error))
   (lw-complex-diskp (lw-complex-sub (lw-complex-mul (lw-dirichlet-sample rate 0 2 error error) (lw-complex-common-dirichlet-prefix nil nil rate 0 count error)) (lw-real-dirichlet-even-prefix rate count error)) (* (lw-real-dirichlet-even-transport-cost rate count) error)))
  :hints (("Goal"
           :induct (lw-real-dirichlet-even-transport-cost rate count)
           :expand ((lw-complex-common-dirichlet-prefix nil nil rate 0 0 error) (lw-real-dirichlet-even-prefix rate 0 error))
           :in-theory (union-theories '(lw-real-dirichlet-even-transport-cost
              lw-dirichlet-sample-rational lw-complex-mul-zero (:executable-counterpart lw-complex-sub)
              (:executable-counterpart lw-complex-diskp)) (theory 'lw-rdet-arithmetic))
           :do-not '(generalize fertilize))
          (and stable-under-simplificationp
               '(:use (lw-rdet-difference-step
                       (:instance lw-dirichlet-sample-product-error (height 0) (left 2) (right count))
                       (:instance lw-complex-add-disk (left (lw-complex-sub (lw-complex-mul (lw-dirichlet-sample rate 0 2 error error) (lw-dirichlet-sample rate 0 count error error)) (lw-dirichlet-sample rate 0 (* 2 count) error error))) (right (lw-complex-sub (lw-complex-mul (lw-dirichlet-sample rate 0 2 error error) (lw-complex-common-dirichlet-prefix nil nil rate 0 (- count 1) error)) (lw-real-dirichlet-even-prefix rate (- count 1) error)))
                         (radius (* (lw-dirichlet-pair-cost rate 0 2 count) error)) (other-radius (* (lw-real-dirichlet-even-transport-cost rate (- count 1)) error))))
                 :do-not-induct t)))
  :rule-classes nil)
