(in-package "ACL2")

(include-book "real-dirichlet-even-transport")
(include-book "euler-dirichlet-prefix")

; The finite eta subtraction cancels the Euler endpoint up to the product error.

(local (defthm lw-erec-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-erec-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-erec-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-erec-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-erec-times-negative (a b) (b a)))
                 :in-theory (disable lw-erec-times-negative)))))

(local (defthm lw-erec-zero-times (equal (* 0 a) 0)))

(local (defthm lw-erec-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-erec-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-erec-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-erec-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-erec-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-erec-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-erec-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-erec-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-erec-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-erec-left-commutes)))))

(local (deftheory lw-erec-arithmetic (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              
              lw-erec-left-commutes lw-erec-left-distributes lw-erec-fold-constants
              lw-erec-times-negative lw-erec-negative-times lw-erec-zero-times
              lw-erec-minus-one lw-erec-double-negative lw-erec-add-cancel lw-erec-double lw-erec-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))

(defun lw-real-euler-eta-multiplier (rate error)
  (lw-complex-scale 2 (lw-dirichlet-sample rate 0 2 error error)))

(defun lw-real-euler-eta-cancellation-residual (rate count error)
  (lw-complex-sub
    (lw-complex-sub (lw-complex-euler-dirichlet-prefix rate 0 (+ 1 (* 2 count)) error) (lw-complex-mul (lw-real-euler-eta-multiplier rate error) (lw-complex-euler-dirichlet-prefix rate 0 count error)))
    (lw-complex-scale (- rate 1) (lw-real-dirichlet-eta-odd-prefix rate count error))))

(defun lw-real-euler-eta-cancellation-cost (rate count)
  (+ (* 2 (abs (- rate 1)) (lw-real-dirichlet-even-transport-cost rate count)) (* 2 (+ 1 count) (lw-dirichlet-pair-cost rate 0 2 (+ 1 count)))))

(local
 (defthm lw-erec-cancellation-algebra
   (implies (and (rationalp coefficient) (rationalp end)
                 (lw-complexp big-prefix) (lw-complexp small-prefix) (lw-complexp evens)
                 (lw-complexp node) (lw-complexp double-node) (lw-complexp base-node))
            (equal
              (lw-complex-sub
                (lw-complex-sub
                  (lw-complex-add (lw-complex-scale coefficient big-prefix) (lw-complex-scale (* 2 end) double-node))
                  (lw-complex-mul (lw-complex-scale 2 base-node)
                    (lw-complex-add (lw-complex-scale coefficient small-prefix) (lw-complex-scale end node))))
                (lw-complex-scale coefficient (lw-complex-sub big-prefix (lw-complex-scale 2 evens))))
              (lw-complex-add
                (lw-complex-scale (* 2 coefficient) (lw-complex-sub evens (lw-complex-mul base-node small-prefix)))
                (lw-complex-scale (* 2 end) (lw-complex-sub double-node (lw-complex-mul base-node node))))))
   :hints (("Goal" :in-theory (union-theories '(lw-complexp lw-complex-add lw-complex-mul lw-complex-sub lw-complex-scale cons-equal) (theory 'lw-erec-arithmetic))
                   :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-erec-real-multiply
   (implies (and (rationalp factor) (lw-complexp point))
            (equal (lw-complex-mul (cons factor 0) point) (lw-complex-scale factor point)))
   :hints (("Goal" :in-theory (union-theories '(lw-complexp lw-complex-mul lw-complex-scale) (theory 'lw-erec-arithmetic))
                   :do-not-induct t))))

(defthm lw-real-euler-eta-cancellation-identity
  (implies
   (and (rationalp rate) (rationalp error) (< 0 error) (natp count))
   (equal (lw-real-euler-eta-cancellation-residual rate count error)
          (lw-complex-add (lw-complex-scale (* 2 (- rate 1)) (lw-complex-sub (lw-real-dirichlet-even-prefix rate count error) (lw-complex-mul (lw-dirichlet-sample rate 0 2 error error) (lw-complex-common-dirichlet-prefix nil nil rate 0 count error))))
                          (lw-complex-scale (* 2 (+ 1 count)) (lw-complex-sub (lw-dirichlet-sample rate 0 (+ 2 (* 2 count)) error error) (lw-complex-mul (lw-dirichlet-sample rate 0 2 error error) (lw-dirichlet-sample rate 0 (+ 1 count) error error)))))))
  :hints (("Goal"
           :use (lw-real-dirichlet-eta-odd-parity lw-real-dirichlet-even-prefix-rational
                 (:instance lw-dirichlet-sample-rational (height 0) (index 2) (log-error error) (node-error error))
                 (:instance lw-dirichlet-sample-rational (height 0) (index (+ 1 count)) (log-error error) (node-error error))
                 (:instance lw-dirichlet-sample-rational (height 0) (index (+ 2 (* 2 count))) (log-error error) (node-error error))
                 (:instance lw-complex-common-dirichlet-prefix-rational (mangoldtp nil) (logp nil) (height 0))
                 (:instance lw-complex-common-dirichlet-prefix-rational (mangoldtp nil) (logp nil) (height 0) (count (+ 1 (* 2 count))))
                 (:instance lw-erec-cancellation-algebra
                   (coefficient (- rate 1)) (end (+ 1 count)) (big-prefix (lw-complex-common-dirichlet-prefix nil nil rate 0 (+ 1 (* 2 count)) error)) (small-prefix (lw-complex-common-dirichlet-prefix nil nil rate 0 count error))
                   (evens (lw-real-dirichlet-even-prefix rate count error)) (base-node (lw-dirichlet-sample rate 0 2 error error)) (node (lw-dirichlet-sample rate 0 (+ 1 count) error error)) (double-node (lw-dirichlet-sample rate 0 (+ 2 (* 2 count)) error error))))
           :in-theory (union-theories '(lw-real-euler-eta-cancellation-residual lw-real-euler-eta-multiplier
              lw-complex-euler-dirichlet-prefix lw-erec-real-multiply) (theory 'lw-erec-arithmetic))
           :do-not-induct t))
  :rule-classes nil)

(defthm lw-real-euler-eta-cancellation-cost-data
  (implies (and (rationalp rate) (<= 0 rate) (natp count))
           (and (rationalp (lw-real-euler-eta-cancellation-cost rate count)) (<= 0 (lw-real-euler-eta-cancellation-cost rate count))))
  :hints (("Goal"
           :use (lw-real-dirichlet-even-transport-cost-data
                 (:instance lw-dirichlet-pair-cost-valid (height 0) (left 2) (right (+ 1 count)))
                 (:instance lw-erec-multiply-order (a 0) (b (lw-real-dirichlet-even-transport-cost rate count)) (factor (* 2 (abs (- rate 1)))))
                 (:instance lw-erec-multiply-order (a 0) (b (lw-dirichlet-pair-cost rate 0 2 (+ 1 count))) (factor (* 2 (+ 1 count)))))
           :in-theory (union-theories '(lw-real-euler-eta-cancellation-cost abs) (theory 'lw-erec-arithmetic))
           :do-not-induct t))
  :rule-classes nil)

(defthm lw-real-euler-eta-multiplier-cap
  (implies (and (rationalp rate) (<= 0 rate) (rationalp error) (< 0 error) (<= error 1))
           (and (lw-complexp (lw-real-euler-eta-multiplier rate error))
                (lw-complex-diskp (lw-real-euler-eta-multiplier rate error) 4)
                (lw-complex-diskp (lw-complex-sub (cons 1 0) (lw-real-euler-eta-multiplier rate error)) 5)))
  :hints (("Goal"
           :use ((:instance lw-dirichlet-sample-unit-cap (height 0) (index 2) (log-error error) (node-error error))
                 (:instance lw-dirichlet-sample-rational (height 0) (index 2) (log-error error) (node-error error))
                 (:instance lw-complex-scale-rational (point (lw-dirichlet-sample rate 0 2 error error)) (factor 2))
                 (:instance lw-complex-scale-disk (point (lw-dirichlet-sample rate 0 2 error error)) (radius 2) (factor 2))
                 (:instance lw-complex-disk-norm-square (point (cons 1 0)) (radius 1))
                 (:instance lw-complex-sub-disk (left (cons 1 0)) (right (lw-real-euler-eta-multiplier rate error)) (radius 1) (other-radius 4)))
           :in-theory (union-theories '(lw-real-euler-eta-multiplier abs (:executable-counterpart lw-complex-norm-square)) (theory 'lw-erec-arithmetic))
           :do-not-induct t))
  :rule-classes nil)

(defthm lw-real-euler-eta-cancellation-error
  (implies
   (and (rationalp rate) (<= 0 rate) (natp count) (rationalp error) (< 0 error))
   (lw-complex-diskp (lw-real-euler-eta-cancellation-residual rate count error) (* (lw-real-euler-eta-cancellation-cost rate count) error)))
  :hints (("Goal"
           :use (lw-real-euler-eta-cancellation-identity lw-real-dirichlet-even-prefix-transport lw-real-dirichlet-even-transport-cost-data
                 (:instance lw-dirichlet-pair-cost-valid (height 0) (left 2) (right (+ 1 count)))
                 lw-real-dirichlet-even-prefix-rational
                 (:instance lw-dirichlet-sample-product-error (height 0) (left 2) (right (+ 1 count)))
                 (:instance lw-dirichlet-sample-rational (height 0) (index 2) (log-error error) (node-error error))
                 (:instance lw-dirichlet-sample-rational (height 0) (index (+ 1 count)) (log-error error) (node-error error))
                 (:instance lw-dirichlet-sample-rational (height 0) (index (+ 2 (* 2 count))) (log-error error) (node-error error))
                 (:instance lw-complex-common-dirichlet-prefix-rational (mangoldtp nil) (logp nil) (height 0))
                 (:instance lw-complex-ring-rational (left (lw-dirichlet-sample rate 0 2 error error)) (right (lw-dirichlet-sample rate 0 (+ 1 count) error error)))
                 (:instance lw-complex-ring-rational (left (lw-dirichlet-sample rate 0 2 error error)) (right (lw-complex-common-dirichlet-prefix nil nil rate 0 count error)))
                 (:instance lw-complex-difference-symmetric (left (lw-complex-mul (lw-dirichlet-sample rate 0 2 error error) (lw-complex-common-dirichlet-prefix nil nil rate 0 count error)))
                   (right (lw-real-dirichlet-even-prefix rate count error)) (radius (* (lw-real-dirichlet-even-transport-cost rate count) error)))
                 (:instance lw-complex-difference-symmetric (left (lw-complex-mul (lw-dirichlet-sample rate 0 2 error error) (lw-dirichlet-sample rate 0 (+ 1 count) error error)))
                   (right (lw-dirichlet-sample rate 0 (+ 2 (* 2 count)) error error)) (radius (* (lw-dirichlet-pair-cost rate 0 2 (+ 1 count)) error)))
                 (:instance lw-complex-scale-disk (factor (* 2 (- rate 1))) (point (lw-complex-sub (lw-real-dirichlet-even-prefix rate count error) (lw-complex-mul (lw-dirichlet-sample rate 0 2 error error) (lw-complex-common-dirichlet-prefix nil nil rate 0 count error)))) (radius (* (lw-real-dirichlet-even-transport-cost rate count) error)))
                 (:instance lw-complex-scale-disk (factor (* 2 (+ 1 count))) (point (lw-complex-sub (lw-dirichlet-sample rate 0 (+ 2 (* 2 count)) error error) (lw-complex-mul (lw-dirichlet-sample rate 0 2 error error) (lw-dirichlet-sample rate 0 (+ 1 count) error error)))) (radius (* (lw-dirichlet-pair-cost rate 0 2 (+ 1 count)) error)))
                 (:instance lw-complex-add-disk (left (lw-complex-scale (* 2 (- rate 1)) (lw-complex-sub (lw-real-dirichlet-even-prefix rate count error) (lw-complex-mul (lw-dirichlet-sample rate 0 2 error error) (lw-complex-common-dirichlet-prefix nil nil rate 0 count error)))))
                   (right (lw-complex-scale (* 2 (+ 1 count)) (lw-complex-sub (lw-dirichlet-sample rate 0 (+ 2 (* 2 count)) error error) (lw-complex-mul (lw-dirichlet-sample rate 0 2 error error) (lw-dirichlet-sample rate 0 (+ 1 count) error error)))))
                   (radius (* 2 (abs (- rate 1)) (lw-real-dirichlet-even-transport-cost rate count) error)) (other-radius (* 2 (+ 1 count) (lw-dirichlet-pair-cost rate 0 2 (+ 1 count)) error))))
           :in-theory (union-theories '(lw-real-euler-eta-cancellation-cost abs) (theory 'lw-erec-arithmetic))
           :do-not-induct t))
  :rule-classes nil)
