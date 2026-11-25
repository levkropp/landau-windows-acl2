(in-package "ACL2")

(include-book "real-dirichlet-eta-prefix")
(include-book "dirichlet-common-precision")

; Splitting the ordinary prefix by parity is an exact finite identity.

(local (defthm lw-rdp-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-rdp-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-rdp-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-rdp-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-rdp-times-negative (a b) (b a)))
                 :in-theory (disable lw-rdp-times-negative)))))

(local (defthm lw-rdp-zero-times (equal (* 0 a) 0)))

(local (defthm lw-rdp-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-rdp-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-rdp-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-rdp-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-rdp-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-rdp-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-rdp-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-rdp-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-rdp-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-rdp-left-commutes)))))

(local (deftheory lw-rdp-arithmetic (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              
              lw-rdp-left-commutes lw-rdp-left-distributes lw-rdp-fold-constants
              lw-rdp-times-negative lw-rdp-negative-times lw-rdp-zero-times
              lw-rdp-minus-one lw-rdp-double-negative lw-rdp-add-cancel lw-rdp-double lw-rdp-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))

(defun lw-real-dirichlet-even-prefix (rate count error)
  (declare (xargs :measure (nfix count) :hints (("Goal" :in-theory (theory 'ground-zero)))))
  (if (zp count) (cons 0 0)
    (lw-complex-add (lw-dirichlet-sample rate 0 (* 2 count) error error) (lw-real-dirichlet-even-prefix rate (- count 1) error))))

(defthm lw-real-dirichlet-even-prefix-rational
  (implies (and (rationalp rate) (rationalp error) (< 0 error))
           (lw-complexp (lw-real-dirichlet-even-prefix rate count error)))
  :hints (("Goal"
           :induct (lw-real-dirichlet-even-prefix rate count error)
           :in-theory (union-theories '(lw-real-dirichlet-even-prefix lw-dirichlet-sample-rational lw-complex-ring-rational) (theory 'lw-rdp-arithmetic)))))

(defthm lw-ordinary-dirichlet-real-prefix-step
  (implies (and (rationalp rate) (rationalp error) (< 0 error) (posp count))
           (equal (lw-complex-common-dirichlet-prefix nil nil rate 0 count error)
                  (lw-complex-add (lw-dirichlet-sample rate 0 count error error) (lw-complex-common-dirichlet-prefix nil nil rate 0 (- count 1) error))))
  :hints (("Goal"
           :cases ((equal count 1))
           :use ((:instance lw-dirichlet-sample-rational (height 0) (index count) (log-error error) (node-error error))
                 (:instance lw-complex-scale-one (point (lw-dirichlet-sample rate 0 count error error))))
           :in-theory (union-theories '(lw-complex-common-dirichlet-prefix lw-common-dirichlet-coefficient lw-zeta-dirichlet-weight
              lw-complex-add-zero lw-dirichlet-sample) (theory 'lw-rdp-arithmetic))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm lw-rdp-pair-arrangement
   (implies (and (lw-complexp even) (lw-complexp odd)
                 (lw-complexp earlier-pairs) (lw-complexp earlier-even))
            (equal (lw-complex-add even (lw-complex-add odd
                      (lw-complex-add earlier-pairs (lw-complex-scale 2 earlier-even))))
                   (lw-complex-add (lw-complex-add (lw-complex-sub odd even) earlier-pairs)
                      (lw-complex-scale 2 (lw-complex-add even earlier-even)))))
   :hints (("Goal"
            :in-theory (union-theories '(lw-complexp lw-complex-add lw-complex-sub lw-complex-scale cons-equal) (theory 'lw-rdp-arithmetic))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-rdp-even-parity
   (implies (and (rationalp rate) (rationalp error) (< 0 error) (natp count))
            (equal (lw-complex-common-dirichlet-prefix nil nil rate 0 (* 2 count) error)
                   (lw-complex-add (lw-real-dirichlet-eta-pairs rate count error) (lw-complex-scale 2 (lw-real-dirichlet-even-prefix rate count error)))))
   :hints (("Goal"
            :induct (lw-real-dirichlet-even-prefix rate count error)
            :in-theory (union-theories '(lw-real-dirichlet-even-prefix lw-real-dirichlet-eta-pairs lw-real-dirichlet-eta-pair
               (:executable-counterpart lw-complex-add) (:executable-counterpart lw-complex-scale)) (theory 'lw-rdp-arithmetic))
            :expand ((lw-complex-common-dirichlet-prefix nil nil rate 0 0 error))
            :do-not '(generalize fertilize))
           (and stable-under-simplificationp
                '(:use ((:instance lw-ordinary-dirichlet-real-prefix-step (count (* 2 count)))
                        (:instance lw-ordinary-dirichlet-real-prefix-step (count (- (* 2 count) 1)))
                        (:instance lw-rdp-pair-arrangement (even (lw-dirichlet-sample rate 0 (* 2 count) error error)) (odd (lw-dirichlet-sample rate 0 (- (* 2 count) 1) error error))
                          (earlier-pairs (lw-real-dirichlet-eta-pairs rate (- count 1) error)) (earlier-even (lw-real-dirichlet-even-prefix rate (- count 1) error)))
                        (:instance lw-dirichlet-sample-rational (height 0) (index (* 2 count)) (log-error error) (node-error error))
                        (:instance lw-dirichlet-sample-rational (height 0) (index (- (* 2 count) 1)) (log-error error) (node-error error))
                        (:instance lw-real-dirichlet-eta-pairs-rational (count (- count 1)))
                        (:instance lw-real-dirichlet-even-prefix-rational (count (- count 1))))
                  :do-not-induct t)))
   :rule-classes nil))

(local
 (defthm lw-rdp-remove-even
   (implies (and (lw-complexp odd) (lw-complexp pairs) (lw-complexp even))
            (equal (lw-complex-sub (lw-complex-add odd (lw-complex-add pairs (lw-complex-scale 2 even)))
                                   (lw-complex-scale 2 even))
                   (lw-complex-add odd pairs)))
   :hints (("Goal" :in-theory (union-theories '(lw-complexp lw-complex-add lw-complex-sub lw-complex-scale cons-equal) (theory 'lw-rdp-arithmetic))
                   :do-not-induct t))
   :rule-classes nil))

(defthm lw-real-dirichlet-eta-odd-parity
  (implies
   (and (rationalp rate) (rationalp error) (< 0 error) (natp count))
   (equal (lw-complex-sub (lw-complex-common-dirichlet-prefix nil nil rate 0 (+ 1 (* 2 count)) error) (lw-complex-scale 2 (lw-real-dirichlet-even-prefix rate count error)))
          (lw-real-dirichlet-eta-odd-prefix rate count error)))
  :hints (("Goal"
           :use (lw-rdp-even-parity lw-real-dirichlet-eta-pairs-rational lw-real-dirichlet-even-prefix-rational
                 (:instance lw-ordinary-dirichlet-real-prefix-step (count (+ 1 (* 2 count))))
                 (:instance lw-dirichlet-sample-rational (height 0) (index (+ 1 (* 2 count))) (log-error error) (node-error error))
                 (:instance lw-rdp-remove-even (odd (lw-dirichlet-sample rate 0 (+ 1 (* 2 count)) error error)) (pairs (lw-real-dirichlet-eta-pairs rate count error)) (even (lw-real-dirichlet-even-prefix rate count error))))
           :in-theory (union-theories '(lw-real-dirichlet-eta-odd-prefix) (theory 'lw-rdp-arithmetic))
           :do-not-induct t))
  :rule-classes nil)
