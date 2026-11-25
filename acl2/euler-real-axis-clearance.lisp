(in-package "ACL2")

(include-book "euler-real-nonvanishing")
(include-book "euler-nonzero-neighborhood")

; Patch the real eta estimate with the certified neighborhood at one.

(local (defthm lw-erac-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-erac-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-erac-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-erac-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-erac-times-negative (a b) (b a)))
                 :in-theory (disable lw-erac-times-negative)))))

(local (defthm lw-erac-zero-times (equal (* 0 a) 0)))

(local (defthm lw-erac-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-erac-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-erac-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-erac-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-erac-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-erac-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-erac-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-erac-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-erac-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-erac-left-commutes)))))

(local (deftheory lw-erac-arithmetic (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              
              lw-erac-left-commutes lw-erac-left-distributes lw-erac-fold-constants
              lw-erac-times-negative lw-erac-negative-times lw-erac-zero-times
              lw-erac-minus-one lw-erac-double-negative lw-erac-add-cancel lw-erac-double lw-erac-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))

(defun lw-euler-real-anchor-radius ()
  (lw-euler-neighborhood-radius 1 0 1/2 1/64))

(defun lw-euler-real-axis-request (lower)
  (min 1/64 (* 1/64 (* (lw-euler-real-anchor-radius) (lw-real-dirichlet-first-gap lower)))))

(defun lw-euler-real-axis-floor (lower)
  (min 1/8 (* 1/32 (* (lw-euler-real-anchor-radius) (lw-real-dirichlet-first-gap lower)))))

(local
 (defthm lw-erac-anchor-radius-positive
   (and (rationalp (lw-euler-real-anchor-radius)) (< 0 (lw-euler-real-anchor-radius)))
   :hints (("Goal"
            :use ((:instance lw-euler-value-anchor-clearance (anchor-error 1/64))
                  (:instance lw-euler-neighborhood-data (rate 1) (height 0) (anchor-error 1/64) (outer-radius 1/2)))
            :in-theory (union-theories '(lw-euler-real-anchor-radius) (theory 'lw-erac-arithmetic))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-euler-real-axis-budget-data
  (implies (and (rationalp lower) (< 0 lower))
           (and (rationalp (lw-euler-real-axis-request lower)) (< 0 (lw-euler-real-axis-request lower)) (<= (lw-euler-real-axis-request lower) 1/64)
                (<= (lw-euler-real-axis-request lower) (* 1/64 (* (lw-euler-real-anchor-radius) (lw-real-dirichlet-first-gap lower))))
                (rationalp (lw-euler-real-axis-floor lower)) (< 0 (lw-euler-real-axis-floor lower)) (<= (lw-euler-real-axis-floor lower) 1/8)
                (<= (lw-euler-real-axis-floor lower) (* 1/32 (* (lw-euler-real-anchor-radius) (lw-real-dirichlet-first-gap lower))))))
  :hints (("Goal"
           :use (lw-erac-anchor-radius-positive
                 (:instance lw-real-dirichlet-first-gap-positive (rate lower))
                 (:instance lw-erac-positive-product (a (lw-euler-real-anchor-radius)) (b (lw-real-dirichlet-first-gap lower))))
           :in-theory (union-theories '(lw-euler-real-axis-request lw-euler-real-axis-floor min) (theory 'lw-erac-arithmetic))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm lw-erac-square-order
   (implies (and (rationalp a) (<= 0 a) (rationalp b) (<= a b))
            (<= (* a a) (* b b)))
   :hints (("Goal"
            :use ((:instance lw-erac-multiply-order (factor a))
                  (:instance lw-erac-multiply-order (factor b)))
            :in-theory (theory 'lw-erac-arithmetic)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-erac-real-offset-disk
   (implies (and (rationalp rate) (rationalp radius) (<= 0 radius) (<= (abs (- rate 1)) radius))
            (lw-complex-diskp (cons (- rate 1) 0) radius))
   :hints (("Goal"
            :use ((:instance lw-complex-disk-norm-square (point (cons (- rate 1) 0)))
                  (:instance lw-erac-square-order (a (abs (- rate 1))) (b radius)))
            :in-theory (union-theories '(lw-complexp lw-complex-norm-square abs) (theory 'lw-erac-arithmetic))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-erac-near-one
   (implies (and (rationalp rate) (<= (abs (- rate 1)) (lw-euler-real-anchor-radius))
                 (rationalp error) (< 0 error) (<= error 1/64))
            (<= 1/64 (lw-complex-norm-square (lw-complex-euler-continuation-value rate 0 error))))
   :hints (("Goal"
            :use (lw-erac-anchor-radius-positive
                  (:instance lw-euler-value-anchor-clearance (anchor-error 1/64))
                  (:instance lw-erac-real-offset-disk (radius (lw-euler-real-anchor-radius)))
                  (:instance lw-complex-euler-neighborhood-value-clearance
                    (rate 1) (height 0) (outer-radius 1/2) (anchor-error 1/64) (point (cons (- rate 1) 0)))
                  (:instance lw-erac-square-order (a 1/8) (b (* 1/4 (lw-euler-value-clearance-size 1 0 1/64))))
                  (:instance lw-euler-value-clearance-data (rate 1) (height 0) (anchor-error 1/64)))
            :in-theory (union-theories '(lw-euler-real-anchor-radius lw-euler-value-clearance-lower) (theory 'lw-erac-arithmetic))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-real-dirichlet-first-gap-monotone
  (implies (and (rationalp lower) (< 0 lower) (rationalp rate) (<= lower rate))
           (<= (lw-real-dirichlet-first-gap lower) (lw-real-dirichlet-first-gap rate)))
  :hints (("Goal"
           :use ((:instance lw-reciprocal-antitone (left (+ 1 (* 1/2 lower))) (right (+ 1 (* 1/2 rate)))))
           :in-theory (union-theories '(lw-real-dirichlet-first-gap) (theory 'lw-erac-arithmetic))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm lw-erac-far-strength
   (implies
    (and (rationalp lower) (< 0 lower) (rationalp rate) (<= lower rate) (< (lw-euler-real-anchor-radius) (abs (- rate 1))))
    (and (not (equal rate 1)) (<= (* (lw-euler-real-anchor-radius) (lw-real-dirichlet-first-gap lower)) (lw-real-euler-eta-lower-strength rate))))
   :hints (("Goal"
            :use (lw-erac-anchor-radius-positive lw-real-dirichlet-first-gap-positive
                  lw-real-dirichlet-first-gap-monotone
                  (:instance lw-real-dirichlet-first-gap-positive (rate lower))
                  (:instance lw-erac-multiply-order
                    (a (lw-euler-real-anchor-radius)) (b (abs (- rate 1))) (factor (lw-real-dirichlet-first-gap lower)))
                  (:instance lw-erac-multiply-order
                    (a (lw-real-dirichlet-first-gap lower)) (b (lw-real-dirichlet-first-gap rate)) (factor (abs (- rate 1)))))
            :in-theory (union-theories '(lw-real-euler-eta-lower-strength abs) (theory 'lw-erac-arithmetic))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-complex-euler-real-axis-clearance
  (implies
   (and (rationalp lower) (< 0 lower) (rationalp rate) (<= lower rate)
       (rationalp error) (< 0 error) (<= error (lw-euler-real-axis-request lower)))
   (<= (* (lw-euler-real-axis-floor lower) (lw-euler-real-axis-floor lower)) (lw-complex-norm-square (lw-complex-euler-continuation-value rate 0 error))))
  :hints (("Goal"
           :cases ((<= (abs (- rate 1)) (lw-euler-real-anchor-radius)))
           :use (lw-euler-real-axis-budget-data lw-erac-near-one lw-erac-far-strength
                 (:instance lw-complex-euler-real-nonvanishing-away-from-one (value-error error))
                 (:instance lw-erac-square-order (a (lw-euler-real-axis-floor lower)) (b 1/8))
                 (:instance lw-erac-square-order (a (lw-euler-real-axis-floor lower)) (b (* 1/32 (lw-real-euler-eta-lower-strength rate)))))
           :in-theory (theory 'lw-erac-arithmetic)
           :do-not-induct t))
  :rule-classes nil)
