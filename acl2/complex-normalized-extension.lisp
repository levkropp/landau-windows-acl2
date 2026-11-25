; Exact cancellation for normalization at one, with complex anchor data.
(in-package "ACL2")
(include-book "euler-log-transform")
(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-reciprocal lw-complex-norm-square
                 lw-complex-l1 lw-rational-power lw-complex-exp-value lw-complex-exp-cap
                 lw-complex-exp-uniform-cap lw-exp-lipschitz-cap lw-log-bounds
                 lw-complex-laplace-point lw-complex-laplace-shifted-value
                 lw-complex-laplace-shifted-grid lw-complex-mul-subtract
                 lw-complex-mul-commutative lw-complex-mul-left-commutes
                 lw-exp-bounds lw-exp-neg-bounds lw-exp-index lw-exp-band lw-exp-sum lw-exp-term
                 lw-damped-phase-sample lw-phase-value
                 lw-complex-exp-integral-value lw-complex-exp-integral-grid
                 lw-complex-exp-primitive-value lw-complex-exp-grid
                 lw-complex-disk-enlarge lw-disk-enlarge lw-precision-fuel)))

(local (in-theory (disable lw-complex-log-ramp-exp lw-complex-log-ramp-endpoint lw-complex-log-ramp-model)))

(local (in-theory (disable lw-euler-uniform-polynomial
 lw-complex-euler-continuation-value lw-polynomial-affine
 lw-polynomial-multiply-linear lw-polynomial-add-constant)))
(local (in-theory (disable lw-complex-quotient lw-euler-log-transform)))
(local (defthm lw-cne-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-cne-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-cne-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-cne-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-cne-times-negative (a b) (b a)))
                 :in-theory (disable lw-cne-times-negative)))))

(local (defthm lw-cne-zero-times (equal (* 0 a) 0)))

(local (defthm lw-cne-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-cne-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-cne-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-cne-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-cne-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-cne-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-cne-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cne-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cne-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-cne-left-commutes)))))

(local (defthm lw-cne-pair-reconstruction
 (implies (lw-complexp point) (equal (cons (car point) (cdr point)) point))
 :hints (("Goal" :in-theory (enable lw-complexp)))))

(local (defthm lw-cne-recover-difference
 (implies (and (lw-complexp a) (lw-complexp b))
 (equal (lw-complex-add (lw-complex-sub a b) b) a))
 :hints (("Goal" :in-theory (union-theories
 '(lw-complexp lw-complex-add lw-complex-sub lw-cne-pair-reconstruction lw-cne-left-commutes lw-cne-left-distributes lw-cne-fold-constants lw-cne-times-negative lw-cne-negative-times lw-cne-zero-times lw-cne-minus-one lw-cne-double-negative lw-cne-add-cancel lw-cne-double lw-cne-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-cne-numerator-ring-step
 (implies (and (lw-complexp point) (lw-complexp anchor) (lw-complexp slope))
 (equal (lw-complex-mul point (lw-complex-sub (lw-complex-add (cons 1 0) anchor) slope))
  (lw-complex-sub point
   (lw-complex-sub (lw-complex-add (lw-complex-mul point slope) anchor)
                  (lw-complex-mul (lw-complex-add (cons 1 0) point) anchor)))))
 :hints (("Goal" :in-theory (union-theories
 '(lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-cne-left-commutes lw-cne-left-distributes lw-cne-fold-constants lw-cne-times-negative lw-cne-negative-times lw-cne-zero-times lw-cne-minus-one lw-cne-double-negative lw-cne-add-cancel lw-cne-double lw-cne-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-cne-numerator-identity
 (implies (and (lw-complexp point) (lw-complexp value) (lw-complexp anchor) (lw-complexp slope)
  (equal (lw-complex-mul point slope) (lw-complex-sub value anchor)))
 (equal (lw-complex-mul point (lw-complex-sub (lw-complex-add (cons 1 0) anchor) slope)) (lw-complex-sub point (lw-complex-sub value (lw-complex-mul (lw-complex-add (cons 1 0) point) anchor)))))
 :hints (("Goal" :use (lw-cne-numerator-ring-step)
 :in-theory (union-theories
 '(lw-cne-recover-difference lw-cne-left-commutes lw-cne-left-distributes lw-cne-fold-constants lw-cne-times-negative lw-cne-negative-times lw-cne-zero-times lw-cne-minus-one lw-cne-double-negative lw-cne-add-cancel lw-cne-double lw-cne-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t))
 :rule-classes nil))

(defun lw-complex-normalized-euler (point value anchor)
 (lw-complex-sub (lw-complex-reciprocal (lw-complex-add (cons 1 0) point))
  (lw-complex-quotient
   (lw-complex-sub value (lw-complex-mul (lw-complex-add (cons 1 0) point) anchor))
   (lw-complex-mul (lw-complex-add (cons 1 0) point) point))))

(local (in-theory (disable lw-complex-normalized-euler)))

(defthm lw-complex-normalized-euler-rational
 (implies (and (lw-complexp point) (lw-complexp value) (lw-complexp anchor))
 (lw-complexp (lw-complex-normalized-euler point value anchor)))
 :hints (("Goal"
 :in-theory (union-theories
 '(lw-complex-normalized-euler lw-complex-ring-rational lw-complex-reciprocal-rational lw-complex-quotient-rational (:executable-counterpart lw-complexp) lw-cne-left-commutes lw-cne-left-distributes lw-cne-fold-constants lw-cne-times-negative lw-cne-negative-times lw-cne-zero-times lw-cne-minus-one lw-cne-double-negative lw-cne-add-cancel lw-cne-double lw-cne-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(local (defthm lw-cne-model-product
 (implies (and (lw-complexp point) (lw-complexp anchor) (lw-complexp slope)
  (not (equal (lw-complex-add (cons 1 0) point) (cons 0 0))))
 (equal (lw-complex-mul (lw-complex-mul (lw-complex-add (cons 1 0) point) point) (lw-complex-quotient (lw-complex-sub (lw-complex-add (cons 1 0) anchor) slope) (lw-complex-add (cons 1 0) point))) (lw-complex-mul point (lw-complex-sub (lw-complex-add (cons 1 0) anchor) slope))))
 :hints (("Goal"
 :use ((:instance lw-complex-quotient-denominator-product (numerator (lw-complex-sub (lw-complex-add (cons 1 0) anchor) slope)) (denominator (lw-complex-add (cons 1 0) point)))
       (:instance lw-complex-mul-associative (left point) (middle (lw-complex-add (cons 1 0) point)) (right (lw-complex-quotient (lw-complex-sub (lw-complex-add (cons 1 0) anchor) slope) (lw-complex-add (cons 1 0) point))))
       (:instance lw-complex-mul-commutative (left (lw-complex-add (cons 1 0) point)) (right point)))
 :in-theory (union-theories
 '(lw-complex-ring-rational lw-complex-quotient-rational (:executable-counterpart lw-complexp) lw-cne-left-commutes lw-cne-left-distributes lw-cne-fold-constants lw-cne-times-negative lw-cne-negative-times lw-cne-zero-times lw-cne-minus-one lw-cne-double-negative lw-cne-add-cancel lw-cne-double lw-cne-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-cne-normalized-product
 (implies (and (lw-complexp point) (lw-complexp value) (lw-complexp anchor)
  (not (equal point (cons 0 0))) (not (equal (lw-complex-add (cons 1 0) point) (cons 0 0))))
 (equal (lw-complex-mul (lw-complex-mul (lw-complex-add (cons 1 0) point) point) (lw-complex-normalized-euler point value anchor)) (lw-complex-sub point (lw-complex-sub value (lw-complex-mul (lw-complex-add (cons 1 0) point) anchor)))))
 :hints (("Goal"
 :use ((:instance lw-complex-product-nonzero (a (lw-complex-add (cons 1 0) point)) (b point))
       (:instance lw-complex-reciprocal-inverse (point (lw-complex-add (cons 1 0) point)))
       (:instance lw-complex-mul-associative (left point) (middle (lw-complex-add (cons 1 0) point)) (right (lw-complex-reciprocal (lw-complex-add (cons 1 0) point))))
       (:instance lw-complex-mul-commutative (left (lw-complex-add (cons 1 0) point)) (right point))
       (:instance lw-complex-quotient-denominator-product
        (numerator (lw-complex-sub value (lw-complex-mul (lw-complex-add (cons 1 0) point) anchor))) (denominator (lw-complex-mul (lw-complex-add (cons 1 0) point) point))))
 :in-theory (union-theories
 '(lw-complex-normalized-euler lw-complex-ring-rational lw-complex-quotient-rational lw-complex-reciprocal-rational lw-complex-mul-subtract lw-complex-mul-one (:executable-counterpart lw-complexp) lw-cne-left-commutes lw-cne-left-distributes lw-cne-fold-constants lw-cne-times-negative lw-cne-negative-times lw-cne-zero-times lw-cne-minus-one lw-cne-double-negative lw-cne-add-cancel lw-cne-double lw-cne-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t))
 :rule-classes nil))

(defthm lw-complex-normalized-euler-divided-identity
 (implies (and (lw-complexp point) (lw-complexp value) (lw-complexp anchor) (lw-complexp slope)
  (not (equal point (cons 0 0))) (not (equal (lw-complex-add (cons 1 0) point) (cons 0 0)))
  (equal (lw-complex-mul point slope) (lw-complex-sub value anchor)))
 (equal (lw-complex-quotient (lw-complex-sub (lw-complex-add (cons 1 0) anchor) slope) (lw-complex-add (cons 1 0) point)) (lw-complex-normalized-euler point value anchor)))
 :hints (("Goal"
 :use (lw-cne-numerator-identity lw-cne-model-product lw-cne-normalized-product
       lw-complex-normalized-euler-rational
       (:instance lw-complex-product-nonzero (a (lw-complex-add (cons 1 0) point)) (b point))
       (:instance lw-complex-linear-solve (a (lw-complex-mul (lw-complex-add (cons 1 0) point) point)) (b (lw-complex-quotient (lw-complex-sub (lw-complex-add (cons 1 0) anchor) slope) (lw-complex-add (cons 1 0) point))) (c (lw-complex-sub point (lw-complex-sub value (lw-complex-mul (lw-complex-add (cons 1 0) point) anchor)))))
       (:instance lw-complex-linear-solve (a (lw-complex-mul (lw-complex-add (cons 1 0) point) point)) (b (lw-complex-normalized-euler point value anchor)) (c (lw-complex-sub point (lw-complex-sub value (lw-complex-mul (lw-complex-add (cons 1 0) point) anchor))))))
 :in-theory (union-theories
 '(lw-complex-ring-rational lw-complex-quotient-rational (:executable-counterpart lw-complexp) lw-cne-left-commutes lw-cne-left-distributes lw-cne-fold-constants lw-cne-times-negative lw-cne-negative-times lw-cne-zero-times lw-cne-minus-one lw-cne-double-negative lw-cne-add-cancel lw-cne-double lw-cne-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(local (defthm lw-cne-difference-ring
 (implies (and (lw-complexp constant) (lw-complexp factor) (lw-complexp s)
  (lw-complexp a) (lw-complexp b) (lw-complexp c) (lw-complexp d))
 (equal
  (lw-complex-sub
   (lw-complex-sub constant (lw-complex-mul (lw-complex-sub a (lw-complex-mul s b)) factor))
   (lw-complex-sub constant (lw-complex-mul (lw-complex-sub c (lw-complex-mul s d)) factor)))
  (lw-complex-mul factor (lw-complex-sub (lw-complex-mul s (lw-complex-sub b d)) (lw-complex-sub a c)))))
 :hints (("Goal" :in-theory (union-theories
 '(lw-complexp lw-complex-sub lw-complex-mul lw-cne-left-commutes lw-cne-left-distributes lw-cne-fold-constants lw-cne-times-negative lw-cne-negative-times lw-cne-zero-times lw-cne-minus-one lw-cne-double-negative lw-cne-add-cancel lw-cne-double lw-cne-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-cne-normalized-difference
 (implies (and (lw-complexp point) (lw-complexp value) (lw-complexp other-value)
  (lw-complexp anchor) (lw-complexp other-anchor))
 (equal (lw-complex-sub (lw-complex-normalized-euler point value anchor) (lw-complex-normalized-euler point other-value other-anchor)) (lw-complex-mul (lw-complex-reciprocal (lw-complex-mul (lw-complex-add (cons 1 0) point) point)) (lw-complex-sub (lw-complex-mul (lw-complex-add (cons 1 0) point) (lw-complex-sub anchor other-anchor)) (lw-complex-sub value other-value)))))
 :hints (("Goal"
 :in-theory (union-theories
 '(lw-complex-normalized-euler lw-complex-quotient lw-cne-difference-ring lw-complex-ring-rational lw-complex-reciprocal-rational (:executable-counterpart lw-complexp) lw-cne-left-commutes lw-cne-left-distributes lw-cne-fold-constants lw-cne-times-negative lw-cne-negative-times lw-cne-zero-times lw-cne-minus-one lw-cne-double-negative lw-cne-add-cancel lw-cne-double lw-cne-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t))))

(defthm lw-complex-normalized-euler-transport
 (implies (and (lw-complexp point) (lw-complexp value) (lw-complexp other-value)
  (lw-complexp anchor) (lw-complexp other-anchor)
  (lw-complex-diskp (lw-complex-add (cons 1 0) point) point-cap)
  (lw-complex-diskp (lw-complex-reciprocal (lw-complex-mul (lw-complex-add (cons 1 0) point) point)) inverse-cap)
  (lw-complex-diskp (lw-complex-sub value other-value) value-error)
  (lw-complex-diskp (lw-complex-sub anchor other-anchor) anchor-error))
 (lw-complex-diskp (lw-complex-sub (lw-complex-normalized-euler point value anchor) (lw-complex-normalized-euler point other-value other-anchor))
  (* inverse-cap (+ value-error (* point-cap anchor-error)))))
 :hints (("Goal"
 :use ((:instance lw-complex-mul-disk (left (lw-complex-add (cons 1 0) point)) (right (lw-complex-sub anchor other-anchor))
        (radius point-cap) (other-radius anchor-error))
       (:instance lw-complex-sub-disk
        (left (lw-complex-mul (lw-complex-add (cons 1 0) point) (lw-complex-sub anchor other-anchor))) (right (lw-complex-sub value other-value))
        (radius (* point-cap anchor-error)) (other-radius value-error))
       (:instance lw-complex-mul-disk (left (lw-complex-reciprocal (lw-complex-mul (lw-complex-add (cons 1 0) point) point))) (right (lw-complex-sub (lw-complex-mul (lw-complex-add (cons 1 0) point) (lw-complex-sub anchor other-anchor)) (lw-complex-sub value other-value)))
        (radius inverse-cap) (other-radius (+ value-error (* point-cap anchor-error)))))
 :in-theory (union-theories
 '(lw-cne-normalized-difference lw-cne-left-commutes lw-cne-left-distributes lw-cne-fold-constants lw-cne-times-negative lw-cne-negative-times lw-cne-zero-times lw-cne-minus-one lw-cne-double-negative lw-cne-add-cancel lw-cne-double lw-cne-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(local (defthm lw-cne-shift-not-one
 (implies (and (lw-complexp point) (not (equal point (cons 0 0))))
 (not (and (equal (+ 1 (car point)) 1) (equal (cdr point) 0))))
 :hints (("Goal" :use (lw-cne-pair-reconstruction)
 :cases ((equal (car point) 0))
 :in-theory (enable lw-complexp)
 :do-not-induct t))))

(defthm lw-complex-normalized-euler-real-anchor
 (implies (and (lw-complexp point) (not (equal point (cons 0 0)))
  (< 0 (+ 1 (car point))) (lw-complexp value) (rationalp gamma))
 (equal (lw-complex-normalized-euler point value (cons gamma 0))
        (lw-euler-log-transform (+ 1 (car point)) (cdr point) value gamma)))
 :hints (("Goal"
 :use (lw-cne-shift-not-one
       (:instance lw-euler-log-transform-normalized
        (rate (+ 1 (car point))) (height (cdr point)) (log-value value) (gamma-value gamma)))
 :in-theory (union-theories
 '(lw-complex-normalized-euler lw-euler-log-transform-normalized lw-complexp lw-complex-add lw-complex-mul lw-complex-scale lw-cne-pair-reconstruction lw-cne-left-commutes lw-cne-left-distributes lw-cne-fold-constants lw-cne-times-negative lw-cne-negative-times lw-cne-zero-times lw-cne-minus-one lw-cne-double-negative lw-cne-add-cancel lw-cne-double lw-cne-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))


