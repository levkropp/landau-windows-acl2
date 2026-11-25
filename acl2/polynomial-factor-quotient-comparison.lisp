(in-package "ACL2")

(include-book "polynomial-accurate-derivative")
(include-book "complex-quotients")

; Compare the two logarithmic derivatives using a margin for the original
; polynomial and a derivative cap independent of the factorization request.

(local (defthm lw-fqc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-fqc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-fqc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-fqc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-fqc-times-negative (a b) (b a)))
                 :in-theory (disable lw-fqc-times-negative)))))

(local (defthm lw-fqc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-fqc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-fqc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-fqc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-fqc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-fqc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-fqc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-fqc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-fqc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-fqc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-fqc-left-commutes)))))

(defun lw-polynomial-factor-quotient-cost (clearance numerator-cap)
 (+ (* 2 (/ clearance)) (* numerator-cap (/ clearance) (/ clearance))))

(local (defthm lw-fqc-cost-expand
 (implies (and (rationalp clearance) (rationalp numerator-cap) (rationalp request))
  (equal (* (lw-polynomial-factor-quotient-cost clearance numerator-cap) request)
         (+ (* (/ clearance) (* 2 request)) (* numerator-cap (/ clearance) (/ clearance) request))))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-factor-quotient-cost lw-fqc-left-commutes lw-fqc-left-distributes lw-fqc-fold-constants lw-fqc-times-negative lw-fqc-negative-times lw-fqc-zero-times lw-fqc-minus-one lw-fqc-double-negative lw-fqc-add-cancel lw-fqc-double lw-fqc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-fqc-original-clearance
 (implies (and (lw-complexp value) (rationalp clearance) (< 0 clearance)
               (not (lw-complex-diskp value (* 2 clearance))))
  (<= (* clearance clearance) (lw-complex-norm-square value)))
 :hints (("Goal"
  :use ((:instance lw-complex-disk-norm-square (point value) (radius (* 2 clearance))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-fqc-left-commutes lw-fqc-left-distributes lw-fqc-fold-constants lw-fqc-times-negative lw-fqc-negative-times lw-fqc-zero-times lw-fqc-minus-one lw-fqc-double-negative lw-fqc-add-cancel lw-fqc-double lw-fqc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :nonlinearp t :do-not-induct t))))

(local (defthm lw-fqc-factor-clearance
 (implies (and (lw-complexp value) (lw-complexp factor-value)
               (rationalp clearance) (< 0 clearance)
               (rationalp error) (<= 0 error) (<= error clearance)
               (not (lw-complex-diskp value (* 2 clearance)))
               (lw-complex-diskp (lw-complex-sub value factor-value) error))
  (<= (* clearance clearance) (lw-complex-norm-square factor-value)))
 :hints (("Goal"
  :use ((:instance lw-complex-difference-symmetric
         (left value) (right factor-value) (radius error))
        (:instance lw-complex-perturbation-excludes-small
         (left value) (right factor-value) (epsilon clearance) (delta clearance))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub factor-value value)) (radius error) (cap clearance))
        (:instance lw-complex-disk-norm-square (point factor-value) (radius clearance)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-fqc-double lw-fqc-left-commutes lw-fqc-left-distributes lw-fqc-fold-constants lw-fqc-times-negative lw-fqc-negative-times lw-fqc-zero-times lw-fqc-minus-one lw-fqc-double-negative lw-fqc-add-cancel lw-fqc-double lw-fqc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))))

(defthm lw-polynomial-square-factor-quotient-error
 (implies (and (and (rationalp tolerance) (< 0 tolerance) (lw-complex-coefficientsp coefficients) (posp count) (lw-polynomial-square-boundary-check coefficients (cons -1 -1) 2 count)) (lw-complex-diskp center 3/2)
               (rationalp clearance) (< 0 clearance) (<= tolerance clearance)
               (not (lw-complex-diskp (lw-complex-polynomial coefficients center 0) (* 2 clearance)))
               (rationalp numerator-cap) (<= 0 numerator-cap)
               (lw-complex-diskp (lw-complex-polynomial-derivative coefficients center) numerator-cap))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-quotient (lw-complex-polynomial-derivative (lw-polynomial-square-factor-polynomial coefficients count tolerance) center) (lw-complex-polynomial (lw-polynomial-square-factor-polynomial coefficients count tolerance) center 0)) (lw-complex-quotient (lw-complex-polynomial-derivative coefficients center) (lw-complex-polynomial coefficients center 0)))
   (* (lw-polynomial-factor-quotient-cost clearance numerator-cap) (lw-polynomial-square-factor-request coefficients count tolerance))))
 :hints (("Goal"
  :use (lw-polynomial-square-factor-polynomial-valid lw-polynomial-square-factor-request-data
        lw-polynomial-square-factor-derivative-error
        (:instance lw-complex-disk-data (point center) (radius 3/2))
        (:instance lw-complex-disk-enlarge (point center) (radius 3/2) (cap 2))
        (:instance lw-polynomial-square-factor-polynomial-value-error (point center))
        (:instance lw-complex-polynomial-rational (point center) (offset 0))
        (:instance lw-complex-polynomial-rational (coefficients (lw-polynomial-square-factor-polynomial coefficients count tolerance)) (point center) (offset 0))
        (:instance lw-complex-polynomial-derivative-rational (point center))
        (:instance lw-complex-polynomial-derivative-rational (coefficients (lw-polynomial-square-factor-polynomial coefficients count tolerance)) (point center))
        (:instance lw-complex-difference-symmetric (left (lw-complex-polynomial-derivative coefficients center)) (right (lw-complex-polynomial-derivative (lw-polynomial-square-factor-polynomial coefficients count tolerance) center)) (radius (* 2 (lw-polynomial-square-factor-request coefficients count tolerance))))
        (:instance lw-complex-difference-symmetric (left (lw-complex-polynomial coefficients center 0)) (right (lw-complex-polynomial (lw-polynomial-square-factor-polynomial coefficients count tolerance) center 0)) (radius (lw-polynomial-square-factor-request coefficients count tolerance)))
        (:instance lw-fqc-original-clearance (value (lw-complex-polynomial coefficients center 0)))
        (:instance lw-fqc-factor-clearance (value (lw-complex-polynomial coefficients center 0)) (factor-value (lw-complex-polynomial (lw-polynomial-square-factor-polynomial coefficients count tolerance) center 0)) (error (lw-polynomial-square-factor-request coefficients count tolerance)))
        (:instance lw-complex-quotient-difference-bound
         (numerator (lw-complex-polynomial-derivative (lw-polynomial-square-factor-polynomial coefficients count tolerance) center)) (denominator (lw-complex-polynomial (lw-polynomial-square-factor-polynomial coefficients count tolerance) center 0))
         (approximate-numerator (lw-complex-polynomial-derivative coefficients center)) (approximate-denominator (lw-complex-polynomial coefficients center 0))
         (left-clearance clearance) (right-clearance clearance)
         (numerator-error (* 2 (lw-polynomial-square-factor-request coefficients count tolerance))) (denominator-error (lw-polynomial-square-factor-request coefficients count tolerance))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-fqc-cost-expand lw-fqc-left-commutes lw-fqc-left-distributes lw-fqc-fold-constants lw-fqc-times-negative lw-fqc-negative-times lw-fqc-zero-times lw-fqc-minus-one lw-fqc-double-negative lw-fqc-add-cancel lw-fqc-double lw-fqc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
