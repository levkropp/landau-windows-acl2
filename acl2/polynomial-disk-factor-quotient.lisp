(in-package "ACL2")

(include-book "polynomial-disk-factor-derivative")
(include-book "polynomial-factor-log-sum")
(include-book "polynomial-square-path-control")

; The disk factorization yields the reciprocal sum on a cleared inner contour.

(local (defthm lw-dfq-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-dfq-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-dfq-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-dfq-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-dfq-times-negative (a b) (b a)))
                 :in-theory (disable lw-dfq-times-negative)))))

(local (defthm lw-dfq-zero-times (equal (* 0 a) 0)))

(local (defthm lw-dfq-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-dfq-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-dfq-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-dfq-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-dfq-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-dfq-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-dfq-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-dfq-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-dfq-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-dfq-left-commutes)))))

(local (defthm lw-dfq-original-clearance
 (implies (and (lw-complexp value) (rationalp clearance) (< 0 clearance)
               (not (lw-complex-diskp value (* 2 clearance))))
  (<= (* clearance clearance) (lw-complex-norm-square value)))
 :hints (("Goal"
  :use ((:instance lw-complex-disk-norm-square (point value) (radius (* 2 clearance))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-dfq-left-commutes lw-dfq-left-distributes lw-dfq-fold-constants lw-dfq-times-negative lw-dfq-negative-times lw-dfq-zero-times lw-dfq-minus-one lw-dfq-double-negative lw-dfq-add-cancel lw-dfq-double lw-dfq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :nonlinearp t :do-not-induct t))))

(local (defthm lw-dfq-factor-clearance
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
 '(fold-consts-in-+ lw-dfq-double lw-dfq-left-commutes lw-dfq-left-distributes lw-dfq-fold-constants lw-dfq-times-negative lw-dfq-negative-times lw-dfq-zero-times lw-dfq-minus-one lw-dfq-double-negative lw-dfq-add-cancel lw-dfq-double lw-dfq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))))

(defun lw-disk-factor-quotient-cost (gap clearance numerator-cap)
 (+ (* (/ clearance) (/ gap))
    (* numerator-cap (/ clearance) (/ clearance))))

(local (defthm lw-dfq-cost-identity
 (implies (and (rationalp gap) (rationalp clearance) (rationalp numerator-cap) (rationalp epsilon))
  (equal (* (lw-disk-factor-quotient-cost gap clearance numerator-cap) epsilon)
         (+ (* (/ clearance) epsilon (/ gap))
            (* numerator-cap (/ clearance) (/ clearance) epsilon))))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-disk-factor-quotient-cost lw-dfq-left-commutes lw-dfq-left-distributes lw-dfq-fold-constants lw-dfq-times-negative lw-dfq-negative-times lw-dfq-zero-times lw-dfq-minus-one lw-dfq-double-negative lw-dfq-add-cancel lw-dfq-double lw-dfq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-polynomial-disk-factor-margin
 (implies (and (and (and (lw-complex-coefficientsp coefficients) (rationalp outer-radius) (<= 0 outer-radius) (rationalp epsilon) (< 0 epsilon)) (rationalp inner-radius) (<= 0 inner-radius) (< inner-radius outer-radius) (lw-complex-diskp center inner-radius)) (rationalp clearance) (< 0 clearance) (<= epsilon clearance) (not (lw-complex-diskp (lw-complex-polynomial coefficients center 0) (* 2 clearance)))) (and (lw-complexp (lw-complex-polynomial (lw-polynomial-disk-factor-polynomial coefficients outer-radius epsilon) center 0))
                      (<= (* clearance clearance) (lw-complex-norm-square (lw-complex-polynomial (lw-polynomial-disk-factor-polynomial coefficients outer-radius epsilon) center 0)))
                      (not (equal (lw-complex-polynomial (lw-polynomial-disk-factor-polynomial coefficients outer-radius epsilon) center 0) (cons 0 0)))))
 :hints (("Goal"
  :use (lw-polynomial-disk-factor-data
        (:instance lw-complex-disk-data (point center) (radius inner-radius))
        (:instance lw-complex-disk-enlarge (point center) (radius inner-radius) (cap outer-radius))
        (:instance lw-polynomial-disk-factor-value-error (point center))
        (:instance lw-complex-polynomial-rational (point center) (offset 0))
        (:instance lw-complex-polynomial-rational (coefficients (lw-polynomial-disk-factor-polynomial coefficients outer-radius epsilon)) (point center) (offset 0))
        (:instance lw-dfq-factor-clearance (value (lw-complex-polynomial coefficients center 0)) (factor-value (lw-complex-polynomial (lw-polynomial-disk-factor-polynomial coefficients outer-radius epsilon) center 0)) (error epsilon))
        (:instance lw-complex-norm-lower-nonzero (point (lw-complex-polynomial (lw-polynomial-disk-factor-polynomial coefficients outer-radius epsilon) center 0)) (lower clearance)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-dfq-left-commutes lw-dfq-left-distributes lw-dfq-fold-constants lw-dfq-times-negative lw-dfq-negative-times lw-dfq-zero-times lw-dfq-minus-one lw-dfq-double-negative lw-dfq-add-cancel lw-dfq-double lw-dfq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-polynomial-disk-factor-sum-identity
 (implies (and (and (and (lw-complex-coefficientsp coefficients) (rationalp outer-radius) (<= 0 outer-radius) (rationalp epsilon) (< 0 epsilon)) (rationalp inner-radius) (<= 0 inner-radius) (< inner-radius outer-radius) (lw-complex-diskp center inner-radius)) (rationalp clearance) (< 0 clearance) (<= epsilon clearance) (not (lw-complex-diskp (lw-complex-polynomial coefficients center 0) (* 2 clearance))))
  (equal (lw-complex-quotient (lw-complex-polynomial-derivative (lw-polynomial-disk-factor-polynomial coefficients outer-radius epsilon) center) (lw-complex-polynomial (lw-polynomial-disk-factor-polynomial coefficients outer-radius epsilon) center 0)) (lw-polynomial-factor-log-sum (lw-polynomial-normalized-factor-roots coefficients outer-radius epsilon) center)))
 :hints (("Goal"
  :use (lw-polynomial-disk-factor-data lw-polynomial-disk-factor-margin
        (:instance lw-complex-disk-data (point center) (radius inner-radius))
        (:instance lw-polynomial-disk-factor-evaluation (point center))
        (:instance lw-polynomial-factor-log-derivative (point center) (roots (lw-polynomial-normalized-factor-roots coefficients outer-radius epsilon)) (leading (lw-polynomial-leading (lw-polynomial-trim coefficients)))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-disk-factor-polynomial lw-dfq-left-commutes lw-dfq-left-distributes lw-dfq-fold-constants lw-dfq-times-negative lw-dfq-negative-times lw-dfq-zero-times lw-dfq-minus-one lw-dfq-double-negative lw-dfq-add-cancel lw-dfq-double lw-dfq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-polynomial-disk-factor-sum-error
 (implies (and (and (and (and (lw-complex-coefficientsp coefficients) (rationalp outer-radius) (<= 0 outer-radius) (rationalp epsilon) (< 0 epsilon)) (rationalp inner-radius) (<= 0 inner-radius) (< inner-radius outer-radius) (lw-complex-diskp center inner-radius)) (rationalp clearance) (< 0 clearance) (<= epsilon clearance) (not (lw-complex-diskp (lw-complex-polynomial coefficients center 0) (* 2 clearance)))) (rationalp numerator-cap) (<= 0 numerator-cap) (lw-complex-diskp (lw-complex-polynomial-derivative coefficients center) numerator-cap))
  (lw-complex-diskp (lw-complex-sub (lw-polynomial-factor-log-sum (lw-polynomial-normalized-factor-roots coefficients outer-radius epsilon) center) (lw-complex-quotient (lw-complex-polynomial-derivative coefficients center) (lw-complex-polynomial coefficients center 0))) (* (lw-disk-factor-quotient-cost (- outer-radius inner-radius) clearance numerator-cap) epsilon)))
 :hints (("Goal"
  :use (lw-polynomial-disk-factor-data lw-polynomial-disk-factor-margin lw-polynomial-disk-factor-sum-identity
        lw-polynomial-disk-factor-derivative-error
        (:instance lw-complex-disk-data (point center) (radius inner-radius))
        (:instance lw-complex-disk-enlarge (point center) (radius inner-radius) (cap outer-radius))
        (:instance lw-polynomial-disk-factor-value-error (point center))
        (:instance lw-complex-polynomial-rational (point center) (offset 0))
        (:instance lw-complex-polynomial-derivative-rational (coefficients (lw-polynomial-disk-factor-polynomial coefficients outer-radius epsilon)) (point center))
        (:instance lw-complex-disk-data (point (lw-complex-polynomial-derivative coefficients center)) (radius numerator-cap))
        (:instance lw-dfq-original-clearance (value (lw-complex-polynomial coefficients center 0)))
        (:instance lw-complex-difference-symmetric (left (lw-complex-polynomial-derivative coefficients center)) (right (lw-complex-polynomial-derivative (lw-polynomial-disk-factor-polynomial coefficients outer-radius epsilon) center)) (radius (* epsilon (/ (- outer-radius inner-radius)))))
        (:instance lw-complex-difference-symmetric (left (lw-complex-polynomial coefficients center 0)) (right (lw-complex-polynomial (lw-polynomial-disk-factor-polynomial coefficients outer-radius epsilon) center 0)) (radius epsilon))
        (:instance lw-complex-quotient-difference-bound
         (numerator (lw-complex-polynomial-derivative (lw-polynomial-disk-factor-polynomial coefficients outer-radius epsilon) center)) (denominator (lw-complex-polynomial (lw-polynomial-disk-factor-polynomial coefficients outer-radius epsilon) center 0)) (approximate-numerator (lw-complex-polynomial-derivative coefficients center)) (approximate-denominator (lw-complex-polynomial coefficients center 0))
         (left-clearance clearance) (right-clearance clearance)
         (numerator-error (* epsilon (/ (- outer-radius inner-radius)))) (denominator-error epsilon)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-dfq-cost-identity lw-dfq-left-commutes lw-dfq-left-distributes lw-dfq-fold-constants lw-dfq-times-negative lw-dfq-negative-times lw-dfq-zero-times lw-dfq-minus-one lw-dfq-double-negative lw-dfq-add-cancel lw-dfq-double lw-dfq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
