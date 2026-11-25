(in-package "ACL2")

(include-book "unit-square-steps")

; Compute a canonical square mesh fine enough for every power through
; the requested degree. Its monomial winding is the degree itself.

(local (defthm lw-upi-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-upi-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-upi-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-upi-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-upi-times-negative (a b) (b a)))
                 :in-theory (disable lw-upi-times-negative)))))

(local (defthm lw-upi-zero-times (equal (* 0 a) 0)))

(local (defthm lw-upi-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-upi-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-upi-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-upi-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-upi-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-upi-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-upi-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-upi-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-upi-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-upi-left-commutes)))))

(defun lw-unit-square-power-count (degree)
 (* 4 (+ 1 (lw-ceiling-rational (/ (lw-ray-power-step-budget degree))))))

(local (defthm lw-upi-count-budget
 (implies (and (rationalp error) (< 0 error))
  (let* ((factor (+ 1 (lw-ceiling-rational (/ error))))
         (count (* 4 factor)))
   (and (posp factor) (posp count) (<= (* 2 (/ count)) error))))
 :hints (("Goal"
  :use ((:instance lw-reciprocal-positive (value error))
        (:instance lw-ceiling-rational-natural (value (/ error)))
        (:instance lw-ceiling-rational-bracket (value (/ error)))
        (:instance lw-upi-multiply-order
          (a (/ error)) (b (+ 1 (lw-ceiling-rational (/ error)))) (factor error))
        (:instance lw-upi-inverse-factor (divisor error) (coefficient 1))
        (:instance lw-positive-division-bound (numerator 2)
          (divisor (* 4 (+ 1 (lw-ceiling-rational (/ error))))) (bound error)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-upi-left-commutes lw-upi-left-distributes lw-upi-fold-constants lw-upi-times-negative lw-upi-negative-times lw-upi-zero-times lw-upi-minus-one lw-upi-double-negative lw-upi-add-cancel lw-upi-double lw-upi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :nonlinearp t))))

(defthm lw-unit-square-power-count-data
 (implies (natp degree)
  (and (posp (lw-unit-square-power-count degree))
       (<= (* 2 (/ (lw-unit-square-power-count degree))) (lw-ray-power-step-budget degree))))
 :hints (("Goal"
  :use (lw-ray-power-step-budget-valid
        (:instance lw-upi-count-budget (error (lw-ray-power-step-budget degree))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-unit-square-power-count lw-upi-left-commutes lw-upi-left-distributes lw-upi-fold-constants lw-upi-times-negative lw-upi-negative-times lw-upi-zero-times lw-upi-minus-one lw-upi-double-negative lw-upi-add-cancel lw-upi-double lw-upi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-unit-square-power-boundary-data
 (implies (natp degree)
  (let ((points (lw-unit-square-boundary (lw-unit-square-power-count degree))))
   (and (consp points) (lw-ray-annulus-pointsp points 1 2)
        (equal (lw-ray-row-last points) (car points))
        (lw-ray-path-step-check points (lw-ray-power-step-budget degree))
        (equal (lw-ray-polygon-index points) 1))))
 :hints (("Goal"
  :use (lw-unit-square-power-count-data lw-ray-power-step-budget-valid
        (:instance lw-unit-square-boundary-data (count (lw-unit-square-power-count degree)))
        (:instance lw-unit-square-boundary-annulus (count (lw-unit-square-power-count degree)))
        (:instance lw-unit-square-boundary-step (count (lw-unit-square-power-count degree)))
        (:instance lw-ray-path-step-enlarge
          (points (lw-unit-square-boundary (lw-unit-square-power-count degree)))
          (delta (* 2 (/ (lw-unit-square-power-count degree)))) (larger (lw-ray-power-step-budget degree)))
        (:instance lw-unit-square-boundary-index
          (factor (+ 1 (lw-ceiling-rational (/ (lw-ray-power-step-budget degree))))))
        (:instance lw-upi-count-budget (error (lw-ray-power-step-budget degree))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-unit-square-power-count lw-upi-left-commutes lw-upi-left-distributes lw-upi-fold-constants lw-upi-times-negative lw-upi-negative-times lw-upi-zero-times lw-upi-minus-one lw-upi-double-negative lw-upi-add-cancel lw-upi-double lw-upi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-unit-square-monomial-index
 (implies (natp degree)
  (equal (lw-ray-polygon-index
           (lw-ray-power-points (lw-unit-square-boundary (lw-unit-square-power-count degree)) degree))
         degree))
 :hints (("Goal"
  :use (lw-unit-square-power-boundary-data
        (:instance lw-ray-power-index-at-computed-step
          (points (lw-unit-square-boundary (lw-unit-square-power-count degree)))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-upi-left-commutes lw-upi-left-distributes lw-upi-fold-constants lw-upi-times-negative lw-upi-negative-times lw-upi-zero-times lw-upi-minus-one lw-upi-double-negative lw-upi-add-cancel lw-upi-double lw-upi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-upi-delta-small
 (implies (and (rationalp upper) (<= 1 upper) (rationalp delta) (< 0 delta)
               (< (+ (* delta upper) (* delta upper)) 1))
          (< delta 1))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance lw-upi-multiply-order (a 1) (b upper) (factor delta)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-upi-left-commutes lw-upi-left-distributes lw-upi-fold-constants lw-upi-times-negative lw-upi-negative-times lw-upi-zero-times lw-upi-minus-one lw-upi-double-negative lw-upi-add-cancel lw-upi-double lw-upi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :nonlinearp t))))

(local (defthm lw-upi-power-head
 (implies (consp points)
  (equal (car (lw-ray-power-points points index)) (lw-complex-power (car points) index)))
 :hints (("Goal" :expand ((lw-ray-power-points points index)) :in-theory (union-theories
 '(fold-consts-in-+ lw-upi-left-commutes lw-upi-left-distributes lw-upi-fold-constants lw-upi-times-negative lw-upi-negative-times lw-upi-zero-times lw-upi-minus-one lw-upi-double-negative lw-upi-add-cancel lw-upi-double lw-upi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-unit-square-monomial-boundary-safe
 (implies (natp degree)
  (lw-ray-safe-polygonp
   (lw-ray-power-points (lw-unit-square-boundary (lw-unit-square-power-count degree)) degree)))
 :hints (("Goal"
  :use (lw-unit-square-power-boundary-data lw-ray-power-step-budget-valid
        (:instance lw-rational-power-at-least-one (base 2) (exponent degree))
        (:instance lw-ray-power-points-annulus
          (points (lw-unit-square-boundary (lw-unit-square-power-count degree))) (index degree))
        (:instance lw-ray-power-points-uniform-step
          (points (lw-unit-square-boundary (lw-unit-square-power-count degree)))
          (index degree) (error (lw-ray-power-step-budget degree))
          (delta (lw-ray-product-step-budget 1 (lw-rational-power 2 degree) 1 (lw-rational-power 2 degree))))
        (:instance lw-upi-delta-small (upper (lw-rational-power 2 degree))
          (delta (lw-ray-product-step-budget 1 (lw-rational-power 2 degree) 1 (lw-rational-power 2 degree))))
        (:instance lw-ray-annulus-closed-polygon-safe
          (points (lw-ray-power-points (lw-unit-square-boundary (lw-unit-square-power-count degree)) degree))
          (lower 1) (upper (lw-rational-power 2 degree))
          (delta (lw-ray-product-step-budget 1 (lw-rational-power 2 degree) 1 (lw-rational-power 2 degree)))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-annulus-data lw-ray-power-points-data lw-ray-power-points-last lw-rational-power-rational lw-upi-power-head lw-upi-left-commutes lw-upi-left-distributes lw-upi-fold-constants lw-upi-times-negative lw-upi-negative-times lw-upi-zero-times lw-upi-minus-one lw-upi-double-negative lw-upi-add-cancel lw-upi-double lw-upi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-unit-square-leading-monomial-index
 (implies (and (natp degree) (lw-complexp leading) (not (equal leading (cons 0 0))))
  (equal (lw-ray-polygon-index
           (lw-ray-multiply-points leading
            (lw-ray-power-points (lw-unit-square-boundary (lw-unit-square-power-count degree)) degree)))
         degree))
 :hints (("Goal"
  :use (lw-unit-square-monomial-index lw-unit-square-monomial-boundary-safe
        (:instance lw-ray-polygon-product-invariant (factor leading)
          (points (lw-ray-power-points (lw-unit-square-boundary (lw-unit-square-power-count degree)) degree))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-upi-left-commutes lw-upi-left-distributes lw-upi-fold-constants lw-upi-times-negative lw-upi-negative-times lw-upi-zero-times lw-upi-minus-one lw-upi-double-negative lw-upi-add-cancel lw-upi-double lw-upi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

