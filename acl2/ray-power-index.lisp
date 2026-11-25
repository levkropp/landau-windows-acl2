(in-package "ACL2")

(include-book "ray-power-samples")

; One computed input step works for every power through the degree.
; Multiplicative winding then computes the sampled monomial index.

(local (defthm lw-rpi-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-rpi-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-rpi-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-rpi-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-rpi-times-negative (a b) (b a)))
                 :in-theory (disable lw-rpi-times-negative)))))

(local (defthm lw-rpi-zero-times (equal (* 0 a) 0)))

(local (defthm lw-rpi-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-rpi-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-rpi-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-rpi-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-rpi-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-rpi-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-rpi-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-rpi-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-rpi-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-rpi-left-commutes)))))

(defun lw-ray-power-step-budget (degree)
 (let ((upper (lw-rational-power 2 degree)))
  (* (lw-ray-product-step-budget 1 upper 1 upper)
     (/ (+ 1 (lw-rational-power 4 degree))))))

(local (defthm lw-rpi-inverse-positive
 (implies (and (rationalp x) (< 0 x)) (< 0 (/ x)))
 :hints (("Goal" :use ((:instance inverse-of-*))
          :in-theory (disable inverse-of-*) :nonlinearp t)) :rule-classes nil))

(local (defthm lw-rpi-precision-algebra
 (implies (and (rationalp delta) (< 0 delta) (rationalp factor) (<= 1 factor))
  (let ((error (* delta (/ (+ 1 factor)))))
   (and (rationalp error) (< 0 error) (<= (* factor error) delta))))
 :hints (("Goal"
  :use ((:instance lw-rpi-inverse-positive (x (+ 1 factor)))
        (:instance lw-rpi-positive-product (a delta) (b (/ (+ 1 factor))))
        (:instance lw-rpi-inverse-factor (divisor (+ 1 factor)) (coefficient delta)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-rpi-left-commutes lw-rpi-left-distributes lw-rpi-fold-constants lw-rpi-times-negative lw-rpi-negative-times lw-rpi-zero-times lw-rpi-minus-one lw-rpi-double-negative lw-rpi-add-cancel lw-rpi-double lw-rpi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :nonlinearp t))))

(defthm lw-ray-power-step-budget-valid
 (implies (natp degree)
  (let* ((upper (lw-rational-power 2 degree))
         (delta (lw-ray-product-step-budget 1 upper 1 upper))
         (error (lw-ray-power-step-budget degree)))
   (and (rationalp error) (< 0 error) (rationalp delta) (< 0 delta)
        (<= (* (lw-rational-power 4 degree) error) delta)
        (< (+ (* delta upper) (* delta upper)) 1))))
 :hints (("Goal"
  :use ((:instance lw-rational-power-at-least-one (base 2) (exponent degree))
        (:instance lw-rational-power-at-least-one (base 4) (exponent degree))
        (:instance lw-ray-product-step-budget-valid
          (lower-left 1) (upper-left (lw-rational-power 2 degree))
          (lower-right 1) (upper-right (lw-rational-power 2 degree)))
        (:instance lw-rpi-precision-algebra
          (delta (lw-ray-product-step-budget 1 (lw-rational-power 2 degree) 1 (lw-rational-power 2 degree)))
          (factor (lw-rational-power 4 degree))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-power-step-budget lw-rational-power-rational lw-rpi-left-commutes lw-rpi-left-distributes lw-rpi-fold-constants lw-rpi-times-negative lw-rpi-negative-times lw-rpi-zero-times lw-rpi-minus-one lw-rpi-double-negative lw-rpi-add-cancel lw-rpi-double lw-rpi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-rpi-head
 (implies (consp points)
  (equal (car (lw-ray-power-points points index)) (lw-complex-power (car points) index)))
 :hints (("Goal" :expand ((lw-ray-power-points points index))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-rpi-left-commutes lw-rpi-left-distributes lw-rpi-fold-constants lw-rpi-times-negative lw-rpi-negative-times lw-rpi-zero-times lw-rpi-minus-one lw-rpi-double-negative lw-rpi-add-cancel lw-rpi-double lw-rpi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-rpi-index-step
 (implies (and (consp points) (lw-ray-annulus-pointsp points 1 2)
               (equal (lw-ray-row-last points) (car points))
               (natp degree) (posp index) (<= index degree)
               (lw-ray-path-step-check points (lw-ray-power-step-budget degree))
               (equal (lw-ray-polygon-index (lw-ray-power-points points (- index 1)))
                      (* (- index 1) (lw-ray-polygon-index points))))
  (equal (lw-ray-polygon-index (lw-ray-power-points points index))
         (* index (lw-ray-polygon-index points))))
 :hints (("Goal"
  :use (lw-ray-power-step-budget-valid
        (:instance lw-ray-annulus-data (lower 1) (upper 2))
        (:instance lw-rational-power-at-least-one (base 2) (exponent degree))
        (:instance lw-ray-power-points-annulus (index 1))
        (:instance lw-ray-power-points-annulus (index (- index 1)))
        (:instance lw-ray-power-points-uniform-step (index 1)
          (error (lw-ray-power-step-budget degree))
          (delta (lw-ray-product-step-budget 1 (lw-rational-power 2 degree) 1 (lw-rational-power 2 degree))))
        (:instance lw-ray-power-points-uniform-step (index (- index 1))
          (error (lw-ray-power-step-budget degree))
          (delta (lw-ray-product-step-budget 1 (lw-rational-power 2 degree) 1 (lw-rational-power 2 degree))))
        (:instance lw-ray-product-index-from-budgets
          (left points) (right (lw-ray-power-points points (- index 1)))
          (lower-left 1) (upper-left (lw-rational-power 2 degree))
          (lower-right 1) (upper-right (lw-rational-power 2 degree))
          (delta (lw-ray-product-step-budget 1 (lw-rational-power 2 degree) 1 (lw-rational-power 2 degree))))
        (:instance lw-ray-power-points-product (index (- index 1))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-power-one-points lw-ray-power-points-data lw-ray-power-points-last lw-rpi-head lw-rational-power-rational lw-ray-polygon-index-integer lw-rpi-left-commutes lw-rpi-left-distributes lw-rpi-fold-constants lw-rpi-times-negative lw-rpi-negative-times lw-rpi-zero-times lw-rpi-minus-one lw-rpi-double-negative lw-rpi-add-cancel lw-rpi-double lw-rpi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(local (defun lw-rpi-countdown (index)
 (declare (xargs :measure (nfix index)))
 (if (zp index) nil (lw-rpi-countdown (- index 1)))))

(defthm lw-ray-power-index-uniform
 (implies (and (consp points) (lw-ray-annulus-pointsp points 1 2)
               (equal (lw-ray-row-last points) (car points))
               (natp degree) (natp index) (<= index degree)
               (lw-ray-path-step-check points (lw-ray-power-step-budget degree)))
  (equal (lw-ray-polygon-index (lw-ray-power-points points index))
         (* index (lw-ray-polygon-index points))))
 :hints (("Goal" :induct (lw-rpi-countdown index)
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-rpi-countdown) lw-ray-power-zero-index lw-ray-polygon-index-integer lw-rpi-left-commutes lw-rpi-left-distributes lw-rpi-fold-constants lw-rpi-times-negative lw-rpi-negative-times lw-rpi-zero-times lw-rpi-minus-one lw-rpi-double-negative lw-rpi-add-cancel lw-rpi-double lw-rpi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
         (and stable-under-simplificationp
          '(:use (lw-rpi-index-step)
            :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-power-zero-index lw-ray-polygon-index-integer lw-rpi-left-commutes lw-rpi-left-distributes lw-rpi-fold-constants lw-rpi-times-negative lw-rpi-negative-times lw-rpi-zero-times lw-rpi-minus-one lw-rpi-double-negative lw-rpi-add-cancel lw-rpi-double lw-rpi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-ray-power-index-at-computed-step
 (implies (and (consp points) (lw-ray-annulus-pointsp points 1 2)
               (equal (lw-ray-row-last points) (car points)) (natp degree)
               (lw-ray-path-step-check points (lw-ray-power-step-budget degree)))
  (equal (lw-ray-polygon-index (lw-ray-power-points points degree))
         (* degree (lw-ray-polygon-index points))))
 :hints (("Goal" :use ((:instance lw-ray-power-index-uniform (index degree)))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-rpi-left-commutes lw-rpi-left-distributes lw-rpi-fold-constants lw-rpi-times-negative lw-rpi-negative-times lw-rpi-zero-times lw-rpi-minus-one lw-rpi-double-negative lw-rpi-add-cancel lw-rpi-double lw-rpi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

