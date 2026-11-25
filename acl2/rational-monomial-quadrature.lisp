(in-package "ACL2")

(include-book "rational-power-secant")

; Left rectangle sums for monomials on the unit interval have mesh error.

(local (defthm lw-rmq-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-rmq-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-rmq-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-rmq-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-rmq-times-negative (a b) (b a)))
                 :in-theory (disable lw-rmq-times-negative)))))

(local (defthm lw-rmq-zero-times (equal (* 0 a) 0)))

(local (defthm lw-rmq-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-rmq-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-rmq-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-rmq-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-rmq-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-rmq-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-rmq-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-rmq-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-rmq-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-rmq-left-commutes)))))

(local
 (defthm lw-rmq-reciprocal-positive
   (implies (and (rationalp value) (< 0 value)) (< 0 (/ value)))
   :hints (("Goal" :use ((:instance inverse-of-* (x value))) :nonlinearp t))
   :rule-classes nil))

(defthm lw-rational-monomial-cell
  (implies (and (rationalp left) (rationalp right) (<= 0 left) (<= left right) (natp degree))
           (let* ((order (+ 1 degree))
                  (primitive (/ (- (lw-rational-power right order) (lw-rational-power left order)) order)))
             (and (<= (* (- right left) (lw-rational-power left degree)) primitive)
                  (<= primitive (* (- right left) (lw-rational-power right degree))))))
  :hints (("Goal"
           :use ((:instance lw-rational-power-secant-identity (degree (+ 1 degree)))
                 (:instance lw-rational-power-secant-bounds (degree (+ 1 degree)))
                 (:instance lw-rmq-reciprocal-positive (value (+ 1 degree)))
                 (:instance lw-rmq-inverse-factor (divisor (+ 1 degree))
                   (coefficient (* (- right left) (lw-rational-power left degree))))
                 (:instance lw-rmq-inverse-factor (divisor (+ 1 degree))
                   (coefficient (* (- right left) (lw-rational-power right degree))))
                 (:instance lw-rmq-multiply-order
                   (a (* (+ 1 degree) (lw-rational-power left degree)))
                   (b (lw-rational-power-secant left right (+ 1 degree))) (factor (- right left)))
                 (:instance lw-rmq-multiply-order
                   (a (lw-rational-power-secant left right (+ 1 degree)))
                   (b (* (+ 1 degree) (lw-rational-power right degree))) (factor (- right left)))
                 (:instance lw-rmq-multiply-order
                   (a (* (- right left) (+ 1 degree) (lw-rational-power left degree)))
                   (b (- (lw-rational-power right (+ 1 degree)) (lw-rational-power left (+ 1 degree))))
                   (factor (/ (+ 1 degree))))
                 (:instance lw-rmq-multiply-order
                   (a (- (lw-rational-power right (+ 1 degree)) (lw-rational-power left (+ 1 degree))))
                   (b (* (- right left) (+ 1 degree) (lw-rational-power right degree)))
                   (factor (/ (+ 1 degree)))))
           :in-theory (union-theories
            '(fold-consts-in-+
              lw-rational-power-rational lw-rational-power-secant-rational
              lw-rmq-left-commutes lw-rmq-left-distributes lw-rmq-fold-constants
              lw-rmq-times-negative lw-rmq-negative-times lw-rmq-zero-times
              lw-rmq-minus-one lw-rmq-double-negative lw-rmq-add-cancel lw-rmq-double lw-rmq-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(defun lw-rational-monomial-grid (mesh degree cells)
  (declare (xargs :measure (nfix cells)
                  :hints (("Goal" :in-theory (theory 'ground-zero)))))
  (if (zp cells)
      0
    (+ (* (/ mesh) (lw-rational-power (* (- cells 1) (/ mesh)) degree)) (lw-rational-monomial-grid mesh degree (- cells 1)))))

(local
 (defthm lw-rmq-inverse-type
   (implies (rationalp value) (rationalp (/ value)))
   :hints (("Goal" :in-theory (theory 'ground-zero)))))

(defthm lw-rational-monomial-grid-rational
   (implies (posp mesh) (rationalp (lw-rational-monomial-grid mesh degree cells)))
   :hints (("Goal" :induct (lw-rational-monomial-grid mesh degree cells)
                   :in-theory (union-theories
            '(fold-consts-in-+
              (:induction lw-rational-monomial-grid) lw-rational-monomial-grid lw-rmq-inverse-type lw-rational-power-rational
              lw-rmq-left-commutes lw-rmq-left-distributes lw-rmq-fold-constants
              lw-rmq-times-negative lw-rmq-negative-times lw-rmq-zero-times
              lw-rmq-minus-one lw-rmq-double-negative lw-rmq-add-cancel lw-rmq-double lw-rmq-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                   :do-not '(generalize fertilize)))
   :rule-classes (:type-prescription))

(local
 (defthm lw-rmq-zero-power
   (implies (posp degree) (equal (lw-rational-power 0 degree) 0))
   :hints (("Goal" :expand ((lw-rational-power 0 degree))
                   :in-theory (union-theories
            '(fold-consts-in-+
              lw-rational-power
              lw-rmq-left-commutes lw-rmq-left-distributes lw-rmq-fold-constants
              lw-rmq-times-negative lw-rmq-negative-times lw-rmq-zero-times
              lw-rmq-minus-one lw-rmq-double-negative lw-rmq-add-cancel lw-rmq-double lw-rmq-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                   :do-not-induct t))))

(local
 (defthm lw-rmq-mesh-data
   (implies (and (posp mesh) (posp cells) (<= cells mesh))
            (and (rationalp (* (- cells 1) (/ mesh))) (rationalp (* cells (/ mesh)))
                 (<= 0 (* (- cells 1) (/ mesh))) (<= (* (- cells 1) (/ mesh)) (* cells (/ mesh))) (<= (* cells (/ mesh)) 1)
                 (equal (- (* cells (/ mesh)) (* (- cells 1) (/ mesh))) (/ mesh))))
   :hints (("Goal"
            :use ((:instance lw-rmq-reciprocal-positive (value mesh))
                  (:instance inverse-of-* (x mesh))
                  (:instance lw-rmq-multiply-order (a cells) (b mesh) (factor (/ mesh)))
                  (:instance lw-rmq-multiply-order (a 0) (b (- cells 1)) (factor (/ mesh))))
            :in-theory (union-theories
            '(fold-consts-in-+
              lw-rmq-inverse-type
              lw-rmq-left-commutes lw-rmq-left-distributes lw-rmq-fold-constants
              lw-rmq-times-negative lw-rmq-negative-times lw-rmq-zero-times
              lw-rmq-minus-one lw-rmq-double-negative lw-rmq-add-cancel lw-rmq-double lw-rmq-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-rmq-grid-step
   (implies (and (rationalp lower) (rationalp upper)
                 (rationalp low-power) (rationalp high-power) (rationalp start-power)
                 (rationalp previous) (rationalp step)
                 (<= (* step low-power) (- upper lower))
                 (<= (- upper lower) (* step high-power))
                 (<= previous lower)
                 (<= lower (+ previous (* step (- low-power start-power)))))
            (and (<= (+ previous (* step low-power)) upper)
                 (<= upper (+ previous (* step low-power) (* step (- high-power start-power))))))
   :hints (("Goal"
            :in-theory (union-theories
            '(fold-consts-in-+

              lw-rmq-left-commutes lw-rmq-left-distributes lw-rmq-fold-constants
              lw-rmq-times-negative lw-rmq-negative-times lw-rmq-zero-times
              lw-rmq-minus-one lw-rmq-double-negative lw-rmq-add-cancel lw-rmq-double lw-rmq-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-rmq-grid-bracket
   (implies (and (posp mesh) (natp degree) (natp cells) (<= cells mesh))
            (and (<= (lw-rational-monomial-grid mesh degree cells) (/ (lw-rational-power (* cells (/ mesh)) (+ 1 degree)) (+ 1 degree)))
                 (<= (/ (lw-rational-power (* cells (/ mesh)) (+ 1 degree)) (+ 1 degree)) (+ (lw-rational-monomial-grid mesh degree cells) (* (/ mesh) (- (lw-rational-power (* cells (/ mesh)) degree) (lw-rational-power 0 degree)))))))
   :hints (("Goal"
            :induct (lw-rational-monomial-grid mesh degree cells)
            :in-theory (union-theories
            '(fold-consts-in-+
              (:induction lw-rational-monomial-grid) lw-rational-monomial-grid
              lw-rmq-zero-power lw-rational-monomial-grid-rational lw-rmq-inverse-type lw-rational-power-rational
              lw-rmq-left-commutes lw-rmq-left-distributes lw-rmq-fold-constants
              lw-rmq-times-negative lw-rmq-negative-times lw-rmq-zero-times
              lw-rmq-minus-one lw-rmq-double-negative lw-rmq-add-cancel lw-rmq-double lw-rmq-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not '(generalize fertilize))
           (and stable-under-simplificationp
                '(:use (lw-rmq-mesh-data
                        (:instance lw-rational-monomial-cell (left (* (- cells 1) (/ mesh))) (right (* cells (/ mesh))))
                        (:instance lw-rmq-grid-step
                          (lower (/ (lw-rational-power (* (- cells 1) (/ mesh)) (+ 1 degree)) (+ 1 degree))) (upper (/ (lw-rational-power (* cells (/ mesh)) (+ 1 degree)) (+ 1 degree)))
                          (low-power (lw-rational-power (* (- cells 1) (/ mesh)) degree)) (high-power (lw-rational-power (* cells (/ mesh)) degree))
                          (start-power (lw-rational-power 0 degree)) (previous (lw-rational-monomial-grid mesh degree (- cells 1))) (step (/ mesh))))
                  :do-not-induct t)))
   :rule-classes nil))

(defthm lw-rational-monomial-grid-error
  (implies (and (posp mesh) (natp degree))
           (let ((value (lw-rational-monomial-grid mesh degree mesh)))
             (and (<= value (/ (+ 1 degree)))
                  (<= (- (/ (+ 1 degree)) value) (/ mesh)))))
  :hints (("Goal"
           :use ((:instance lw-rmq-grid-bracket (cells mesh))
                 (:instance inverse-of-* (x mesh))
                 (:instance lw-rational-power-nonnegative (base 0) (exponent degree))
                 (:instance lw-rmq-reciprocal-positive (value mesh))
                 (:instance lw-rmq-multiply-order
                   (a (- 1 (lw-rational-power 0 degree))) (b 1) (factor (/ mesh))))
           :in-theory (union-theories
            '(fold-consts-in-+
              lw-rational-power-one lw-rational-monomial-grid-rational lw-rmq-inverse-type lw-rational-power-rational
              lw-rmq-left-commutes lw-rmq-left-distributes lw-rmq-fold-constants
              lw-rmq-times-negative lw-rmq-negative-times lw-rmq-zero-times
              lw-rmq-minus-one lw-rmq-double-negative lw-rmq-add-cancel lw-rmq-double lw-rmq-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
