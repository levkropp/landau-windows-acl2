(in-package "ACL2")

(include-book "polynomial-outer-mesh")
(include-book "polynomial-root-search")

; One common mesh meets both outer winding and small-cell variation budgets.

(local (defthm lw-pgrm-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pgrm-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pgrm-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pgrm-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pgrm-times-negative (a b) (b a)))
                 :in-theory (disable lw-pgrm-times-negative)))))

(local (defthm lw-pgrm-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pgrm-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pgrm-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pgrm-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pgrm-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pgrm-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pgrm-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-pgrm-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pgrm-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pgrm-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-pgrm-left-commutes)))))
(defun lw-polynomial-outer-coefficients (coefficients)
 (lw-polynomial-rescale coefficients (lw-polynomial-leading-radius coefficients) 0))
(defun lw-polynomial-global-root-factor (coefficients epsilon)
 (+ (lw-unit-square-mesh-factor (lw-polynomial-outer-step coefficients))
    (lw-polynomial-root-count (lw-polynomial-outer-coefficients coefficients) (cons -1 -1) 2 epsilon)))
(defun lw-polynomial-global-root-count (coefficients epsilon)
 (* 4 (lw-polynomial-global-root-factor coefficients epsilon)))
(defun lw-polynomial-global-root-grid (coefficients epsilon)
 (lw-polynomial-grid (lw-polynomial-outer-coefficients coefficients)
                      (cons -1 -1) 2 (lw-polynomial-global-root-count coefficients epsilon)))

(local (defthm lw-pgrm-product-rational
 (implies (and (rationalp a) (rationalp b)) (rationalp (* a b)))
 :rule-classes (:rewrite :type-prescription)))
(local (defthm lw-pgrm-inverse-rational
 (implies (rationalp x) (rationalp (/ x))) :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-pgrm-division-enlarge
 (implies (and (rationalp numerator) (<= 0 numerator)
               (rationalp divisor) (< 0 divisor) (rationalp larger) (<= divisor larger)
               (rationalp bound) (<= 0 bound)
               (<= (* numerator (/ divisor)) bound))
  (<= (* numerator (/ larger)) bound))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance lw-pgrm-multiply-order (a (* numerator (/ divisor))) (b bound) (factor divisor))
        (:instance lw-pgrm-inverse-factor (coefficient numerator))
        (:instance lw-pgrm-multiply-order (a divisor) (b larger) (factor bound))
        (:instance lw-positive-division-bound (divisor larger)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-pgrm-product-rational lw-pgrm-inverse-rational lw-pgrm-left-commutes lw-pgrm-left-distributes lw-pgrm-fold-constants lw-pgrm-times-negative lw-pgrm-negative-times lw-pgrm-zero-times lw-pgrm-minus-one lw-pgrm-double-negative lw-pgrm-add-cancel lw-pgrm-double lw-pgrm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))))

(local (defthm lw-pgrm-mesh-budget
 (implies (and (posp outer-factor) (posp root-count)
               (rationalp step) (<= 0 step)
               (<= (* 2 (/ (* 4 outer-factor))) step)
               (rationalp mass) (<= 0 mass)
               (rationalp epsilon) (< 0 epsilon)
               (<= (* 4 mass (/ root-count)) epsilon))
  (let ((count (* 4 (+ outer-factor root-count))))
   (and (posp (+ outer-factor root-count)) (posp count)
        (<= (* 2 (/ count)) step)
        (<= (* 4 mass (/ count)) epsilon))))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance lw-pgrm-division-enlarge (numerator 2) (divisor (* 4 outer-factor))
          (larger (* 4 (+ outer-factor root-count))) (bound step))
        (:instance lw-pgrm-division-enlarge (numerator (* 4 mass)) (divisor root-count)
          (larger (* 4 (+ outer-factor root-count))) (bound epsilon)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-pgrm-product-rational lw-pgrm-left-commutes lw-pgrm-left-distributes lw-pgrm-fold-constants lw-pgrm-times-negative lw-pgrm-negative-times lw-pgrm-zero-times lw-pgrm-minus-one lw-pgrm-double-negative lw-pgrm-add-cancel lw-pgrm-double lw-pgrm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :nonlinearp t))))

(defthm lw-polynomial-global-root-count-data
 (implies (and (lw-complex-coefficientsp coefficients)
               (not (equal (lw-polynomial-leading coefficients) (cons 0 0)))
               (rationalp epsilon) (< 0 epsilon))
  (and (posp (lw-polynomial-global-root-factor coefficients epsilon))
       (posp (lw-polynomial-global-root-count coefficients epsilon))
       (<= (* 2 (/ (lw-polynomial-global-root-count coefficients epsilon)))
           (lw-polynomial-outer-step coefficients))
       (<= (* 2 (lw-polynomial-grid-step 2 (lw-polynomial-global-root-count coefficients epsilon))
                (lw-polynomial-lipschitz-cap (lw-polynomial-outer-coefficients coefficients)
                  (lw-polynomial-grid-radius (cons -1 -1) 2))) epsilon)))
 :hints (("Goal"
  :use (lw-polynomial-outer-step-data lw-polynomial-leading-radius-data
        (:instance lw-unit-square-mesh-factor-data (error (lw-polynomial-outer-step coefficients)))
        (:instance lw-polynomial-rescale-valid (factor (lw-polynomial-leading-radius coefficients)) (offset 0))
        (:instance lw-polynomial-root-count-data
          (coefficients (lw-polynomial-outer-coefficients coefficients)) (anchor (cons -1 -1)) (side 2))
        (:instance lw-polynomial-lipschitz-cap-data
          (coefficients (lw-polynomial-outer-coefficients coefficients))
          (bound (lw-polynomial-grid-radius (cons -1 -1) 2)))
        (:instance lw-pgrm-mesh-budget
          (outer-factor (lw-unit-square-mesh-factor (lw-polynomial-outer-step coefficients)))
          (root-count (lw-polynomial-root-count (lw-polynomial-outer-coefficients coefficients) (cons -1 -1) 2 epsilon))
          (step (lw-polynomial-outer-step coefficients))
          (mass (lw-polynomial-lipschitz-cap (lw-polynomial-outer-coefficients coefficients)
                  (lw-polynomial-grid-radius (cons -1 -1) 2)))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-global-root-factor lw-polynomial-global-root-count lw-polynomial-outer-coefficients lw-polynomial-grid-step lw-polynomial-grid-radius lw-complex-l1 lw-complexp abs lw-pgrm-left-commutes lw-pgrm-left-distributes lw-pgrm-fold-constants lw-pgrm-times-negative lw-pgrm-negative-times lw-pgrm-zero-times lw-pgrm-minus-one lw-pgrm-double-negative lw-pgrm-add-cancel lw-pgrm-double lw-pgrm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-polynomial-global-root-grid-data
 (implies (and (lw-complex-coefficientsp coefficients)
               (not (equal (lw-polynomial-leading coefficients) (cons 0 0)))
               (rationalp epsilon) (< 0 epsilon))
  (and (lw-ray-gridp (lw-polynomial-global-root-grid coefficients epsilon)
                      (+ 1 (lw-polynomial-global-root-count coefficients epsilon)))
       (equal (len (lw-polynomial-global-root-grid coefficients epsilon))
              (+ 1 (lw-polynomial-global-root-count coefficients epsilon)))
       (lw-ray-grid-near-check (lw-polynomial-global-root-grid coefficients epsilon) epsilon)))
 :hints (("Goal"
  :use (lw-polynomial-global-root-count-data lw-polynomial-leading-radius-data
        (:instance lw-polynomial-rescale-valid (factor (lw-polynomial-leading-radius coefficients)) (offset 0))
        (:instance lw-polynomial-grid-data
          (coefficients (lw-polynomial-outer-coefficients coefficients)) (anchor (cons -1 -1)) (side 2)
          (count (lw-polynomial-global-root-count coefficients epsilon)))
        (:instance lw-polynomial-grid-near
          (coefficients (lw-polynomial-outer-coefficients coefficients)) (anchor (cons -1 -1)) (side 2)
          (count (lw-polynomial-global-root-count coefficients epsilon))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-global-root-grid lw-polynomial-outer-coefficients lw-complexp lw-pgrm-left-commutes lw-pgrm-left-distributes lw-pgrm-fold-constants lw-pgrm-times-negative lw-pgrm-negative-times lw-pgrm-zero-times lw-pgrm-minus-one lw-pgrm-double-negative lw-pgrm-add-cancel lw-pgrm-double lw-pgrm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-polynomial-global-root-grid-index
 (implies (and (lw-complex-coefficientsp coefficients) (consp coefficients) (consp (cdr coefficients))
               (not (equal (lw-polynomial-leading coefficients) (cons 0 0)))
               (rationalp epsilon) (< 0 epsilon))
  (equal (lw-ray-grid-boundary-index (lw-polynomial-global-root-grid coefficients epsilon))
         (len (lw-polynomial-without-leading coefficients))))
 :hints (("Goal"
  :use (lw-polynomial-global-root-count-data lw-polynomial-leading-radius-data
        (:instance lw-polynomial-rescale-valid (factor (lw-polynomial-leading-radius coefficients)) (offset 0))
        (:instance lw-polynomial-outer-boundary-index-at-mesh (factor (lw-polynomial-global-root-factor coefficients epsilon)))
        (:instance lw-unit-square-boundary-canonical (count (lw-polynomial-global-root-count coefficients epsilon)))
        (:instance lw-polynomial-grid-boundary-as-polygon
          (coefficients (lw-polynomial-outer-coefficients coefficients)) (anchor (cons -1 -1)) (side 2)
          (count (lw-polynomial-global-root-count coefficients epsilon))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-global-root-grid lw-polynomial-global-root-count lw-polynomial-outer-coefficients lw-complexp lw-pgrm-left-commutes lw-pgrm-left-distributes lw-pgrm-fold-constants lw-pgrm-times-negative lw-pgrm-negative-times lw-pgrm-zero-times lw-pgrm-minus-one lw-pgrm-double-negative lw-pgrm-add-cancel lw-pgrm-double lw-pgrm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))
