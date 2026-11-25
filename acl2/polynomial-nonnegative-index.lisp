(in-package "ACL2")

(include-book "polynomial-boundary-factor-paths")

; The coarse polynomial index is a nonnegative count of generated rational factors.

(local (defthm lw-pni-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pni-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pni-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pni-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pni-times-negative (a b) (b a)))
                 :in-theory (disable lw-pni-times-negative)))))

(local (defthm lw-pni-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pni-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pni-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pni-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pni-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pni-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pni-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-pni-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pni-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pni-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-pni-left-commutes)))))
(local (defthm lw-pni-product-rational
 (implies (and (rationalp a) (rationalp b)) (rationalp (* a b)))
 :rule-classes (:rewrite :type-prescription)))
(local (defthm lw-pni-sum-rational
 (implies (and (rationalp a) (rationalp b)) (rationalp (+ a b)))
 :rule-classes (:rewrite :type-prescription)))
(local (defthm lw-pni-inverse-rational
 (implies (rationalp a) (rationalp (/ a))) :rule-classes (:rewrite :type-prescription)))

(defun lw-polynomial-square-comparison-step (coefficients coarse)
 (let* ((target (lw-polynomial-factor-mesh-step (lw-polynomial-square-factor-roots coefficients coarse) (lw-polynomial-leading (lw-polynomial-trim coefficients)))) (budget (lw-polynomial-square-factor-error coefficients coarse)) (denominator (+ 1 (lw-polynomial-factor-lipschitz (lw-polynomial-square-factor-roots coefficients coarse) (lw-polynomial-leading (lw-polynomial-trim coefficients)))))
        (candidate (if (equal denominator 0) 0 (* budget (/ denominator)))))
  (if (< candidate target) candidate target)))

(local (defthm lw-pni-common-step
 (implies (and (rationalp target) (< 0 target) (rationalp budget) (< 0 budget)
               (rationalp gain) (<= 0 gain))
  (let* ((candidate (* budget (/ (+ 1 gain))))
         (step (if (< candidate target) candidate target)))
   (and (rationalp step) (< 0 step) (<= step target) (<= step budget)
        (<= (* gain step) budget))))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance lw-reciprocal-positive (value (+ 1 gain)))
        (:instance lw-pni-positive-product (a budget) (b (/ (+ 1 gain))))
        (:instance lw-pni-inverse-factor (divisor (+ 1 gain)) (coefficient budget)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-pni-product-rational lw-pni-sum-rational lw-pni-inverse-rational lw-pni-left-commutes lw-pni-left-distributes lw-pni-fold-constants lw-pni-times-negative lw-pni-negative-times lw-pni-zero-times lw-pni-minus-one lw-pni-double-negative lw-pni-add-cancel lw-pni-double lw-pni-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :nonlinearp t))))


(defthm lw-polynomial-square-comparison-step-data
 (implies (and (lw-complex-coefficientsp coefficients) (posp coarse)
               (lw-polynomial-square-boundary-check coefficients (cons -1 -1) 2 coarse))
  (and (rationalp (lw-polynomial-square-comparison-step coefficients coarse)) (< 0 (lw-polynomial-square-comparison-step coefficients coarse)) (<= (lw-polynomial-square-comparison-step coefficients coarse) (lw-polynomial-factor-mesh-step (lw-polynomial-square-factor-roots coefficients coarse) (lw-polynomial-leading (lw-polynomial-trim coefficients))))
       (<= (* (lw-polynomial-factor-lipschitz (lw-polynomial-square-factor-roots coefficients coarse) (lw-polynomial-leading (lw-polynomial-trim coefficients))) (lw-polynomial-square-comparison-step coefficients coarse)) (lw-polynomial-square-factor-error coefficients coarse))))
 :hints (("Goal"
  :use ((:instance lw-polynomial-square-factor-error-data (count coarse))
        (:instance lw-polynomial-square-factor-data (count coarse))
        (:instance lw-polynomial-square-factors-away (count coarse))
        (:instance lw-polynomial-factor-mesh-step-data (roots (lw-polynomial-square-factor-roots coefficients coarse)) (leading (lw-polynomial-leading (lw-polynomial-trim coefficients))))
        (:instance lw-polynomial-factor-lipschitz-data (roots (lw-polynomial-square-factor-roots coefficients coarse)) (leading (lw-polynomial-leading (lw-polynomial-trim coefficients))))
        (:instance lw-pni-common-step (target (lw-polynomial-factor-mesh-step (lw-polynomial-square-factor-roots coefficients coarse) (lw-polynomial-leading (lw-polynomial-trim coefficients)))) (budget (lw-polynomial-square-factor-error coefficients coarse)) (gain (lw-polynomial-factor-lipschitz (lw-polynomial-square-factor-roots coefficients coarse) (lw-polynomial-leading (lw-polynomial-trim coefficients))))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-square-comparison-step lw-pni-left-commutes lw-pni-left-distributes lw-pni-fold-constants lw-pni-times-negative lw-pni-negative-times lw-pni-zero-times lw-pni-minus-one lw-pni-double-negative lw-pni-add-cancel lw-pni-double lw-pni-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defun lw-polynomial-square-refinement-factor (coefficients coarse)
 (* 4 (lw-unit-square-mesh-factor (lw-polynomial-square-comparison-step coefficients coarse))))
(defun lw-polynomial-square-refined-count (coefficients coarse)
 (* coarse (lw-polynomial-square-refinement-factor coefficients coarse)))

(local (defthm lw-pni-division-enlarge
 (implies (and (rationalp numerator) (<= 0 numerator)
               (rationalp divisor) (< 0 divisor) (rationalp larger) (<= divisor larger)
               (rationalp bound) (<= 0 bound)
               (<= (* numerator (/ divisor)) bound))
  (<= (* numerator (/ larger)) bound))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance lw-pni-multiply-order (a (* numerator (/ divisor))) (b bound) (factor divisor))
        (:instance lw-pni-inverse-factor (coefficient numerator))
        (:instance lw-pni-multiply-order (a divisor) (b larger) (factor bound))
        (:instance lw-positive-division-bound (divisor larger)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-pni-product-rational lw-pni-inverse-rational lw-pni-left-commutes lw-pni-left-distributes lw-pni-fold-constants lw-pni-times-negative lw-pni-negative-times lw-pni-zero-times lw-pni-minus-one lw-pni-double-negative lw-pni-add-cancel lw-pni-double lw-pni-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))))


(local (defthm lw-pni-refine-mesh
 (implies (and (posp coarse) (posp factor) (rationalp step) (<= 0 step) (<= (* 2 (/ factor)) step))
  (and (posp (* coarse factor)) (<= (* 2 (/ (* coarse factor))) step)))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance lw-pni-multiply-order (a 1) (b coarse))
        (:instance lw-pni-division-enlarge (numerator 2) (divisor factor) (larger (* coarse factor)) (bound step)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-pni-product-rational lw-pni-left-commutes lw-pni-left-distributes lw-pni-fold-constants lw-pni-times-negative lw-pni-negative-times lw-pni-zero-times lw-pni-minus-one lw-pni-double-negative lw-pni-add-cancel lw-pni-double lw-pni-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :nonlinearp t))))

(defthm lw-polynomial-square-refined-count-data
 (implies (and (lw-complex-coefficientsp coefficients) (posp coarse)
               (lw-polynomial-square-boundary-check coefficients (cons -1 -1) 2 coarse))
  (and (posp (lw-polynomial-square-refinement-factor coefficients coarse)) (posp (lw-polynomial-square-refined-count coefficients coarse)) (<= (* 2 (/ (lw-polynomial-square-refined-count coefficients coarse))) (lw-polynomial-square-comparison-step coefficients coarse))))
 :hints (("Goal"
  :use (lw-polynomial-square-comparison-step-data
        (:instance lw-unit-square-mesh-factor-data (error (lw-polynomial-square-comparison-step coefficients coarse)))
        (:instance lw-pni-refine-mesh (factor (* 4 (lw-unit-square-mesh-factor (lw-polynomial-square-comparison-step coefficients coarse)))) (step (lw-polynomial-square-comparison-step coefficients coarse))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-square-refinement-factor lw-polynomial-square-refined-count lw-pni-left-commutes lw-pni-left-distributes lw-pni-fold-constants lw-pni-times-negative lw-pni-negative-times lw-pni-zero-times lw-pni-minus-one lw-pni-double-negative lw-pni-add-cancel lw-pni-double lw-pni-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-polynomial-square-factor-homotopy
 (implies (and (lw-complex-coefficientsp coefficients) (posp coarse)
               (lw-polynomial-square-boundary-check coefficients (cons -1 -1) 2 coarse)
               (posp fine) (<= (* 2 (/ fine)) (lw-polynomial-square-comparison-step coefficients coarse)))
  (equal (lw-ray-polygon-index (lw-polynomial-path-values coefficients (lw-unit-square-boundary fine))) (lw-ray-polygon-index (lw-polynomial-factor-path-values (lw-polynomial-square-factor-roots coefficients coarse) (lw-polynomial-leading (lw-polynomial-trim coefficients)) (lw-unit-square-boundary fine)))))
 :hints (("Goal"
  :use (lw-polynomial-square-comparison-step-data
        (:instance lw-polynomial-square-factor-error-data (count coarse))
        (:instance lw-polynomial-square-factor-data (count coarse))
        (:instance lw-polynomial-square-factors-away (count coarse))
        (:instance lw-polynomial-factor-lipschitz-data (roots (lw-polynomial-square-factor-roots coefficients coarse)) (leading (lw-polynomial-leading (lw-polynomial-trim coefficients))))
        (:instance lw-unit-square-boundary-data (count fine))
        (:instance lw-unit-square-boundary-points (count fine))
        (:instance lw-unit-square-boundary-step (count fine))
        (:instance lw-polynomial-factor-path-data (roots (lw-polynomial-square-factor-roots coefficients coarse)) (leading (lw-polynomial-leading (lw-polynomial-trim coefficients))) (points (lw-unit-square-boundary fine)))
        (:instance lw-polynomial-factor-path-closed (roots (lw-polynomial-square-factor-roots coefficients coarse)) (leading (lw-polynomial-leading (lw-polynomial-trim coefficients))) (points (lw-unit-square-boundary fine)))
        (:instance lw-polynomial-factor-path-step (roots (lw-polynomial-square-factor-roots coefficients coarse)) (leading (lw-polynomial-leading (lw-polynomial-trim coefficients))) (points (lw-unit-square-boundary fine)) (error (* 2 (/ fine))))
        (:instance lw-pni-multiply-order (a (* 2 (/ fine))) (b (lw-polynomial-square-comparison-step coefficients coarse)) (factor (lw-polynomial-factor-lipschitz (lw-polynomial-square-factor-roots coefficients coarse) (lw-polynomial-leading (lw-polynomial-trim coefficients)))))
        (:instance lw-ray-path-step-enlarge (points (lw-polynomial-factor-path-values (lw-polynomial-square-factor-roots coefficients coarse) (lw-polynomial-leading (lw-polynomial-trim coefficients)) (lw-unit-square-boundary fine))) (delta (* (lw-polynomial-factor-lipschitz (lw-polynomial-square-factor-roots coefficients coarse) (lw-polynomial-leading (lw-polynomial-trim coefficients))) (* 2 (/ fine)))) (larger (lw-polynomial-square-factor-error coefficients coarse)))
        (:instance lw-ray-closed-path-step (points (lw-polynomial-factor-path-values (lw-polynomial-square-factor-roots coefficients coarse) (lw-polynomial-leading (lw-polynomial-trim coefficients)) (lw-unit-square-boundary fine))) (delta (lw-polynomial-square-factor-error coefficients coarse)))
        (:instance lw-ray-close-polygon-data (points (lw-polynomial-factor-path-values (lw-polynomial-square-factor-roots coefficients coarse) (lw-polynomial-leading (lw-polynomial-trim coefficients)) (lw-unit-square-boundary fine))))
        (:instance lw-ray-step-self-near (points (lw-ray-close-polygon (lw-polynomial-factor-path-values (lw-polynomial-square-factor-roots coefficients coarse) (lw-polynomial-leading (lw-polynomial-trim coefficients)) (lw-unit-square-boundary fine)))) (delta (lw-polynomial-square-factor-error coefficients coarse)))
        (:instance lw-polynomial-square-factor-path-avoids (count coarse) (points (lw-unit-square-boundary fine)))
        (:instance lw-polynomial-square-factor-path-comparison (count coarse) (points (lw-unit-square-boundary fine)))
        (:instance lw-ray-polygon-pointwise-perturbation (bottom (lw-polynomial-factor-path-values (lw-polynomial-square-factor-roots coefficients coarse) (lw-polynomial-leading (lw-polynomial-trim coefficients)) (lw-unit-square-boundary fine))) (top (lw-polynomial-path-values coefficients (lw-unit-square-boundary fine))) (beta (lw-polynomial-square-factor-error coefficients coarse)) (delta (lw-polynomial-square-factor-error coefficients coarse))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-pni-product-rational lw-pni-inverse-rational lw-pni-left-commutes lw-pni-left-distributes lw-pni-fold-constants lw-pni-times-negative lw-pni-negative-times lw-pni-zero-times lw-pni-minus-one lw-pni-double-negative lw-pni-add-cancel lw-pni-double lw-pni-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-polynomial-checked-square-factor-count
 (implies (and (lw-complex-coefficientsp coefficients) (posp coarse)
               (lw-polynomial-square-boundary-check coefficients (cons -1 -1) 2 coarse))
  (equal (lw-ray-grid-boundary-index (lw-polynomial-grid coefficients (cons -1 -1) 2 coarse))
         (lw-unit-square-factor-count (lw-polynomial-square-factor-roots coefficients coarse))))
 :hints (("Goal"
  :use (lw-polynomial-square-comparison-step-data lw-polynomial-square-refined-count-data
        (:instance lw-polynomial-square-factor-data (count coarse))
        (:instance lw-polynomial-square-factors-away (count coarse))
        (:instance lw-polynomial-factor-square-index (roots (lw-polynomial-square-factor-roots coefficients coarse)) (leading (lw-polynomial-leading (lw-polynomial-trim coefficients))) (count (lw-polynomial-square-refined-count coefficients coarse)))
        (:instance lw-polynomial-square-factor-homotopy (fine (lw-polynomial-square-refined-count coefficients coarse)))
        (:instance lw-polynomial-square-refinement-index (anchor (cons -1 -1)) (side 2) (factor (lw-polynomial-square-refinement-factor coefficients coarse)))
        (:instance lw-polynomial-grid-boundary-as-polygon (anchor (cons -1 -1)) (side 2) (count (lw-polynomial-square-refined-count coefficients coarse)))
        (:instance lw-unit-square-boundary-canonical (count (lw-polynomial-square-refined-count coefficients coarse))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-square-refined-count (:executable-counterpart lw-complexp) lw-pni-left-commutes lw-pni-left-distributes lw-pni-fold-constants lw-pni-times-negative lw-pni-negative-times lw-pni-zero-times lw-pni-minus-one lw-pni-double-negative lw-pni-add-cancel lw-pni-double lw-pni-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-polynomial-checked-square-index-nonnegative
 (implies (and (lw-complex-coefficientsp coefficients) (posp coarse)
               (lw-polynomial-square-boundary-check coefficients (cons -1 -1) 2 coarse))
  (let ((index (lw-ray-grid-boundary-index (lw-polynomial-grid coefficients (cons -1 -1) 2 coarse))))
   (and (<= 0 index) (<= index (len (lw-polynomial-without-leading (lw-polynomial-trim coefficients)))))))
 :hints (("Goal"
  :use (lw-polynomial-checked-square-factor-count
        (:instance lw-polynomial-square-factor-data (count coarse))
        (:instance lw-unit-square-factor-count-data (roots (lw-polynomial-square-factor-roots coefficients coarse))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-pni-left-commutes lw-pni-left-distributes lw-pni-fold-constants lw-pni-times-negative lw-pni-negative-times lw-pni-zero-times lw-pni-minus-one lw-pni-double-negative lw-pni-add-cancel lw-pni-double lw-pni-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
