(in-package "ACL2")

(include-book "polynomial-accurate-paths")

(local (defthm lw-pai-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pai-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pai-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pai-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pai-times-negative (a b) (b a)))
                 :in-theory (disable lw-pai-times-negative)))))

(local (defthm lw-pai-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pai-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pai-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pai-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pai-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pai-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pai-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-pai-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pai-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pai-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-pai-left-commutes)))))

(local (defthm lw-pai-product-rational
 (implies (and (rationalp a) (rationalp b)) (rationalp (* a b)))
 :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-pai-sum-rational
 (implies (and (rationalp a) (rationalp b)) (rationalp (+ a b)))
 :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-pai-inverse-rational
 (implies (rationalp a) (rationalp (/ a))) :rule-classes (:rewrite :type-prescription)))

(defun lw-polynomial-square-accurate-step (coefficients coarse tolerance)
 (let* ((target (lw-polynomial-factor-mesh-step (lw-polynomial-square-accurate-roots coefficients coarse tolerance) (lw-polynomial-leading (lw-polynomial-trim coefficients)))) (budget (lw-polynomial-square-factor-request coefficients coarse tolerance)) (denominator (+ 1 (lw-polynomial-factor-lipschitz (lw-polynomial-square-accurate-roots coefficients coarse tolerance) (lw-polynomial-leading (lw-polynomial-trim coefficients)))))
        (candidate (if (equal denominator 0) 0 (* budget (/ denominator)))))
  (if (< candidate target) candidate target)))

(local (defthm lw-pai-common-step
 (implies (and (rationalp target) (< 0 target) (rationalp budget) (< 0 budget)
               (rationalp gain) (<= 0 gain))
  (let* ((candidate (* budget (/ (+ 1 gain))))
         (step (if (< candidate target) candidate target)))
   (and (rationalp step) (< 0 step) (<= step target) (<= step budget)
        (<= (* gain step) budget))))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance lw-reciprocal-positive (value (+ 1 gain)))
        (:instance lw-pai-positive-product (a budget) (b (/ (+ 1 gain))))
        (:instance lw-pai-inverse-factor (divisor (+ 1 gain)) (coefficient budget)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-pai-product-rational lw-pai-sum-rational lw-pai-inverse-rational lw-pai-left-commutes lw-pai-left-distributes lw-pai-fold-constants lw-pai-times-negative lw-pai-negative-times lw-pai-zero-times lw-pai-minus-one lw-pai-double-negative lw-pai-add-cancel lw-pai-double lw-pai-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :nonlinearp t))))

(defthm lw-polynomial-square-accurate-step-data
 (implies (and (rationalp tolerance) (< 0 tolerance) (lw-complex-coefficientsp coefficients) (posp coarse)
               (lw-polynomial-square-boundary-check coefficients (cons -1 -1) 2 coarse))
  (and (rationalp (lw-polynomial-square-accurate-step coefficients coarse tolerance)) (< 0 (lw-polynomial-square-accurate-step coefficients coarse tolerance)) (<= (lw-polynomial-square-accurate-step coefficients coarse tolerance) (lw-polynomial-factor-mesh-step (lw-polynomial-square-accurate-roots coefficients coarse tolerance) (lw-polynomial-leading (lw-polynomial-trim coefficients))))
       (<= (* (lw-polynomial-factor-lipschitz (lw-polynomial-square-accurate-roots coefficients coarse tolerance) (lw-polynomial-leading (lw-polynomial-trim coefficients))) (lw-polynomial-square-accurate-step coefficients coarse tolerance)) (lw-polynomial-square-factor-request coefficients coarse tolerance))))
 :hints (("Goal"
  :use ((:instance lw-polynomial-square-factor-request-data (count coarse))
        (:instance lw-polynomial-square-accurate-data (count coarse))
        (:instance lw-polynomial-square-accurate-away (count coarse))
        (:instance lw-polynomial-factor-mesh-step-data (roots (lw-polynomial-square-accurate-roots coefficients coarse tolerance)) (leading (lw-polynomial-leading (lw-polynomial-trim coefficients))))
        (:instance lw-polynomial-factor-lipschitz-data (roots (lw-polynomial-square-accurate-roots coefficients coarse tolerance)) (leading (lw-polynomial-leading (lw-polynomial-trim coefficients))))
        (:instance lw-pai-common-step (target (lw-polynomial-factor-mesh-step (lw-polynomial-square-accurate-roots coefficients coarse tolerance) (lw-polynomial-leading (lw-polynomial-trim coefficients)))) (budget (lw-polynomial-square-factor-request coefficients coarse tolerance)) (gain (lw-polynomial-factor-lipschitz (lw-polynomial-square-accurate-roots coefficients coarse tolerance) (lw-polynomial-leading (lw-polynomial-trim coefficients))))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-square-accurate-step lw-pai-left-commutes lw-pai-left-distributes lw-pai-fold-constants lw-pai-times-negative lw-pai-negative-times lw-pai-zero-times lw-pai-minus-one lw-pai-double-negative lw-pai-add-cancel lw-pai-double lw-pai-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defun lw-polynomial-square-accurate-refinement-factor (coefficients coarse tolerance)
 (* 4 (lw-unit-square-mesh-factor (lw-polynomial-square-accurate-step coefficients coarse tolerance))))

(defun lw-polynomial-square-accurate-refined-count (coefficients coarse tolerance)
 (* coarse (lw-polynomial-square-accurate-refinement-factor coefficients coarse tolerance)))

(local (defthm lw-pai-division-enlarge
 (implies (and (rationalp numerator) (<= 0 numerator)
               (rationalp divisor) (< 0 divisor) (rationalp larger) (<= divisor larger)
               (rationalp bound) (<= 0 bound)
               (<= (* numerator (/ divisor)) bound))
  (<= (* numerator (/ larger)) bound))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance lw-pai-multiply-order (a (* numerator (/ divisor))) (b bound) (factor divisor))
        (:instance lw-pai-inverse-factor (coefficient numerator))
        (:instance lw-pai-multiply-order (a divisor) (b larger) (factor bound))
        (:instance lw-positive-division-bound (divisor larger)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-pai-product-rational lw-pai-inverse-rational lw-pai-left-commutes lw-pai-left-distributes lw-pai-fold-constants lw-pai-times-negative lw-pai-negative-times lw-pai-zero-times lw-pai-minus-one lw-pai-double-negative lw-pai-add-cancel lw-pai-double lw-pai-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))))

(local (defthm lw-pai-refine-mesh
 (implies (and (posp coarse) (posp factor) (rationalp step) (<= 0 step) (<= (* 2 (/ factor)) step))
  (and (posp (* coarse factor)) (<= (* 2 (/ (* coarse factor))) step)))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance lw-pai-multiply-order (a 1) (b coarse))
        (:instance lw-pai-division-enlarge (numerator 2) (divisor factor) (larger (* coarse factor)) (bound step)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-pai-product-rational lw-pai-left-commutes lw-pai-left-distributes lw-pai-fold-constants lw-pai-times-negative lw-pai-negative-times lw-pai-zero-times lw-pai-minus-one lw-pai-double-negative lw-pai-add-cancel lw-pai-double lw-pai-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :nonlinearp t))))

(defthm lw-polynomial-square-accurate-refined-count-data
 (implies (and (rationalp tolerance) (< 0 tolerance) (lw-complex-coefficientsp coefficients) (posp coarse)
               (lw-polynomial-square-boundary-check coefficients (cons -1 -1) 2 coarse))
  (and (posp (lw-polynomial-square-accurate-refinement-factor coefficients coarse tolerance)) (posp (lw-polynomial-square-accurate-refined-count coefficients coarse tolerance)) (<= (* 2 (/ (lw-polynomial-square-accurate-refined-count coefficients coarse tolerance))) (lw-polynomial-square-accurate-step coefficients coarse tolerance))))
 :hints (("Goal"
  :use (lw-polynomial-square-accurate-step-data
        (:instance lw-unit-square-mesh-factor-data (error (lw-polynomial-square-accurate-step coefficients coarse tolerance)))
        (:instance lw-pai-refine-mesh (factor (* 4 (lw-unit-square-mesh-factor (lw-polynomial-square-accurate-step coefficients coarse tolerance)))) (step (lw-polynomial-square-accurate-step coefficients coarse tolerance))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-square-accurate-refinement-factor lw-polynomial-square-accurate-refined-count lw-pai-left-commutes lw-pai-left-distributes lw-pai-fold-constants lw-pai-times-negative lw-pai-negative-times lw-pai-zero-times lw-pai-minus-one lw-pai-double-negative lw-pai-add-cancel lw-pai-double lw-pai-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-polynomial-square-accurate-homotopy
 (implies (and (rationalp tolerance) (< 0 tolerance) (lw-complex-coefficientsp coefficients) (posp coarse)
               (lw-polynomial-square-boundary-check coefficients (cons -1 -1) 2 coarse)
               (posp fine) (<= (* 2 (/ fine)) (lw-polynomial-square-accurate-step coefficients coarse tolerance)))
  (equal (lw-ray-polygon-index (lw-polynomial-path-values coefficients (lw-unit-square-boundary fine))) (lw-ray-polygon-index (lw-polynomial-factor-path-values (lw-polynomial-square-accurate-roots coefficients coarse tolerance) (lw-polynomial-leading (lw-polynomial-trim coefficients)) (lw-unit-square-boundary fine)))))
 :hints (("Goal"
  :use (lw-polynomial-square-accurate-step-data
        (:instance lw-polynomial-square-factor-request-data (count coarse))
        (:instance lw-polynomial-square-accurate-data (count coarse))
        (:instance lw-polynomial-square-accurate-away (count coarse))
        (:instance lw-polynomial-factor-lipschitz-data (roots (lw-polynomial-square-accurate-roots coefficients coarse tolerance)) (leading (lw-polynomial-leading (lw-polynomial-trim coefficients))))
        (:instance lw-unit-square-boundary-data (count fine))
        (:instance lw-unit-square-boundary-points (count fine))
        (:instance lw-unit-square-boundary-step (count fine))
        (:instance lw-polynomial-factor-path-data (roots (lw-polynomial-square-accurate-roots coefficients coarse tolerance)) (leading (lw-polynomial-leading (lw-polynomial-trim coefficients))) (points (lw-unit-square-boundary fine)))
        (:instance lw-polynomial-factor-path-closed (roots (lw-polynomial-square-accurate-roots coefficients coarse tolerance)) (leading (lw-polynomial-leading (lw-polynomial-trim coefficients))) (points (lw-unit-square-boundary fine)))
        (:instance lw-polynomial-factor-path-step (roots (lw-polynomial-square-accurate-roots coefficients coarse tolerance)) (leading (lw-polynomial-leading (lw-polynomial-trim coefficients))) (points (lw-unit-square-boundary fine)) (error (* 2 (/ fine))))
        (:instance lw-pai-multiply-order (a (* 2 (/ fine))) (b (lw-polynomial-square-accurate-step coefficients coarse tolerance)) (factor (lw-polynomial-factor-lipschitz (lw-polynomial-square-accurate-roots coefficients coarse tolerance) (lw-polynomial-leading (lw-polynomial-trim coefficients)))))
        (:instance lw-ray-path-step-enlarge (points (lw-polynomial-factor-path-values (lw-polynomial-square-accurate-roots coefficients coarse tolerance) (lw-polynomial-leading (lw-polynomial-trim coefficients)) (lw-unit-square-boundary fine))) (delta (* (lw-polynomial-factor-lipschitz (lw-polynomial-square-accurate-roots coefficients coarse tolerance) (lw-polynomial-leading (lw-polynomial-trim coefficients))) (* 2 (/ fine)))) (larger (lw-polynomial-square-factor-request coefficients coarse tolerance)))
        (:instance lw-ray-closed-path-step (points (lw-polynomial-factor-path-values (lw-polynomial-square-accurate-roots coefficients coarse tolerance) (lw-polynomial-leading (lw-polynomial-trim coefficients)) (lw-unit-square-boundary fine))) (delta (lw-polynomial-square-factor-request coefficients coarse tolerance)))
        (:instance lw-ray-close-polygon-data (points (lw-polynomial-factor-path-values (lw-polynomial-square-accurate-roots coefficients coarse tolerance) (lw-polynomial-leading (lw-polynomial-trim coefficients)) (lw-unit-square-boundary fine))))
        (:instance lw-ray-step-self-near (points (lw-ray-close-polygon (lw-polynomial-factor-path-values (lw-polynomial-square-accurate-roots coefficients coarse tolerance) (lw-polynomial-leading (lw-polynomial-trim coefficients)) (lw-unit-square-boundary fine)))) (delta (lw-polynomial-square-factor-request coefficients coarse tolerance)))
        (:instance lw-polynomial-square-accurate-path-avoids (count coarse) (points (lw-unit-square-boundary fine)))
        (:instance lw-polynomial-square-accurate-path-comparison (count coarse) (points (lw-unit-square-boundary fine)))
        (:instance lw-ray-polygon-pointwise-perturbation (bottom (lw-polynomial-factor-path-values (lw-polynomial-square-accurate-roots coefficients coarse tolerance) (lw-polynomial-leading (lw-polynomial-trim coefficients)) (lw-unit-square-boundary fine))) (top (lw-polynomial-path-values coefficients (lw-unit-square-boundary fine))) (beta (lw-polynomial-square-factor-request coefficients coarse tolerance)) (delta (lw-polynomial-square-factor-request coefficients coarse tolerance))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-pai-product-rational lw-pai-inverse-rational lw-pai-left-commutes lw-pai-left-distributes lw-pai-fold-constants lw-pai-times-negative lw-pai-negative-times lw-pai-zero-times lw-pai-minus-one lw-pai-double-negative lw-pai-add-cancel lw-pai-double lw-pai-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-polynomial-checked-square-accurate-count
 (implies (and (rationalp tolerance) (< 0 tolerance) (lw-complex-coefficientsp coefficients) (posp coarse)
               (lw-polynomial-square-boundary-check coefficients (cons -1 -1) 2 coarse))
  (equal (lw-ray-grid-boundary-index (lw-polynomial-grid coefficients (cons -1 -1) 2 coarse))
         (lw-unit-square-factor-count (lw-polynomial-square-accurate-roots coefficients coarse tolerance))))
 :hints (("Goal"
  :use (lw-polynomial-square-accurate-step-data lw-polynomial-square-accurate-refined-count-data
        (:instance lw-polynomial-square-accurate-data (count coarse))
        (:instance lw-polynomial-square-accurate-away (count coarse))
        (:instance lw-polynomial-factor-square-index (roots (lw-polynomial-square-accurate-roots coefficients coarse tolerance)) (leading (lw-polynomial-leading (lw-polynomial-trim coefficients))) (count (lw-polynomial-square-accurate-refined-count coefficients coarse tolerance)))
        (:instance lw-polynomial-square-accurate-homotopy (fine (lw-polynomial-square-accurate-refined-count coefficients coarse tolerance)))
        (:instance lw-polynomial-square-refinement-index (anchor (cons -1 -1)) (side 2) (factor (lw-polynomial-square-accurate-refinement-factor coefficients coarse tolerance)))
        (:instance lw-polynomial-grid-boundary-as-polygon (anchor (cons -1 -1)) (side 2) (count (lw-polynomial-square-accurate-refined-count coefficients coarse tolerance)))
        (:instance lw-unit-square-boundary-canonical (count (lw-polynomial-square-accurate-refined-count coefficients coarse tolerance))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-square-accurate-refined-count (:executable-counterpart lw-complexp) lw-pai-left-commutes lw-pai-left-distributes lw-pai-fold-constants lw-pai-times-negative lw-pai-negative-times lw-pai-zero-times lw-pai-minus-one lw-pai-double-negative lw-pai-add-cancel lw-pai-double lw-pai-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
