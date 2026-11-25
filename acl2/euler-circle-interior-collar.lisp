(in-package "ACL2")

(include-book "unit-circle-nearby-point")
(include-book "euler-circle-count-requests")
(include-book "polynomial-lipschitz")
(include-book "circle-interior-count-polynomial")

; One fixed polynomial supplies the Lipschitz cap for all refinements.
(defun lw-euler-circle-collar-base-error (center radius plus-arcs minus-arcs)
  (* 1/16 (lw-euler-circle-count-request center radius plus-arcs minus-arcs 1)))

(defun lw-euler-circle-collar-width (center radius plus-arcs minus-arcs)
  (min (* 1/2 radius) (* 1/8 (lw-euler-circle-anchor-min plus-arcs minus-arcs) (/ (+ 1 (lw-polynomial-lipschitz-cap (lw-euler-circle-global-polynomial center radius 0 (lw-euler-circle-collar-base-error center radius plus-arcs minus-arcs)) radius))))))

(local (defthm lw-eccl-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-eccl-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-eccl-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-eccl-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-eccl-times-negative (a b) (b a)))
                 :in-theory (disable lw-eccl-times-negative)))))

(local (defthm lw-eccl-zero-times (equal (* 0 a) 0)))

(local (defthm lw-eccl-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-eccl-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-eccl-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-eccl-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-eccl-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-eccl-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-eccl-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-eccl-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-eccl-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-eccl-left-commutes)))))
(local
 (defthm lw-eccl-base-data
   (implies (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
            (and (rationalp (lw-euler-circle-collar-base-error center radius plus-arcs minus-arcs)) (< 0 (lw-euler-circle-collar-base-error center radius plus-arcs minus-arcs))
                 (<= (* (lw-euler-circle-outer-gap center radius) (lw-euler-circle-collar-base-error center radius plus-arcs minus-arcs)) (* 1/16 (lw-euler-circle-anchor-min plus-arcs minus-arcs)))
                 (lw-complex-coefficientsp (lw-euler-circle-global-polynomial center radius 0 (lw-euler-circle-collar-base-error center radius plus-arcs minus-arcs)))))
   :hints (("Goal"
            :use ((:instance lw-euler-circle-count-request-adequate (target 0) (request 1))
                  (:instance lw-euler-circle-global-polynomials-valid (target 0) (error (lw-euler-circle-collar-base-error center radius plus-arcs minus-arcs))))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-euler-circle-collar-base-error lw-euler-circle-count-modelp lw-eccl-left-commutes lw-eccl-left-distributes lw-eccl-fold-constants lw-eccl-times-negative lw-eccl-negative-times lw-eccl-zero-times lw-eccl-minus-one lw-eccl-double-negative lw-eccl-add-cancel lw-eccl-double lw-eccl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-eccl-width-budget
   (implies (and (rationalp radius) (< 0 radius)
                 (rationalp anchor) (< 0 anchor) (rationalp slope) (<= 0 slope))
            (let ((width (min (* 1/2 radius) (* 1/8 anchor (/ (+ 1 slope))))))
              (and (rationalp width) (< 0 width) (<= width (* 1/2 radius))
                   (<= (* 2 width slope) (* 1/4 anchor)))))
   :hints (("Goal"
            :use ((:instance lw-eccl-inverse-factor (divisor (+ 1 slope)) (coefficient (* 1/8 anchor)))
                  (:instance lw-eccl-multiply-order
                    (a slope) (b (+ 1 slope)) (factor (* 1/8 anchor (/ (+ 1 slope)))))
                  (:instance lw-eccl-multiply-order
                    (a (* 1/2 radius)) (b (* 1/8 anchor (/ (+ 1 slope)))) (factor slope)))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) min lw-reciprocal-positive lw-eccl-left-commutes lw-eccl-left-distributes lw-eccl-fold-constants lw-eccl-times-negative lw-eccl-negative-times lw-eccl-zero-times lw-eccl-minus-one lw-eccl-double-negative lw-eccl-add-cancel lw-eccl-double lw-eccl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :nonlinearp t :do-not-induct t))
   :rule-classes nil))

(defthm lw-euler-circle-collar-width-data
  (implies (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
           (and (rationalp (lw-euler-circle-collar-width center radius plus-arcs minus-arcs)) (< 0 (lw-euler-circle-collar-width center radius plus-arcs minus-arcs)) (<= (lw-euler-circle-collar-width center radius plus-arcs minus-arcs) (* 1/2 radius))
                (<= (* 2 (lw-euler-circle-collar-width center radius plus-arcs minus-arcs) (lw-polynomial-lipschitz-cap (lw-euler-circle-global-polynomial center radius 0 (lw-euler-circle-collar-base-error center radius plus-arcs minus-arcs)) radius)) (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs)))))
  :hints (("Goal"
           :use (lw-euler-circle-outer-data lw-eccl-base-data
                 (:instance lw-euler-circle-anchor-min-data (point (cons 1 0)))
                 (:instance lw-polynomial-lipschitz-cap-data (coefficients (lw-euler-circle-global-polynomial center radius 0 (lw-euler-circle-collar-base-error center radius plus-arcs minus-arcs))) (bound radius))
                 (:instance lw-eccl-width-budget (anchor (lw-euler-circle-anchor-min plus-arcs minus-arcs)) (slope (lw-polynomial-lipschitz-cap (lw-euler-circle-global-polynomial center radius 0 (lw-euler-circle-collar-base-error center radius plus-arcs minus-arcs)) radius))))
           :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-euler-circle-collar-width (:executable-counterpart lw-complex-norm-square) lw-eccl-left-commutes lw-eccl-left-distributes lw-eccl-fold-constants lw-eccl-times-negative lw-eccl-negative-times lw-eccl-zero-times lw-eccl-minus-one lw-eccl-double-negative lw-eccl-add-cancel lw-eccl-double lw-eccl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm lw-eccl-defect-bound
   (implies (and (rationalp radius) (rationalp width) (< 0 width)
                 (rationalp norm) (<= (* (- radius width) (- radius width)) norm))
            (<= (- (* radius radius) norm) (* 2 radius width)))
   :hints (("Goal"
            :use ((:instance lw-eccl-positive-product (a width) (b width)))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) consp lw-eccl-left-commutes lw-eccl-left-distributes lw-eccl-fold-constants lw-eccl-times-negative lw-eccl-negative-times lw-eccl-zero-times lw-eccl-minus-one lw-eccl-double-negative lw-eccl-add-cancel lw-eccl-double lw-eccl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :nonlinearp t :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-eccl-defect-budget
   (implies (and (rationalp radius) (< 0 radius) (rationalp width) (< 0 width)
                 (rationalp norm) (<= (* (- radius width) (- radius width)) norm))
            (<= (- radius (* (/ radius) norm)) (* 2 width)))
   :hints (("Goal"
            :use (lw-eccl-defect-bound
                  (:instance lw-eccl-multiply-order
                    (a (- (* radius radius) norm)) (b (* 2 radius width)) (factor (/ radius)))
                  (:instance lw-eccl-inverse-factor (divisor radius) (coefficient radius))
                  (:instance lw-eccl-inverse-factor (divisor radius) (coefficient width)))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-reciprocal-positive lw-eccl-left-commutes lw-eccl-left-distributes lw-eccl-fold-constants lw-eccl-times-negative lw-eccl-negative-times lw-eccl-zero-times lw-eccl-minus-one lw-eccl-double-negative lw-eccl-add-cancel lw-eccl-double lw-eccl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-eccl-member-typed
   (implies (and (lw-ray-pointsp roots) (member-equal point roots))
            (lw-complexp point))
   :hints (("Goal" :induct (member-equal point roots)
                   :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) member-equal lw-ray-pointsp lw-eccl-left-commutes lw-eccl-left-distributes lw-eccl-fold-constants lw-eccl-times-negative lw-eccl-negative-times lw-eccl-zero-times lw-eccl-minus-one lw-eccl-double-negative lw-eccl-add-cancel lw-eccl-double lw-eccl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local
 (defthm lw-eccl-root-data
   (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
                (natp target) (rationalp error) (< 0 error) (<= (* (lw-euler-circle-outer-gap center radius) error) (* 1/8 (lw-euler-circle-anchor-min plus-arcs minus-arcs)))
                (rationalp epsilon) (< 0 epsilon) (<= epsilon (* 1/8 (lw-euler-circle-anchor-min plus-arcs minus-arcs)))
                (member-equal point (lw-euler-circle-factor-roots center radius target error epsilon))
                (< (lw-complex-norm-square point) (* radius radius)))
            (and (lw-complex-coefficientsp (lw-euler-circle-global-polynomial center radius target error))
                 (lw-ray-pointsp (lw-euler-circle-factor-roots center radius target error epsilon))
                 (lw-complexp point)
                 (lw-complex-diskp point radius)
                 (lw-complex-diskp point (lw-euler-circle-outer-radius center radius))
                 (lw-complex-diskp (lw-complex-polynomial (lw-euler-circle-global-polynomial center radius target error) point 0) epsilon)))
   :hints (("Goal"
            :use (lw-euler-circle-outer-data lw-euler-circle-global-polynomials-valid
                  (:instance lw-polynomial-disk-factor-data (coefficients (lw-euler-circle-global-polynomial center radius target error)) (outer-radius (lw-euler-circle-outer-radius center radius)))
                  (:instance lw-eccl-member-typed (roots (lw-euler-circle-factor-roots center radius target error epsilon)))
                  (:instance lw-complex-disk-norm-square)
                  (:instance lw-complex-disk-enlarge (cap (lw-euler-circle-outer-radius center radius)))
                  (:instance lw-polynomial-disk-factor-value-error (coefficients (lw-euler-circle-global-polynomial center radius target error)) (outer-radius (lw-euler-circle-outer-radius center radius)))
                  (:instance lw-polynomial-disk-factor-evaluation (coefficients (lw-euler-circle-global-polynomial center radius target error)) (outer-radius (lw-euler-circle-outer-radius center radius)))
                  (:instance lw-polynomial-factor-member-zero (roots (lw-euler-circle-factor-roots center radius target error epsilon))
                    (leading (lw-polynomial-leading (lw-polynomial-trim (lw-euler-circle-global-polynomial center radius target error)))) (root point)))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-euler-circle-factor-roots lw-complex-polynomial-rational lw-complex-sub-zero lw-eccl-left-commutes lw-eccl-left-distributes lw-eccl-fold-constants lw-eccl-times-negative lw-eccl-negative-times lw-eccl-zero-times lw-eccl-minus-one lw-eccl-double-negative lw-eccl-add-cancel lw-eccl-double lw-eccl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-eccl-close-to-boundary
   (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs) (lw-complex-diskp point radius) (<= (* (- radius (lw-euler-circle-collar-width center radius plus-arcs minus-arcs)) (- radius (lw-euler-circle-collar-width center radius plus-arcs minus-arcs))) (lw-complex-norm-square point)))
            (and (lw-complexp (lw-circle-nearby-unit-point point radius)) (equal (lw-complex-norm-square (lw-circle-nearby-unit-point point radius)) 1)
                 (lw-complex-diskp (lw-complex-scale radius (lw-circle-nearby-unit-point point radius)) radius)
                 (lw-complex-diskp (lw-complex-sub (lw-complex-scale radius (lw-circle-nearby-unit-point point radius)) point) (* 2 (lw-euler-circle-collar-width center radius plus-arcs minus-arcs)))))
   :hints (("Goal"
            :use (lw-euler-circle-outer-data lw-euler-circle-collar-width-data
                  (:instance lw-complex-disk-data)
                  lw-circle-nearby-unit-point-data
                  (:instance lw-eccl-defect-budget (width (lw-euler-circle-collar-width center radius plus-arcs minus-arcs)) (norm (lw-complex-norm-square point)))
                  (:instance lw-complex-disk-norm-square (point (lw-circle-nearby-unit-point point radius)) (radius 1))
                  (:instance lw-complex-scale-disk (point (lw-circle-nearby-unit-point point radius)) (factor radius) (radius 1))
                  (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-scale radius (lw-circle-nearby-unit-point point radius)) point))
                    (radius (- radius (* (/ radius) (lw-complex-norm-square point)))) (cap (* 2 (lw-euler-circle-collar-width center radius plus-arcs minus-arcs)))))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) abs lw-complex-norm-square-valid lw-eccl-left-commutes lw-eccl-left-distributes lw-eccl-fold-constants lw-eccl-times-negative lw-eccl-negative-times lw-eccl-zero-times lw-eccl-minus-one lw-eccl-double-negative lw-eccl-add-cancel lw-eccl-double lw-eccl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-eccl-nearby-base-bound
   (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
                (natp target) (rationalp error) (< 0 error) (<= (* (lw-euler-circle-outer-gap center radius) error) (* 1/8 (lw-euler-circle-anchor-min plus-arcs minus-arcs)))
                (rationalp epsilon) (< 0 epsilon) (<= epsilon (* 1/8 (lw-euler-circle-anchor-min plus-arcs minus-arcs)))
                (member-equal point (lw-euler-circle-factor-roots center radius target error epsilon))
                (< (lw-complex-norm-square point) (* radius radius)) (<= (* (- radius (lw-euler-circle-collar-width center radius plus-arcs minus-arcs)) (- radius (lw-euler-circle-collar-width center radius plus-arcs minus-arcs))) (lw-complex-norm-square point)))
            (and (lw-complex-diskp (lw-complex-polynomial (lw-euler-circle-global-polynomial center radius 0 (lw-euler-circle-collar-base-error center radius plus-arcs minus-arcs)) (lw-complex-scale radius (lw-circle-nearby-unit-point point radius)) 0) (* 9/16 (lw-euler-circle-anchor-min plus-arcs minus-arcs)))
                 (lw-complexp (lw-circle-nearby-unit-point point radius)) (equal (lw-complex-norm-square (lw-circle-nearby-unit-point point radius)) 1)))
   :hints (("Goal"
            :use (lw-euler-circle-outer-data lw-euler-circle-collar-width-data lw-eccl-base-data lw-eccl-root-data
                  lw-eccl-close-to-boundary
                  (:instance lw-euler-circle-anchor-min-data (point (lw-circle-nearby-unit-point point radius)))
                  (:instance lw-complex-euler-uniform-polynomial-cauchy
                    (rate (car center)) (height (cdr center)) (radius (lw-euler-circle-outer-radius center radius))
                    (left-target 0) (left-error (* (lw-euler-circle-outer-gap center radius) (lw-euler-circle-collar-base-error center radius plus-arcs minus-arcs)))
                    (right-target target) (right-error (* (lw-euler-circle-outer-gap center radius) error)))
                  (:instance lw-complex-polynomial-lipschitz (coefficients (lw-euler-circle-global-polynomial center radius 0 (lw-euler-circle-collar-base-error center radius plus-arcs minus-arcs)))
                    (left (lw-complex-scale radius (lw-circle-nearby-unit-point point radius))) (right point) (bound radius) (step (* 2 (lw-euler-circle-collar-width center radius plus-arcs minus-arcs))))
                  (:instance lw-complex-difference-triangle (left (lw-complex-polynomial (lw-euler-circle-global-polynomial center radius 0 (lw-euler-circle-collar-base-error center radius plus-arcs minus-arcs)) point 0)) (middle (lw-complex-polynomial (lw-euler-circle-global-polynomial center radius target error) point 0))
                    (right (cons 0 0)) (radius (+ (* (lw-euler-circle-outer-gap center radius) (lw-euler-circle-collar-base-error center radius plus-arcs minus-arcs)) (* (lw-euler-circle-outer-gap center radius) error))) (other-radius epsilon))
                  (:instance lw-complex-difference-triangle (left (lw-complex-polynomial (lw-euler-circle-global-polynomial center radius 0 (lw-euler-circle-collar-base-error center radius plus-arcs minus-arcs)) (lw-complex-scale radius (lw-circle-nearby-unit-point point radius)) 0)) (middle (lw-complex-polynomial (lw-euler-circle-global-polynomial center radius 0 (lw-euler-circle-collar-base-error center radius plus-arcs minus-arcs)) point 0))
                    (right (cons 0 0)) (radius (* 2 (lw-euler-circle-collar-width center radius plus-arcs minus-arcs) (lw-polynomial-lipschitz-cap (lw-euler-circle-global-polynomial center radius 0 (lw-euler-circle-collar-base-error center radius plus-arcs minus-arcs)) radius))) (other-radius (+ (+ (* (lw-euler-circle-outer-gap center radius) (lw-euler-circle-collar-base-error center radius plus-arcs minus-arcs)) (* (lw-euler-circle-outer-gap center radius) error)) epsilon)))
                  (:instance lw-complex-disk-enlarge (point (lw-complex-polynomial (lw-euler-circle-global-polynomial center radius 0 (lw-euler-circle-collar-base-error center radius plus-arcs minus-arcs)) (lw-complex-scale radius (lw-circle-nearby-unit-point point radius)) 0))
                    (radius (+ (* 2 (lw-euler-circle-collar-width center radius plus-arcs minus-arcs) (lw-polynomial-lipschitz-cap (lw-euler-circle-global-polynomial center radius 0 (lw-euler-circle-collar-base-error center radius plus-arcs minus-arcs)) radius)) (+ (+ (* (lw-euler-circle-outer-gap center radius) (lw-euler-circle-collar-base-error center radius plus-arcs minus-arcs)) (* (lw-euler-circle-outer-gap center radius) error)) epsilon))) (cap (* 9/16 (lw-euler-circle-anchor-min plus-arcs minus-arcs)))))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-euler-circle-global-polynomial lw-complex-polynomial-rational lw-complex-scale-rational lw-complex-sub-zero lw-eccl-left-commutes lw-eccl-left-distributes lw-eccl-fold-constants lw-eccl-times-negative lw-eccl-negative-times lw-eccl-zero-times lw-eccl-minus-one lw-eccl-double-negative lw-eccl-add-cancel lw-eccl-double lw-eccl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-eccl-smaller-than-anchor
   (implies (and (rationalp anchor) (< 0 anchor))
            (< (* 9/16 anchor 9/16 anchor) (* anchor anchor)))
   :hints (("Goal" :use ((:instance lw-eccl-positive-product (a anchor) (b anchor)))
                   :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) consp lw-eccl-left-commutes lw-eccl-left-distributes lw-eccl-fold-constants lw-eccl-times-negative lw-eccl-negative-times lw-eccl-zero-times lw-eccl-minus-one lw-eccl-double-negative lw-eccl-add-cancel lw-eccl-double lw-eccl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
   :rule-classes nil))

(defthm lw-euler-circle-factor-interior-gap
  (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
                (natp target) (rationalp error) (< 0 error) (<= (* (lw-euler-circle-outer-gap center radius) error) (* 1/8 (lw-euler-circle-anchor-min plus-arcs minus-arcs)))
                (rationalp epsilon) (< 0 epsilon) (<= epsilon (* 1/8 (lw-euler-circle-anchor-min plus-arcs minus-arcs)))
                (member-equal point (lw-euler-circle-factor-roots center radius target error epsilon))
                (< (lw-complex-norm-square point) (* radius radius)))
           (< (lw-complex-norm-square point) (* (- radius (lw-euler-circle-collar-width center radius plus-arcs minus-arcs)) (- radius (lw-euler-circle-collar-width center radius plus-arcs minus-arcs)))))
  :hints (("Goal"
           :use (lw-euler-circle-outer-data lw-eccl-base-data lw-eccl-nearby-base-bound
                 (:instance lw-euler-circle-anchor-min-data (point (lw-circle-nearby-unit-point point radius)))
                 (:instance lw-euler-circle-global-polynomial-clearance
                   (point (lw-circle-nearby-unit-point point radius)) (target 0) (error (lw-euler-circle-collar-base-error center radius plus-arcs minus-arcs)))
                 (:instance lw-eccl-smaller-than-anchor (anchor (lw-euler-circle-anchor-min plus-arcs minus-arcs)))
                 (:instance lw-complex-disk-norm-square (point (lw-complex-polynomial (lw-euler-circle-global-polynomial center radius 0 (lw-euler-circle-collar-base-error center radius plus-arcs minus-arcs)) (lw-complex-scale radius (lw-circle-nearby-unit-point point radius)) 0)) (radius (* 9/16 (lw-euler-circle-anchor-min plus-arcs minus-arcs)))))
           :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-euler-circle-global-polynomial-value lw-eccl-left-commutes lw-eccl-left-distributes lw-eccl-fold-constants lw-eccl-times-negative lw-eccl-negative-times lw-eccl-zero-times lw-eccl-minus-one lw-eccl-double-negative lw-eccl-add-cancel lw-eccl-double lw-eccl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defun lw-eccl-collar-witness (roots radius cutoff)
   (if (endp roots) nil
     (let ((root (car roots)))
       (if (and (< (lw-complex-norm-square root) (* radius radius))
                (<= (* cutoff cutoff) (lw-complex-norm-square root)))
           root
         (lw-eccl-collar-witness (cdr roots) radius cutoff))))))

(local
 (defthm lw-eccl-collar-witness-data
   (implies (lw-ray-pointsp roots)
            (if (lw-eccl-collar-witness roots radius cutoff)
                (and (member-equal (lw-eccl-collar-witness roots radius cutoff) roots)
                     (< (lw-complex-norm-square (lw-eccl-collar-witness roots radius cutoff)) (* radius radius))
                     (<= (* cutoff cutoff) (lw-complex-norm-square (lw-eccl-collar-witness roots radius cutoff))))
              (lw-circle-interior-rootsp (lw-circle-pole-roots roots radius) cutoff)))
   :hints (("Goal" :induct (lw-eccl-collar-witness roots radius cutoff)
                   :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-eccl-collar-witness lw-circle-pole-roots lw-circle-interior-rootsp lw-ray-pointsp lw-complexp member-equal endp lw-eccl-left-commutes lw-eccl-left-distributes lw-eccl-fold-constants lw-eccl-times-negative lw-eccl-negative-times lw-eccl-zero-times lw-eccl-minus-one lw-eccl-double-negative lw-eccl-add-cancel lw-eccl-double lw-eccl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
                   :do-not '(generalize fertilize)))
   :rule-classes nil))

(defthm lw-euler-circle-interior-collar
  (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
                (natp target) (rationalp error) (< 0 error) (<= (* (lw-euler-circle-outer-gap center radius) error) (* 1/8 (lw-euler-circle-anchor-min plus-arcs minus-arcs)))
                (rationalp epsilon) (< 0 epsilon) (<= epsilon (* 1/8 (lw-euler-circle-anchor-min plus-arcs minus-arcs))))
           (and (rationalp (- radius (lw-euler-circle-collar-width center radius plus-arcs minus-arcs))) (< 0 (- radius (lw-euler-circle-collar-width center radius plus-arcs minus-arcs))) (< (- radius (lw-euler-circle-collar-width center radius plus-arcs minus-arcs)) radius)
                (lw-circle-interior-rootsp (lw-circle-pole-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius) (- radius (lw-euler-circle-collar-width center radius plus-arcs minus-arcs)))))
  :hints (("Goal"
           :use (lw-euler-circle-outer-data lw-euler-circle-collar-width-data lw-euler-circle-global-polynomials-valid
                 (:instance lw-polynomial-disk-factor-data
                   (coefficients (lw-euler-circle-global-polynomial center radius target error))
                   (outer-radius (lw-euler-circle-outer-radius center radius)))
                 (:instance lw-eccl-collar-witness-data (roots (lw-euler-circle-factor-roots center radius target error epsilon)) (cutoff (- radius (lw-euler-circle-collar-width center radius plus-arcs minus-arcs))))
                 (:instance lw-euler-circle-factor-interior-gap (point (lw-eccl-collar-witness (lw-euler-circle-factor-roots center radius target error epsilon) radius (- radius (lw-euler-circle-collar-width center radius plus-arcs minus-arcs))))))
           :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-euler-circle-factor-roots lw-eccl-left-commutes lw-eccl-left-distributes lw-eccl-fold-constants lw-eccl-times-negative lw-eccl-negative-times lw-eccl-zero-times lw-eccl-minus-one lw-eccl-double-negative lw-eccl-add-cancel lw-eccl-double lw-eccl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
