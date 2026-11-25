(in-package "ACL2")

(include-book "polynomial-derivative-coefficients")
(include-book "euler-local-coefficients")

; Shift one global Euler polynomial without changing its coefficients
; with the evaluation point. Inner circles stay inside the outer disk.

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

(local (defthm lw-esp-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-esp-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-esp-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-esp-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-esp-times-negative (a b) (b a)))
                 :in-theory (disable lw-esp-times-negative)))))

(local (defthm lw-esp-zero-times (equal (* 0 a) 0)))

(local (defthm lw-esp-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-esp-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-esp-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-esp-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-esp-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-esp-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-esp-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-esp-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-esp-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-esp-left-commutes)))))

(defthm lw-euler-shifted-center-data
 (implies (and (rationalp rate) (rationalp height)
               (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
               (rationalp radius) (< 0 radius) (<= radius outer-radius)
               (lw-complex-diskp center (- outer-radius radius)))
  (and (lw-complexp center)
       (rationalp (+ rate (car center))) (< radius (+ rate (car center)))
       (rationalp (+ height (cdr center)))
       (lw-complex-diskp center outer-radius)))
 :hints (("Goal"
  :use ((:instance lw-complex-disk-data (point center) (radius (- outer-radius radius)))
        (:instance lw-complex-disk-coordinates (point center) (radius (- outer-radius radius)))
        (:instance lw-complex-disk-enlarge (point center) (radius (- outer-radius radius)) (cap outer-radius)))
  :in-theory (union-theories
 '(lw-complexp abs lw-esp-left-commutes lw-esp-left-distributes lw-esp-fold-constants lw-esp-times-negative lw-esp-negative-times lw-esp-zero-times lw-esp-minus-one lw-esp-double-negative lw-esp-add-cancel lw-esp-double lw-esp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(local (defthm lw-esp-circle-data
 (implies (and (rationalp rate) (rationalp height)
               (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
               (rationalp radius) (< 0 radius) (<= radius outer-radius)
               (lw-complex-diskp center (- outer-radius radius))
               (lw-complex-diskp point radius))
  (and (lw-complexp point) (lw-complex-diskp (lw-complex-add center point) outer-radius)
       (rationalp (+ (+ rate (car center)) (car point))) (< 0 (+ (+ rate (car center)) (car point)))
       (rationalp (+ (+ height (cdr center)) (cdr point)))))
 :hints (("Goal"
  :use (lw-euler-shifted-center-data
        (:instance lw-complex-disk-data)
        (:instance lw-complex-add-disk (left center) (right point) (radius (- outer-radius radius)) (other-radius radius))
        (:instance lw-euler-disk-point-data (rate (+ rate (car center))) (height (+ height (cdr center))) (offset point)))
  :in-theory (union-theories
 '( lw-esp-left-commutes lw-esp-left-distributes lw-esp-fold-constants lw-esp-times-negative lw-esp-negative-times lw-esp-zero-times lw-esp-minus-one lw-esp-double-negative lw-esp-add-cancel lw-esp-double lw-esp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))
 :rule-classes nil))

(defun lw-euler-shifted-polynomial (rate height outer-radius center target error)
 (lw-polynomial-affine (lw-euler-uniform-polynomial rate height outer-radius target error) center (cons 1 0)))

(local (in-theory (disable lw-euler-shifted-polynomial)))

(defthm lw-euler-shifted-polynomial-valid
 (implies (and (rationalp rate) (rationalp height)
               (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
               (lw-complexp center) (natp target) (rationalp error) (< 0 error))
  (and (lw-complex-coefficientsp (lw-euler-shifted-polynomial rate height outer-radius center target error))
       (equal (len (lw-euler-shifted-polynomial rate height outer-radius center target error)) (len (lw-euler-uniform-polynomial rate height outer-radius target error)))))
 :hints (("Goal"
  :use ((:instance lw-euler-uniform-polynomial-valid (radius outer-radius))
        (:instance lw-polynomial-affine-valid (coefficients (lw-euler-uniform-polynomial rate height outer-radius target error)) (slope (cons 1 0))))
  :in-theory (union-theories
 '(lw-euler-shifted-polynomial (:executable-counterpart lw-complexp) lw-esp-left-commutes lw-esp-left-distributes lw-esp-fold-constants lw-esp-times-negative lw-esp-negative-times lw-esp-zero-times lw-esp-minus-one lw-esp-double-negative lw-esp-add-cancel lw-esp-double lw-esp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-euler-shifted-polynomial-evaluation
 (implies (and (rationalp rate) (rationalp height)
               (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
               (lw-complexp center) (lw-complexp point) (natp target)
               (rationalp error) (< 0 error))
  (equal (lw-complex-polynomial (lw-euler-shifted-polynomial rate height outer-radius center target error) point 0)
         (lw-complex-polynomial (lw-euler-uniform-polynomial rate height outer-radius target error) (lw-complex-add center point) 0)))
 :hints (("Goal"
  :use ((:instance lw-euler-uniform-polynomial-valid (radius outer-radius))
        (:instance lw-polynomial-affine-evaluation (coefficients (lw-euler-uniform-polynomial rate height outer-radius target error)) (slope (cons 1 0))))
  :in-theory (union-theories
 '(lw-euler-shifted-polynomial lw-complex-mul-one (:executable-counterpart lw-complexp) lw-esp-left-commutes lw-esp-left-distributes lw-esp-fold-constants lw-esp-times-negative lw-esp-negative-times lw-esp-zero-times lw-esp-minus-one lw-esp-double-negative lw-esp-add-cancel lw-esp-double lw-esp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(local (defthm lw-esp-reconstruction
 (implies (consp value) (equal (cons (car value) (cdr value)) value))))

(local (defthm lw-esp-unit-linear-shift
 (implies (lw-complex-coefficientsp coefficients)
  (equal (lw-polynomial-multiply-linear (cons 0 0) (cons 1 0) coefficients)
         (if (endp coefficients) nil (cons (cons 0 0) coefficients))))
 :hints (("Goal"
  :induct (lw-polynomial-multiply-linear (cons 0 0) (cons 1 0) coefficients)
  :in-theory (union-theories
 '(lw-polynomial-multiply-linear lw-polynomial-add-constant lw-complex-coefficientsp lw-complex-mul-zero lw-complex-mul-one lw-complex-add-zero lw-esp-reconstruction (:executable-counterpart lw-complexp) endp lw-esp-left-commutes lw-esp-left-distributes lw-esp-fold-constants lw-esp-times-negative lw-esp-negative-times lw-esp-zero-times lw-esp-minus-one lw-esp-double-negative lw-esp-add-cancel lw-esp-double lw-esp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-polynomial-affine-identity
 (implies (lw-complex-coefficientsp coefficients)
  (equal (lw-polynomial-affine coefficients (cons 0 0) (cons 1 0)) coefficients))
 :hints (("Goal"
  :induct (lw-polynomial-affine coefficients (cons 0 0) (cons 1 0))
  :in-theory (union-theories
 '(lw-polynomial-affine lw-esp-unit-linear-shift lw-polynomial-add-constant lw-complex-coefficientsp lw-complex-add-zero lw-esp-reconstruction (:executable-counterpart lw-complexp) endp lw-esp-left-commutes lw-esp-left-distributes lw-esp-fold-constants lw-esp-times-negative lw-esp-negative-times lw-esp-zero-times lw-esp-minus-one lw-esp-double-negative lw-esp-add-cancel lw-esp-double lw-esp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-euler-shifted-polynomial-at-zero
 (implies (and (rationalp rate) (rationalp height)
               (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
               (natp target) (rationalp error) (< 0 error))
  (equal (lw-euler-shifted-polynomial rate height outer-radius (cons 0 0) target error) (lw-euler-uniform-polynomial rate height outer-radius target error)))
 :hints (("Goal"
  :use ((:instance lw-euler-uniform-polynomial-valid (radius outer-radius))
        (:instance lw-polynomial-affine-identity (coefficients (lw-euler-uniform-polynomial rate height outer-radius target error))))
  :in-theory (union-theories
 '(lw-euler-shifted-polynomial lw-esp-left-commutes lw-esp-left-distributes lw-esp-fold-constants lw-esp-times-negative lw-esp-negative-times lw-esp-zero-times lw-esp-minus-one lw-esp-double-negative lw-esp-add-cancel lw-esp-double lw-esp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))


(local (defthm lw-esp-polynomial-comparison-with-accuracy
 (implies (and (rationalp rate) (rationalp height)
               (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
               (rationalp radius) (< 0 radius) (<= radius outer-radius)
               (lw-complex-diskp center (- outer-radius radius)) (lw-complex-diskp point radius)
               (natp left-target) (natp right-target)
               (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error)
               (rationalp value-error) (< 0 value-error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-polynomial (lw-euler-shifted-polynomial rate height outer-radius center left-target left-error) point 0) (lw-complex-polynomial (lw-euler-uniform-polynomial (+ rate (car center)) (+ height (cdr center)) radius right-target right-error) point 0))
   (+ left-error right-error (* 1/2 value-error))))
 :hints (("Goal"
  :use (lw-euler-shifted-center-data lw-esp-circle-data
        (:instance lw-euler-shifted-polynomial-valid (target left-target) (error left-error))
        (:instance lw-euler-uniform-polynomial-valid (rate (+ rate (car center))) (height (+ height (cdr center))) (target right-target) (error right-error))
        (:instance lw-complex-polynomial-rational (coefficients (lw-euler-shifted-polynomial rate height outer-radius center left-target left-error)) (offset 0))
        (:instance lw-complex-polynomial-rational (coefficients (lw-euler-uniform-polynomial (+ rate (car center)) (+ height (cdr center)) radius right-target right-error)) (offset 0))
        (:instance lw-complex-euler-continuation-value-rational
         (rate (+ (+ rate (car center)) (car point))) (height (+ (+ height (cdr center)) (cdr point))) (error value-error))
        (:instance lw-euler-shifted-polynomial-evaluation (target left-target) (error left-error))
        (:instance lw-complex-euler-uniform-polynomial-comparison
         (radius outer-radius) (target left-target) (error left-error) (point (lw-complex-add center point)))
        (:instance lw-complex-euler-uniform-polynomial-comparison
         (rate (+ rate (car center))) (height (+ height (cdr center))) (target right-target) (error right-error))
        (:instance lw-complex-difference-symmetric
         (left (lw-complex-polynomial (lw-euler-uniform-polynomial (+ rate (car center)) (+ height (cdr center)) radius right-target right-error) point 0)) (right (lw-complex-euler-continuation-value (+ (+ rate (car center)) (car point)) (+ (+ height (cdr center)) (cdr point)) value-error)) (radius (+ right-error (* 1/4 value-error))))
        (:instance lw-complex-difference-triangle
         (left (lw-complex-polynomial (lw-euler-shifted-polynomial rate height outer-radius center left-target left-error) point 0)) (middle (lw-complex-euler-continuation-value (+ (+ rate (car center)) (car point)) (+ (+ height (cdr center)) (cdr point)) value-error)) (right (lw-complex-polynomial (lw-euler-uniform-polynomial (+ rate (car center)) (+ height (cdr center)) radius right-target right-error) point 0))
         (radius (+ left-error (* 1/4 value-error))) (other-radius (+ right-error (* 1/4 value-error))))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub (lw-complex-polynomial (lw-euler-shifted-polynomial rate height outer-radius center left-target left-error) point 0) (lw-complex-polynomial (lw-euler-uniform-polynomial (+ rate (car center)) (+ height (cdr center)) radius right-target right-error) point 0)))
         (radius (+ left-error (* 1/4 value-error) right-error (* 1/4 value-error)))
         (cap (+ left-error right-error (* 1/2 value-error)))))
  :in-theory (union-theories
 '(lw-complex-add lw-esp-left-commutes lw-esp-left-distributes lw-esp-fold-constants lw-esp-times-negative lw-esp-negative-times lw-esp-zero-times lw-esp-minus-one lw-esp-double-negative lw-esp-add-cancel lw-esp-double lw-esp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))
 :rule-classes nil))

(defthm lw-complex-euler-shifted-polynomial-comparison
 (implies (and (rationalp rate) (rationalp height)
               (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
               (rationalp radius) (< 0 radius) (<= radius outer-radius)
               (lw-complex-diskp center (- outer-radius radius)) (lw-complex-diskp point radius)
               (natp left-target) (natp right-target)
               (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-polynomial (lw-euler-shifted-polynomial rate height outer-radius center left-target left-error) point 0) (lw-complex-polynomial (lw-euler-uniform-polynomial (+ rate (car center)) (+ height (cdr center)) radius right-target right-error) point 0)) (+ left-error right-error)))
 :hints (("Goal"
  :cases ((lw-complex-diskp (lw-complex-sub (lw-complex-polynomial (lw-euler-shifted-polynomial rate height outer-radius center left-target left-error) point 0) (lw-complex-polynomial (lw-euler-uniform-polynomial (+ rate (car center)) (+ height (cdr center)) radius right-target right-error) point 0)) (+ left-error right-error)))
  :use (lw-euler-shifted-center-data lw-esp-circle-data
        (:instance lw-euler-shifted-polynomial-valid (target left-target) (error left-error))
        (:instance lw-euler-uniform-polynomial-valid (rate (+ rate (car center))) (height (+ height (cdr center))) (target right-target) (error right-error))
        (:instance lw-complex-polynomial-rational (coefficients (lw-euler-shifted-polynomial rate height outer-radius center left-target left-error)) (offset 0))
        (:instance lw-complex-polynomial-rational (coefficients (lw-euler-uniform-polynomial (+ rate (car center)) (+ height (cdr center)) radius right-target right-error)) (offset 0))
        (:instance lw-complex-operations-rational (left (lw-complex-polynomial (lw-euler-shifted-polynomial rate height outer-radius center left-target left-error) point 0)) (right (lw-complex-polynomial (lw-euler-uniform-polynomial (+ rate (car center)) (+ height (cdr center)) radius right-target right-error) point 0)) (factor 1))
        (:instance lw-complex-disk-gap-refinement-excludes
         (point (lw-complex-sub (lw-complex-polynomial (lw-euler-shifted-polynomial rate height outer-radius center left-target left-error) point 0) (lw-complex-polynomial (lw-euler-uniform-polynomial (+ rate (car center)) (+ height (cdr center)) radius right-target right-error) point 0))) (radius (+ left-error right-error)) (cost 1/2))
        (:instance lw-esp-polynomial-comparison-with-accuracy
         (value-error (lw-disk-gap-refinement (lw-complex-sub (lw-complex-polynomial (lw-euler-shifted-polynomial rate height outer-radius center left-target left-error) point 0) (lw-complex-polynomial (lw-euler-uniform-polynomial (+ rate (car center)) (+ height (cdr center)) radius right-target right-error) point 0)) (+ left-error right-error) 1/2))))
  :in-theory (union-theories
 '( lw-esp-left-commutes lw-esp-left-distributes lw-esp-fold-constants lw-esp-times-negative lw-esp-negative-times lw-esp-zero-times lw-esp-minus-one lw-esp-double-negative lw-esp-add-cancel lw-esp-double lw-esp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))


