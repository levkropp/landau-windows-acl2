(in-package "ACL2")

(include-book "euler-local-coefficients")
(include-book "polynomial-quadratic-bounds")

; Uniform polynomial caps give an increment bound for the actual Euler name.
; Every approximation budget is independent and eliminated arithmetically.

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

(local (in-theory
 (disable lw-complex-log-ramp-start lw-complex-log-ramp-cap
          lw-complex-log-ramp-independent-exp lw-complex-log-ramp-independent-endpoint
          lw-complex-log-ramp-independent-model
          lw-complex-log-ramp-independent-model-identity
          lw-smoothed-ramp-log-error lw-smoothed-ramp-unit-error lw-mangoldt-bounds
          lw-complex-sub-add-first lw-complex-add-commutative lw-complex-add-left-commutes)))

(local (in-theory (disable lw-euler-uniform-polynomial lw-euler-coefficient-polynomial
 lw-complex-euler-polynomial-coefficient lw-complex-euler-coefficient-value
 lw-complex-euler-local-coefficient-value lw-euler-uniform-coefficient-cap
 lw-complex-euler-continuation-value lw-complex-polynomial lw-complex-coefficient-at
 lw-polynomial-coefficient-caps lw-polynomial-cap-index lw-complex-linear-remainder)))

(local (defthm lw-equ-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-equ-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-equ-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-equ-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-equ-times-negative (a b) (b a)))
                 :in-theory (disable lw-equ-times-negative)))))

(local (defthm lw-equ-zero-times (equal (* 0 a) 0)))

(local (defthm lw-equ-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-equ-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-equ-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-equ-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-equ-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-equ-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-equ-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-equ-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-equ-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-equ-left-commutes)))))

(defthm lw-euler-polynomial-coefficient-caps
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate) (natp target) (rationalp error) (< 0 error))
  (lw-polynomial-coefficient-caps (lw-euler-coefficient-polynomial rate height radius target error) (+ -1 (lw-euler-uniform-coefficient-cap rate height radius) error)))
 :hints (("Goal"
  :cases ((lw-polynomial-coefficient-caps (lw-euler-coefficient-polynomial rate height radius target error) (+ -1 (lw-euler-uniform-coefficient-cap rate height radius) error)))
  :use ((:instance lw-euler-polynomial-coefficient-rational (index 0))
        (:instance lw-polynomial-cap-index-data (coefficients (lw-euler-coefficient-polynomial rate height radius target error)) (cap (+ -1 (lw-euler-uniform-coefficient-cap rate height radius) error)))
        (:instance lw-complex-coefficient-at-nth (coefficients (lw-euler-coefficient-polynomial rate height radius target error)) (offset 0)
         (target (lw-polynomial-cap-index (lw-euler-coefficient-polynomial rate height radius target error) (+ -1 (lw-euler-uniform-coefficient-cap rate height radius) error))))
        (:instance lw-complex-euler-polynomial-coefficient-cap
         (index (lw-polynomial-cap-index (lw-euler-coefficient-polynomial rate height radius target error) (+ -1 (lw-euler-uniform-coefficient-cap rate height radius) error)))))
  :in-theory (union-theories
   '(lw-complex-euler-polynomial-coefficient lw-equ-left-commutes lw-equ-left-distributes lw-equ-fold-constants lw-equ-times-negative lw-equ-negative-times lw-equ-zero-times lw-equ-minus-one lw-equ-double-negative lw-equ-add-cancel lw-equ-double lw-equ-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-complex-euler-polynomial-quadratic-bound
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate) (natp target) (rationalp error) (< 0 error)
               (lw-complex-diskp point step) (<= step 1/2))
  (lw-complex-diskp
   (lw-complex-linear-remainder
    (lw-complex-polynomial (lw-euler-coefficient-polynomial rate height radius target error) point 0) (lw-complex-polynomial (lw-euler-coefficient-polynomial rate height radius target error) (cons 0 0) 0) (lw-complex-euler-polynomial-coefficient rate height radius target 1 error) point)
   (* 2 (+ -1 (lw-euler-uniform-coefficient-cap rate height radius) error) step step)))
 :hints (("Goal"
  :use (lw-euler-uniform-coefficient-cap-valid lw-euler-polynomial-coefficient-caps
        (:instance lw-euler-polynomial-coefficient-rational (index 1))
        (:instance lw-complex-polynomial-quadratic-bound (coefficients (lw-euler-coefficient-polynomial rate height radius target error)) (cap (+ -1 (lw-euler-uniform-coefficient-cap rate height radius) error)) (radius step)))
  :in-theory (union-theories
   '(lw-complex-linear-remainder lw-complex-euler-polynomial-coefficient lw-equ-left-commutes lw-equ-left-distributes lw-equ-fold-constants lw-equ-times-negative lw-equ-negative-times lw-equ-zero-times lw-equ-minus-one lw-equ-double-negative lw-equ-add-cancel lw-equ-double lw-equ-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-euler-normalized-polynomial-comparison
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate) (natp target) (rationalp error) (< 0 error)
               (rationalp value-error) (< 0 value-error) (lw-complex-diskp point 1))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-polynomial (lw-euler-coefficient-polynomial rate height radius target error) point 0) (lw-complex-euler-continuation-value (+ rate (car (lw-complex-scale radius point))) (+ height (cdr (lw-complex-scale radius point))) value-error))
   (+ error (* 1/4 value-error))))
 :hints (("Goal"
  :use (lw-euler-uniform-polynomial-valid
        (:instance lw-complex-disk-data (radius 1))
        (:instance lw-complex-scale-disk (factor radius) (radius 1))
        (:instance lw-polynomial-rescale-evaluation
         (coefficients (lw-euler-uniform-polynomial rate height radius target error)) (factor radius) (offset 0))
        (:instance lw-complex-euler-uniform-polynomial-comparison (point (lw-complex-scale radius point))))
  :in-theory (union-theories
   '(lw-euler-coefficient-polynomial abs lw-equ-left-commutes lw-equ-left-distributes lw-equ-fold-constants lw-equ-times-negative lw-equ-negative-times lw-equ-zero-times lw-equ-minus-one lw-equ-double-negative lw-equ-add-cancel lw-equ-double lw-equ-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(local (defthm lw-equ-point-data
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate)
               (lw-complex-diskp point step) (<= step 1/2))
  (and (lw-complexp point) (rationalp step) (<= 0 step) (lw-complex-diskp point 1)
       (lw-complex-diskp (lw-complex-scale radius point) radius)
       (rationalp (+ rate (car (lw-complex-scale radius point)))) (< 0 (+ rate (car (lw-complex-scale radius point))))
       (rationalp (+ height (cdr (lw-complex-scale radius point)))) (<= 0 (* step step))))
 :hints (("Goal"
  :use ((:instance lw-complex-disk-data (radius step))
        (:instance lw-complex-disk-enlarge (radius step) (cap 1))
        (:instance lw-complex-scale-disk (factor radius) (radius 1))
        (:instance lw-euler-disk-point-data (offset (lw-complex-scale radius point))))
  :in-theory (union-theories
   '(abs lw-equ-left-commutes lw-equ-left-distributes lw-equ-fold-constants lw-equ-times-negative lw-equ-negative-times lw-equ-zero-times lw-equ-minus-one lw-equ-double-negative lw-equ-add-cancel lw-equ-double lw-equ-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp t :do-not-induct t))
 :rule-classes nil))

(defthm lw-complex-euler-normalized-quadratic-with-margin
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate)
               (lw-complex-diskp point step) (<= step 1/2)
               (rationalp shifted-error) (< 0 shifted-error)
               (rationalp center-error) (< 0 center-error)
               (rationalp coefficient-error) (< 0 coefficient-error) (rationalp approximation-error) (< 0 approximation-error))
  (lw-complex-diskp (lw-complex-linear-remainder (lw-complex-euler-continuation-value (+ rate (car (lw-complex-scale radius point))) (+ height (cdr (lw-complex-scale radius point))) shifted-error) (lw-complex-euler-continuation-value rate height center-error) (lw-complex-euler-coefficient-value rate height radius 1 coefficient-error) point) (+ (+ (* 2 (+ -1 (lw-euler-uniform-coefficient-cap rate height radius)) step step) (* 1/4 shifted-error) (* 1/4 center-error) (* coefficient-error step)) (* (+ 2 step (* 2 step step)) approximation-error))))
 :hints (("Goal"
  :use (lw-equ-point-data lw-euler-uniform-coefficient-cap-valid
        (:instance lw-euler-polynomial-coefficient-rational (target 0) (index 1) (error approximation-error))
        (:instance lw-complex-euler-coefficient-value-rational (index 1) (error coefficient-error))
        (:instance lw-complex-euler-continuation-value-rational
         (rate (+ rate (car (lw-complex-scale radius point)))) (height (+ height (cdr (lw-complex-scale radius point)))) (error shifted-error))
        (:instance lw-complex-euler-continuation-value-rational (error center-error))
        (:instance lw-complex-polynomial-rational (coefficients (lw-euler-coefficient-polynomial rate height radius 0 approximation-error)) (offset 0))
        (:instance lw-complex-polynomial-rational (coefficients (lw-euler-coefficient-polynomial rate height radius 0 approximation-error)) (offset 0) (point (cons 0 0)))
        (:instance lw-complex-zero-disk (radius 1))
        (:instance lw-complex-euler-normalized-polynomial-comparison
         (target 0) (error approximation-error) (value-error shifted-error))
        (:instance lw-complex-euler-normalized-polynomial-comparison
         (target 0) (error approximation-error) (value-error center-error) (point (cons 0 0)))
        (:instance lw-complex-difference-symmetric (left (lw-complex-polynomial (lw-euler-coefficient-polynomial rate height radius 0 approximation-error) point 0)) (right (lw-complex-euler-continuation-value (+ rate (car (lw-complex-scale radius point))) (+ height (cdr (lw-complex-scale radius point))) shifted-error))
         (radius (+ approximation-error (* 1/4 shifted-error))))
        (:instance lw-complex-difference-symmetric (left (lw-complex-polynomial (lw-euler-coefficient-polynomial rate height radius 0 approximation-error) (cons 0 0) 0)) (right (lw-complex-euler-continuation-value rate height center-error))
         (radius (+ approximation-error (* 1/4 center-error))))
        (:instance lw-complex-euler-polynomial-coefficient-cauchy
         (index 1) (left-target 1) (left-error coefficient-error) (right-target 0) (right-error approximation-error))
        (:instance lw-complex-linear-remainder-comparison
         (value (lw-complex-euler-continuation-value (+ rate (car (lw-complex-scale radius point))) (+ height (cdr (lw-complex-scale radius point))) shifted-error)) (anchor (lw-complex-euler-continuation-value rate height center-error)) (slope (lw-complex-euler-coefficient-value rate height radius 1 coefficient-error))
         (other-value (lw-complex-polynomial (lw-euler-coefficient-polynomial rate height radius 0 approximation-error) point 0)) (other-anchor (lw-complex-polynomial (lw-euler-coefficient-polynomial rate height radius 0 approximation-error) (cons 0 0) 0)) (other-slope (lw-complex-euler-polynomial-coefficient rate height radius 0 1 approximation-error)) (radius step)
         (value-error (+ approximation-error (* 1/4 shifted-error)))
         (anchor-error (+ approximation-error (* 1/4 center-error)))
         (slope-error (+ coefficient-error approximation-error)))
        (:instance lw-complex-euler-polynomial-quadratic-bound (target 0) (error approximation-error))
        (:instance lw-complex-linear-remainder-rational (value (lw-complex-euler-continuation-value (+ rate (car (lw-complex-scale radius point))) (+ height (cdr (lw-complex-scale radius point))) shifted-error)) (anchor (lw-complex-euler-continuation-value rate height center-error)) (slope (lw-complex-euler-coefficient-value rate height radius 1 coefficient-error)))
        (:instance lw-complex-linear-remainder-rational (value (lw-complex-polynomial (lw-euler-coefficient-polynomial rate height radius 0 approximation-error) point 0)) (anchor (lw-complex-polynomial (lw-euler-coefficient-polynomial rate height radius 0 approximation-error) (cons 0 0) 0)) (slope (lw-complex-euler-polynomial-coefficient rate height radius 0 1 approximation-error)))
        (:instance lw-complex-difference-triangle
         (left (lw-complex-linear-remainder (lw-complex-euler-continuation-value (+ rate (car (lw-complex-scale radius point))) (+ height (cdr (lw-complex-scale radius point))) shifted-error) (lw-complex-euler-continuation-value rate height center-error) (lw-complex-euler-coefficient-value rate height radius 1 coefficient-error) point)) (middle (lw-complex-linear-remainder (lw-complex-polynomial (lw-euler-coefficient-polynomial rate height radius 0 approximation-error) point 0) (lw-complex-polynomial (lw-euler-coefficient-polynomial rate height radius 0 approximation-error) (cons 0 0) 0) (lw-complex-euler-polynomial-coefficient rate height radius 0 1 approximation-error) point)) (right (cons 0 0))
         (radius (+ (* 2 approximation-error) (* 1/4 shifted-error) (* 1/4 center-error)
                    (* (+ coefficient-error approximation-error) step)))
         (other-radius (* 2 (+ -1 (lw-euler-uniform-coefficient-cap rate height radius) approximation-error) step step))))
  :in-theory (union-theories
   '(lw-complex-euler-coefficient-value lw-complex-scale-zero lw-complex-sub-zero lw-complexp lw-equ-left-commutes lw-equ-left-distributes lw-equ-fold-constants lw-equ-times-negative lw-equ-negative-times lw-equ-zero-times lw-equ-minus-one lw-equ-double-negative lw-equ-add-cancel lw-equ-double lw-equ-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-euler-normalized-quadratic-increment
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate)
               (lw-complex-diskp point step) (<= step 1/2)
               (rationalp shifted-error) (< 0 shifted-error)
               (rationalp center-error) (< 0 center-error)
               (rationalp coefficient-error) (< 0 coefficient-error))
  (lw-complex-diskp (lw-complex-linear-remainder (lw-complex-euler-continuation-value (+ rate (car (lw-complex-scale radius point))) (+ height (cdr (lw-complex-scale radius point))) shifted-error) (lw-complex-euler-continuation-value rate height center-error) (lw-complex-euler-coefficient-value rate height radius 1 coefficient-error) point) (+ (* 2 (+ -1 (lw-euler-uniform-coefficient-cap rate height radius)) step step) (* 1/4 shifted-error) (* 1/4 center-error) (* coefficient-error step))))
 :hints (("Goal"
  :cases ((lw-complex-diskp (lw-complex-linear-remainder (lw-complex-euler-continuation-value (+ rate (car (lw-complex-scale radius point))) (+ height (cdr (lw-complex-scale radius point))) shifted-error) (lw-complex-euler-continuation-value rate height center-error) (lw-complex-euler-coefficient-value rate height radius 1 coefficient-error) point) (+ (* 2 (+ -1 (lw-euler-uniform-coefficient-cap rate height radius)) step step) (* 1/4 shifted-error) (* 1/4 center-error) (* coefficient-error step))))
  :use (lw-equ-point-data lw-euler-uniform-coefficient-cap-valid
        (:instance lw-complex-euler-coefficient-value-rational (index 1) (error coefficient-error))
        (:instance lw-complex-euler-continuation-value-rational
         (rate (+ rate (car (lw-complex-scale radius point)))) (height (+ height (cdr (lw-complex-scale radius point)))) (error shifted-error))
        (:instance lw-complex-euler-continuation-value-rational (error center-error))
        (:instance lw-complex-linear-remainder-rational (value (lw-complex-euler-continuation-value (+ rate (car (lw-complex-scale radius point))) (+ height (cdr (lw-complex-scale radius point))) shifted-error)) (anchor (lw-complex-euler-continuation-value rate height center-error)) (slope (lw-complex-euler-coefficient-value rate height radius 1 coefficient-error)))
        (:instance lw-complex-disk-gap-refinement-excludes (point (lw-complex-linear-remainder (lw-complex-euler-continuation-value (+ rate (car (lw-complex-scale radius point))) (+ height (cdr (lw-complex-scale radius point))) shifted-error) (lw-complex-euler-continuation-value rate height center-error) (lw-complex-euler-coefficient-value rate height radius 1 coefficient-error) point)) (radius (+ (* 2 (+ -1 (lw-euler-uniform-coefficient-cap rate height radius)) step step) (* 1/4 shifted-error) (* 1/4 center-error) (* coefficient-error step))) (cost (+ 2 step (* 2 step step))))
        (:instance lw-complex-euler-normalized-quadratic-with-margin
         (approximation-error (lw-disk-gap-refinement (lw-complex-linear-remainder (lw-complex-euler-continuation-value (+ rate (car (lw-complex-scale radius point))) (+ height (cdr (lw-complex-scale radius point))) shifted-error) (lw-complex-euler-continuation-value rate height center-error) (lw-complex-euler-coefficient-value rate height radius 1 coefficient-error) point) (+ (* 2 (+ -1 (lw-euler-uniform-coefficient-cap rate height radius)) step step) (* 1/4 shifted-error) (* 1/4 center-error) (* coefficient-error step)) (+ 2 step (* 2 step step))))))
  :in-theory (union-theories
   '( lw-equ-left-commutes lw-equ-left-distributes lw-equ-fold-constants lw-equ-times-negative lw-equ-negative-times lw-equ-zero-times lw-equ-minus-one lw-equ-double-negative lw-equ-add-cancel lw-equ-double lw-equ-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp t :do-not-induct t)))

(local (defthm lw-equ-scale-product
 (implies (and (rationalp a) (rationalp b) (lw-complexp left) (lw-complexp right))
  (equal (lw-complex-mul (lw-complex-scale a left) (lw-complex-scale b right))
         (lw-complex-scale (* a b) (lw-complex-mul left right))))
 :hints (("Goal" :in-theory (union-theories
   '(lw-complexp lw-complex-mul lw-complex-scale lw-equ-left-commutes lw-equ-left-distributes lw-equ-fold-constants lw-equ-times-negative lw-equ-negative-times lw-equ-zero-times lw-equ-minus-one lw-equ-double-negative lw-equ-add-cancel lw-equ-double lw-equ-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))))))

(local (defthm lw-equ-unscale-product
 (implies (and (rationalp radius) (< 0 radius) (lw-complexp slope) (lw-complexp point))
  (equal (lw-complex-mul (lw-complex-scale (/ radius) slope) (lw-complex-scale radius point))
         (lw-complex-mul slope point)))
 :hints (("Goal"
  :use ((:instance lw-equ-scale-product (a (/ radius)) (b radius) (left slope) (right point))
        (:instance inverse-of-* (x radius))
        (:instance lw-complex-operations-rational (left slope) (right point) (factor 1)))
  :in-theory (union-theories
   '(lw-complex-scale-one lw-equ-left-commutes lw-equ-left-distributes lw-equ-fold-constants lw-equ-times-negative lw-equ-negative-times lw-equ-zero-times lw-equ-minus-one lw-equ-double-negative lw-equ-add-cancel lw-equ-double lw-equ-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t))))

(local (defthm lw-equ-first-power
 (implies (rationalp radius) (equal (lw-rational-power radius 1) radius))
 :hints (("Goal" :expand ((lw-rational-power radius 1) (lw-rational-power radius 0))
  :in-theory (union-theories
   '( lw-equ-left-commutes lw-equ-left-distributes lw-equ-fold-constants lw-equ-times-negative lw-equ-negative-times lw-equ-zero-times lw-equ-minus-one lw-equ-double-negative lw-equ-add-cancel lw-equ-double lw-equ-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))))))

(local (defthm lw-equ-local-slope-product
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate) (lw-complexp point) (rationalp derivative-error) (< 0 derivative-error))
  (equal (lw-complex-mul (lw-complex-euler-local-coefficient-value rate height radius 1 derivative-error) (lw-complex-scale radius point)) (lw-complex-mul (lw-complex-euler-coefficient-value rate height radius 1 (lw-euler-local-coefficient-request radius 1 derivative-error)) point)))
 :hints (("Goal"
  :use ((:instance lw-euler-local-coefficient-request-valid (index 1) (error derivative-error))
        (:instance lw-complex-euler-coefficient-value-rational (index 1) (error (lw-euler-local-coefficient-request radius 1 derivative-error))))
  :in-theory (union-theories
   '(lw-complex-euler-local-coefficient-value lw-equ-first-power lw-equ-unscale-product lw-equ-left-commutes lw-equ-left-distributes lw-equ-fold-constants lw-equ-times-negative lw-equ-negative-times lw-equ-zero-times lw-equ-minus-one lw-equ-double-negative lw-equ-add-cancel lw-equ-double lw-equ-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t))))

(defthm lw-complex-euler-scaled-quadratic-increment
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate) (lw-complex-diskp point step) (<= step 1/2)
               (rationalp shifted-error) (< 0 shifted-error) (rationalp center-error) (< 0 center-error)
               (rationalp derivative-error) (< 0 derivative-error))
  (lw-complex-diskp (lw-complex-linear-remainder (lw-complex-euler-continuation-value (+ rate (car (lw-complex-scale radius point))) (+ height (cdr (lw-complex-scale radius point))) shifted-error) (lw-complex-euler-continuation-value rate height center-error) (lw-complex-euler-local-coefficient-value rate height radius 1 derivative-error) (lw-complex-scale radius point))
   (+ (* 2 (+ -1 (lw-euler-uniform-coefficient-cap rate height radius)) step step) (* 1/4 shifted-error) (* 1/4 center-error) (* derivative-error radius step))))
 :hints (("Goal"
  :use (lw-equ-point-data lw-euler-uniform-coefficient-cap-valid
        (:instance lw-euler-local-coefficient-request-valid (index 1) (error derivative-error))
        (:instance lw-complex-euler-normalized-quadratic-increment (coefficient-error (lw-euler-local-coefficient-request radius 1 derivative-error)))
        (:instance lw-equ-multiply-order (a (lw-euler-local-coefficient-request radius 1 derivative-error)) (b (* derivative-error (lw-rational-power radius 1))) (factor step))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-linear-remainder (lw-complex-euler-continuation-value (+ rate (car (lw-complex-scale radius point))) (+ height (cdr (lw-complex-scale radius point))) shifted-error) (lw-complex-euler-continuation-value rate height center-error) (lw-complex-euler-local-coefficient-value rate height radius 1 derivative-error) (lw-complex-scale radius point)))
         (radius (+ (* 2 (+ -1 (lw-euler-uniform-coefficient-cap rate height radius)) step step) (* 1/4 shifted-error) (* 1/4 center-error) (* (lw-euler-local-coefficient-request radius 1 derivative-error) step)))
         (cap (+ (* 2 (+ -1 (lw-euler-uniform-coefficient-cap rate height radius)) step step) (* 1/4 shifted-error) (* 1/4 center-error) (* derivative-error radius step)))))
  :in-theory (union-theories
   '(lw-complex-linear-remainder lw-equ-local-slope-product lw-equ-first-power lw-equ-left-commutes lw-equ-left-distributes lw-equ-fold-constants lw-equ-times-negative lw-equ-negative-times lw-equ-zero-times lw-equ-minus-one lw-equ-double-negative lw-equ-add-cancel lw-equ-double lw-equ-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(local (defthm lw-equ-rescale-point
 (implies (and (rationalp radius) (< 0 radius) (lw-complexp point))
  (equal (lw-complex-scale radius (lw-complex-scale (/ radius) point)) point))
 :hints (("Goal"
  :use ((:instance inverse-of-* (x radius)))
  :in-theory (union-theories
   '(lw-complex-scale-compose lw-complex-scale-one lw-equ-left-commutes lw-equ-left-distributes lw-equ-fold-constants lw-equ-times-negative lw-equ-negative-times lw-equ-zero-times lw-equ-minus-one lw-equ-double-negative lw-equ-add-cancel lw-equ-double lw-equ-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t))))

(local (defthm lw-equ-physical-point-data
 (implies (and (rationalp radius) (< 0 radius) (lw-complex-diskp offset delta) (<= delta (/ radius 2)))
  (and (lw-complexp offset) (rationalp delta) (<= 0 delta)
       (lw-complex-diskp (lw-complex-scale (/ radius) offset) (* delta (/ radius)))
       (rationalp (* delta (/ radius))) (<= 0 (* delta (/ radius))) (<= (* delta (/ radius)) 1/2)))
 :hints (("Goal"
  :use ((:instance lw-complex-disk-data (point offset) (radius delta))
        (:instance lw-complex-scale-disk (point offset) (radius delta) (factor (/ radius)))
        (:instance lw-positive-division-bound (numerator delta) (divisor radius) (bound 1/2)))
  :in-theory (union-theories
   '(abs lw-equ-left-commutes lw-equ-left-distributes lw-equ-fold-constants lw-equ-times-negative lw-equ-negative-times lw-equ-zero-times lw-equ-minus-one lw-equ-double-negative lw-equ-add-cancel lw-equ-double lw-equ-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(defun lw-euler-derivative-curvature (rate height radius)
 (* 2 (+ -1 (lw-euler-uniform-coefficient-cap rate height radius)) (/ radius) (/ radius)))

(local (in-theory (disable lw-euler-derivative-curvature)))

(defthm lw-complex-euler-quadratic-increment
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate) (lw-complex-diskp offset delta) (<= delta (/ radius 2))
               (rationalp shifted-error) (< 0 shifted-error) (rationalp center-error) (< 0 center-error)
               (rationalp derivative-error) (< 0 derivative-error))
  (lw-complex-diskp
   (lw-complex-linear-remainder
    (lw-complex-euler-continuation-value (+ rate (car offset)) (+ height (cdr offset)) shifted-error)
    (lw-complex-euler-continuation-value rate height center-error)
    (lw-complex-euler-local-coefficient-value rate height radius 1 derivative-error) offset)
   (+ (* (lw-euler-derivative-curvature rate height radius) delta delta)
      (* 1/4 shifted-error) (* 1/4 center-error) (* derivative-error delta))))
 :hints (("Goal"
  :use (lw-equ-physical-point-data
        (:instance lw-complex-euler-scaled-quadratic-increment
         (point (lw-complex-scale (/ radius) offset)) (step (* delta (/ radius))))
        (:instance lw-equ-rescale-point (point offset))
        (:instance lw-equ-inverse-factor (divisor radius) (coefficient delta))
        (:instance lw-equ-inverse-factor (divisor radius) (coefficient (* delta derivative-error))))
  :in-theory (union-theories
   '(lw-euler-derivative-curvature lw-equ-rescale-point lw-equ-left-commutes lw-equ-left-distributes lw-equ-fold-constants lw-equ-times-negative lw-equ-negative-times lw-equ-zero-times lw-equ-minus-one lw-equ-double-negative lw-equ-add-cancel lw-equ-double lw-equ-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))



