; A midpoint clearance certifies an entire rational circular arc.
(in-package "ACL2")
(include-book "complex-circles")
(include-book "euler-contour-patches")
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
(local (in-theory (disable lw-euler-value-clearance-check
 lw-euler-local-normalized-radius lw-euler-local-normalized-cap lw-euler-local-normalized-anchor
 lw-complex-segment)))
(local (defthm lw-eca-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-eca-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-eca-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-eca-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-eca-times-negative (a b) (b a)))
                 :in-theory (disable lw-eca-times-negative)))))

(local (defthm lw-eca-zero-times (equal (* 0 a) 0)))

(local (defthm lw-eca-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-eca-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-eca-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-eca-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-eca-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-eca-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-eca-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-eca-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-eca-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-eca-left-commutes)))))
(defun lw-euler-circle-arc (sign left right patch) (list sign left right patch))
(defun lw-euler-circle-arc-sign (arc) (nth 0 arc))
(defun lw-euler-circle-arc-left (arc) (nth 1 arc))
(defun lw-euler-circle-arc-right (arc) (nth 2 arc))
(defun lw-euler-circle-arc-patch (arc) (nth 3 arc))
(defun lw-euler-circle-arc-midpoint (arc)
 (* 1/2 (+ (lw-euler-circle-arc-left arc) (lw-euler-circle-arc-right arc))))
(defun lw-euler-circle-arc-reach (radius arc)
 (* 1/2 radius (- (lw-euler-circle-arc-right arc) (lw-euler-circle-arc-left arc))))
(defun lw-euler-circle-arc-point (center radius arc parameter)
 (lw-complex-circle-point center radius (lw-euler-circle-arc-sign arc) parameter))
(defun lw-euler-circle-arcp (center radius arc)
 (and (lw-complexp center) (rationalp radius) (< 0 radius)
      (true-listp arc) (equal (len arc) 4)
      (or (equal (lw-euler-circle-arc-sign arc) 1) (equal (lw-euler-circle-arc-sign arc) -1))
      (rationalp (lw-euler-circle-arc-left arc)) (rationalp (lw-euler-circle-arc-right arc))
      (<= -2 (lw-euler-circle-arc-left arc))
      (<= (lw-euler-circle-arc-left arc) (lw-euler-circle-arc-right arc))
      (<= (lw-euler-circle-arc-right arc) 2)
      (lw-euler-contour-patchp (lw-euler-circle-arc-patch arc))
      (<= 0 (- (lw-euler-contour-radius (lw-euler-circle-arc-patch arc)) (lw-euler-circle-arc-reach radius arc)))
      (lw-complex-diskp
       (lw-complex-sub (lw-euler-circle-arc-point center radius arc (lw-euler-circle-arc-midpoint arc))
                       (lw-euler-contour-center (lw-euler-circle-arc-patch arc)))
       (- (lw-euler-contour-radius (lw-euler-circle-arc-patch arc)) (lw-euler-circle-arc-reach radius arc)))))
(local (in-theory (disable lw-euler-circle-arc lw-euler-circle-arc-sign lw-euler-circle-arc-left lw-euler-circle-arc-right lw-euler-circle-arc-patch lw-euler-circle-arc-midpoint lw-euler-circle-arc-reach lw-euler-circle-arc-point lw-euler-circle-arcp lw-euler-contour-patchp lw-euler-contour-pointp lw-euler-contour-radius lw-euler-contour-center lw-euler-contour-cap lw-euler-contour-anchor)))
(local (defthm lw-eca-midpoint-distance
 (implies (and (rationalp left) (rationalp right) (rationalp parameter) (<= left parameter) (<= parameter right))
 (<= (abs (- parameter (* 1/2 (+ left right)))) (* 1/2 (- right left))))
 :hints (("Goal" :in-theory (union-theories
 '(abs lw-eca-left-commutes lw-eca-left-distributes lw-eca-fold-constants lw-eca-times-negative lw-eca-negative-times lw-eca-zero-times lw-eca-minus-one lw-eca-double-negative lw-eca-add-cancel lw-eca-double lw-eca-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-euler-circle-arc-data
 (implies (lw-euler-circle-arcp center radius arc)
 (and (lw-complexp center) (rationalp radius) (< 0 radius)
      (or (equal (lw-euler-circle-arc-sign arc) 1) (equal (lw-euler-circle-arc-sign arc) -1))
      (rationalp (lw-euler-circle-arc-left arc)) (rationalp (lw-euler-circle-arc-right arc)) (<= -2 (lw-euler-circle-arc-left arc)) (<= (lw-euler-circle-arc-left arc) (lw-euler-circle-arc-right arc)) (<= (lw-euler-circle-arc-right arc) 2)
      (rationalp (lw-euler-circle-arc-midpoint arc)) (<= (lw-euler-circle-arc-left arc) (lw-euler-circle-arc-midpoint arc)) (<= (lw-euler-circle-arc-midpoint arc) (lw-euler-circle-arc-right arc))
      (rationalp (lw-euler-circle-arc-reach radius arc)) (<= 0 (lw-euler-circle-arc-reach radius arc))
      (lw-euler-contour-patchp (lw-euler-circle-arc-patch arc))
      (lw-complexp (lw-euler-circle-arc-point center radius arc (lw-euler-circle-arc-midpoint arc)))
      (lw-complex-diskp (lw-complex-sub (lw-euler-circle-arc-point center radius arc (lw-euler-circle-arc-midpoint arc)) (lw-euler-contour-center (lw-euler-circle-arc-patch arc))) (- (lw-euler-contour-radius (lw-euler-circle-arc-patch arc)) (lw-euler-circle-arc-reach radius arc)))))
 :hints (("Goal"
 :use ((:instance lw-complex-circle-point-rational (sign (lw-euler-circle-arc-sign arc)) (parameter (lw-euler-circle-arc-midpoint arc))))
 :in-theory (union-theories
 '(lw-euler-circle-arcp lw-euler-circle-arc-midpoint lw-euler-circle-arc-reach lw-euler-circle-arc-point lw-eca-left-commutes lw-eca-left-distributes lw-eca-fold-constants lw-eca-times-negative lw-eca-negative-times lw-eca-zero-times lw-eca-minus-one lw-eca-double-negative lw-eca-add-cancel lw-eca-double lw-eca-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp t :do-not-induct t)))

(defthm lw-euler-circle-arc-point-rational
 (implies (and (lw-euler-circle-arcp center radius arc) (rationalp parameter))
 (lw-complexp (lw-euler-circle-arc-point center radius arc parameter)))
 :hints (("Goal" :use (lw-euler-circle-arc-data
       (:instance lw-complex-circle-point-rational (sign (lw-euler-circle-arc-sign arc))))
 :in-theory (union-theories
 '(lw-euler-circle-arc-point lw-eca-left-commutes lw-eca-left-distributes lw-eca-fold-constants lw-eca-times-negative lw-eca-negative-times lw-eca-zero-times lw-eca-minus-one lw-eca-double-negative lw-eca-add-cancel lw-eca-double lw-eca-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-euler-circle-arc-midpoint-bound
 (implies (and (lw-euler-circle-arcp center radius arc) (rationalp parameter) (<= (lw-euler-circle-arc-left arc) parameter) (<= parameter (lw-euler-circle-arc-right arc)))
 (lw-complex-diskp (lw-complex-sub (lw-euler-circle-arc-point center radius arc parameter) (lw-euler-circle-arc-point center radius arc (lw-euler-circle-arc-midpoint arc))) (lw-euler-circle-arc-reach radius arc)))
 :hints (("Goal"
 :use (lw-euler-circle-arc-data
       (:instance lw-eca-midpoint-distance (left (lw-euler-circle-arc-left arc)) (right (lw-euler-circle-arc-right arc)))
       (:instance lw-eca-multiply-order (a (abs (- parameter (lw-euler-circle-arc-midpoint arc)))) (b (* 1/2 (- (lw-euler-circle-arc-right arc) (lw-euler-circle-arc-left arc)))) (factor radius))
       (:instance lw-complex-circle-point-lipschitz (sign (lw-euler-circle-arc-sign arc)) (left parameter) (right (lw-euler-circle-arc-midpoint arc)))
       (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-euler-circle-arc-point center radius arc parameter) (lw-euler-circle-arc-point center radius arc (lw-euler-circle-arc-midpoint arc)))) (radius (* radius (abs (- parameter (lw-euler-circle-arc-midpoint arc))))) (cap (lw-euler-circle-arc-reach radius arc))))
 :in-theory (union-theories
 '(abs lw-euler-circle-arc-point lw-euler-circle-arc-midpoint lw-euler-circle-arc-reach lw-eca-left-commutes lw-eca-left-distributes lw-eca-fold-constants lw-eca-times-negative lw-eca-negative-times lw-eca-zero-times lw-eca-minus-one lw-eca-double-negative lw-eca-add-cancel lw-eca-double lw-eca-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-euler-circle-arc-coverage
 (implies (and (lw-euler-circle-arcp center radius arc) (rationalp parameter) (<= (lw-euler-circle-arc-left arc) parameter) (<= parameter (lw-euler-circle-arc-right arc)))
 (lw-euler-contour-pointp (lw-euler-circle-arc-patch arc) (lw-euler-circle-arc-point center radius arc parameter)))
 :hints (("Goal"
 :use (lw-euler-circle-arc-data lw-euler-circle-arc-point-rational lw-euler-circle-arc-midpoint-bound
       (:instance lw-euler-contour-patch-data (patch (lw-euler-circle-arc-patch arc)))
       (:instance lw-complex-difference-triangle (left (lw-euler-circle-arc-point center radius arc parameter)) (middle (lw-euler-circle-arc-point center radius arc (lw-euler-circle-arc-midpoint arc))) (right (lw-euler-contour-center (lw-euler-circle-arc-patch arc)))
        (radius (lw-euler-circle-arc-reach radius arc)) (other-radius (- (lw-euler-contour-radius (lw-euler-circle-arc-patch arc)) (lw-euler-circle-arc-reach radius arc)))))
 :in-theory (union-theories
 '(lw-euler-contour-pointp lw-eca-left-commutes lw-eca-left-distributes lw-eca-fold-constants lw-eca-times-negative lw-eca-negative-times lw-eca-zero-times lw-eca-minus-one lw-eca-double-negative lw-eca-add-cancel lw-eca-double lw-eca-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-euler-circle-arc-shifted-check
 (implies (and (lw-euler-circle-arcp center radius arc) (rationalp parameter) (<= (lw-euler-circle-arc-left arc) parameter) (<= parameter (lw-euler-circle-arc-right arc)))
 (and (lw-complexp (lw-euler-circle-arc-point center radius arc parameter)) (rationalp (car (lw-euler-circle-arc-point center radius arc parameter))) (< 0 (car (lw-euler-circle-arc-point center radius arc parameter))) (rationalp (cdr (lw-euler-circle-arc-point center radius arc parameter)))
      (lw-euler-value-clearance-check (car (lw-euler-circle-arc-point center radius arc parameter)) (cdr (lw-euler-circle-arc-point center radius arc parameter)) (lw-euler-contour-anchor (lw-euler-circle-arc-patch arc)))))
 :hints (("Goal" :use (lw-euler-circle-arc-data lw-euler-circle-arc-coverage
       (:instance lw-euler-contour-point-data (patch (lw-euler-circle-arc-patch arc)) (point (lw-euler-circle-arc-point center radius arc parameter))))
 :in-theory (union-theories
 '( lw-eca-left-commutes lw-eca-left-distributes lw-eca-fold-constants lw-eca-times-negative lw-eca-negative-times lw-eca-zero-times lw-eca-minus-one lw-eca-double-negative lw-eca-add-cancel lw-eca-double lw-eca-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

