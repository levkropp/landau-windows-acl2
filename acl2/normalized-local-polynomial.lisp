; Polynomial normalization away from the two displayed linear denominators.
(in-package "ACL2")
(include-book "linear-inverse-polynomials")
(include-book "polynomial-subtraction")
(include-book "polynomial-product")
(include-book "complex-normalized-extension")
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
(local (in-theory (disable lw-linear-polynomial lw-linear-inverse-polynomial lw-linear-inverse-cap
 lw-polynomial-subtract lw-polynomial-product lw-polynomial-multiply-coefficients
 lw-complex-polynomial lw-complex-normalized-euler lw-complex-quotient)))
(local (defthm lw-nlp-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-nlp-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-nlp-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-nlp-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-nlp-times-negative (a b) (b a)))
                 :in-theory (disable lw-nlp-times-negative)))))

(local (defthm lw-nlp-zero-times (equal (* 0 a) 0)))

(local (defthm lw-nlp-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-nlp-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-nlp-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-nlp-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-nlp-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-nlp-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-nlp-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-nlp-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-nlp-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-nlp-left-commutes)))))

(local (defthm lw-nlp-real-pair
 (implies (rationalp gamma) (lw-complexp (cons gamma 0)))
 :hints (("Goal" :in-theory (union-theories
 '(lw-complexp lw-nlp-left-commutes lw-nlp-left-distributes lw-nlp-fold-constants lw-nlp-times-negative lw-nlp-negative-times lw-nlp-zero-times lw-nlp-minus-one lw-nlp-double-negative lw-nlp-add-cancel lw-nlp-double lw-nlp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-nlp-real-multiple
 (implies (and (rationalp gamma) (lw-complexp value))
 (and (equal (lw-complex-mul (cons gamma 0) value) (lw-complex-scale gamma value))
      (equal (lw-complex-mul value (cons gamma 0)) (lw-complex-scale gamma value))))
 :hints (("Goal" :in-theory (union-theories
 '(lw-complexp lw-complex-mul lw-complex-scale lw-nlp-left-commutes lw-nlp-left-distributes lw-nlp-fold-constants lw-nlp-times-negative lw-nlp-negative-times lw-nlp-zero-times lw-nlp-minus-one lw-nlp-double-negative lw-nlp-add-cancel lw-nlp-double lw-nlp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-nlp-shift-sum
 (implies (and (lw-complexp anchor) (lw-complexp point))
 (equal (lw-complex-add (cons 1 0) (lw-complex-add (lw-complex-sub anchor (cons 1 0)) point)) (lw-complex-add anchor point)))
 :hints (("Goal" :in-theory (union-theories
 '(lw-complexp lw-complex-add lw-complex-sub lw-nlp-left-commutes lw-nlp-left-distributes lw-nlp-fold-constants lw-nlp-times-negative lw-nlp-negative-times lw-nlp-zero-times lw-nlp-minus-one lw-nlp-double-negative lw-nlp-add-cancel lw-nlp-double lw-nlp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defun lw-normalized-local-point-cap (anchor radius) (+ 1 (lw-complex-l1 anchor) radius))
(defun lw-normalized-local-numerator-cap (anchor radius log-cap)
 (+ log-cap (* 2 (lw-normalized-local-point-cap anchor radius))))
(defun lw-normalized-local-inverse-cost (anchor radius log-cap)
 (+ 1 (* (lw-normalized-local-numerator-cap anchor radius log-cap)
         (+ (/ (* 1/4 (lw-complex-l1 (lw-complex-sub anchor (cons 1 0)))))
            (* 4 (lw-linear-inverse-cap anchor))))))
(defun lw-normalized-local-transport-cost (anchor radius)
 (* (/ (* 1/4 (lw-complex-l1 anchor)))
    (/ (* 1/4 (lw-complex-l1 (lw-complex-sub anchor (cons 1 0)))))
    (+ 1 (lw-normalized-local-point-cap anchor radius))))
(defun lw-normalized-local-cap (anchor radius log-cap)
 (+ (* 4 (lw-linear-inverse-cap anchor))
    (* (lw-normalized-local-numerator-cap anchor radius log-cap)
       (* 4 (lw-linear-inverse-cap anchor))
       (* 4 (lw-linear-inverse-cap (lw-complex-sub anchor (cons 1 0)))))))

(local (in-theory (disable lw-normalized-local-point-cap lw-normalized-local-numerator-cap
 lw-normalized-local-inverse-cost lw-normalized-local-transport-cost lw-normalized-local-cap)))

(defthm lw-normalized-local-cap-data
 (implies (and (lw-complexp anchor) (not (equal anchor (cons 0 0)))
  (not (equal (lw-complex-sub anchor (cons 1 0)) (cons 0 0))) (rationalp radius) (<= 0 radius) (rationalp log-cap) (<= 0 log-cap))
 (and (rationalp (lw-normalized-local-point-cap anchor radius)) (< 0 (lw-normalized-local-point-cap anchor radius)) (rationalp (lw-normalized-local-numerator-cap anchor radius log-cap)) (< 0 (lw-normalized-local-numerator-cap anchor radius log-cap))
      (rationalp (lw-normalized-local-inverse-cost anchor radius log-cap)) (< 0 (lw-normalized-local-inverse-cost anchor radius log-cap)) (rationalp (lw-normalized-local-transport-cost anchor radius)) (< 0 (lw-normalized-local-transport-cost anchor radius))
      (rationalp (lw-normalized-local-cap anchor radius log-cap)) (< 0 (lw-normalized-local-cap anchor radius log-cap))))
 :hints (("Goal"
 :use ((:instance lw-complex-ring-rational (left anchor) (right (cons 1 0)))
       (:instance lw-linear-inverse-cap-data)
       (:instance lw-linear-inverse-cap-data (anchor (lw-complex-sub anchor (cons 1 0))))
       (:instance lw-reciprocal-positive (value (* 1/4 (lw-complex-l1 anchor))))
       (:instance lw-reciprocal-positive (value (* 1/4 (lw-complex-l1 (lw-complex-sub anchor (cons 1 0))))))
       (:instance lw-nlp-positive-product (a (lw-normalized-local-numerator-cap anchor radius log-cap)) (b (+ (/ (* 1/4 (lw-complex-l1 (lw-complex-sub anchor (cons 1 0))))) (* 4 (lw-linear-inverse-cap anchor)))))
       (:instance lw-nlp-positive-product (a (/ (* 1/4 (lw-complex-l1 anchor)))) (b (/ (* 1/4 (lw-complex-l1 (lw-complex-sub anchor (cons 1 0)))))))
       (:instance lw-nlp-positive-product (a (* (/ (* 1/4 (lw-complex-l1 anchor))) (/ (* 1/4 (lw-complex-l1 (lw-complex-sub anchor (cons 1 0))))))) (b (+ 1 (lw-normalized-local-point-cap anchor radius))))
       (:instance lw-nlp-positive-product (a (lw-normalized-local-numerator-cap anchor radius log-cap)) (b (* 4 (lw-linear-inverse-cap anchor))))
       (:instance lw-nlp-positive-product (a (* (lw-normalized-local-numerator-cap anchor radius log-cap) (* 4 (lw-linear-inverse-cap anchor)))) (b (* 4 (lw-linear-inverse-cap (lw-complex-sub anchor (cons 1 0)))))))
 :in-theory (union-theories
 '(lw-normalized-local-point-cap lw-normalized-local-numerator-cap lw-normalized-local-inverse-cost lw-normalized-local-transport-cost lw-normalized-local-cap (:executable-counterpart lw-complexp) lw-nlp-left-commutes lw-nlp-left-distributes lw-nlp-fold-constants lw-nlp-times-negative lw-nlp-negative-times lw-nlp-zero-times lw-nlp-minus-one lw-nlp-double-negative lw-nlp-add-cancel lw-nlp-double lw-nlp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t)))

(defthm lw-normalized-local-point-data
 (implies (and (lw-complexp anchor) (not (equal anchor (cons 0 0))) (not (equal (lw-complex-sub anchor (cons 1 0)) (cons 0 0)))
 (rationalp radius) (<= 0 radius) (<= radius (* 1/4 (lw-complex-l1 anchor)))
 (<= radius (* 1/4 (lw-complex-l1 (lw-complex-sub anchor (cons 1 0))))) (lw-complex-diskp point radius))
 (and (lw-complexp point) (lw-complexp (lw-complex-add anchor point)) (not (equal (lw-complex-add anchor point) (cons 0 0)))
      (lw-complexp (lw-complex-add (lw-complex-sub anchor (cons 1 0)) point)) (not (equal (lw-complex-add (lw-complex-sub anchor (cons 1 0)) point) (cons 0 0)))
      (lw-complex-diskp (lw-complex-add anchor point) (lw-normalized-local-point-cap anchor radius))
      (lw-complex-diskp (lw-complex-reciprocal (lw-complex-add anchor point)) (/ (* 1/4 (lw-complex-l1 anchor))))
      (lw-complex-diskp (lw-complex-reciprocal (lw-complex-add (lw-complex-sub anchor (cons 1 0)) point)) (/ (* 1/4 (lw-complex-l1 (lw-complex-sub anchor (cons 1 0))))))
      (lw-complex-diskp (lw-complex-reciprocal (lw-complex-mul (lw-complex-add anchor point) (lw-complex-add (lw-complex-sub anchor (cons 1 0)) point))) (* (/ (* 1/4 (lw-complex-l1 anchor))) (/ (* 1/4 (lw-complex-l1 (lw-complex-sub anchor (cons 1 0)))))))))
 :hints (("Goal"
 :use ((:instance lw-complex-disk-data)
       (:instance lw-complex-ring-rational (left anchor) (right (cons 1 0)))
       (:instance lw-linear-inverse-cap-data)
       (:instance lw-linear-inverse-cap-data (anchor (lw-complex-sub anchor (cons 1 0))))
       lw-linear-denominator-clearance
       (:instance lw-linear-denominator-clearance (anchor (lw-complex-sub anchor (cons 1 0))))
       (:instance lw-complex-l1-clearance (point anchor))
       (:instance lw-complex-add-disk (left anchor) (right point) (radius (lw-complex-l1 anchor)) (other-radius radius))
       (:instance lw-complex-disk-enlarge (point (lw-complex-add anchor point)) (radius (+ (lw-complex-l1 anchor) radius)) (cap (lw-normalized-local-point-cap anchor radius)))
       (:instance lw-complex-reciprocal-product (a (lw-complex-add anchor point)) (b (lw-complex-add (lw-complex-sub anchor (cons 1 0)) point)))
       (:instance lw-complex-mul-disk (left (lw-complex-reciprocal (lw-complex-add anchor point))) (right (lw-complex-reciprocal (lw-complex-add (lw-complex-sub anchor (cons 1 0)) point))) (radius (/ (* 1/4 (lw-complex-l1 anchor)))) (other-radius (/ (* 1/4 (lw-complex-l1 (lw-complex-sub anchor (cons 1 0))))))))
 :in-theory (union-theories
 '(lw-normalized-local-point-cap lw-complex-reciprocal-product (:executable-counterpart lw-complexp) lw-nlp-left-commutes lw-nlp-left-distributes lw-nlp-fold-constants lw-nlp-times-negative lw-nlp-negative-times lw-nlp-zero-times lw-nlp-minus-one lw-nlp-double-negative lw-nlp-add-cancel lw-nlp-double lw-nlp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defun lw-normalized-local-numerator (anchor coefficients gamma)
 (lw-polynomial-subtract coefficients
  (lw-polynomial-multiply-coefficients (cons gamma 0) (lw-linear-polynomial anchor))))
(local (in-theory (disable lw-normalized-local-numerator)))

(defthm lw-normalized-local-numerator-valid
 (implies (and (lw-complexp anchor) (lw-complex-coefficientsp coefficients) (rationalp gamma))
 (lw-complex-coefficientsp (lw-normalized-local-numerator anchor coefficients gamma)))
 :hints (("Goal"
 :use (lw-linear-polynomial-valid
       (:instance lw-polynomial-multiply-coefficients-valid (coefficients (lw-linear-polynomial anchor)) (factor (cons gamma 0)))
       (:instance lw-polynomial-subtract-valid (left coefficients) (right (lw-polynomial-multiply-coefficients (cons gamma 0) (lw-linear-polynomial anchor)))))
 :in-theory (union-theories
 '(lw-normalized-local-numerator lw-nlp-real-pair lw-nlp-left-commutes lw-nlp-left-distributes lw-nlp-fold-constants lw-nlp-times-negative lw-nlp-negative-times lw-nlp-zero-times lw-nlp-minus-one lw-nlp-double-negative lw-nlp-add-cancel lw-nlp-double lw-nlp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-normalized-local-numerator-evaluation
 (implies (and (lw-complexp anchor) (lw-complexp point) (lw-complex-coefficientsp coefficients) (rationalp gamma))
 (equal (lw-complex-polynomial (lw-normalized-local-numerator anchor coefficients gamma) point 0) (lw-complex-sub (lw-complex-polynomial coefficients point 0) (lw-complex-scale gamma (lw-complex-add anchor point)))))
 :hints (("Goal"
 :use (lw-linear-polynomial-valid lw-linear-polynomial-evaluation
       (:instance lw-polynomial-multiply-coefficients-valid (coefficients (lw-linear-polynomial anchor)) (factor (cons gamma 0)))
       (:instance lw-polynomial-multiply-coefficients-evaluation (coefficients (lw-linear-polynomial anchor)) (factor (cons gamma 0)) (offset 0))
       (:instance lw-polynomial-subtract-evaluation (left coefficients) (right (lw-polynomial-multiply-coefficients (cons gamma 0) (lw-linear-polynomial anchor)))))
 :in-theory (union-theories
 '(lw-normalized-local-numerator lw-nlp-real-pair lw-nlp-real-multiple lw-complex-ring-rational lw-nlp-left-commutes lw-nlp-left-distributes lw-nlp-fold-constants lw-nlp-times-negative lw-nlp-negative-times lw-nlp-zero-times lw-nlp-minus-one lw-nlp-double-negative lw-nlp-add-cancel lw-nlp-double lw-nlp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defun lw-normalized-local-polynomial (anchor coefficients gamma error)
 (lw-polynomial-subtract (lw-linear-inverse-polynomial anchor error)
  (lw-polynomial-product (lw-normalized-local-numerator anchor coefficients gamma)
   (lw-polynomial-product (lw-linear-inverse-polynomial anchor error)
    (lw-linear-inverse-polynomial (lw-complex-sub anchor (cons 1 0)) error)))))
(local (in-theory (disable lw-normalized-local-polynomial)))

(defthm lw-normalized-local-polynomial-valid
 (implies (and (lw-complexp anchor) (lw-complex-coefficientsp coefficients) (rationalp gamma))
 (lw-complex-coefficientsp (lw-normalized-local-polynomial anchor coefficients gamma error)))
 :hints (("Goal"
 :use (lw-normalized-local-numerator-valid
       (:instance lw-complex-ring-rational (left anchor) (right (cons 1 0)))
       lw-linear-inverse-polynomial-valid
       (:instance lw-linear-inverse-polynomial-valid (anchor (lw-complex-sub anchor (cons 1 0))))
       (:instance lw-polynomial-product-valid (left (lw-linear-inverse-polynomial anchor error)) (right (lw-linear-inverse-polynomial (lw-complex-sub anchor (cons 1 0)) error)))
       (:instance lw-polynomial-product-valid (left (lw-normalized-local-numerator anchor coefficients gamma)) (right (lw-polynomial-product (lw-linear-inverse-polynomial anchor error) (lw-linear-inverse-polynomial (lw-complex-sub anchor (cons 1 0)) error))))
       (:instance lw-polynomial-subtract-valid (left (lw-linear-inverse-polynomial anchor error)) (right (lw-polynomial-product (lw-normalized-local-numerator anchor coefficients gamma) (lw-polynomial-product (lw-linear-inverse-polynomial anchor error) (lw-linear-inverse-polynomial (lw-complex-sub anchor (cons 1 0)) error))))))
 :in-theory (union-theories
 '(lw-normalized-local-polynomial (:executable-counterpart lw-complexp) lw-nlp-left-commutes lw-nlp-left-distributes lw-nlp-fold-constants lw-nlp-times-negative lw-nlp-negative-times lw-nlp-zero-times lw-nlp-minus-one lw-nlp-double-negative lw-nlp-add-cancel lw-nlp-double lw-nlp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-normalized-local-polynomial-evaluation
 (implies (and (lw-complexp anchor) (lw-complexp point) (lw-complex-coefficientsp coefficients) (rationalp gamma))
 (equal (lw-complex-polynomial (lw-normalized-local-polynomial anchor coefficients gamma error) point 0) (lw-complex-sub (lw-complex-polynomial (lw-linear-inverse-polynomial anchor error) point 0) (lw-complex-mul (lw-complex-polynomial (lw-normalized-local-numerator anchor coefficients gamma) point 0) (lw-complex-mul (lw-complex-polynomial (lw-linear-inverse-polynomial anchor error) point 0) (lw-complex-polynomial (lw-linear-inverse-polynomial (lw-complex-sub anchor (cons 1 0)) error) point 0))))))
 :hints (("Goal"
 :use (lw-normalized-local-numerator-valid
       (:instance lw-complex-ring-rational (left anchor) (right (cons 1 0)))
       lw-linear-inverse-polynomial-valid
       (:instance lw-linear-inverse-polynomial-valid (anchor (lw-complex-sub anchor (cons 1 0))))
       (:instance lw-polynomial-product-valid (left (lw-linear-inverse-polynomial anchor error)) (right (lw-linear-inverse-polynomial (lw-complex-sub anchor (cons 1 0)) error)))
       (:instance lw-polynomial-product-valid (left (lw-normalized-local-numerator anchor coefficients gamma)) (right (lw-polynomial-product (lw-linear-inverse-polynomial anchor error) (lw-linear-inverse-polynomial (lw-complex-sub anchor (cons 1 0)) error))))
       (:instance lw-polynomial-product-evaluation (left (lw-linear-inverse-polynomial anchor error)) (right (lw-linear-inverse-polynomial (lw-complex-sub anchor (cons 1 0)) error)))
       (:instance lw-polynomial-product-evaluation (left (lw-normalized-local-numerator anchor coefficients gamma)) (right (lw-polynomial-product (lw-linear-inverse-polynomial anchor error) (lw-linear-inverse-polynomial (lw-complex-sub anchor (cons 1 0)) error))))
       (:instance lw-polynomial-subtract-evaluation (left (lw-linear-inverse-polynomial anchor error)) (right (lw-polynomial-product (lw-normalized-local-numerator anchor coefficients gamma) (lw-polynomial-product (lw-linear-inverse-polynomial anchor error) (lw-linear-inverse-polynomial (lw-complex-sub anchor (cons 1 0)) error))))))
 :in-theory (union-theories
 '(lw-normalized-local-polynomial (:executable-counterpart lw-complexp) lw-nlp-left-commutes lw-nlp-left-distributes lw-nlp-fold-constants lw-nlp-times-negative lw-nlp-negative-times lw-nlp-zero-times lw-nlp-minus-one lw-nlp-double-negative lw-nlp-add-cancel lw-nlp-double lw-nlp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defun lw-complex-local-normalization (anchor point value gamma)
 (lw-complex-sub (lw-complex-reciprocal (lw-complex-add anchor point))
  (lw-complex-mul
   (lw-complex-sub value (lw-complex-scale gamma (lw-complex-add anchor point)))
   (lw-complex-mul (lw-complex-reciprocal (lw-complex-add anchor point))
    (lw-complex-reciprocal (lw-complex-add (lw-complex-sub anchor (cons 1 0)) point))))))
(local (in-theory (disable lw-complex-local-normalization)))

(defthm lw-complex-local-normalization-rational
 (implies (and (lw-complexp anchor) (lw-complexp point) (lw-complexp value) (rationalp gamma))
 (lw-complexp (lw-complex-local-normalization anchor point value gamma)))
 :hints (("Goal"
 :in-theory (union-theories
 '(lw-complex-local-normalization lw-complex-ring-rational lw-complex-reciprocal-rational lw-complex-scale-rational (:executable-counterpart lw-complexp) lw-nlp-left-commutes lw-nlp-left-distributes lw-nlp-fold-constants lw-nlp-times-negative lw-nlp-negative-times lw-nlp-zero-times lw-nlp-minus-one lw-nlp-double-negative lw-nlp-add-cancel lw-nlp-double lw-nlp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-complex-local-normalization-normalized
 (implies (and (lw-complexp anchor) (lw-complexp point) (lw-complexp value) (rationalp gamma)
  (not (equal (lw-complex-add anchor point) (cons 0 0))) (not (equal (lw-complex-add (lw-complex-sub anchor (cons 1 0)) point) (cons 0 0))))
 (equal (lw-complex-local-normalization anchor point value gamma) (lw-complex-normalized-euler (lw-complex-add (lw-complex-sub anchor (cons 1 0)) point) value (cons gamma 0))))
 :hints (("Goal"
 :use ((:instance lw-complex-reciprocal-product (a (lw-complex-add anchor point)) (b (lw-complex-add (lw-complex-sub anchor (cons 1 0)) point))))
 :in-theory (union-theories
 '(lw-complex-local-normalization lw-complex-normalized-euler lw-complex-quotient lw-nlp-shift-sum lw-nlp-real-pair lw-nlp-real-multiple lw-complex-reciprocal-product lw-complex-ring-rational (:executable-counterpart lw-complexp) lw-nlp-left-commutes lw-nlp-left-distributes lw-nlp-fold-constants lw-nlp-times-negative lw-nlp-negative-times lw-nlp-zero-times lw-nlp-minus-one lw-nlp-double-negative lw-nlp-add-cancel lw-nlp-double lw-nlp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-normalized-local-numerator-bound
 (implies (and (lw-complexp anchor) (not (equal anchor (cons 0 0))) (not (equal (lw-complex-sub anchor (cons 1 0)) (cons 0 0)))
 (rationalp radius) (<= 0 radius) (<= radius (* 1/4 (lw-complex-l1 anchor)))
 (<= radius (* 1/4 (lw-complex-l1 (lw-complex-sub anchor (cons 1 0))))) (lw-complex-diskp point radius) (lw-complex-coefficientsp coefficients)
 (rationalp log-cap) (<= 0 log-cap) (rationalp gamma) (<= (abs gamma) 2)
 (lw-complex-diskp (lw-complex-polynomial coefficients point 0) log-cap))
 (lw-complex-diskp (lw-complex-polynomial (lw-normalized-local-numerator anchor coefficients gamma) point 0) (lw-normalized-local-numerator-cap anchor radius log-cap)))
 :hints (("Goal"
 :use (lw-normalized-local-cap-data lw-normalized-local-point-data lw-normalized-local-numerator-evaluation
       (:instance lw-complex-scale-disk (point (lw-complex-add anchor point)) (factor gamma) (radius (lw-normalized-local-point-cap anchor radius)))
       (:instance lw-nlp-multiply-order (a (abs gamma)) (b 2) (factor (lw-normalized-local-point-cap anchor radius)))
       (:instance lw-complex-disk-enlarge (point (lw-complex-scale gamma (lw-complex-add anchor point))) (radius (* (abs gamma) (lw-normalized-local-point-cap anchor radius))) (cap (* 2 (lw-normalized-local-point-cap anchor radius))))
       (:instance lw-complex-sub-disk (left (lw-complex-polynomial coefficients point 0)) (right (lw-complex-scale gamma (lw-complex-add anchor point))) (radius log-cap) (other-radius (* 2 (lw-normalized-local-point-cap anchor radius)))))
 :in-theory (union-theories
 '(lw-normalized-local-numerator-cap abs lw-nlp-left-commutes lw-nlp-left-distributes lw-nlp-fold-constants lw-nlp-times-negative lw-nlp-negative-times lw-nlp-zero-times lw-nlp-minus-one lw-nlp-double-negative lw-nlp-add-cancel lw-nlp-double lw-nlp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-normalized-local-polynomial-bound
 (implies (and (lw-complexp anchor) (not (equal anchor (cons 0 0))) (not (equal (lw-complex-sub anchor (cons 1 0)) (cons 0 0)))
 (rationalp radius) (<= 0 radius) (<= radius (* 1/4 (lw-complex-l1 anchor)))
 (<= radius (* 1/4 (lw-complex-l1 (lw-complex-sub anchor (cons 1 0))))) (lw-complex-diskp point radius) (lw-complex-coefficientsp coefficients)
 (rationalp log-cap) (<= 0 log-cap) (rationalp gamma) (<= (abs gamma) 2)
 (lw-complex-diskp (lw-complex-polynomial coefficients point 0) log-cap))
 (lw-complex-diskp (lw-complex-polynomial (lw-normalized-local-polynomial anchor coefficients gamma error) point 0) (lw-normalized-local-cap anchor radius log-cap)))
 :hints (("Goal"
 :use (lw-normalized-local-point-data lw-normalized-local-cap-data lw-normalized-local-numerator-bound
       lw-normalized-local-polynomial-evaluation
       (:instance lw-complex-ring-rational (left anchor) (right (cons 1 0)))
       lw-linear-inverse-polynomial-cap
       (:instance lw-linear-inverse-polynomial-cap (anchor (lw-complex-sub anchor (cons 1 0))))
       (:instance lw-complex-mul-disk (left (lw-complex-polynomial (lw-linear-inverse-polynomial anchor error) point 0)) (right (lw-complex-polynomial (lw-linear-inverse-polynomial (lw-complex-sub anchor (cons 1 0)) error) point 0)) (radius (* 4 (lw-linear-inverse-cap anchor))) (other-radius (* 4 (lw-linear-inverse-cap (lw-complex-sub anchor (cons 1 0))))))
       (:instance lw-complex-mul-disk (left (lw-complex-polynomial (lw-normalized-local-numerator anchor coefficients gamma) point 0)) (right (lw-complex-mul (lw-complex-polynomial (lw-linear-inverse-polynomial anchor error) point 0) (lw-complex-polynomial (lw-linear-inverse-polynomial (lw-complex-sub anchor (cons 1 0)) error) point 0))) (radius (lw-normalized-local-numerator-cap anchor radius log-cap)) (other-radius (* (* 4 (lw-linear-inverse-cap anchor)) (* 4 (lw-linear-inverse-cap (lw-complex-sub anchor (cons 1 0)))))))
       (:instance lw-complex-sub-disk (left (lw-complex-polynomial (lw-linear-inverse-polynomial anchor error) point 0)) (right (lw-complex-mul (lw-complex-polynomial (lw-normalized-local-numerator anchor coefficients gamma) point 0) (lw-complex-mul (lw-complex-polynomial (lw-linear-inverse-polynomial anchor error) point 0) (lw-complex-polynomial (lw-linear-inverse-polynomial (lw-complex-sub anchor (cons 1 0)) error) point 0)))) (radius (* 4 (lw-linear-inverse-cap anchor))) (other-radius (* (lw-normalized-local-numerator-cap anchor radius log-cap) (* 4 (lw-linear-inverse-cap anchor)) (* 4 (lw-linear-inverse-cap (lw-complex-sub anchor (cons 1 0))))))))
 :in-theory (union-theories
 '(lw-normalized-local-cap (:executable-counterpart lw-complexp) lw-nlp-left-commutes lw-nlp-left-distributes lw-nlp-fold-constants lw-nlp-times-negative lw-nlp-negative-times lw-nlp-zero-times lw-nlp-minus-one lw-nlp-double-negative lw-nlp-add-cancel lw-nlp-double lw-nlp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(local (defthm lw-nlp-difference-ring
 (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp n) (lw-complexp x) (lw-complexp y))
 (equal (lw-complex-sub (lw-complex-sub a (lw-complex-mul n x)) (lw-complex-sub b (lw-complex-mul n y)))
        (lw-complex-sub (lw-complex-sub a b) (lw-complex-mul n (lw-complex-sub x y)))))
 :hints (("Goal" :in-theory (union-theories
 '(lw-complexp lw-complex-sub lw-complex-mul lw-nlp-left-commutes lw-nlp-left-distributes lw-nlp-fold-constants lw-nlp-times-negative lw-nlp-negative-times lw-nlp-zero-times lw-nlp-minus-one lw-nlp-double-negative lw-nlp-add-cancel lw-nlp-double lw-nlp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-normalized-local-polynomial-error
 (implies (and (lw-complexp anchor) (not (equal anchor (cons 0 0))) (not (equal (lw-complex-sub anchor (cons 1 0)) (cons 0 0)))
 (rationalp radius) (<= 0 radius) (<= radius (* 1/4 (lw-complex-l1 anchor)))
 (<= radius (* 1/4 (lw-complex-l1 (lw-complex-sub anchor (cons 1 0))))) (lw-complex-diskp point radius) (lw-complex-coefficientsp coefficients)
 (rationalp log-cap) (<= 0 log-cap) (rationalp gamma) (<= (abs gamma) 2)
 (lw-complex-diskp (lw-complex-polynomial coefficients point 0) log-cap) (rationalp error) (< 0 error))
 (lw-complex-diskp (lw-complex-sub (lw-complex-local-normalization anchor point (lw-complex-polynomial coefficients point 0) gamma) (lw-complex-polynomial (lw-normalized-local-polynomial anchor coefficients gamma error) point 0)) (* (lw-normalized-local-inverse-cost anchor radius log-cap) error)))
 :hints (("Goal"
 :use (lw-normalized-local-point-data lw-normalized-local-cap-data
       lw-normalized-local-numerator-valid lw-normalized-local-numerator-evaluation lw-normalized-local-numerator-bound
       lw-normalized-local-polynomial-evaluation
       (:instance lw-complex-ring-rational (left anchor) (right (cons 1 0)))
       lw-linear-inverse-polynomial-valid
       (:instance lw-linear-inverse-polynomial-valid (anchor (lw-complex-sub anchor (cons 1 0))))
       (:instance lw-complex-polynomial-rational (offset 0))
       (:instance lw-complex-polynomial-rational (coefficients (lw-normalized-local-numerator anchor coefficients gamma)) (offset 0))
       (:instance lw-complex-polynomial-rational (coefficients (lw-linear-inverse-polynomial anchor error)) (offset 0))
       (:instance lw-complex-polynomial-rational (coefficients (lw-linear-inverse-polynomial (lw-complex-sub anchor (cons 1 0)) error)) (offset 0))
       lw-linear-inverse-polynomial-cap
       lw-linear-inverse-polynomial-error
       (:instance lw-linear-inverse-polynomial-error (anchor (lw-complex-sub anchor (cons 1 0))))
       (:instance lw-complex-mul-difference-bound (a (lw-complex-reciprocal (lw-complex-add anchor point))) (b (lw-complex-reciprocal (lw-complex-add (lw-complex-sub anchor (cons 1 0)) point))) (c (lw-complex-polynomial (lw-linear-inverse-polynomial anchor error) point 0)) (d (lw-complex-polynomial (lw-linear-inverse-polynomial (lw-complex-sub anchor (cons 1 0)) error) point 0))
        (right-cap (/ (* 1/4 (lw-complex-l1 (lw-complex-sub anchor (cons 1 0)))))) (left-cap (* 4 (lw-linear-inverse-cap anchor))) (left-error error) (right-error error))
       (:instance lw-complex-mul-disk (left (lw-complex-polynomial (lw-normalized-local-numerator anchor coefficients gamma) point 0)) (right (lw-complex-sub (lw-complex-mul (lw-complex-reciprocal (lw-complex-add anchor point)) (lw-complex-reciprocal (lw-complex-add (lw-complex-sub anchor (cons 1 0)) point))) (lw-complex-mul (lw-complex-polynomial (lw-linear-inverse-polynomial anchor error) point 0) (lw-complex-polynomial (lw-linear-inverse-polynomial (lw-complex-sub anchor (cons 1 0)) error) point 0))))
        (radius (lw-normalized-local-numerator-cap anchor radius log-cap)) (other-radius (* (+ (/ (* 1/4 (lw-complex-l1 (lw-complex-sub anchor (cons 1 0))))) (* 4 (lw-linear-inverse-cap anchor))) error)))
       (:instance lw-complex-sub-disk (left (lw-complex-sub (lw-complex-reciprocal (lw-complex-add anchor point)) (lw-complex-polynomial (lw-linear-inverse-polynomial anchor error) point 0))) (right (lw-complex-mul (lw-complex-polynomial (lw-normalized-local-numerator anchor coefficients gamma) point 0) (lw-complex-sub (lw-complex-mul (lw-complex-reciprocal (lw-complex-add anchor point)) (lw-complex-reciprocal (lw-complex-add (lw-complex-sub anchor (cons 1 0)) point))) (lw-complex-mul (lw-complex-polynomial (lw-linear-inverse-polynomial anchor error) point 0) (lw-complex-polynomial (lw-linear-inverse-polynomial (lw-complex-sub anchor (cons 1 0)) error) point 0)))))
        (radius error) (other-radius (* (lw-normalized-local-numerator-cap anchor radius log-cap) (+ (/ (* 1/4 (lw-complex-l1 (lw-complex-sub anchor (cons 1 0))))) (* 4 (lw-linear-inverse-cap anchor))) error)))
       (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-local-normalization anchor point (lw-complex-polynomial coefficients point 0) gamma) (lw-complex-polynomial (lw-normalized-local-polynomial anchor coefficients gamma error) point 0)))
        (radius (+ error (* (lw-normalized-local-numerator-cap anchor radius log-cap) (+ (/ (* 1/4 (lw-complex-l1 (lw-complex-sub anchor (cons 1 0))))) (* 4 (lw-linear-inverse-cap anchor))) error))) (cap (* (lw-normalized-local-inverse-cost anchor radius log-cap) error))))
 :in-theory (union-theories
 '(lw-normalized-local-polynomial-evaluation lw-normalized-local-numerator-evaluation lw-complex-local-normalization lw-normalized-local-inverse-cost lw-nlp-difference-ring lw-complex-ring-rational lw-complex-reciprocal-rational lw-complex-scale-rational (:executable-counterpart lw-complexp) lw-nlp-left-commutes lw-nlp-left-distributes lw-nlp-fold-constants lw-nlp-times-negative lw-nlp-negative-times lw-nlp-zero-times lw-nlp-minus-one lw-nlp-double-negative lw-nlp-add-cancel lw-nlp-double lw-nlp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-complex-local-normalization-transport
 (implies (and (lw-complexp anchor) (not (equal anchor (cons 0 0))) (not (equal (lw-complex-sub anchor (cons 1 0)) (cons 0 0)))
 (rationalp radius) (<= 0 radius) (<= radius (* 1/4 (lw-complex-l1 anchor)))
 (<= radius (* 1/4 (lw-complex-l1 (lw-complex-sub anchor (cons 1 0))))) (lw-complex-diskp point radius)
  (lw-complexp value) (lw-complexp other-value) (rationalp gamma) (rationalp other-gamma)
  (lw-complex-diskp (lw-complex-sub value other-value) value-error)
  (lw-complex-diskp (lw-complex-sub (cons gamma 0) (cons other-gamma 0)) gamma-error))
 (lw-complex-diskp
  (lw-complex-sub (lw-complex-local-normalization anchor point value gamma)
                  (lw-complex-local-normalization anchor point other-value other-gamma))
  (* (/ (* 1/4 (lw-complex-l1 anchor))) (/ (* 1/4 (lw-complex-l1 (lw-complex-sub anchor (cons 1 0))))) (+ value-error (* (lw-normalized-local-point-cap anchor radius) gamma-error)))))
 :hints (("Goal"
 :use (lw-normalized-local-point-data
       lw-complex-local-normalization-normalized
       (:instance lw-complex-local-normalization-normalized (value other-value) (gamma other-gamma))
       (:instance lw-complex-normalized-euler-transport (point (lw-complex-add (lw-complex-sub anchor (cons 1 0)) point))
        (value value) (other-value other-value) (anchor (cons gamma 0)) (other-anchor (cons other-gamma 0))
        (point-cap (lw-normalized-local-point-cap anchor radius)) (inverse-cap (* (/ (* 1/4 (lw-complex-l1 anchor))) (/ (* 1/4 (lw-complex-l1 (lw-complex-sub anchor (cons 1 0))))))) (anchor-error gamma-error)))
 :in-theory (union-theories
 '(lw-complex-local-normalization-normalized lw-nlp-shift-sum lw-nlp-real-pair lw-complex-ring-rational (:executable-counterpart lw-complexp) lw-nlp-left-commutes lw-nlp-left-distributes lw-nlp-fold-constants lw-nlp-times-negative lw-nlp-negative-times lw-nlp-zero-times lw-nlp-minus-one lw-nlp-double-negative lw-nlp-add-cancel lw-nlp-double lw-nlp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-complex-real-difference-bound
 (implies (and (rationalp gamma) (rationalp other-gamma)
  (rationalp error) (<= 0 error) (<= (abs (- gamma other-gamma)) error))
 (lw-complex-diskp (lw-complex-sub (cons gamma 0) (cons other-gamma 0)) error))
 :hints (("Goal"
 :use ((:instance lw-complex-scale-disk (point (cons 1 0)) (radius 1) (factor (- gamma other-gamma)))
       (:instance lw-complex-disk-enlarge (point (lw-complex-scale (- gamma other-gamma) (cons 1 0))) (radius (abs (- gamma other-gamma))) (cap error)))
 :in-theory (union-theories
 '(abs lw-complex-sub lw-complex-scale (:executable-counterpart lw-complex-diskp) lw-nlp-left-commutes lw-nlp-left-distributes lw-nlp-fold-constants lw-nlp-times-negative lw-nlp-negative-times lw-nlp-zero-times lw-nlp-minus-one lw-nlp-double-negative lw-nlp-add-cancel lw-nlp-double lw-nlp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))


