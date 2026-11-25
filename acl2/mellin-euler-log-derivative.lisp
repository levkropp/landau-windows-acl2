(in-package "ACL2")

(include-book "euler-log-transform")
(include-book "mellin-zeta-derivative")

; Normalize the checked Euler logarithmic derivative with a computed
; request, then identify this actual family with the improper Mellin name.

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

(local (in-theory (disable lw-euler-bounds lw-euler-log-transform
 lw-euler-log-transform-cost lw-complex-euler-log-derivative-value
 lw-complex-zeta-euler-log-derivative-value lw-mellin-zeta-derivative-value
 lw-euler-value-clearance-check lw-dirichlet-transform)))

(local (defthm lw-mel-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-mel-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-mel-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-mel-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-mel-times-negative (a b) (b a)))
                 :in-theory (disable lw-mel-times-negative)))))

(local (defthm lw-mel-zero-times (equal (* 0 a) 0)))

(local (defthm lw-mel-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-mel-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-mel-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-mel-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-mel-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-mel-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-mel-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-mel-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-mel-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-mel-left-commutes)))))

(defun lw-mellin-euler-log-request (rate height error)
 (lw-euler-rounding-precision (lw-euler-log-transform-cost rate height) error))

(local (in-theory (disable lw-mellin-euler-log-request)))

(defthm lw-mellin-euler-log-request-data
 (implies (and (rationalp rate) (< 0 rate) (rationalp height)
               (not (and (equal rate 1) (equal height 0)))
               (rationalp error) (< 0 error))
  (and (rationalp (lw-mellin-euler-log-request rate height error)) (< 0 (lw-mellin-euler-log-request rate height error)) (<= (lw-mellin-euler-log-request rate height error) 1)
       (<= (* (lw-euler-log-transform-cost rate height) (lw-mellin-euler-log-request rate height error)) (* 1/2 error))
       (<= (* 2 (lw-mellin-euler-log-request rate height error)) (* 1/2 error))))
 :hints (("Goal"
  :use (lw-euler-log-transform-cost-data
        (:instance lw-euler-rounding-precision-valid (cost (lw-euler-log-transform-cost rate height)))
        (:instance lw-mel-multiply-order (a 2) (b (lw-euler-log-transform-cost rate height)) (factor (lw-mellin-euler-log-request rate height error))))
  :in-theory (union-theories
 '(lw-mellin-euler-log-request lw-mel-left-commutes lw-mel-left-distributes lw-mel-fold-constants lw-mel-times-negative lw-mel-negative-times lw-mel-zero-times lw-mel-minus-one lw-mel-double-negative lw-mel-add-cancel lw-mel-double lw-mel-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defun lw-mellin-euler-log-value (rate height radius anchor-error error)
 (lw-euler-log-transform rate height (lw-complex-euler-log-derivative-value rate height radius anchor-error (lw-mellin-euler-log-request rate height error)) (car (lw-euler-bounds (lw-mellin-euler-log-request rate height error)))))

(local (in-theory (disable lw-mellin-euler-log-value)))

(defthm lw-mellin-euler-log-value-rational
 (implies (and (rationalp rate) (< 0 rate) (rationalp height)
               (not (and (equal rate 1) (equal height 0)))
               (lw-euler-value-clearance-check rate height anchor-error)
               (rationalp radius) (< 0 radius) (< radius rate)
               (rationalp error) (< 0 error))
  (lw-complexp (lw-mellin-euler-log-value rate height radius anchor-error error)))
 :hints (("Goal"
  :use (lw-mellin-euler-log-request-data
        (:instance lw-complex-euler-log-derivative-rational (error (lw-mellin-euler-log-request rate height error)))
        (:instance lw-euler-bounds-interval (epsilon (lw-mellin-euler-log-request rate height error)))
        (:instance lw-euler-log-transform-rational (log-value (lw-complex-euler-log-derivative-value rate height radius anchor-error (lw-mellin-euler-log-request rate height error))) (gamma-value (car (lw-euler-bounds (lw-mellin-euler-log-request rate height error))))))
  :in-theory (union-theories
 '(lw-mellin-euler-log-value lw-intervalp lw-mel-left-commutes lw-mel-left-distributes lw-mel-fold-constants lw-mel-times-negative lw-mel-negative-times lw-mel-zero-times lw-mel-minus-one lw-mel-double-negative lw-mel-add-cancel lw-mel-double lw-mel-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-mellin-euler-log-certificate-independence
 (implies (and (rationalp rate) (< 0 rate) (rationalp height)
               (not (and (equal rate 1) (equal height 0)))
               (lw-euler-value-clearance-check rate height left-anchor)
               (lw-euler-value-clearance-check rate height right-anchor)
               (rationalp radius) (< 0 radius) (< radius rate)
               (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
  (lw-complex-diskp (lw-complex-sub (lw-mellin-euler-log-value rate height radius left-anchor left-error) (lw-mellin-euler-log-value rate height radius right-anchor right-error)) (* 1/2 (+ left-error right-error))))
 :hints (("Goal"
  :use ((:instance lw-mellin-euler-log-request-data (error left-error))
        (:instance lw-mellin-euler-log-request-data (error right-error))
        (:instance lw-complex-euler-log-derivative-rational (anchor-error left-anchor) (error (lw-mellin-euler-log-request rate height left-error)))
        (:instance lw-complex-euler-log-derivative-rational (anchor-error right-anchor) (error (lw-mellin-euler-log-request rate height right-error)))
        (:instance lw-complex-euler-log-derivative-certificate-independence
         (left-error (lw-mellin-euler-log-request rate height left-error)) (right-error (lw-mellin-euler-log-request rate height right-error)))
        (:instance lw-euler-bounds-interval (epsilon (lw-mellin-euler-log-request rate height left-error)))
        (:instance lw-euler-bounds-interval (epsilon (lw-mellin-euler-log-request rate height right-error)))
        (:instance lw-euler-lower-cauchy (left-error (lw-mellin-euler-log-request rate height left-error)) (right-error (lw-mellin-euler-log-request rate height right-error)))
        (:instance lw-euler-log-transform-transport
         (left (lw-complex-euler-log-derivative-value rate height radius left-anchor (lw-mellin-euler-log-request rate height left-error))) (right (lw-complex-euler-log-derivative-value rate height radius right-anchor (lw-mellin-euler-log-request rate height right-error)))
         (left-gamma (car (lw-euler-bounds (lw-mellin-euler-log-request rate height left-error)))) (right-gamma (car (lw-euler-bounds (lw-mellin-euler-log-request rate height right-error))))
         (log-error (+ (lw-mellin-euler-log-request rate height left-error) (lw-mellin-euler-log-request rate height right-error))) (gamma-error (+ (lw-mellin-euler-log-request rate height left-error) (lw-mellin-euler-log-request rate height right-error))))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub (lw-mellin-euler-log-value rate height radius left-anchor left-error) (lw-mellin-euler-log-value rate height radius right-anchor right-error)))
         (radius (+ (* (lw-zeta-euler-inverse-cap (+ rate 1) height) (lw-zeta-euler-inverse-cap rate height) (+ (lw-mellin-euler-log-request rate height left-error) (lw-mellin-euler-log-request rate height right-error))) (* (lw-zeta-euler-inverse-cap rate height) (+ (lw-mellin-euler-log-request rate height left-error) (lw-mellin-euler-log-request rate height right-error)))))
         (cap (* 1/2 (+ left-error right-error)))))
  :in-theory (union-theories
 '(lw-mellin-euler-log-value lw-euler-log-transform-cost lw-intervalp lw-mel-left-commutes lw-mel-left-distributes lw-mel-fold-constants lw-mel-times-negative lw-mel-negative-times lw-mel-zero-times lw-mel-minus-one lw-mel-double-negative lw-mel-add-cancel lw-mel-double lw-mel-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-mellin-euler-log-value-cauchy
 (implies (and (rationalp rate) (< 0 rate) (rationalp height)
               (not (and (equal rate 1) (equal height 0)))
               (lw-euler-value-clearance-check rate height anchor-error)
               (rationalp radius) (< 0 radius) (< radius rate)
               (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
  (lw-complex-diskp
   (lw-complex-sub (lw-mellin-euler-log-value rate height radius anchor-error left-error)
                   (lw-mellin-euler-log-value rate height radius anchor-error right-error))
   (* 1/2 (+ left-error right-error))))
 :hints (("Goal"
  :use ((:instance lw-mellin-euler-log-certificate-independence (left-anchor anchor-error) (right-anchor anchor-error)))
  :in-theory (union-theories
 '( lw-mel-left-commutes lw-mel-left-distributes lw-mel-fold-constants lw-mel-times-negative lw-mel-negative-times lw-mel-zero-times lw-mel-minus-one lw-mel-double-negative lw-mel-add-cancel lw-mel-double lw-mel-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))


(local (defthm lw-mel-complement-residual
 (implies (and (lw-complexp point) (lw-complexp left) (lw-complexp right))
  (equal (lw-complex-sub (lw-complex-sub point left) right)
         (lw-complex-scale -1 (lw-complex-sub left (lw-complex-sub point right)))))
 :hints (("Goal"
  :in-theory (union-theories
 '(lw-complexp lw-complex-sub lw-complex-scale lw-mel-left-commutes lw-mel-left-distributes lw-mel-fold-constants lw-mel-times-negative lw-mel-negative-times lw-mel-zero-times lw-mel-minus-one lw-mel-double-negative lw-mel-add-cancel lw-mel-double lw-mel-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(defthm lw-mellin-euler-log-zeta-comparison
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (lw-euler-value-clearance-check rate height anchor-error)
               (rationalp radius) (< 0 radius) (< radius rate)
               (rationalp euler-error) (< 0 euler-error) (rationalp zeta-error) (< 0 zeta-error))
  (lw-complex-diskp (lw-complex-sub (lw-mellin-euler-log-value rate height radius anchor-error euler-error) (lw-mellin-zeta-derivative-value rate height radius zeta-error)) (+ (* 1/2 euler-error) (* 1/2 zeta-error))))
 :hints (("Goal"
  :use (lw-zeta-euler-inverse-cap-data
        (:instance lw-mellin-euler-log-request-data (error euler-error))
        (:instance lw-complex-euler-log-derivative-rational (error (lw-mellin-euler-log-request rate height euler-error)))
        (:instance lw-complex-zeta-euler-log-derivative-rational (error (* 1/4 zeta-error)))
        (:instance lw-complex-euler-zeta-log-agreement (euler-error (lw-mellin-euler-log-request rate height euler-error)) (zeta-error (* 1/4 zeta-error)))
        (:instance lw-complex-operations-rational (left (lw-complex-reciprocal (cons (- rate 1) height))) (right (lw-complex-euler-log-derivative-value rate height radius anchor-error (lw-mellin-euler-log-request rate height euler-error))) (factor 1))
        (:instance lw-euler-bounds-interval (epsilon (lw-mellin-euler-log-request rate height euler-error)))
        (:instance lw-euler-bounds-interval (epsilon (* 1/4 zeta-error)))
        (:instance lw-euler-lower-cauchy (left-error (lw-mellin-euler-log-request rate height euler-error)) (right-error (* 1/4 zeta-error)))
        (:instance lw-complex-scale-disk
         (point (lw-complex-sub (lw-complex-euler-log-derivative-value rate height radius anchor-error (lw-mellin-euler-log-request rate height euler-error)) (lw-complex-sub (lw-complex-reciprocal (cons (- rate 1) height)) (lw-complex-zeta-euler-log-derivative-value rate height radius (* 1/4 zeta-error)))))
         (radius (+ (lw-mellin-euler-log-request rate height euler-error) (* 1/4 zeta-error))) (factor -1))
        (:instance lw-dirichlet-transform-transport
         (left (lw-complex-sub (lw-complex-reciprocal (cons (- rate 1) height)) (lw-complex-euler-log-derivative-value rate height radius anchor-error (lw-mellin-euler-log-request rate height euler-error)))) (right (lw-complex-zeta-euler-log-derivative-value rate height radius (* 1/4 zeta-error)))
         (left-gamma (car (lw-euler-bounds (lw-mellin-euler-log-request rate height euler-error)))) (right-gamma (car (lw-euler-bounds (* 1/4 zeta-error))))
         (prime-error (+ (lw-mellin-euler-log-request rate height euler-error) (* 1/4 zeta-error))) (gamma-error (+ (lw-mellin-euler-log-request rate height euler-error) (* 1/4 zeta-error))))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub (lw-mellin-euler-log-value rate height radius anchor-error euler-error) (lw-mellin-zeta-derivative-value rate height radius zeta-error)))
         (radius (+ (lw-mellin-euler-log-request rate height euler-error) (* 1/4 zeta-error) (lw-mellin-euler-log-request rate height euler-error) (* 1/4 zeta-error)))
         (cap (+ (* 1/2 euler-error) (* 1/2 zeta-error)))))
  :in-theory (union-theories
 '(lw-mellin-euler-log-value lw-euler-log-transform lw-mellin-zeta-derivative-value lw-mel-complement-residual lw-intervalp (:executable-counterpart abs) lw-mel-left-commutes lw-mel-left-distributes lw-mel-fold-constants lw-mel-times-negative lw-mel-negative-times lw-mel-zero-times lw-mel-minus-one lw-mel-double-negative lw-mel-add-cancel lw-mel-double lw-mel-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(local (defthm lw-mel-with-auxiliary-error
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (lw-euler-value-clearance-check rate height anchor-error)
               (rationalp radius) (< 0 radius) (< radius rate)
               (rationalp integral-error) (< 0 integral-error)
               (rationalp euler-error) (< 0 euler-error) (rationalp zeta-error) (< 0 zeta-error))
  (lw-complex-diskp (lw-complex-sub (lw-mellin-integral rate height 0 integral-error) (lw-mellin-euler-log-value rate height radius anchor-error euler-error)) (+ (+ (* 5 integral-error) (* 1/2 euler-error)) zeta-error)))
 :hints (("Goal"
  :use (lw-mellin-euler-log-zeta-comparison
        (:instance lw-mellin-zeta-derivative-comparison (left-error integral-error) (right-error zeta-error))
        (:instance lw-mellin-integral-rational (sigma rate) (index 0) (error integral-error))
        (:instance lw-mellin-euler-log-value-rational (error euler-error))
        (:instance lw-mellin-zeta-derivative-value-rational (error zeta-error))
        (:instance lw-complex-difference-symmetric
         (left (lw-mellin-euler-log-value rate height radius anchor-error euler-error)) (right (lw-mellin-zeta-derivative-value rate height radius zeta-error)) (radius (+ (* 1/2 euler-error) (* 1/2 zeta-error))))
        (:instance lw-complex-difference-triangle
         (left (lw-mellin-integral rate height 0 integral-error)) (middle (lw-mellin-zeta-derivative-value rate height radius zeta-error)) (right (lw-mellin-euler-log-value rate height radius anchor-error euler-error))
         (radius (+ (* 5 integral-error) (* 1/2 zeta-error)))
         (other-radius (+ (* 1/2 euler-error) (* 1/2 zeta-error))))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub (lw-mellin-integral rate height 0 integral-error) (lw-mellin-euler-log-value rate height radius anchor-error euler-error)))
         (radius (+ (* 5 integral-error) (* 1/2 zeta-error) (* 1/2 euler-error) (* 1/2 zeta-error)))
         (cap (+ (+ (* 5 integral-error) (* 1/2 euler-error)) zeta-error))))
  :in-theory (union-theories
 '( lw-mel-left-commutes lw-mel-left-distributes lw-mel-fold-constants lw-mel-times-negative lw-mel-negative-times lw-mel-zero-times lw-mel-minus-one lw-mel-double-negative lw-mel-add-cancel lw-mel-double lw-mel-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))
 :rule-classes nil))

(defthm lw-mellin-euler-log-comparison
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (lw-euler-value-clearance-check rate height anchor-error)
               (rationalp radius) (< 0 radius) (< radius rate)
               (rationalp integral-error) (< 0 integral-error)
               (rationalp euler-error) (< 0 euler-error))
  (lw-complex-diskp (lw-complex-sub (lw-mellin-integral rate height 0 integral-error) (lw-mellin-euler-log-value rate height radius anchor-error euler-error)) (+ (* 5 integral-error) (* 1/2 euler-error))))
 :hints (("Goal"
  :cases ((lw-complex-diskp (lw-complex-sub (lw-mellin-integral rate height 0 integral-error) (lw-mellin-euler-log-value rate height radius anchor-error euler-error)) (+ (* 5 integral-error) (* 1/2 euler-error))))
  :use ((:instance lw-mellin-integral-rational (sigma rate) (index 0) (error integral-error))
        (:instance lw-mellin-euler-log-value-rational (error euler-error))
        (:instance lw-complex-operations-rational (left (lw-mellin-integral rate height 0 integral-error)) (right (lw-mellin-euler-log-value rate height radius anchor-error euler-error)) (factor 1))
        (:instance lw-complex-disk-gap-refinement-excludes
         (point (lw-complex-sub (lw-mellin-integral rate height 0 integral-error) (lw-mellin-euler-log-value rate height radius anchor-error euler-error))) (radius (+ (* 5 integral-error) (* 1/2 euler-error))) (cost 1))
        (:instance lw-mel-with-auxiliary-error
         (zeta-error (lw-disk-gap-refinement (lw-complex-sub (lw-mellin-integral rate height 0 integral-error) (lw-mellin-euler-log-value rate height radius anchor-error euler-error)) (+ (* 5 integral-error) (* 1/2 euler-error)) 1))))
  :in-theory (union-theories
 '( lw-mel-left-commutes lw-mel-left-distributes lw-mel-fold-constants lw-mel-times-negative lw-mel-negative-times lw-mel-zero-times lw-mel-minus-one lw-mel-double-negative lw-mel-add-cancel lw-mel-double lw-mel-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-mellin-euler-log-right-comparison
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (rationalp radius) (< 0 radius) (< radius rate)
               (rationalp integral-error) (< 0 integral-error)
               (rationalp euler-error) (< 0 euler-error))
  (lw-complex-diskp
   (lw-complex-sub (lw-mellin-integral rate height 0 integral-error)
    (lw-mellin-euler-log-value rate height radius (lw-euler-zeta-clearance-request rate height) euler-error))
   (+ (* 5 integral-error) (* 1/2 euler-error))))
 :hints (("Goal"
  :use (lw-euler-zeta-clearance-check
        (:instance lw-mellin-euler-log-comparison (anchor-error (lw-euler-zeta-clearance-request rate height))))
  :in-theory (union-theories
 '( lw-mel-left-commutes lw-mel-left-distributes lw-mel-fold-constants lw-mel-times-negative lw-mel-negative-times lw-mel-zero-times lw-mel-minus-one lw-mel-double-negative lw-mel-add-cancel lw-mel-double lw-mel-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-mellin-euler-log-computed-comparison
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (rationalp radius) (< 0 radius) (< radius rate) (rationalp error) (< 0 error))
  (lw-complex-diskp
   (lw-complex-sub (lw-mellin-integral rate height 0 (/ error 10))
    (lw-mellin-euler-log-value rate height radius (lw-euler-zeta-clearance-request rate height) error))
   error))
 :hints (("Goal"
  :use ((:instance lw-mellin-euler-log-right-comparison (integral-error (/ error 10)) (euler-error error)))
  :in-theory (union-theories
 '( lw-mel-left-commutes lw-mel-left-distributes lw-mel-fold-constants lw-mel-times-negative lw-mel-negative-times lw-mel-zero-times lw-mel-minus-one lw-mel-double-negative lw-mel-add-cancel lw-mel-double lw-mel-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))


