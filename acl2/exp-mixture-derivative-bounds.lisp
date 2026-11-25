(in-package "ACL2")

(include-book "exp-mixture-derivatives")

; Uniform quantitative derivative bounds for finite exponential mixtures.
; Degree choice may be made after the finite node and point requests are fixed.

(local (in-theory
 (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
          lw-complex-diskp lw-diskp lw-complex-power lw-rational-power
          lw-complex-polynomial lw-complex-polynomial-derivative lw-complex-coefficient-at
          lw-exp-mixturep lw-exp-mixture-coefficient lw-exp-mixture-coefficients
          lw-exp-mixture-value lw-exp-mixture-common-value lw-exp-mixture-affine-polynomial
          lw-exp-mixture-degree lw-exp-mixture-degree-raw lw-exp-mixture-budget lw-exp-mixture-mass
          lw-exp-mixture-derivative-nodes lw-exp-mixture-taylor-value
          lw-complex-mul-subtract lw-complex-mul-commutative lw-complex-mul-left-commutes)))

(local (defthm lw-xdb-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-xdb-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-xdb-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-xdb-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-xdb-times-negative (a b) (b a)))
                 :in-theory (disable lw-xdb-times-negative)))))

(local (defthm lw-xdb-zero-times (equal (* 0 a) 0)))

(local (defthm lw-xdb-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-xdb-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-xdb-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-xdb-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-xdb-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-xdb-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-xdb-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-xdb-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-xdb-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-xdb-left-commutes)))))

(local (defthm lw-xdb-three-halves
 (implies (rationalp x) (equal (* 3/2 x) (+ x (* 1/2 x))))
 :hints (("Goal" :use ((:instance distributivity (x x) (y 1) (z 1/2)))))))

(local (defthm lw-xdb-length-natural
 (natp (len nodes))
 :hints (("Goal" :induct (len nodes) :in-theory (enable len)))
 :rule-classes (:rewrite :type-prescription)))

(defthm lw-exp-mixture-arbitrary-polynomial-common-comparison
 (implies (and (lw-exp-mixturep nodes) (lw-complex-diskp point radius)
               (rationalp budget) (< 0 budget) (natp degree)
               (<= (lw-exp-mixture-degree-raw nodes radius budget) degree)
               (rationalp request) (< 0 request))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-polynomial (lw-exp-mixture-coefficients nodes 0 (+ 1 degree)) point 0) (lw-exp-mixture-common-value nodes point request))
   (+ (* 3/2 (len nodes) budget) (* (lw-exp-mixture-mass nodes) request))))
 :hints (("Goal"
  :use (lw-exp-mixture-uniform-tail-raw
        (:instance lw-complex-disk-data)
        (:instance lw-exp-mixture-coefficients-valid (offset 0) (count (+ 1 degree)))
        (:instance lw-complex-polynomial-rational (coefficients (lw-exp-mixture-coefficients nodes 0 (+ 1 degree))) (offset 0))
        lw-exp-mixture-value-rational lw-exp-mixture-common-value-rational
        lw-exp-mixture-common-comparison lw-xdb-length-natural
        (:instance lw-exp-mixture-polynomial-value)
        (:instance lw-complex-difference-triangle
         (left (lw-complex-polynomial (lw-exp-mixture-coefficients nodes 0 (+ 1 degree)) point 0)) (middle (lw-exp-mixture-value nodes point budget))
         (right (lw-exp-mixture-common-value nodes point request)) (radius (* (len nodes) budget))
         (other-radius (+ (* 1/2 (len nodes) budget) (* (lw-exp-mixture-mass nodes) request)))))
  :in-theory (union-theories
   '(lw-xdb-three-halves lw-xdb-left-commutes lw-xdb-left-distributes lw-xdb-fold-constants lw-xdb-times-negative lw-xdb-negative-times lw-xdb-zero-times lw-xdb-minus-one lw-xdb-double-negative lw-xdb-add-cancel lw-xdb-double lw-xdb-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(defun lw-exp-mixture-derivative-degree (nodes radius error)
 (+ 1 (lw-exp-mixture-degree-raw (lw-exp-mixture-derivative-nodes nodes) radius (lw-exp-mixture-budget (lw-exp-mixture-derivative-nodes nodes) error))))

(local (in-theory (disable lw-exp-mixture-derivative-degree)))

(defthm lw-exp-mixture-derivative-degree-data
 (implies (and (lw-exp-mixturep nodes) (rationalp radius) (<= 0 radius) (rationalp error) (< 0 error))
  (and (posp (lw-exp-mixture-derivative-degree nodes radius error))
       (<= (lw-exp-mixture-degree-raw (lw-exp-mixture-derivative-nodes nodes) radius (lw-exp-mixture-budget (lw-exp-mixture-derivative-nodes nodes) error)) (- (lw-exp-mixture-derivative-degree nodes radius error) 1))))
 :hints (("Goal"
  :use (lw-exp-mixture-derivative-nodes-valid
        (:instance lw-exp-mixture-budget-positive (nodes (lw-exp-mixture-derivative-nodes nodes)))
        (:instance lw-exp-mixture-degree-raw-natural (nodes (lw-exp-mixture-derivative-nodes nodes)) (budget (lw-exp-mixture-budget (lw-exp-mixture-derivative-nodes nodes) error))))
  :in-theory (union-theories
   '(lw-exp-mixture-derivative-degree lw-xdb-left-commutes lw-xdb-left-distributes lw-xdb-fold-constants lw-xdb-times-negative lw-xdb-negative-times lw-xdb-zero-times lw-xdb-minus-one lw-xdb-double-negative lw-xdb-add-cancel lw-xdb-double lw-xdb-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-exp-mixture-polynomial-derivative-common-comparison
 (implies (and (lw-exp-mixturep nodes) (lw-complex-diskp point radius)
               (rationalp error) (< 0 error) (natp degree) (<= (lw-exp-mixture-derivative-degree nodes radius error) degree)
               (rationalp request) (< 0 request))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-polynomial-derivative (lw-exp-mixture-coefficients nodes 0 (+ 1 degree)) point)
                   (lw-exp-mixture-common-value (lw-exp-mixture-derivative-nodes nodes) point request))
   (+ (* 3/2 error) (* (lw-exp-mixture-mass (lw-exp-mixture-derivative-nodes nodes)) request))))
 :hints (("Goal"
  :use (lw-exp-mixture-derivative-nodes-valid lw-exp-mixture-derivative-degree-data
        (:instance lw-exp-mixture-mass-nonnegative (nodes (lw-exp-mixture-derivative-nodes nodes)))
        (:instance lw-complex-disk-data)
        (:instance lw-exp-mixture-budget-positive (nodes (lw-exp-mixture-derivative-nodes nodes)))
        (:instance lw-exp-mixture-budget-adequate (nodes (lw-exp-mixture-derivative-nodes nodes)))
        (:instance lw-exp-mixture-polynomial-derivative (count (+ 1 degree)))
        (:instance lw-exp-mixture-arbitrary-polynomial-common-comparison
         (nodes (lw-exp-mixture-derivative-nodes nodes)) (budget (lw-exp-mixture-budget (lw-exp-mixture-derivative-nodes nodes) error)) (degree (- degree 1)))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub (lw-complex-polynomial-derivative (lw-exp-mixture-coefficients nodes 0 (+ 1 degree)) point)
                                (lw-exp-mixture-common-value (lw-exp-mixture-derivative-nodes nodes) point request)))
         (radius (+ (* 3/2 (len (lw-exp-mixture-derivative-nodes nodes)) (lw-exp-mixture-budget (lw-exp-mixture-derivative-nodes nodes) error)) (* (lw-exp-mixture-mass (lw-exp-mixture-derivative-nodes nodes)) request)))
         (cap (+ (* 3/2 error) (* (lw-exp-mixture-mass (lw-exp-mixture-derivative-nodes nodes)) request)))))
  :in-theory (union-theories
   '( lw-xdb-left-commutes lw-xdb-left-distributes lw-xdb-fold-constants lw-xdb-times-negative lw-xdb-negative-times lw-xdb-zero-times lw-xdb-minus-one lw-xdb-double-negative lw-xdb-add-cancel lw-xdb-double lw-xdb-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(local (defthm lw-xdb-product-difference
 (implies (and (lw-complexp slope) (lw-complexp left) (lw-complexp right))
  (equal (lw-complex-sub (lw-complex-mul slope left) (lw-complex-mul slope right))
         (lw-complex-mul slope (lw-complex-sub left right))))
 :hints (("Goal" :in-theory (union-theories
   '(lw-complexp lw-complex-sub lw-complex-mul lw-complex-scale lw-xdb-left-commutes lw-xdb-left-distributes lw-xdb-fold-constants lw-xdb-times-negative lw-xdb-negative-times lw-xdb-zero-times lw-xdb-minus-one lw-xdb-double-negative lw-xdb-add-cancel lw-xdb-double lw-xdb-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))))))

(defthm lw-exp-mixture-affine-derivative-common-comparison
 (implies (and (lw-exp-mixturep nodes) (lw-complex-diskp center radius) (lw-complex-diskp slope slope-cap)
               (natp target) (rationalp ordinary-error) (< 0 ordinary-error)
               (rationalp error) (< 0 error) (<= (lw-exp-mixture-derivative-degree nodes radius error) target)
               (rationalp request) (< 0 request))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-complex-coefficient-at (lw-exp-mixture-affine-polynomial nodes center slope radius target ordinary-error) 1 0)
    (lw-complex-mul slope (lw-exp-mixture-common-value (lw-exp-mixture-derivative-nodes nodes) center request)))
   (* slope-cap (+ (* 3/2 error) (* (lw-exp-mixture-mass (lw-exp-mixture-derivative-nodes nodes)) request)))))
 :hints (("Goal"
  :use (lw-exp-mixture-derivative-nodes-valid
        (:instance lw-complex-disk-data (point center))
        (:instance lw-complex-disk-data (point slope) (radius slope-cap))
        (:instance lw-exp-mixture-degree-data (error ordinary-error))
        (:instance lw-exp-mixture-affine-linear-coefficient
         (count (+ 1 (lw-exp-mixture-degree nodes radius target ordinary-error))))
        (:instance lw-exp-mixture-polynomial-derivative (point center)
         (count (+ 1 (lw-exp-mixture-degree nodes radius target ordinary-error))))
        (:instance lw-exp-mixture-coefficients-valid (offset 0)
         (count (+ 1 (lw-exp-mixture-degree nodes radius target ordinary-error))))
        (:instance lw-complex-polynomial-derivative-rational (point center)
         (coefficients (lw-exp-mixture-coefficients nodes 0 (+ 1 (lw-exp-mixture-degree nodes radius target ordinary-error)))))
        (:instance lw-exp-mixture-common-value-rational (nodes (lw-exp-mixture-derivative-nodes nodes)) (point center))
        (:instance lw-exp-mixture-polynomial-derivative-common-comparison
         (point center) (degree (lw-exp-mixture-degree nodes radius target ordinary-error)))
        (:instance lw-complex-mul-disk (left slope)
         (right (lw-complex-sub
          (lw-complex-polynomial-derivative (lw-exp-mixture-coefficients nodes 0 (+ 1 (lw-exp-mixture-degree nodes radius target ordinary-error))) center)
          (lw-exp-mixture-common-value (lw-exp-mixture-derivative-nodes nodes) center request)))
         (radius slope-cap) (other-radius (+ (* 3/2 error) (* (lw-exp-mixture-mass (lw-exp-mixture-derivative-nodes nodes)) request)))))
  :in-theory (union-theories
   '(lw-exp-mixture-affine-polynomial lw-xdb-product-difference lw-xdb-left-commutes lw-xdb-left-distributes lw-xdb-fold-constants lw-xdb-times-negative lw-xdb-negative-times lw-xdb-zero-times lw-xdb-minus-one lw-xdb-double-negative lw-xdb-add-cancel lw-xdb-double lw-xdb-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

