(in-package "ACL2")

(include-book "exp-mixture-bounds")
(include-book "polynomial-affine")

; Connect the existing uniform mixture polynomials to samples at a
; caller-selected common precision, then compose with an affine argument.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-scale-add lw-complex-scale-product
                 lw-complex-power lw-complex-power-add lw-complex-power-power
                 lw-complex-exp-term lw-complex-exp-sum lw-complex-exp-value
                 lw-complex-l1 lw-exp-term lw-exp-sum lw-exp-band lw-exp-index
                 lw-exp-bounds lw-complex-polynomial lw-exp-mixture-coefficients
                 lw-exp-mixture-taylor-value lw-exp-mixture-block lw-exp-mixture-coefficient
                 lw-complex-disk-enlarge lw-disk-enlarge)))

(local (in-theory (disable lw-exp-mixturep lw-exp-mixture-value
 lw-exp-mixture-node-precision lw-exp-mixture-budget lw-exp-mixture-degree
 lw-exp-mixture-coefficients lw-exp-mixture-taylor-value
 lw-complex-polynomial lw-polynomial-affine)))

(local (defthm lw-xmp-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-xmp-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-xmp-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-xmp-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-xmp-times-negative (a b) (b a)))
                 :in-theory (disable lw-xmp-times-negative)))))

(local (defthm lw-xmp-zero-times (equal (* 0 a) 0)))

(local (defthm lw-xmp-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-xmp-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-xmp-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-xmp-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-xmp-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-xmp-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-xmp-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-xmp-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-xmp-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-xmp-left-commutes)))))

(defun lw-exp-mixture-common-value (nodes point request)
 (if (consp nodes)
  (lw-complex-add
   (lw-complex-mul (cdar nodes)
    (lw-complex-exp-value (lw-complex-scale (caar nodes) point) request))
   (lw-exp-mixture-common-value (cdr nodes) point request))
  (cons 0 0)))

(defun lw-exp-mixture-mass (nodes)
 (if (consp nodes) (+ (lw-complex-l1 (cdar nodes)) (lw-exp-mixture-mass (cdr nodes))) 0))

(local (in-theory (disable lw-exp-mixture-common-value lw-exp-mixture-mass)))

(defthm lw-exp-mixture-common-value-rational
 (implies (and (lw-exp-mixturep nodes) (lw-complexp point) (rationalp request) (< 0 request))
  (lw-complexp (lw-exp-mixture-common-value nodes point request)))
 :hints (("Goal" :induct (lw-exp-mixturep nodes)
  :in-theory (e/d (lw-exp-mixturep lw-exp-mixture-common-value lw-complexp
                   lw-complex-add lw-complex-mul lw-complex-scale)
                  (lw-complex-exp-value-rational)))
         (and stable-under-simplificationp
          '(:use ((:instance lw-complex-exp-value-rational
                   (point (lw-complex-scale (caar nodes) point)) (error request)))
            :do-not-induct t))))

(defthm lw-exp-mixture-mass-nonnegative
 (implies (lw-exp-mixturep nodes)
  (and (rationalp (lw-exp-mixture-mass nodes)) (<= 0 (lw-exp-mixture-mass nodes))))
 :hints (("Goal" :induct (lw-exp-mixturep nodes)
                 :in-theory (e/d (lw-exp-mixturep lw-exp-mixture-mass) (lw-complex-l1-bound)))
         (and stable-under-simplificationp
          '(:use ((:instance lw-complex-l1-bound (point (cdar nodes)))) :do-not-induct t))))

(local (defthm lw-xmp-mul-difference
 (implies (and (lw-complexp point) (lw-complexp left) (lw-complexp right))
  (equal (lw-complex-sub (lw-complex-mul point left) (lw-complex-mul point right))
         (lw-complex-mul point (lw-complex-sub left right))))
 :hints (("Goal" :in-theory (enable lw-complexp lw-complex-sub lw-complex-mul)
                 :do-not-induct t)) :rule-classes nil))

(defthm lw-exp-mixture-node-common-comparison
 (implies (and (rationalp value) (<= 0 value) (lw-complexp base) (lw-complexp point)
               (rationalp budget) (< 0 budget) (rationalp request) (< 0 request))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-complex-mul base (lw-complex-exp-value (lw-complex-scale value point)
                             (lw-exp-mixture-node-precision base budget)))
    (lw-complex-mul base (lw-complex-exp-value (lw-complex-scale value point) request)))
   (+ (* 1/2 budget) (* (lw-complex-l1 base) request))))
 :hints (("Goal"
  :use (lw-exp-mixture-node-precision-adequate
        (:instance lw-complex-l1-bound (point base))
        (:instance lw-complex-scale-rational (factor value))
        (:instance lw-complex-exp-value-rational (point (lw-complex-scale value point))
         (error (lw-exp-mixture-node-precision base budget)))
        (:instance lw-complex-exp-value-rational (point (lw-complex-scale value point)) (error request))
        (:instance lw-complex-exp-value-cauchy (point (lw-complex-scale value point))
         (left-error (lw-exp-mixture-node-precision base budget)) (right-error request))
        (:instance lw-xmp-mul-difference (point base)
         (left (lw-complex-exp-value (lw-complex-scale value point) (lw-exp-mixture-node-precision base budget)))
         (right (lw-complex-exp-value (lw-complex-scale value point) request)))
        (:instance lw-complex-mul-disk (left base)
         (right (lw-complex-sub
          (lw-complex-exp-value (lw-complex-scale value point) (lw-exp-mixture-node-precision base budget))
          (lw-complex-exp-value (lw-complex-scale value point) request)))
         (radius (lw-complex-l1 base)) (other-radius (+ (lw-exp-mixture-node-precision base budget) request)))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub
          (lw-complex-mul base (lw-complex-exp-value (lw-complex-scale value point)
                               (lw-exp-mixture-node-precision base budget)))
          (lw-complex-mul base (lw-complex-exp-value (lw-complex-scale value point) request))))
         (radius (* (lw-complex-l1 base) (+ (lw-exp-mixture-node-precision base budget) request)))
         (cap (+ (* 1/2 budget) (* (lw-complex-l1 base) request)))))
  :in-theory (union-theories
   '( lw-xmp-left-commutes lw-xmp-left-distributes lw-xmp-fold-constants lw-xmp-times-negative lw-xmp-negative-times lw-xmp-zero-times lw-xmp-minus-one lw-xmp-double-negative lw-xmp-add-cancel lw-xmp-double lw-xmp-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(local (defthm lw-xmp-add-differences
 (equal (lw-complex-sub (lw-complex-add a b) (lw-complex-add c d))
        (lw-complex-add (lw-complex-sub a c) (lw-complex-sub b d)))
 :hints (("Goal" :in-theory (enable lw-complex-sub lw-complex-add)))))

(local (defthm lw-xmp-zero-disk
 (lw-complex-diskp (cons 0 0) 0)
 :hints (("Goal" :in-theory (enable lw-complex-diskp lw-complexp lw-diskp)))))

(local (defthm lw-xmp-sub-self
 (equal (lw-complex-sub point point) (cons 0 0))
 :hints (("Goal" :in-theory (enable lw-complex-sub)))))

(defthm lw-exp-mixture-common-comparison
 (implies (and (lw-exp-mixturep nodes) (lw-complexp point)
               (rationalp budget) (< 0 budget) (rationalp request) (< 0 request))
  (lw-complex-diskp
   (lw-complex-sub (lw-exp-mixture-value nodes point budget)
                   (lw-exp-mixture-common-value nodes point request))
   (+ (* 1/2 (len nodes) budget) (* (lw-exp-mixture-mass nodes) request))))
 :hints (("Goal" :induct (lw-exp-mixturep nodes)
                 :in-theory (e/d (lw-exp-mixturep lw-exp-mixture-mass)
                  (lw-exp-mixture-node-common-comparison lw-complex-add-disk)))
         (and stable-under-simplificationp
          '(:expand ((lw-exp-mixture-value nodes point budget)
                     (lw-exp-mixture-common-value nodes point request)
                     (lw-exp-mixture-value nil point budget)
                     (lw-exp-mixture-common-value nil point request))
            :use ((:instance lw-exp-mixture-node-common-comparison (value (caar nodes)) (base (cdar nodes)))
                  (:instance lw-complex-add-disk
                   (left (lw-complex-sub
                    (lw-complex-mul (cdar nodes) (lw-complex-exp-value (lw-complex-scale (caar nodes) point)
                                                  (lw-exp-mixture-node-precision (cdar nodes) budget)))
                    (lw-complex-mul (cdar nodes) (lw-complex-exp-value (lw-complex-scale (caar nodes) point) request))))
                   (right (lw-complex-sub (lw-exp-mixture-value (cdr nodes) point budget)
                                         (lw-exp-mixture-common-value (cdr nodes) point request)))
                   (radius (+ (* 1/2 budget) (* (lw-complex-l1 (cdar nodes)) request)))
                   (other-radius (+ (* 1/2 (len (cdr nodes)) budget) (* (lw-exp-mixture-mass (cdr nodes)) request)))))
            :nonlinearp nil :do-not-induct t))))

(defthm lw-exp-mixture-polynomial-common-comparison
 (implies (and (lw-exp-mixturep nodes) (lw-complex-diskp point radius)
               (natp target) (rationalp error) (< 0 error) (rationalp request) (< 0 request))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-complex-polynomial
     (lw-exp-mixture-coefficients nodes 0 (+ 1 (lw-exp-mixture-degree nodes radius target error))) point 0)
    (lw-exp-mixture-common-value nodes point request))
   (+ (* 3/2 error) (* (lw-exp-mixture-mass nodes) request))))
 :hints (("Goal"
  :use ((:instance lw-complex-disk-data)
        lw-exp-mixture-computed-uniform-polynomial lw-exp-mixture-budget-positive lw-exp-mixture-budget-adequate
        lw-exp-mixture-degree-data
        (:instance lw-exp-mixture-coefficients-valid (offset 0)
         (count (+ 1 (lw-exp-mixture-degree nodes radius target error))))
        (:instance lw-complex-polynomial-rational
         (coefficients (lw-exp-mixture-coefficients nodes 0 (+ 1 (lw-exp-mixture-degree nodes radius target error))))
         (offset 0))
        (:instance lw-exp-mixture-value-rational (budget (lw-exp-mixture-budget nodes error)))
        lw-exp-mixture-common-value-rational lw-exp-mixture-mass-nonnegative
        (:instance lw-exp-mixture-common-comparison (budget (lw-exp-mixture-budget nodes error)))
        (:instance lw-complex-difference-triangle
         (left (lw-complex-polynomial
          (lw-exp-mixture-coefficients nodes 0 (+ 1 (lw-exp-mixture-degree nodes radius target error))) point 0))
         (middle (lw-exp-mixture-value nodes point (lw-exp-mixture-budget nodes error)))
         (right (lw-exp-mixture-common-value nodes point request))
         (radius error)
         (other-radius (+ (* 1/2 (len nodes) (lw-exp-mixture-budget nodes error))
                          (* (lw-exp-mixture-mass nodes) request))))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub
          (lw-complex-polynomial
           (lw-exp-mixture-coefficients nodes 0 (+ 1 (lw-exp-mixture-degree nodes radius target error))) point 0)
          (lw-exp-mixture-common-value nodes point request)))
         (radius (+ error (* 1/2 (len nodes) (lw-exp-mixture-budget nodes error))
                          (* (lw-exp-mixture-mass nodes) request)))
         (cap (+ (* 3/2 error) (* (lw-exp-mixture-mass nodes) request)))))
  :in-theory (union-theories
   '( lw-xmp-left-commutes lw-xmp-left-distributes lw-xmp-fold-constants lw-xmp-times-negative lw-xmp-negative-times lw-xmp-zero-times lw-xmp-minus-one lw-xmp-double-negative lw-xmp-add-cancel lw-xmp-double lw-xmp-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(defun lw-exp-mixture-affine-polynomial (nodes center slope argument-cap target error)
 (lw-polynomial-affine
  (lw-exp-mixture-coefficients nodes 0 (+ 1 (lw-exp-mixture-degree nodes argument-cap target error)))
  center slope))

(local (in-theory (disable lw-exp-mixture-affine-polynomial)))

(defthm lw-exp-mixture-affine-polynomial-valid
 (implies (and (lw-exp-mixturep nodes) (lw-complexp center) (lw-complexp slope)
               (rationalp argument-cap) (<= 0 argument-cap) (natp target) (rationalp error) (< 0 error))
  (lw-complex-coefficientsp (lw-exp-mixture-affine-polynomial nodes center slope argument-cap target error)))
 :hints (("Goal"
  :use ((:instance lw-exp-mixture-degree-data (radius argument-cap))
        (:instance lw-exp-mixture-coefficients-valid (offset 0)
         (count (+ 1 (lw-exp-mixture-degree nodes argument-cap target error))))
        (:instance lw-polynomial-affine-valid
         (coefficients (lw-exp-mixture-coefficients nodes 0 (+ 1 (lw-exp-mixture-degree nodes argument-cap target error))))))
  :in-theory (union-theories
   '(lw-exp-mixture-affine-polynomial lw-xmp-left-commutes lw-xmp-left-distributes lw-xmp-fold-constants lw-xmp-times-negative lw-xmp-negative-times lw-xmp-zero-times lw-xmp-minus-one lw-xmp-double-negative lw-xmp-add-cancel lw-xmp-double lw-xmp-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-exp-mixture-affine-common-comparison
 (implies (and (lw-exp-mixturep nodes) (lw-complexp center) (lw-complexp slope) (lw-complexp point)
               (lw-complex-diskp (lw-complex-add center (lw-complex-mul slope point)) argument-cap)
               (natp target) (rationalp error) (< 0 error) (rationalp request) (< 0 request))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-complex-polynomial
     (lw-exp-mixture-affine-polynomial nodes center slope argument-cap target error) point 0)
    (lw-exp-mixture-common-value nodes (lw-complex-add center (lw-complex-mul slope point)) request))
   (+ (* 3/2 error) (* (lw-exp-mixture-mass nodes) request))))
 :hints (("Goal"
  :use ((:instance lw-complex-disk-data
         (point (lw-complex-add center (lw-complex-mul slope point))) (radius argument-cap))
        (:instance lw-exp-mixture-degree-data (radius argument-cap))
        (:instance lw-exp-mixture-coefficients-valid (offset 0)
         (count (+ 1 (lw-exp-mixture-degree nodes argument-cap target error))))
        (:instance lw-polynomial-affine-evaluation
         (coefficients (lw-exp-mixture-coefficients nodes 0 (+ 1 (lw-exp-mixture-degree nodes argument-cap target error)))))
        (:instance lw-exp-mixture-polynomial-common-comparison
         (point (lw-complex-add center (lw-complex-mul slope point))) (radius argument-cap)))
  :in-theory (union-theories
   '(lw-exp-mixture-affine-polynomial lw-xmp-left-commutes lw-xmp-left-distributes lw-xmp-fold-constants lw-xmp-times-negative lw-xmp-negative-times lw-xmp-zero-times lw-xmp-minus-one lw-xmp-double-negative lw-xmp-add-cancel lw-xmp-double lw-xmp-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

