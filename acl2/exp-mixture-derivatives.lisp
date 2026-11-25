(in-package "ACL2")

(include-book "exp-mixture-precision")
(include-book "polynomial-derivatives")

; Multiplying each exponential base by its rate gives the derivative mixture.
; All identities concern actual finite rational coefficient constructors.

(local (in-theory
 (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
          lw-complex-diskp lw-diskp lw-complex-power lw-rational-power
          lw-complex-polynomial lw-complex-polynomial-horner lw-complex-polynomial-derivative
          lw-complex-coefficient-at lw-exp-mixturep lw-exp-mixture-coefficient lw-exp-mixture-coefficients
          lw-exp-term lw-exp-mixture-common-value lw-exp-mixture-affine-polynomial
          lw-exp-mixture-degree lw-exp-mixture-degree-raw lw-exp-mixture-budget
          lw-complex-mul-subtract lw-complex-mul-commutative lw-complex-mul-left-commutes)))

(local (defthm lw-xmd-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-xmd-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-xmd-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-xmd-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-xmd-times-negative (a b) (b a)))
                 :in-theory (disable lw-xmd-times-negative)))))

(local (defthm lw-xmd-zero-times (equal (* 0 a) 0)))

(local (defthm lw-xmd-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-xmd-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-xmd-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-xmd-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-xmd-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-xmd-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-xmd-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-xmd-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-xmd-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-xmd-left-commutes)))))

(defun lw-exp-mixture-derivative-nodes (nodes)
 (if (consp nodes)
  (cons (cons (caar nodes) (lw-complex-scale (caar nodes) (cdar nodes)))
        (lw-exp-mixture-derivative-nodes (cdr nodes)))
  nil))

(defthm lw-exp-mixture-derivative-nodes-valid
 (implies (lw-exp-mixturep nodes)
  (and (lw-exp-mixturep (lw-exp-mixture-derivative-nodes nodes))
       (equal (len (lw-exp-mixture-derivative-nodes nodes)) (len nodes))))
 :hints (("Goal" :induct (lw-exp-mixture-derivative-nodes nodes)
  :in-theory (union-theories
   '(lw-exp-mixture-derivative-nodes lw-exp-mixturep lw-complex-scale-rational len lw-xmd-left-commutes lw-xmd-left-distributes lw-xmd-fold-constants lw-xmd-times-negative lw-xmd-negative-times lw-xmd-zero-times lw-xmd-minus-one lw-xmd-double-negative lw-xmd-add-cancel lw-xmd-double lw-xmd-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory)))))

(local (defthm lw-xmd-term-recurrence
 (implies (and (rationalp rate) (natp index))
  (equal (* (+ 1 index) (lw-exp-term rate (+ 1 index))) (* rate (lw-exp-term rate index))))
 :hints (("Goal"
  :use ((:instance lw-exp-term-successor (value rate))
        (:instance lw-exp-term-rational (value rate))
        (:instance lw-xmd-inverse-factor (divisor (+ 1 index)) (coefficient (* rate (lw-exp-term rate index)))))
  :in-theory (union-theories
   '( lw-xmd-left-commutes lw-xmd-left-distributes lw-xmd-fold-constants lw-xmd-times-negative lw-xmd-negative-times lw-xmd-zero-times lw-xmd-minus-one lw-xmd-double-negative lw-xmd-add-cancel lw-xmd-double lw-xmd-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t))))

(local (defthm lw-xmd-scaled-term
 (implies (and (rationalp rate) (natp index) (lw-complexp base))
  (equal (lw-complex-scale (+ 1 index) (lw-complex-scale (lw-exp-term rate (+ 1 index)) base))
         (lw-complex-scale (lw-exp-term rate index) (lw-complex-scale rate base))))
 :hints (("Goal"
  :use (lw-xmd-term-recurrence
        (:instance lw-exp-term-rational (value rate))
        (:instance lw-exp-term-rational (value rate) (index (+ 1 index))))
  :in-theory (union-theories
   '(lw-complex-scale-compose lw-xmd-left-commutes lw-xmd-left-distributes lw-xmd-fold-constants lw-xmd-times-negative lw-xmd-negative-times lw-xmd-zero-times lw-xmd-minus-one lw-xmd-double-negative lw-xmd-add-cancel lw-xmd-double lw-xmd-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t))))

(defthm lw-exp-mixture-coefficient-recurrence
 (implies (and (lw-exp-mixturep nodes) (natp index))
  (equal (lw-complex-scale (+ 1 index) (lw-exp-mixture-coefficient nodes (+ 1 index)))
         (lw-exp-mixture-coefficient (lw-exp-mixture-derivative-nodes nodes) index)))
 :hints (("Goal" :induct (lw-exp-mixture-derivative-nodes nodes)
  :in-theory (union-theories
   '(lw-exp-mixture-derivative-nodes lw-exp-mixturep lw-exp-mixture-coefficient lw-xmd-scaled-term lw-complex-scale-add lw-complex-scale-zero lw-complex-scale-rational lw-exp-mixture-coefficient-rational lw-exp-term-rational lw-complexp lw-xmd-left-commutes lw-xmd-left-distributes lw-xmd-fold-constants lw-xmd-times-negative lw-xmd-negative-times lw-xmd-zero-times lw-xmd-minus-one lw-xmd-double-negative lw-xmd-add-cancel lw-xmd-double lw-xmd-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory)))))

(local (in-theory (disable lw-exp-mixture-derivative-nodes)))

(local (defthm lw-xmd-empty-coefficients
 (implies (zp count) (equal (lw-exp-mixture-coefficients nodes offset count) nil))
 :hints (("Goal" :expand ((lw-exp-mixture-coefficients nodes offset count)) :in-theory (union-theories
   '( lw-xmd-left-commutes lw-xmd-left-distributes lw-xmd-fold-constants lw-xmd-times-negative lw-xmd-negative-times lw-xmd-zero-times lw-xmd-minus-one lw-xmd-double-negative lw-xmd-add-cancel lw-xmd-double lw-xmd-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))))))

(local (defthm lw-xmd-empty-polynomial
 (equal (lw-complex-polynomial nil point offset) (cons 0 0))
 :hints (("Goal" :in-theory (enable lw-complex-polynomial)))))

(local (defthm lw-xmd-empty-derivative
 (equal (lw-complex-polynomial-derivative nil point) (cons 0 0))
 :hints (("Goal" :in-theory (enable lw-complex-polynomial-derivative)))))

(local (defthm lw-xmd-offset-horner
 (implies (and (lw-exp-mixturep nodes) (natp offset) (posp count) (lw-complexp point))
  (equal (lw-complex-polynomial (lw-exp-mixture-coefficients nodes offset count) point 0)
         (lw-complex-add (lw-exp-mixture-coefficient nodes offset)
          (lw-complex-mul point (lw-complex-polynomial (lw-exp-mixture-coefficients nodes (+ 1 offset) (- count 1)) point 0)))))
 :hints (("Goal"
  :use ((:instance lw-exp-mixture-coefficients-valid)
        (:instance lw-exp-mixture-coefficients-valid (offset (+ 1 offset)) (count (- count 1)))
        (:instance lw-complex-polynomial-horner (coefficients (lw-exp-mixture-coefficients nodes offset count))))
  :expand ((lw-exp-mixture-coefficients nodes offset count))
  :in-theory (union-theories
   '( lw-xmd-left-commutes lw-xmd-left-distributes lw-xmd-fold-constants lw-xmd-times-negative lw-xmd-negative-times lw-xmd-zero-times lw-xmd-minus-one lw-xmd-double-negative lw-xmd-add-cancel lw-xmd-double lw-xmd-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t))))

(local (defthm lw-xmd-derivative-step
 (implies (and (lw-exp-mixturep nodes) (natp offset) (posp count) (lw-complexp point))
  (equal (lw-complex-polynomial-derivative (lw-exp-mixture-coefficients nodes offset count) point)
         (lw-complex-add (lw-complex-polynomial (lw-exp-mixture-coefficients nodes (+ 1 offset) (- count 1)) point 0)
          (lw-complex-mul point (lw-complex-polynomial-derivative (lw-exp-mixture-coefficients nodes (+ 1 offset) (- count 1)) point)))))
 :hints (("Goal"
  :expand ((lw-exp-mixture-coefficients nodes offset count)
           (lw-complex-polynomial-derivative
            (cons (lw-exp-mixture-coefficient nodes offset) (lw-exp-mixture-coefficients nodes (+ 1 offset) (- count 1))) point))
  :in-theory (union-theories
   '( lw-xmd-left-commutes lw-xmd-left-distributes lw-xmd-fold-constants lw-xmd-times-negative lw-xmd-negative-times lw-xmd-zero-times lw-xmd-minus-one lw-xmd-double-negative lw-xmd-add-cancel lw-xmd-double lw-xmd-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t))))

(local (defthm lw-xmd-weighted-coefficient
 (implies (and (lw-exp-mixturep nodes) (natp offset))
  (equal (lw-exp-mixture-coefficient (lw-exp-mixture-derivative-nodes nodes) offset)
         (lw-complex-scale (+ 1 offset) (lw-exp-mixture-coefficient nodes (+ 1 offset)))))
 :hints (("Goal"
  :use ((:instance lw-exp-mixture-coefficient-recurrence (index offset)))
  :in-theory (union-theories
   '( lw-xmd-left-commutes lw-xmd-left-distributes lw-xmd-fold-constants lw-xmd-times-negative lw-xmd-negative-times lw-xmd-zero-times lw-xmd-minus-one lw-xmd-double-negative lw-xmd-add-cancel lw-xmd-double lw-xmd-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))))))

(local (defthm lw-xmd-derivative-algebra
 (implies (and (rationalp offset) (lw-complexp point) (lw-complexp head)
               (lw-complexp original-tail) (lw-complexp weighted-tail))
  (equal
   (lw-complex-add
    (lw-complex-add head (lw-complex-mul point original-tail))
    (lw-complex-mul point (lw-complex-sub weighted-tail (lw-complex-scale (+ 1 offset) original-tail))))
   (lw-complex-sub
    (lw-complex-add (lw-complex-scale (+ 1 offset) head) (lw-complex-mul point weighted-tail))
    (lw-complex-scale offset (lw-complex-add head (lw-complex-mul point original-tail))))))
 :hints (("Goal"
  :in-theory (union-theories
   '(lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale lw-xmd-left-commutes lw-xmd-left-distributes lw-xmd-fold-constants lw-xmd-times-negative lw-xmd-negative-times lw-xmd-zero-times lw-xmd-minus-one lw-xmd-double-negative lw-xmd-add-cancel lw-xmd-double lw-xmd-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t))))

(local (defun lw-xmd-derivative-induct (offset count)
 (declare (xargs :measure (nfix count)))
 (if (or (zp count) (<= count 1)) offset
  (lw-xmd-derivative-induct (+ 1 offset) (- count 1)))))

(defthm lw-exp-mixture-offset-polynomial-derivative
 (implies (and (lw-exp-mixturep nodes) (natp offset) (posp count) (lw-complexp point))
  (equal
   (lw-complex-polynomial-derivative (lw-exp-mixture-coefficients nodes offset count) point)
   (lw-complex-sub (lw-complex-polynomial (lw-exp-mixture-coefficients (lw-exp-mixture-derivative-nodes nodes) offset (- count 1)) point 0)
    (lw-complex-scale offset (lw-complex-polynomial (lw-exp-mixture-coefficients nodes (+ 1 offset) (- count 1)) point 0)))))
 :hints (("Goal"
  :induct (lw-xmd-derivative-induct offset count)
  :in-theory (union-theories
   '((:induction lw-xmd-derivative-induct) lw-xmd-derivative-step lw-xmd-offset-horner lw-xmd-weighted-coefficient lw-xmd-derivative-algebra lw-xmd-empty-coefficients lw-xmd-empty-polynomial lw-xmd-empty-derivative lw-exp-mixture-derivative-nodes-valid lw-exp-mixture-coefficients-valid lw-exp-mixture-coefficient-rational lw-complex-polynomial-rational lw-complex-add-zero lw-complex-sub-zero lw-complex-mul-zero lw-complex-scale-zero lw-complexp lw-xmd-left-commutes lw-xmd-left-distributes lw-xmd-fold-constants lw-xmd-times-negative lw-xmd-negative-times lw-xmd-zero-times lw-xmd-minus-one lw-xmd-double-negative lw-xmd-add-cancel lw-xmd-double lw-xmd-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory)))))

(defthm lw-exp-mixture-polynomial-derivative
 (implies (and (lw-exp-mixturep nodes) (posp count) (lw-complexp point))
  (equal (lw-complex-polynomial-derivative (lw-exp-mixture-coefficients nodes 0 count) point)
         (lw-complex-polynomial (lw-exp-mixture-coefficients (lw-exp-mixture-derivative-nodes nodes) 0 (- count 1)) point 0)))
 :hints (("Goal"
  :use ((:instance lw-exp-mixture-offset-polynomial-derivative (offset 0)))
  :in-theory (union-theories
   '(lw-complex-scale lw-complex-sub-zero lw-complex-polynomial-rational lw-exp-mixture-derivative-nodes-valid lw-exp-mixture-coefficients-valid lw-complexp lw-xmd-left-commutes lw-xmd-left-distributes lw-xmd-fold-constants lw-xmd-times-negative lw-xmd-negative-times lw-xmd-zero-times lw-xmd-minus-one lw-xmd-double-negative lw-xmd-add-cancel lw-xmd-double lw-xmd-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-exp-mixture-affine-linear-coefficient
 (implies (and (lw-exp-mixturep nodes) (posp count) (lw-complexp center) (lw-complexp slope))
  (equal
   (lw-complex-coefficient-at
    (lw-polynomial-affine (lw-exp-mixture-coefficients nodes 0 count) center slope) 1 0)
   (lw-complex-mul slope (lw-complex-polynomial (lw-exp-mixture-coefficients (lw-exp-mixture-derivative-nodes nodes) 0 (- count 1)) center 0))))
 :hints (("Goal"
  :use ((:instance lw-exp-mixture-coefficients-valid (offset 0))
        (:instance lw-polynomial-affine-linear-coefficient (coefficients (lw-exp-mixture-coefficients nodes 0 count)))
        (:instance lw-exp-mixture-polynomial-derivative (point center)))
  :in-theory (union-theories
   '( lw-xmd-left-commutes lw-xmd-left-distributes lw-xmd-fold-constants lw-xmd-times-negative lw-xmd-negative-times lw-xmd-zero-times lw-xmd-minus-one lw-xmd-double-negative lw-xmd-add-cancel lw-xmd-double lw-xmd-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t)))


