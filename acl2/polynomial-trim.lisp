(in-package "ACL2")

(include-book "polynomial-division-leading")

; Remove trailing zero coefficients without changing any polynomial value.

(local (defthm lw-ptr-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ptr-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ptr-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ptr-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ptr-times-negative (a b) (b a)))
                 :in-theory (disable lw-ptr-times-negative)))))

(local (defthm lw-ptr-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ptr-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ptr-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ptr-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ptr-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ptr-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ptr-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ptr-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ptr-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ptr-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ptr-left-commutes)))))
(defun lw-polynomial-trim (coefficients)
 (declare (xargs :measure (acl2-count coefficients) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (endp coefficients) nil
  (let ((tail (lw-polynomial-trim (cdr coefficients))))
   (if (consp tail) (cons (car coefficients) tail)
    (if (equal (car coefficients) (cons 0 0)) nil (list (car coefficients)))))))

(local (defthm lw-ptr-length-natural
 (natp (len coefficients))
 :hints (("Goal" :induct (len coefficients) :in-theory (union-theories
 '(fold-consts-in-+ len endp lw-ptr-left-commutes lw-ptr-left-distributes lw-ptr-fold-constants lw-ptr-times-negative lw-ptr-negative-times lw-ptr-zero-times lw-ptr-minus-one lw-ptr-double-negative lw-ptr-add-cancel lw-ptr-double lw-ptr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))
 :rule-classes (:rewrite :type-prescription)))

(defthm lw-polynomial-trim-valid
 (implies (lw-complex-coefficientsp coefficients)
  (and (lw-complex-coefficientsp (lw-polynomial-trim coefficients))
       (<= (len (lw-polynomial-trim coefficients)) (len coefficients))))
 :hints (("Goal" :induct (lw-polynomial-trim coefficients)
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-polynomial-trim) lw-polynomial-trim lw-complex-coefficientsp len endp lw-ptr-length-natural lw-ptr-left-commutes lw-ptr-left-distributes lw-ptr-fold-constants lw-ptr-times-negative lw-ptr-negative-times lw-ptr-zero-times lw-ptr-minus-one lw-ptr-double-negative lw-ptr-add-cancel lw-ptr-double lw-ptr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-ptr-leading-cons
 (implies (consp tail)
  (equal (lw-polynomial-leading (cons head tail)) (lw-polynomial-leading tail)))
 :hints (("Goal" :expand ((lw-polynomial-leading (cons head tail))) :in-theory (union-theories
 '(fold-consts-in-+ endp lw-ptr-left-commutes lw-ptr-left-distributes lw-ptr-fold-constants lw-ptr-times-negative lw-ptr-negative-times lw-ptr-zero-times lw-ptr-minus-one lw-ptr-double-negative lw-ptr-add-cancel lw-ptr-double lw-ptr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-polynomial-trim-nonzero-leading
 (implies (consp (lw-polynomial-trim coefficients))
  (not (equal (lw-polynomial-leading (lw-polynomial-trim coefficients)) (cons 0 0))))
 :hints (("Goal" :induct (lw-polynomial-trim coefficients)
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-polynomial-trim) lw-polynomial-trim lw-ptr-leading-cons lw-polynomial-leading endp lw-ptr-left-commutes lw-ptr-left-distributes lw-ptr-fold-constants lw-ptr-times-negative lw-ptr-negative-times lw-ptr-zero-times lw-ptr-minus-one lw-ptr-double-negative lw-ptr-add-cancel lw-ptr-double lw-ptr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defun lw-ptr-offset-induct (coefficients offset)
 (declare (xargs :measure (acl2-count coefficients) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (endp coefficients) offset (lw-ptr-offset-induct (cdr coefficients) (+ 1 offset)))))

(local (defthm lw-ptr-empty-polynomial
 (equal (lw-complex-polynomial nil point offset) (cons 0 0))
 :hints (("Goal" :expand ((lw-complex-polynomial nil point offset)) :in-theory (union-theories
 '(fold-consts-in-+ lw-ptr-left-commutes lw-ptr-left-distributes lw-ptr-fold-constants lw-ptr-times-negative lw-ptr-negative-times lw-ptr-zero-times lw-ptr-minus-one lw-ptr-double-negative lw-ptr-add-cancel lw-ptr-double lw-ptr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-ptr-zero-multiple
 (equal (lw-complex-mul (cons 0 0) point) (cons 0 0))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-mul lw-ptr-left-commutes lw-ptr-left-distributes lw-ptr-fold-constants lw-ptr-times-negative lw-ptr-negative-times lw-ptr-zero-times lw-ptr-minus-one lw-ptr-double-negative lw-ptr-add-cancel lw-ptr-double lw-ptr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-polynomial-trim-evaluation
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp point) (natp offset))
  (equal (lw-complex-polynomial (lw-polynomial-trim coefficients) point offset)
         (lw-complex-polynomial coefficients point offset)))
 :hints (("Goal" :induct (lw-ptr-offset-induct coefficients offset)
          :expand ((lw-complex-polynomial coefficients point offset))
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-ptr-offset-induct) lw-polynomial-trim lw-complex-polynomial lw-complex-coefficientsp lw-complex-power-rational lw-complex-ring-rational lw-complex-add-zero lw-ptr-empty-polynomial lw-ptr-zero-multiple endp lw-ptr-left-commutes lw-ptr-left-distributes lw-ptr-fold-constants lw-ptr-times-negative lw-ptr-negative-times lw-ptr-zero-times lw-ptr-minus-one lw-ptr-double-negative lw-ptr-add-cancel lw-ptr-double lw-ptr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-polynomial-trim-normalized
 (implies (and (lw-complex-coefficientsp coefficients) (consp coefficients)
               (not (equal (lw-polynomial-leading coefficients) (cons 0 0))))
  (equal (lw-polynomial-trim coefficients) coefficients))
 :hints (("Goal" :induct (lw-polynomial-trim coefficients)
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-polynomial-trim) lw-polynomial-trim lw-polynomial-leading lw-complex-coefficientsp endp lw-ptr-left-commutes lw-ptr-left-distributes lw-ptr-fold-constants lw-ptr-times-negative lw-ptr-negative-times lw-ptr-zero-times lw-ptr-minus-one lw-ptr-double-negative lw-ptr-add-cancel lw-ptr-double lw-ptr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))
