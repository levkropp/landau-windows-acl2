(in-package "ACL2")

(include-book "polynomial-monomials")

; Separate a finite polynomial into its actual leading monomial and
; the lower coefficient list. No factorization hypothesis is used.

(local (defthm lw-ple-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ple-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ple-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ple-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ple-times-negative (a b) (b a)))
                 :in-theory (disable lw-ple-times-negative)))))

(local (defthm lw-ple-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ple-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ple-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ple-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ple-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ple-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ple-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ple-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ple-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ple-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ple-left-commutes)))))

(local (defthm lw-ple-length-natural
 (natp (len coefficients)) :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-ple-polynomial-empty
 (equal (lw-complex-polynomial nil point offset) (cons 0 0))
 :hints (("Goal" :expand ((lw-complex-polynomial nil point offset)) :in-theory (union-theories
 '(fold-consts-in-+ lw-ple-left-commutes lw-ple-left-distributes lw-ple-fold-constants lw-ple-times-negative lw-ple-negative-times lw-ple-zero-times lw-ple-minus-one lw-ple-double-negative lw-ple-add-cancel lw-ple-double lw-ple-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-ple-polynomial-step
 (implies (consp coefficients)
  (equal (lw-complex-polynomial coefficients point offset)
   (lw-complex-add (lw-complex-mul (car coefficients) (lw-complex-power point offset))
                   (lw-complex-polynomial (cdr coefficients) point (+ 1 offset)))))
 :hints (("Goal" :expand ((lw-complex-polynomial coefficients point offset)) :in-theory (union-theories
 '(fold-consts-in-+ lw-ple-left-commutes lw-ple-left-distributes lw-ple-fold-constants lw-ple-times-negative lw-ple-negative-times lw-ple-zero-times lw-ple-minus-one lw-ple-double-negative lw-ple-add-cancel lw-ple-double lw-ple-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defun lw-ple-append-induct (left offset)
 (declare (xargs :measure (acl2-count left) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (endp left) offset (lw-ple-append-induct (cdr left) (+ 1 offset)))))

(defthm lw-complex-polynomial-append
 (implies (and (lw-complex-coefficientsp left) (lw-complex-coefficientsp right)
               (lw-complexp point) (natp offset))
  (equal (lw-complex-polynomial (append left right) point offset)
   (lw-complex-add (lw-complex-polynomial left point offset)
    (lw-complex-polynomial right point (+ offset (len left))))))
 :hints (("Goal" :induct (lw-ple-append-induct left offset)
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-ple-append-induct) append len lw-ple-length-natural lw-complex-coefficientsp lw-ple-polynomial-step lw-ple-polynomial-empty lw-complex-polynomial-rational lw-complex-power-rational lw-complex-ring-rational lw-complex-add-associative lw-complex-add-zero lw-ple-left-commutes lw-ple-left-distributes lw-ple-fold-constants lw-ple-times-negative lw-ple-negative-times lw-ple-zero-times lw-ple-minus-one lw-ple-double-negative lw-ple-add-cancel lw-ple-double lw-ple-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defun lw-polynomial-leading (coefficients)
 (declare (xargs :measure (acl2-count coefficients) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (endp coefficients) (cons 0 0)
  (if (endp (cdr coefficients)) (car coefficients) (lw-polynomial-leading (cdr coefficients)))))

(defun lw-polynomial-without-leading (coefficients)
 (declare (xargs :measure (acl2-count coefficients) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (or (endp coefficients) (endp (cdr coefficients))) nil
  (cons (car coefficients) (lw-polynomial-without-leading (cdr coefficients)))))

(defthm lw-polynomial-leading-valid
 (implies (lw-complex-coefficientsp coefficients)
  (and (lw-complexp (lw-polynomial-leading coefficients))
       (lw-complex-coefficientsp (lw-polynomial-without-leading coefficients))
       (equal (len (lw-polynomial-without-leading coefficients))
              (if (consp coefficients) (- (len coefficients) 1) 0))))
 :hints (("Goal" :induct (lw-polynomial-without-leading coefficients)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-leading lw-polynomial-without-leading lw-complex-coefficientsp len (:executable-counterpart lw-complexp) lw-ple-left-commutes lw-ple-left-distributes lw-ple-fold-constants lw-ple-times-negative lw-ple-negative-times lw-ple-zero-times lw-ple-minus-one lw-ple-double-negative lw-ple-add-cancel lw-ple-double lw-ple-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-ple-pair
 (implies (consp coefficients) (equal (cons (car coefficients) (cdr coefficients)) coefficients))))

(defthm lw-polynomial-leading-split
 (implies (and (consp coefficients) (lw-complex-coefficientsp coefficients))
  (equal (append (lw-polynomial-without-leading coefficients) (list (lw-polynomial-leading coefficients)))
         coefficients))
 :hints (("Goal" :induct (lw-polynomial-without-leading coefficients)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-leading lw-polynomial-without-leading lw-complex-coefficientsp append lw-ple-pair lw-ple-left-commutes lw-ple-left-distributes lw-ple-fold-constants lw-ple-times-negative lw-ple-negative-times lw-ple-zero-times lw-ple-minus-one lw-ple-double-negative lw-ple-add-cancel lw-ple-double lw-ple-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-ple-single-polynomial
 (implies (and (lw-complexp leading) (lw-complexp point))
  (equal (lw-complex-polynomial (list leading) point offset)
         (lw-complex-mul leading (lw-complex-power point offset))))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-ple-polynomial-step lw-ple-polynomial-empty lw-complex-power-rational lw-complex-ring-rational lw-complex-add-zero lw-ple-left-commutes lw-ple-left-distributes lw-ple-fold-constants lw-ple-times-negative lw-ple-negative-times lw-ple-zero-times lw-ple-minus-one lw-ple-double-negative lw-ple-add-cancel lw-ple-double lw-ple-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-polynomial-leading-evaluation
 (implies (and (consp coefficients) (lw-complex-coefficientsp coefficients) (lw-complexp point))
  (equal (lw-complex-polynomial coefficients point 0)
   (lw-complex-add
    (lw-complex-polynomial (lw-polynomial-without-leading coefficients) point 0)
    (lw-complex-mul (lw-polynomial-leading coefficients)
     (lw-complex-power point (len (lw-polynomial-without-leading coefficients)))))))
 :hints (("Goal"
  :use (lw-polynomial-leading-split lw-polynomial-leading-valid
        (:instance lw-complex-polynomial-append
          (left (lw-polynomial-without-leading coefficients))
          (right (list (lw-polynomial-leading coefficients))) (offset 0)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-coefficientsp lw-ple-length-natural lw-ple-single-polynomial lw-ple-left-commutes lw-ple-left-distributes lw-ple-fold-constants lw-ple-times-negative lw-ple-negative-times lw-ple-zero-times lw-ple-minus-one lw-ple-double-negative lw-ple-add-cancel lw-ple-double lw-ple-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

