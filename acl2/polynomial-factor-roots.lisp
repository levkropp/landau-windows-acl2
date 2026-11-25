(in-package "ACL2")

(include-book "polynomial-factor-budgets")

; A terminating list of rational linear factors, obtained by repeated
; approximate root search and exact synthetic division.

(local (defthm lw-pfr-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pfr-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pfr-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pfr-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pfr-times-negative (a b) (b a)))
                 :in-theory (disable lw-pfr-times-negative)))))

(local (defthm lw-pfr-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pfr-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pfr-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pfr-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pfr-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pfr-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pfr-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-pfr-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pfr-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pfr-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-pfr-left-commutes)))))
(local (defthm lw-pfr-length-natural
 (natp (len coefficients))
 :hints (("Goal" :induct (len coefficients) :in-theory (union-theories
 '(fold-consts-in-+ len endp lw-pfr-left-commutes lw-pfr-left-distributes lw-pfr-fold-constants lw-pfr-times-negative lw-pfr-negative-times lw-pfr-zero-times lw-pfr-minus-one lw-pfr-double-negative lw-pfr-add-cancel lw-pfr-double lw-pfr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))
 :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-pfr-base-length
 (implies (and (lw-polynomial-factor-inputp coefficients bound epsilon)
               (not (consp (cdr coefficients))))
  (equal (len coefficients) 1))
 :rule-classes nil
 :hints (("Goal" :expand ((len coefficients)) :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-factor-inputp lw-complex-coefficientsp len endp lw-pfr-left-commutes lw-pfr-left-distributes lw-pfr-fold-constants lw-pfr-times-negative lw-pfr-negative-times lw-pfr-zero-times lw-pfr-minus-one lw-pfr-double-negative lw-pfr-add-cancel lw-pfr-double lw-pfr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
          :do-not-induct t))))

(defun lw-polynomial-factor-roots (coefficients bound epsilon)
 (declare (xargs :measure (len coefficients)
  :hints (("Goal" :use (lw-polynomial-factor-step-data)
           :in-theory (theory 'ground-zero)))))
 (if (or (not (lw-polynomial-factor-inputp coefficients bound epsilon))
         (not (consp (cdr coefficients)))) nil
  (let* ((root (lw-polynomial-factor-root coefficients epsilon))
         (quotient (lw-polynomial-divided-difference coefficients root))
         (next-error (lw-polynomial-factor-next-error coefficients bound epsilon)))
   (cons root (lw-polynomial-factor-roots quotient bound next-error)))))

(defthm lw-polynomial-factor-roots-data
 (implies (lw-polynomial-factor-inputp coefficients bound epsilon)
  (and (lw-ray-pointsp (lw-polynomial-factor-roots coefficients bound epsilon))
       (equal (len (lw-polynomial-factor-roots coefficients bound epsilon))
              (- (len coefficients) 1))))
 :hints (("Goal" :induct (lw-polynomial-factor-roots coefficients bound epsilon)
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-polynomial-factor-roots) lw-polynomial-factor-roots lw-ray-pointsp len endp lw-pfr-length-natural lw-pfr-left-commutes lw-pfr-left-distributes lw-pfr-fold-constants lw-pfr-times-negative lw-pfr-negative-times lw-pfr-zero-times lw-pfr-minus-one lw-pfr-double-negative lw-pfr-add-cancel lw-pfr-double lw-pfr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
         (and stable-under-simplificationp
          '(:use (lw-polynomial-factor-step-data lw-pfr-base-length) :do-not-induct t))))

(defun lw-polynomial-linear-factor-value (roots leading point)
 (declare (xargs :measure (acl2-count roots) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (endp roots) leading
  (lw-complex-mul (lw-complex-sub point (car roots))
   (lw-polynomial-linear-factor-value (cdr roots) leading point))))

(defthm lw-polynomial-linear-factor-value-rational
 (implies (and (lw-ray-pointsp roots) (lw-complexp leading) (lw-complexp point))
  (lw-complexp (lw-polynomial-linear-factor-value roots leading point)))
 :hints (("Goal" :induct (lw-polynomial-linear-factor-value roots leading point)
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-polynomial-linear-factor-value) lw-polynomial-linear-factor-value lw-ray-pointsp lw-complex-ring-rational endp lw-pfr-left-commutes lw-pfr-left-distributes lw-pfr-fold-constants lw-pfr-times-negative lw-pfr-negative-times lw-pfr-zero-times lw-pfr-minus-one lw-pfr-double-negative lw-pfr-add-cancel lw-pfr-double lw-pfr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))
