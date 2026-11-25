(in-package "ACL2")

(include-book "polynomial-division-leading")
(include-book "polynomial-streaming-search")

; Error requests for recursive approximate synthetic division.

(local (defthm lw-pfb-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pfb-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pfb-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pfb-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pfb-times-negative (a b) (b a)))
                 :in-theory (disable lw-pfb-times-negative)))))

(local (defthm lw-pfb-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pfb-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pfb-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pfb-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pfb-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pfb-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pfb-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-pfb-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pfb-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pfb-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-pfb-left-commutes)))))
(defun lw-polynomial-factor-inputp (coefficients bound epsilon)
 (and (lw-complex-coefficientsp coefficients) (consp coefficients)
      (not (equal (lw-polynomial-leading coefficients) (cons 0 0)))
      (rationalp bound) (<= 0 bound) (rationalp epsilon) (< 0 epsilon)))

(defun lw-polynomial-factor-root (coefficients epsilon)
 (lw-polynomial-global-root-point-fast coefficients (* 1/2 epsilon)))

(defun lw-polynomial-factor-next-error (coefficients bound epsilon)
 (let ((denominator (* 2 (+ 1 bound (* 2 (lw-polynomial-leading-radius coefficients))))))
  (if (equal denominator 0) 0 (* epsilon (/ denominator)))))

(local (defthm lw-pfb-product-rational
 (implies (and (rationalp a) (rationalp b)) (rationalp (* a b)))
 :rule-classes (:rewrite :type-prescription)))
(local (defthm lw-pfb-inverse-rational
 (implies (rationalp x) (rationalp (/ x))) :rule-classes (:rewrite :type-prescription)))
(local (defthm lw-pfb-sum-rational
 (implies (and (rationalp a) (rationalp b)) (rationalp (+ a b)))
 :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-pfb-error-budget
 (implies (and (rationalp bound) (<= 0 bound) (rationalp radius) (<= 1 radius)
               (rationalp epsilon) (< 0 epsilon))
  (let* ((denominator (* 2 (+ 1 bound (* 2 radius))))
         (request (* epsilon (/ denominator))))
   (and (not (equal denominator 0)) (rationalp request) (< 0 request)
        (<= (+ (* 1/2 epsilon) (* (+ bound (* 2 radius)) request)) epsilon))))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance lw-reciprocal-positive (value (* 2 (+ 1 bound (* 2 radius)))))
        (:instance lw-pfb-positive-product (a epsilon) (b (/ (* 2 (+ 1 bound (* 2 radius))))))
        (:instance lw-pfb-inverse-factor (divisor (* 2 (+ 1 bound (* 2 radius)))) (coefficient epsilon)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-pfb-product-rational lw-pfb-inverse-rational lw-pfb-sum-rational lw-pfb-left-commutes lw-pfb-left-distributes lw-pfb-fold-constants lw-pfb-times-negative lw-pfb-negative-times lw-pfb-zero-times lw-pfb-minus-one lw-pfb-double-negative lw-pfb-add-cancel lw-pfb-double lw-pfb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :nonlinearp t))))

(defthm lw-polynomial-factor-next-error-data
 (implies (lw-polynomial-factor-inputp coefficients bound epsilon)
  (and (rationalp (lw-polynomial-factor-next-error coefficients bound epsilon))
       (< 0 (lw-polynomial-factor-next-error coefficients bound epsilon))
       (<= (+ (* 1/2 epsilon)
              (* (+ bound (* 2 (lw-polynomial-leading-radius coefficients)))
                 (lw-polynomial-factor-next-error coefficients bound epsilon)))
           epsilon)))
 :hints (("Goal" :use (lw-polynomial-leading-radius-data
                       (:instance lw-pfb-error-budget (radius (lw-polynomial-leading-radius coefficients))))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-factor-inputp lw-polynomial-factor-next-error lw-pfb-left-commutes lw-pfb-left-distributes lw-pfb-fold-constants lw-pfb-times-negative lw-pfb-negative-times lw-pfb-zero-times lw-pfb-minus-one lw-pfb-double-negative lw-pfb-add-cancel lw-pfb-double lw-pfb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
          :do-not-induct t)))

(defthm lw-polynomial-factor-step-data
 (implies (and (lw-polynomial-factor-inputp coefficients bound epsilon)
               (consp (cdr coefficients)))
  (let* ((root (lw-polynomial-factor-root coefficients epsilon))
         (quotient (lw-polynomial-divided-difference coefficients root)))
   (and (lw-complexp root)
        (lw-complex-diskp root (* 2 (lw-polynomial-leading-radius coefficients)))
        (lw-complex-diskp (lw-complex-polynomial coefficients root 0) (* 1/2 epsilon))
        (lw-polynomial-factor-inputp quotient bound
         (lw-polynomial-factor-next-error coefficients bound epsilon))
        (equal (len quotient) (- (len coefficients) 1))
        (equal (lw-polynomial-leading quotient) (lw-polynomial-leading coefficients)))))
 :hints (("Goal"
  :use (lw-polynomial-factor-next-error-data
        (:instance lw-polynomial-approximate-root-fast (epsilon (* 1/2 epsilon)))
        (:instance lw-polynomial-divided-difference-valid (anchor (lw-polynomial-factor-root coefficients epsilon)))
        (:instance lw-polynomial-divided-difference-leading (anchor (lw-polynomial-factor-root coefficients epsilon)))
        (:instance lw-polynomial-divided-difference-nonempty (anchor (lw-polynomial-factor-root coefficients epsilon))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-factor-inputp lw-polynomial-factor-root lw-pfb-product-rational lw-pfb-left-commutes lw-pfb-left-distributes lw-pfb-fold-constants lw-pfb-times-negative lw-pfb-negative-times lw-pfb-zero-times lw-pfb-minus-one lw-pfb-double-negative lw-pfb-add-cancel lw-pfb-double lw-pfb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))
