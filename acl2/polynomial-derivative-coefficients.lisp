(in-package "ACL2")

(include-book "polynomial-derivatives")

; Explicit coefficient lists for formal polynomial derivatives.
; The weighted-tail identity keeps the evaluation independent of degree.

(local (in-theory
 (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
          lw-complex-diskp lw-diskp lw-complex-power lw-rational-power
          lw-complex-polynomial lw-complex-polynomial-horner lw-complex-coefficient-at
          lw-polynomial-affine lw-polynomial-add-constant lw-polynomial-multiply-linear
          lw-complex-mul-subtract lw-complex-mul-commutative lw-complex-mul-left-commutes)))

(local (defthm lw-pdtc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pdtc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pdtc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pdtc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pdtc-times-negative (a b) (b a)))
                 :in-theory (disable lw-pdtc-times-negative)))))

(local (defthm lw-pdtc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pdtc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pdtc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pdtc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pdtc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pdtc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pdtc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-pdtc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pdtc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pdtc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-pdtc-left-commutes)))))

(local (defthm lw-pdtc-polynomial-nil
 (equal (lw-complex-polynomial nil point offset) (cons 0 0))
 :hints (("Goal" :in-theory (union-theories
 '(lw-complex-polynomial endp lw-pdtc-left-commutes lw-pdtc-left-distributes lw-pdtc-fold-constants lw-pdtc-times-negative lw-pdtc-negative-times lw-pdtc-zero-times lw-pdtc-minus-one lw-pdtc-double-negative lw-pdtc-add-cancel lw-pdtc-double lw-pdtc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))


(defun lw-polynomial-weighted-coefficients (coefficients start)
 (if (endp coefficients) nil
  (cons (lw-complex-scale start (car coefficients))
        (lw-polynomial-weighted-coefficients (cdr coefficients) (+ 1 start)))))

(local (in-theory (disable lw-polynomial-weighted-coefficients)))

(defthm lw-polynomial-weighted-coefficients-valid
 (implies (and (lw-complex-coefficientsp coefficients) (rationalp start))
  (and (lw-complex-coefficientsp (lw-polynomial-weighted-coefficients coefficients start))
       (equal (len (lw-polynomial-weighted-coefficients coefficients start)) (len coefficients))))
 :hints (("Goal"
  :induct (lw-polynomial-weighted-coefficients coefficients start)
  :in-theory (union-theories
 '(lw-polynomial-weighted-coefficients lw-complex-coefficientsp lw-complex-scale-rational len endp lw-pdtc-left-commutes lw-pdtc-left-distributes lw-pdtc-fold-constants lw-pdtc-times-negative lw-pdtc-negative-times lw-pdtc-zero-times lw-pdtc-minus-one lw-pdtc-double-negative lw-pdtc-add-cancel lw-pdtc-double lw-pdtc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-pdtc-weighted-horner
 (implies (and (rationalp start) (lw-complexp a) (lw-complexp tail-value)
               (lw-complexp tail-derivative) (lw-complexp point))
  (equal
   (lw-complex-add (lw-complex-scale start a)
    (lw-complex-mul point
     (lw-complex-add (lw-complex-scale (+ 1 start) tail-value)
                    (lw-complex-mul point tail-derivative))))
   (lw-complex-add
    (lw-complex-scale start (lw-complex-add a (lw-complex-mul point tail-value)))
    (lw-complex-mul point
     (lw-complex-add tail-value (lw-complex-mul point tail-derivative))))))
 :hints (("Goal"
  :in-theory (union-theories
 '(lw-complexp lw-complex-add lw-complex-mul lw-complex-scale lw-pdtc-left-commutes lw-pdtc-left-distributes lw-pdtc-fold-constants lw-pdtc-times-negative lw-pdtc-negative-times lw-pdtc-zero-times lw-pdtc-minus-one lw-pdtc-double-negative lw-pdtc-add-cancel lw-pdtc-double lw-pdtc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(defthm lw-polynomial-weighted-coefficients-evaluation
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp point) (rationalp start))
  (equal
   (lw-complex-polynomial (lw-polynomial-weighted-coefficients coefficients start) point 0)
   (lw-complex-add
    (lw-complex-scale start (lw-complex-polynomial coefficients point 0))
    (lw-complex-mul point (lw-complex-polynomial-derivative coefficients point)))))
 :hints (("Goal"
  :induct (lw-polynomial-weighted-coefficients coefficients start)
  :in-theory (union-theories
 '(lw-pdtc-polynomial-nil (:executable-counterpart lw-complexp) lw-polynomial-weighted-coefficients lw-polynomial-weighted-coefficients-valid lw-complex-coefficientsp lw-complex-polynomial-horner lw-complex-polynomial-derivative lw-complex-polynomial-rational lw-complex-polynomial-derivative-rational lw-pdtc-weighted-horner lw-complex-scale-rational lw-complex-add-zero lw-complex-mul-zero lw-complex-scale-zero endp lw-pdtc-left-commutes lw-pdtc-left-distributes lw-pdtc-fold-constants lw-pdtc-times-negative lw-pdtc-negative-times lw-pdtc-zero-times lw-pdtc-minus-one lw-pdtc-double-negative lw-pdtc-add-cancel lw-pdtc-double lw-pdtc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-pdtc-weighted-nil
 (equal (lw-polynomial-weighted-coefficients nil start) nil)
 :hints (("Goal" :in-theory (union-theories
 '(lw-polynomial-weighted-coefficients endp lw-pdtc-left-commutes lw-pdtc-left-distributes lw-pdtc-fold-constants lw-pdtc-times-negative lw-pdtc-negative-times lw-pdtc-zero-times lw-pdtc-minus-one lw-pdtc-double-negative lw-pdtc-add-cancel lw-pdtc-double lw-pdtc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-pdtc-derivative-nil
 (equal (lw-complex-polynomial-derivative nil point) (cons 0 0))
 :hints (("Goal" :in-theory (union-theories
 '(lw-complex-polynomial-derivative endp lw-pdtc-left-commutes lw-pdtc-left-distributes lw-pdtc-fold-constants lw-pdtc-times-negative lw-pdtc-negative-times lw-pdtc-zero-times lw-pdtc-minus-one lw-pdtc-double-negative lw-pdtc-add-cancel lw-pdtc-double lw-pdtc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))


(defun lw-polynomial-derivative-coefficients (coefficients)
 (lw-polynomial-weighted-coefficients (cdr coefficients) 1))

(local (in-theory (disable lw-polynomial-derivative-coefficients)))

(defthm lw-polynomial-derivative-coefficients-valid
 (implies (lw-complex-coefficientsp coefficients)
  (and (lw-complex-coefficientsp (lw-polynomial-derivative-coefficients coefficients))
       (equal (len (lw-polynomial-derivative-coefficients coefficients)) (len (cdr coefficients)))))
 :hints (("Goal"
  :use ((:instance lw-polynomial-weighted-coefficients-valid (coefficients (cdr coefficients)) (start 1)))
  :in-theory (union-theories
 '(lw-polynomial-derivative-coefficients lw-complex-coefficientsp lw-pdtc-left-commutes lw-pdtc-left-distributes lw-pdtc-fold-constants lw-pdtc-times-negative lw-pdtc-negative-times lw-pdtc-zero-times lw-pdtc-minus-one lw-pdtc-double-negative lw-pdtc-add-cancel lw-pdtc-double lw-pdtc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-polynomial-derivative-coefficients-evaluation
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp point))
  (equal
   (lw-complex-polynomial (lw-polynomial-derivative-coefficients coefficients) point 0)
   (lw-complex-polynomial-derivative coefficients point)))
 :hints (("Goal"
  :use ((:instance lw-polynomial-weighted-coefficients-evaluation
         (coefficients (cdr coefficients)) (start 1))
        (:instance lw-complex-polynomial-rational (coefficients (cdr coefficients)) (offset 0)))
  :expand ((lw-complex-polynomial-derivative coefficients point))
  :in-theory (union-theories
 '(lw-pdtc-weighted-nil lw-pdtc-derivative-nil lw-pdtc-polynomial-nil lw-polynomial-derivative-coefficients lw-complex-coefficientsp lw-complex-scale-one lw-complex-add-zero lw-complex-mul-zero (:executable-counterpart lw-complexp) endp lw-pdtc-left-commutes lw-pdtc-left-distributes lw-pdtc-fold-constants lw-pdtc-times-negative lw-pdtc-negative-times lw-pdtc-zero-times lw-pdtc-minus-one lw-pdtc-double-negative lw-pdtc-add-cancel lw-pdtc-double lw-pdtc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

