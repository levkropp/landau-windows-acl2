(in-package "ACL2")

(include-book "polynomial-leading")

; A sharp degree bound retains the one power needed for leading-term
; dominance at large radius. The mass is the finite sum of coefficient L1s.

(local (defthm lw-pdb-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pdb-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pdb-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pdb-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pdb-times-negative (a b) (b a)))
                 :in-theory (disable lw-pdb-times-negative)))))

(local (defthm lw-pdb-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pdb-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pdb-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pdb-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pdb-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pdb-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pdb-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-pdb-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pdb-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pdb-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-pdb-left-commutes)))))

(local (defthm lw-pdb-length-natural
 (natp (len coefficients)) :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-pdb-empty-polynomial
 (equal (lw-complex-polynomial nil point 0) (cons 0 0))
 :hints (("Goal" :expand ((lw-complex-polynomial nil point 0)) :in-theory (union-theories
 '(fold-consts-in-+ lw-pdb-left-commutes lw-pdb-left-distributes lw-pdb-fold-constants lw-pdb-times-negative lw-pdb-negative-times lw-pdb-zero-times lw-pdb-minus-one lw-pdb-double-negative lw-pdb-add-cancel lw-pdb-double lw-pdb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-pdb-zero-disk
 (lw-complex-diskp (cons 0 0) 0)
 :hints (("Goal" :in-theory (enable lw-complex-diskp lw-complexp lw-diskp)))))

(local (defthm lw-pdb-power-step
 (implies (posp degree)
  (equal (lw-rational-power radius degree)
         (* radius (lw-rational-power radius (- degree 1)))))
 :hints (("Goal" :expand ((lw-rational-power radius degree)) :in-theory (union-theories
 '(fold-consts-in-+ lw-pdb-left-commutes lw-pdb-left-distributes lw-pdb-fold-constants lw-pdb-times-negative lw-pdb-negative-times lw-pdb-zero-times lw-pdb-minus-one lw-pdb-double-negative lw-pdb-add-cancel lw-pdb-double lw-pdb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-pdb-single-value
 (implies (and (lw-complex-coefficientsp coefficients) (consp coefficients)
               (equal (cdr coefficients) nil) (lw-complexp point))
  (equal (lw-complex-polynomial coefficients point 0) (car coefficients)))
 :hints (("Goal"
  :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-coefficientsp lw-complex-polynomial-horner lw-pdb-empty-polynomial lw-complex-mul-zero lw-complex-add-zero (:executable-counterpart lw-complexp) lw-pdb-left-commutes lw-pdb-left-distributes lw-pdb-fold-constants lw-pdb-times-negative lw-pdb-negative-times lw-pdb-zero-times lw-pdb-minus-one lw-pdb-double-negative lw-pdb-add-cancel lw-pdb-double lw-pdb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-pdb-single-bound
 (implies (and (lw-complex-coefficientsp coefficients) (consp coefficients)
               (equal (cdr coefficients) nil) (lw-complexp point)
               (rationalp radius) (<= 1 radius) (natp degree))
  (lw-complex-diskp (lw-complex-polynomial coefficients point 0)
                    (* (lw-complex-coefficient-mass coefficients) (lw-rational-power radius degree))))
 :hints (("Goal"
  :use ((:instance lw-complex-l1-bound (point (car coefficients)))
        (:instance lw-rational-power-at-least-one (base radius) (exponent degree))
        (:instance lw-pdb-multiply-order (a 1) (b (lw-rational-power radius degree))
          (factor (lw-complex-l1 (car coefficients))))
        (:instance lw-complex-disk-enlarge
          (point (car coefficients)) (radius (lw-complex-l1 (car coefficients)))
          (cap (* (lw-complex-l1 (car coefficients)) (lw-rational-power radius degree)))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-coefficientsp lw-pdb-single-value lw-complex-coefficient-mass lw-rational-power-rational lw-pdb-left-commutes lw-pdb-left-distributes lw-pdb-fold-constants lw-pdb-times-negative lw-pdb-negative-times lw-pdb-zero-times lw-pdb-minus-one lw-pdb-double-negative lw-pdb-add-cancel lw-pdb-double lw-pdb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-pdb-zero-length
 (implies (and (lw-complex-coefficientsp coefficients) (equal (len coefficients) 0))
          (equal coefficients nil))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-coefficientsp len lw-pdb-length-natural lw-pdb-left-commutes lw-pdb-left-distributes lw-pdb-fold-constants lw-pdb-times-negative lw-pdb-negative-times lw-pdb-zero-times lw-pdb-minus-one lw-pdb-double-negative lw-pdb-add-cancel lw-pdb-double lw-pdb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
          :cases ((consp coefficients))))))

(local (defthm lw-pdb-base
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp point)
               (rationalp radius) (<= 1 radius) (natp degree)
               (<= (len coefficients) (+ 1 degree))
               (or (endp coefficients) (endp (cdr coefficients)) (zp degree)))
  (lw-complex-diskp (lw-complex-polynomial coefficients point 0)
                    (* (lw-complex-coefficient-mass coefficients) (lw-rational-power radius degree))))
 :hints (("Goal" :use (lw-pdb-single-bound
        (:instance lw-complex-l1-bound (point (car coefficients)))
        (:instance lw-pdb-zero-length (coefficients (cdr coefficients))))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-coefficientsp len lw-pdb-length-natural lw-pdb-empty-polynomial lw-complex-coefficient-mass lw-rational-power-rational lw-pdb-zero-disk lw-pdb-left-commutes lw-pdb-left-distributes lw-pdb-fold-constants lw-pdb-times-negative lw-pdb-negative-times lw-pdb-zero-times lw-pdb-minus-one lw-pdb-double-negative lw-pdb-add-cancel lw-pdb-double lw-pdb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
          :cases ((consp coefficients))))))

(local (defthm lw-pdb-mass-budget
 (implies (and (rationalp head) (<= 0 head) (rationalp tail) (rationalp power) (<= 1 power))
  (<= (+ head (* tail power)) (* (+ head tail) power)))
 :hints (("Goal" :use ((:instance lw-pdb-multiply-order (a 1) (b power) (factor head)))
          :in-theory (union-theories
 '( lw-pdb-left-commutes lw-pdb-left-distributes lw-pdb-fold-constants lw-pdb-times-negative lw-pdb-negative-times lw-pdb-zero-times lw-pdb-minus-one lw-pdb-double-negative lw-pdb-add-cancel lw-pdb-double lw-pdb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))) :rule-classes nil))

(local (defthm lw-pdb-step
 (implies (and (lw-complex-coefficientsp coefficients) (consp coefficients)
               (consp (cdr coefficients)) (lw-complexp point)
               (lw-complex-diskp point radius) (rationalp radius) (<= 1 radius) (posp degree)
               (lw-complex-diskp (lw-complex-polynomial (cdr coefficients) point 0)
                (* (lw-complex-coefficient-mass (cdr coefficients)) (lw-rational-power radius (- degree 1)))))
  (lw-complex-diskp (lw-complex-polynomial coefficients point 0)
                    (* (lw-complex-coefficient-mass coefficients) (lw-rational-power radius degree))))
 :hints (("Goal"
  :use ((:instance lw-complex-l1-bound (point (car coefficients)))
        (:instance lw-complex-coefficient-mass-valid (coefficients (cdr coefficients)))
        (:instance lw-rational-power-at-least-one (base radius) (exponent degree))
        (:instance lw-complex-mul-disk (left point) (radius radius)
          (right (lw-complex-polynomial (cdr coefficients) point 0))
          (other-radius (* (lw-complex-coefficient-mass (cdr coefficients)) (lw-rational-power radius (- degree 1)))))
        (:instance lw-complex-add-disk (left (car coefficients))
          (radius (lw-complex-l1 (car coefficients)))
          (right (lw-complex-mul point (lw-complex-polynomial (cdr coefficients) point 0)))
          (other-radius (* radius (lw-complex-coefficient-mass (cdr coefficients)) (lw-rational-power radius (- degree 1)))))
        (:instance lw-pdb-mass-budget (head (lw-complex-l1 (car coefficients)))
          (tail (lw-complex-coefficient-mass (cdr coefficients))) (power (lw-rational-power radius degree)))
        (:instance lw-complex-disk-enlarge
          (point (lw-complex-polynomial coefficients point 0))
          (radius (+ (lw-complex-l1 (car coefficients))
                     (* (lw-complex-coefficient-mass (cdr coefficients)) (lw-rational-power radius degree))))
          (cap (* (lw-complex-coefficient-mass coefficients) (lw-rational-power radius degree)))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-coefficientsp lw-complex-polynomial-horner lw-complex-coefficient-mass lw-pdb-power-step lw-rational-power-rational lw-pdb-left-commutes lw-pdb-left-distributes lw-pdb-fold-constants lw-pdb-times-negative lw-pdb-negative-times lw-pdb-zero-times lw-pdb-minus-one lw-pdb-double-negative lw-pdb-add-cancel lw-pdb-double lw-pdb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(local (defun lw-pdb-induct (coefficients degree)
 (declare (xargs :measure (acl2-count coefficients) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (or (endp coefficients) (endp (cdr coefficients)) (zp degree)) nil
  (lw-pdb-induct (cdr coefficients) (- degree 1)))))

(defthm lw-complex-polynomial-degree-bound
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complex-diskp point radius)
               (rationalp radius) (<= 1 radius) (natp degree)
               (<= (len coefficients) (+ 1 degree)))
  (lw-complex-diskp (lw-complex-polynomial coefficients point 0)
                    (* (lw-complex-coefficient-mass coefficients) (lw-rational-power radius degree))))
 :hints (("Goal" :induct (lw-pdb-induct coefficients degree)
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-pdb-induct) lw-complex-coefficientsp len lw-pdb-length-natural lw-complex-disk-data lw-pdb-base lw-pdb-left-commutes lw-pdb-left-distributes lw-pdb-fold-constants lw-pdb-times-negative lw-pdb-negative-times lw-pdb-zero-times lw-pdb-minus-one lw-pdb-double-negative lw-pdb-add-cancel lw-pdb-double lw-pdb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) )
         (and stable-under-simplificationp
          '(:use (lw-pdb-step)
            :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-coefficientsp len lw-pdb-length-natural lw-complex-disk-data lw-pdb-base lw-pdb-left-commutes lw-pdb-left-distributes lw-pdb-fold-constants lw-pdb-times-negative lw-pdb-negative-times lw-pdb-zero-times lw-pdb-minus-one lw-pdb-double-negative lw-pdb-add-cancel lw-pdb-double lw-pdb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-pdb-positive-length
 (implies (consp coefficients) (posp (len coefficients)))
 :rule-classes nil
 :hints (("Goal" :expand ((len coefficients)) :in-theory (union-theories
 '(fold-consts-in-+ lw-pdb-length-natural lw-pdb-left-commutes lw-pdb-left-distributes lw-pdb-fold-constants lw-pdb-times-negative lw-pdb-negative-times lw-pdb-zero-times lw-pdb-minus-one lw-pdb-double-negative lw-pdb-add-cancel lw-pdb-double lw-pdb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-complex-polynomial-sharp-length-bound
 (implies (and (consp coefficients) (lw-complex-coefficientsp coefficients)
               (lw-complex-diskp point radius) (rationalp radius) (<= 1 radius))
  (lw-complex-diskp (lw-complex-polynomial coefficients point 0)
                    (* (lw-complex-coefficient-mass coefficients)
                       (lw-rational-power radius (- (len coefficients) 1)))))
 :hints (("Goal"
  :use (lw-pdb-positive-length
        (:instance lw-complex-polynomial-degree-bound (degree (- (len coefficients) 1))))
  :in-theory (union-theories
 '(fold-consts-in-+ len lw-pdb-length-natural lw-pdb-left-commutes lw-pdb-left-distributes lw-pdb-fold-constants lw-pdb-times-negative lw-pdb-negative-times lw-pdb-zero-times lw-pdb-minus-one lw-pdb-double-negative lw-pdb-add-cancel lw-pdb-double lw-pdb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-pdb-lower-consp
 (implies (and (consp coefficients) (consp (cdr coefficients)))
  (consp (lw-polynomial-without-leading coefficients)))
 :hints (("Goal" :expand ((lw-polynomial-without-leading coefficients)) :in-theory (union-theories
 '(fold-consts-in-+ lw-pdb-left-commutes lw-pdb-left-distributes lw-pdb-fold-constants lw-pdb-times-negative lw-pdb-negative-times lw-pdb-zero-times lw-pdb-minus-one lw-pdb-double-negative lw-pdb-add-cancel lw-pdb-double lw-pdb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-pdb-subtract-add
 (implies (and (lw-complexp a) (lw-complexp b))
          (equal (lw-complex-sub (lw-complex-add a b) b) a))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complexp lw-complex-add lw-complex-sub lw-pdb-left-commutes lw-pdb-left-distributes lw-pdb-fold-constants lw-pdb-times-negative lw-pdb-negative-times lw-pdb-zero-times lw-pdb-minus-one lw-pdb-double-negative lw-pdb-add-cancel lw-pdb-double lw-pdb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-polynomial-leading-remainder-bound
 (implies (and (lw-complex-coefficientsp coefficients) (consp coefficients) (consp (cdr coefficients))
               (lw-complex-diskp point radius) (rationalp radius) (<= 1 radius))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-polynomial coefficients point 0)
    (lw-complex-mul (lw-polynomial-leading coefficients)
     (lw-complex-power point (len (lw-polynomial-without-leading coefficients)))))
   (* (lw-complex-coefficient-mass (lw-polynomial-without-leading coefficients))
      (lw-rational-power radius (- (len (lw-polynomial-without-leading coefficients)) 1)))))
 :hints (("Goal"
  :use (lw-polynomial-leading-evaluation lw-polynomial-leading-valid
        (:instance lw-complex-polynomial-sharp-length-bound
          (coefficients (lw-polynomial-without-leading coefficients))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-pdb-lower-consp lw-pdb-subtract-add lw-complex-disk-data lw-complex-polynomial-rational lw-complex-power-rational lw-complex-ring-rational lw-pdb-left-commutes lw-pdb-left-distributes lw-pdb-fold-constants lw-pdb-times-negative lw-pdb-negative-times lw-pdb-zero-times lw-pdb-minus-one lw-pdb-double-negative lw-pdb-add-cancel lw-pdb-double lw-pdb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

