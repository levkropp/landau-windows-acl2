(in-package "ACL2")

(include-book "polynomial-coefficient-maps")

; Finite coefficient caps give a uniform quadratic remainder estimate.
; A computed first failed coefficient makes the cap checker effective.

(local (in-theory
 (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
          lw-complex-diskp lw-diskp lw-complex-power lw-rational-power
          lw-complex-polynomial lw-complex-polynomial-horner lw-complex-coefficient-at
          lw-complex-mul-subtract lw-complex-mul-commutative lw-complex-mul-left-commutes
          lw-complex-disk-enlarge lw-disk-enlarge)))

(local (defthm lw-pqb-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pqb-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pqb-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pqb-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pqb-times-negative (a b) (b a)))
                 :in-theory (disable lw-pqb-times-negative)))))

(local (defthm lw-pqb-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pqb-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pqb-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pqb-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pqb-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pqb-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pqb-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-pqb-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pqb-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pqb-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-pqb-left-commutes)))))

(defun lw-polynomial-coefficient-caps (coefficients cap)
 (if (endp coefficients) t
  (and (lw-complex-diskp (car coefficients) cap)
       (lw-polynomial-coefficient-caps (cdr coefficients) cap))))

(defun lw-polynomial-cap-index (coefficients cap)
 (if (endp coefficients) 0
  (if (lw-complex-diskp (car coefficients) cap)
      (+ 1 (lw-polynomial-cap-index (cdr coefficients) cap))
    0)))

(local (defthm lw-pqb-length-nonnegative
 (<= 0 (len coefficients))
 :hints (("Goal" :induct (len coefficients) :in-theory (enable len)))
 :rule-classes (:rewrite :linear)))

(defthm lw-polynomial-cap-index-data
 (implies (and (lw-complex-coefficientsp coefficients)
               (not (lw-polynomial-coefficient-caps coefficients cap)))
  (let ((index (lw-polynomial-cap-index coefficients cap)))
   (and (natp index) (< index (len coefficients))
        (not (lw-complex-diskp (nth index coefficients) cap)))))
 :hints (("Goal" :induct (lw-polynomial-cap-index coefficients cap)
  :in-theory (union-theories
   '(lw-polynomial-cap-index lw-polynomial-coefficient-caps lw-complex-coefficientsp nth len lw-pqb-length-nonnegative nfix endp lw-pqb-left-commutes lw-pqb-left-distributes lw-pqb-fold-constants lw-pqb-times-negative lw-pqb-negative-times lw-pqb-zero-times lw-pqb-minus-one lw-pqb-double-negative lw-pqb-add-cancel lw-pqb-double lw-pqb-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory)))))

(local (defthm lw-pqb-power-step
 (implies (and (rationalp radius) (natp offset))
  (equal (lw-rational-power radius (+ 1 offset)) (* radius (lw-rational-power radius offset))))
 :hints (("Goal" :expand ((lw-rational-power radius (+ 1 offset)))
  :in-theory (union-theories
   '( lw-pqb-left-commutes lw-pqb-left-distributes lw-pqb-fold-constants lw-pqb-times-negative lw-pqb-negative-times lw-pqb-zero-times lw-pqb-minus-one lw-pqb-double-negative lw-pqb-add-cancel lw-pqb-double lw-pqb-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))))))

(local (defthm lw-pqb-tail-budget
 (implies (and (rationalp cap) (<= 0 cap) (rationalp radius) (<= 0 radius) (<= radius 1/2)
               (rationalp weight) (<= 0 weight))
  (and (<= 0 (* 2 cap weight))
       (<= (+ (* cap weight) (* 2 cap radius weight)) (* 2 cap weight))))
 :hints (("Goal" :nonlinearp t))
 :rule-classes nil))

(defthm lw-complex-polynomial-coefficient-tail-bound
 (implies (and (lw-complex-coefficientsp coefficients) (lw-polynomial-coefficient-caps coefficients cap)
               (rationalp cap) (<= 0 cap) (lw-complex-diskp point radius) (<= radius 1/2) (natp offset))
  (lw-complex-diskp (lw-complex-polynomial coefficients point offset)
                   (* 2 cap (lw-rational-power radius offset))))
 :hints (("Goal" :induct (lw-complex-polynomial coefficients point offset)
  :in-theory (union-theories
   '(lw-complex-polynomial lw-polynomial-coefficient-caps lw-complex-coefficientsp lw-pqb-power-step endp lw-pqb-left-commutes lw-pqb-left-distributes lw-pqb-fold-constants lw-pqb-times-negative lw-pqb-negative-times lw-pqb-zero-times lw-pqb-minus-one lw-pqb-double-negative lw-pqb-add-cancel lw-pqb-double lw-pqb-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory)) )
 (and stable-under-simplificationp
  '(:use ((:instance lw-complex-disk-data)
          (:instance lw-rational-power-rational (base radius) (exponent offset))
          (:instance lw-rational-power-nonnegative (base radius) (exponent offset))
          (:instance lw-complex-power-disk (index offset))
          (:instance lw-complex-mul-disk (left (car coefficients)) (right (lw-complex-power point offset))
           (radius cap) (other-radius (lw-rational-power radius offset)))
          (:instance lw-complex-add-disk
           (left (lw-complex-mul (car coefficients) (lw-complex-power point offset)))
           (right (lw-complex-polynomial (cdr coefficients) point (+ 1 offset)))
           (radius (* cap (lw-rational-power radius offset)))
           (other-radius (* 2 cap (lw-rational-power radius (+ 1 offset)))))
          (:instance lw-pqb-tail-budget (weight (lw-rational-power radius offset)))
          (:instance lw-complex-zero-disk (radius (* 2 cap (lw-rational-power radius offset))))
          (:instance lw-complex-disk-enlarge
           (point (lw-complex-polynomial coefficients point offset))
           (radius (+ (* cap (lw-rational-power radius offset))
                      (* 2 cap (lw-rational-power radius (+ 1 offset)))))
           (cap (* 2 cap (lw-rational-power radius offset)))))
    :in-theory (union-theories
   '(lw-complex-polynomial lw-polynomial-coefficient-caps lw-complex-coefficientsp lw-pqb-power-step endp lw-pqb-left-commutes lw-pqb-left-distributes lw-pqb-fold-constants lw-pqb-times-negative lw-pqb-negative-times lw-pqb-zero-times lw-pqb-minus-one lw-pqb-double-negative lw-pqb-add-cancel lw-pqb-double lw-pqb-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
    :nonlinearp nil :do-not-induct t))))

(local (defthm lw-pqb-nil-coefficient
 (equal (lw-complex-coefficient-at nil target offset) (cons 0 0))
 :hints (("Goal" :in-theory (enable lw-complex-coefficient-at)))))

(local (defthm lw-pqb-first-coefficient
 (implies (and (lw-complex-coefficientsp coefficients) (natp offset))
  (equal (lw-complex-coefficient-at coefficients offset offset)
         (if (consp coefficients) (car coefficients) (cons 0 0))))
 :hints (("Goal"
  :use ((:instance lw-complex-coefficient-at-below-offset
         (coefficients (cdr coefficients)) (target offset) (offset (+ 1 offset))))
  :expand ((lw-complex-coefficient-at coefficients offset offset))
  :in-theory (union-theories
   '(lw-pqb-nil-coefficient lw-complex-coefficientsp lw-complex-add-zero lw-complexp endp lw-pqb-left-commutes lw-pqb-left-distributes lw-pqb-fold-constants lw-pqb-times-negative lw-pqb-negative-times lw-pqb-zero-times lw-pqb-minus-one lw-pqb-double-negative lw-pqb-add-cancel lw-pqb-double lw-pqb-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t))))

(local (defthm lw-pqb-second-coefficient
 (implies (lw-complex-coefficientsp coefficients)
  (equal (lw-complex-coefficient-at coefficients 1 0)
         (if (consp (cdr coefficients)) (cadr coefficients) (cons 0 0))))
 :hints (("Goal"
  :use ((:instance lw-pqb-first-coefficient (coefficients (cdr coefficients)) (offset 1))
        (:instance lw-complex-coefficient-at-rational (coefficients (cdr coefficients)) (target 1) (offset 1)))
  :expand ((lw-complex-coefficient-at coefficients 1 0))
  :in-theory (union-theories
   '(lw-pqb-nil-coefficient lw-complex-coefficientsp lw-complex-add-zero lw-complexp endp lw-pqb-left-commutes lw-pqb-left-distributes lw-pqb-fold-constants lw-pqb-times-negative lw-pqb-negative-times lw-pqb-zero-times lw-pqb-minus-one lw-pqb-double-negative lw-pqb-add-cancel lw-pqb-double lw-pqb-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t))))

(defthm lw-complex-polynomial-at-zero
 (implies (lw-complex-coefficientsp coefficients)
  (equal (lw-complex-polynomial coefficients (cons 0 0) 0)
         (lw-complex-coefficient-at coefficients 0 0)))
 :hints (("Goal"
  :cases ((consp coefficients))
  :use ((:instance lw-pqb-first-coefficient (offset 0))
        (:instance lw-complex-polynomial-horner (point (cons 0 0)))
        (:instance lw-complex-polynomial-rational (coefficients (cdr coefficients)) (point (cons 0 0)) (offset 0)))
  :expand ((lw-complex-polynomial nil (cons 0 0) 0))
  :in-theory (union-theories
   '(lw-complex-coefficientsp lw-complexp lw-complex-mul-zero lw-complex-add-zero lw-pqb-left-commutes lw-pqb-left-distributes lw-pqb-fold-constants lw-pqb-times-negative lw-pqb-negative-times lw-pqb-zero-times lw-pqb-minus-one lw-pqb-double-negative lw-pqb-add-cancel lw-pqb-double lw-pqb-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-complex-polynomial-quadratic-identity
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp point))
  (equal
   (lw-complex-sub
    (lw-complex-sub (lw-complex-polynomial coefficients point 0)
                    (lw-complex-polynomial coefficients (cons 0 0) 0))
    (lw-complex-mul (lw-complex-coefficient-at coefficients 1 0) point))
   (lw-complex-polynomial (cddr coefficients) point 2)))
 :hints (("Goal"
  :use ((:instance lw-pqb-first-coefficient (offset 0))
        lw-pqb-second-coefficient lw-complex-polynomial-at-zero
        (:instance lw-complex-polynomial-rational (coefficients (cddr coefficients)) (offset 2)))
  :expand ((lw-complex-polynomial coefficients point 0)
           (lw-complex-polynomial (cdr coefficients) point 1)
           (lw-complex-polynomial nil point 0)
           (lw-complex-polynomial nil point 1)
           (lw-complex-polynomial nil point 2)
           (lw-complex-power point 0) (lw-complex-power point 1))
  :in-theory (union-theories
   '(lw-complex-coefficientsp lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale endp lw-pqb-left-commutes lw-pqb-left-distributes lw-pqb-fold-constants lw-pqb-times-negative lw-pqb-negative-times lw-pqb-zero-times lw-pqb-minus-one lw-pqb-double-negative lw-pqb-add-cancel lw-pqb-double lw-pqb-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t)))

(local (defthm lw-pqb-power-two
 (equal (lw-rational-power radius 2) (* (fix radius) (fix radius)))
 :hints (("Goal" :expand ((lw-rational-power radius 2) (lw-rational-power radius 1) (lw-rational-power radius 0))
  :in-theory (union-theories
   '( lw-pqb-left-commutes lw-pqb-left-distributes lw-pqb-fold-constants lw-pqb-times-negative lw-pqb-negative-times lw-pqb-zero-times lw-pqb-minus-one lw-pqb-double-negative lw-pqb-add-cancel lw-pqb-double lw-pqb-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))))))

(defthm lw-complex-polynomial-quadratic-bound
 (implies (and (lw-complex-coefficientsp coefficients) (lw-polynomial-coefficient-caps coefficients cap)
               (rationalp cap) (<= 0 cap) (lw-complex-diskp point radius) (<= radius 1/2))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-complex-sub (lw-complex-polynomial coefficients point 0)
                    (lw-complex-polynomial coefficients (cons 0 0) 0))
    (lw-complex-mul (lw-complex-coefficient-at coefficients 1 0) point))
   (* 2 cap radius radius)))
 :hints (("Goal"
  :use (lw-complex-polynomial-quadratic-identity lw-complex-disk-data
        (:instance lw-complex-polynomial-coefficient-tail-bound (coefficients (cddr coefficients)) (offset 2)))
  :in-theory (union-theories
   '(lw-complex-polynomial-quadratic-identity lw-polynomial-coefficient-caps lw-complex-coefficientsp lw-pqb-power-two lw-pqb-left-commutes lw-pqb-left-distributes lw-pqb-fold-constants lw-pqb-times-negative lw-pqb-negative-times lw-pqb-zero-times lw-pqb-minus-one lw-pqb-double-negative lw-pqb-add-cancel lw-pqb-double lw-pqb-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t)))

(defun lw-complex-linear-remainder (value anchor slope point)
 (lw-complex-sub (lw-complex-sub value anchor) (lw-complex-mul slope point)))

(local (in-theory (disable lw-complex-linear-remainder)))

(defthm lw-complex-linear-remainder-rational
 (implies (and (lw-complexp value) (lw-complexp anchor) (lw-complexp slope) (lw-complexp point))
  (lw-complexp (lw-complex-linear-remainder value anchor slope point)))
 :hints (("Goal"
  :use ((:instance lw-complex-operations-rational (left value) (right anchor) (factor 1))
        (:instance lw-complex-operations-rational (left slope) (right point) (factor 1))
        (:instance lw-complex-operations-rational
         (left (lw-complex-sub value anchor)) (right (lw-complex-mul slope point)) (factor 1)))
  :in-theory (union-theories
   '(lw-complex-linear-remainder lw-complex-operations-rational lw-pqb-left-commutes lw-pqb-left-distributes lw-pqb-fold-constants lw-pqb-times-negative lw-pqb-negative-times lw-pqb-zero-times lw-pqb-minus-one lw-pqb-double-negative lw-pqb-add-cancel lw-pqb-double lw-pqb-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t)))

(local (defthm lw-pqb-remainder-difference
 (implies (and (lw-complexp value) (lw-complexp anchor) (lw-complexp slope) (lw-complexp point)
               (lw-complexp other-value) (lw-complexp other-anchor) (lw-complexp other-slope))
  (equal
   (lw-complex-sub (lw-complex-linear-remainder value anchor slope point)
                   (lw-complex-linear-remainder other-value other-anchor other-slope point))
   (lw-complex-sub
    (lw-complex-sub (lw-complex-sub value other-value) (lw-complex-sub anchor other-anchor))
    (lw-complex-mul (lw-complex-sub slope other-slope) point))))
 :hints (("Goal"
  :in-theory (union-theories
   '(lw-complex-linear-remainder lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale lw-pqb-left-commutes lw-pqb-left-distributes lw-pqb-fold-constants lw-pqb-times-negative lw-pqb-negative-times lw-pqb-zero-times lw-pqb-minus-one lw-pqb-double-negative lw-pqb-add-cancel lw-pqb-double lw-pqb-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t))))

(defthm lw-complex-linear-remainder-comparison
 (implies (and (lw-complexp value) (lw-complexp anchor) (lw-complexp slope)
               (lw-complexp other-value) (lw-complexp other-anchor) (lw-complexp other-slope)
               (lw-complex-diskp point radius)
               (lw-complex-diskp (lw-complex-sub value other-value) value-error)
               (lw-complex-diskp (lw-complex-sub anchor other-anchor) anchor-error)
               (lw-complex-diskp (lw-complex-sub slope other-slope) slope-error))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-linear-remainder value anchor slope point)
                   (lw-complex-linear-remainder other-value other-anchor other-slope point))
   (+ value-error anchor-error (* slope-error radius))))
 :hints (("Goal"
  :use (lw-complex-disk-data
        (:instance lw-complex-sub-disk
         (left (lw-complex-sub value other-value)) (right (lw-complex-sub anchor other-anchor))
         (radius value-error) (other-radius anchor-error))
        (:instance lw-complex-mul-disk (left (lw-complex-sub slope other-slope)) (right point)
         (radius slope-error) (other-radius radius))
        (:instance lw-complex-sub-disk
         (left (lw-complex-sub (lw-complex-sub value other-value) (lw-complex-sub anchor other-anchor)))
         (right (lw-complex-mul (lw-complex-sub slope other-slope) point))
         (radius (+ value-error anchor-error)) (other-radius (* slope-error radius))))
  :in-theory (union-theories
   '(lw-pqb-remainder-difference lw-pqb-left-commutes lw-pqb-left-distributes lw-pqb-fold-constants lw-pqb-times-negative lw-pqb-negative-times lw-pqb-zero-times lw-pqb-minus-one lw-pqb-double-negative lw-pqb-add-cancel lw-pqb-double lw-pqb-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t)))



