(in-package "ACL2")

(include-book "unit-square-power-index")

; A positive rational step target determines a square mesh, always a multiple of four.

(local (defthm lw-usm-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-usm-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-usm-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-usm-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-usm-times-negative (a b) (b a)))
                 :in-theory (disable lw-usm-times-negative)))))

(local (defthm lw-usm-zero-times (equal (* 0 a) 0)))

(local (defthm lw-usm-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-usm-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-usm-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-usm-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-usm-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-usm-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-usm-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-usm-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-usm-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-usm-left-commutes)))))
(defun lw-unit-square-mesh-factor (error)
 (if (equal error 0) 1 (+ 1 (lw-ceiling-rational (/ error)))))

(local (defthm lw-usm-count-budget
 (implies (and (rationalp error) (< 0 error))
  (let* ((factor (+ 1 (lw-ceiling-rational (/ error))))
         (count (* 4 factor)))
   (and (posp factor) (posp count) (<= (* 2 (/ count)) error))))
 :hints (("Goal"
  :use ((:instance lw-reciprocal-positive (value error))
        (:instance lw-ceiling-rational-natural (value (/ error)))
        (:instance lw-ceiling-rational-bracket (value (/ error)))
        (:instance lw-usm-multiply-order
          (a (/ error)) (b (+ 1 (lw-ceiling-rational (/ error)))) (factor error))
        (:instance lw-usm-inverse-factor (divisor error) (coefficient 1))
        (:instance lw-positive-division-bound (numerator 2)
          (divisor (* 4 (+ 1 (lw-ceiling-rational (/ error))))) (bound error)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-usm-left-commutes lw-usm-left-distributes lw-usm-fold-constants lw-usm-times-negative lw-usm-negative-times lw-usm-zero-times lw-usm-minus-one lw-usm-double-negative lw-usm-add-cancel lw-usm-double lw-usm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :nonlinearp t))))


(defthm lw-unit-square-mesh-factor-data
 (implies (and (rationalp error) (< 0 error))
  (and (posp (lw-unit-square-mesh-factor error))
       (posp (* 4 (lw-unit-square-mesh-factor error)))
       (<= (* 2 (/ (* 4 (lw-unit-square-mesh-factor error)))) error)))
 :hints (("Goal" :use (lw-usm-count-budget)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-unit-square-mesh-factor lw-usm-left-commutes lw-usm-left-distributes lw-usm-fold-constants lw-usm-times-negative lw-usm-negative-times lw-usm-zero-times lw-usm-minus-one lw-usm-double-negative lw-usm-add-cancel lw-usm-double lw-usm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-unit-square-boundary-at-budget
 (implies (and (posp factor) (rationalp error) (<= 0 error)
               (<= (* 2 (/ (* 4 factor))) error))
  (let ((points (lw-unit-square-boundary (* 4 factor))))
   (and (consp points) (lw-ray-pointsp points)
        (lw-ray-annulus-pointsp points 1 2)
        (equal (lw-ray-row-last points) (car points))
        (lw-ray-path-step-check points error)
        (equal (lw-ray-polygon-index points) 1))))
 :hints (("Goal"
  :use (lw-unit-square-boundary-index
        (:instance lw-unit-square-boundary-data (count (* 4 factor)))
        (:instance lw-unit-square-boundary-annulus (count (* 4 factor)))
        (:instance lw-unit-square-boundary-step (count (* 4 factor)))
        (:instance lw-ray-path-step-enlarge (points (lw-unit-square-boundary (* 4 factor)))
          (delta (* 2 (/ (* 4 factor)))) (larger error)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-usm-left-commutes lw-usm-left-distributes lw-usm-fold-constants lw-usm-times-negative lw-usm-negative-times lw-usm-zero-times lw-usm-minus-one lw-usm-double-negative lw-usm-add-cancel lw-usm-double lw-usm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
