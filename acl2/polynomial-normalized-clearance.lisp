(in-package "ACL2")

(include-book "polynomial-square-normalization")

; The physical coarse certificate supplies unit-square clearance after normalization.

(local (defthm lw-pnc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pnc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pnc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pnc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pnc-times-negative (a b) (b a)))
                 :in-theory (disable lw-pnc-times-negative)))))

(local (defthm lw-pnc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pnc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pnc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pnc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pnc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pnc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pnc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-pnc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pnc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pnc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-pnc-left-commutes)))))
(local (defthm lw-pnc-rational-inverse
 (implies (rationalp x) (rationalp (/ x)))
 :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-pnc-rational-product
 (implies (and (rationalp x) (rationalp y)) (rationalp (* x y)))
 :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-pnc-parameter
 (implies (and (posp count) (natp index) (<= index count))
  (and (rationalp (* index (/ count))) (<= 0 (* index (/ count))) (<= (* index (/ count)) 1)))
 :hints (("Goal"
  :use ((:instance lw-reciprocal-positive (value count))
        (:instance inverse-of-* (x count))
        (:instance lw-pnc-multiply-order (a 0) (b index) (factor (/ count)))
        (:instance lw-pnc-multiply-order (a index) (b count) (factor (/ count))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-pnc-rational-inverse lw-pnc-rational-product lw-pnc-left-commutes lw-pnc-left-distributes lw-pnc-fold-constants lw-pnc-times-negative lw-pnc-negative-times lw-pnc-zero-times lw-pnc-minus-one lw-pnc-double-negative lw-pnc-add-cancel lw-pnc-double lw-pnc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))


(local (defthm lw-pnc-side-point
 (implies (and (natp edge) (< edge 4) (rationalp parameter) (<= 0 parameter) (<= parameter 1))
  (lw-unit-square-pointp
   (lw-complex-segment (lw-polynomial-square-edge-left '(-1 . -1) 2 edge)
                       (lw-polynomial-square-edge-right '(-1 . -1) 2 edge) parameter)))
 :hints (("Goal" :cases ((equal edge 0) (equal edge 1) (equal edge 2))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-unit-square-point-coordinates lw-polynomial-square-edge-left lw-polynomial-square-edge-right lw-complex-segment lw-complex-add lw-complex-scale lw-complexp lw-pnc-left-commutes lw-pnc-left-distributes lw-pnc-fold-constants lw-pnc-times-negative lw-pnc-negative-times lw-pnc-zero-times lw-pnc-minus-one lw-pnc-double-negative lw-pnc-add-cancel lw-pnc-double lw-pnc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
          :do-not-induct t))))


(local (defthm lw-pnc-point-type
 (implies (lw-unit-square-pointp point) (lw-complexp point))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-unit-square-pointp lw-pnc-left-commutes lw-pnc-left-distributes lw-pnc-fold-constants lw-pnc-times-negative lw-pnc-negative-times lw-pnc-zero-times lw-pnc-minus-one lw-pnc-double-negative lw-pnc-add-cancel lw-pnc-double lw-pnc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))))

(defthm lw-polynomial-normalized-square-clearance
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor) (rationalp side) (< 0 side)
               (posp coarse) (lw-polynomial-square-boundary-check coefficients anchor side coarse)
               (lw-unit-square-pointp point))
  (not (lw-complex-diskp
   (lw-complex-polynomial (lw-polynomial-square-normalize coefficients anchor side) point 0)
   (lw-polynomial-square-clearance coefficients anchor side coarse))))
 :hints (("Goal"
  :use (lw-unit-square-edge-data lw-polynomial-square-normalize-evaluation
        (:instance lw-polynomial-square-forward-side (edge (lw-unit-square-edge-number point))
          (parameter (lw-unit-square-edge-parameter point)))
        (:instance lw-polynomial-square-side-excludes-clearance (count coarse)
          (edge (lw-unit-square-edge-number point)) (parameter (lw-unit-square-edge-parameter point))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-pnc-point-type lw-pnc-left-commutes lw-pnc-left-distributes lw-pnc-fold-constants lw-pnc-times-negative lw-pnc-negative-times lw-pnc-zero-times lw-pnc-minus-one lw-pnc-double-negative lw-pnc-add-cancel lw-pnc-double lw-pnc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-unit-square-line-point-data
 (implies (and (posp count) (natp edge) (< edge 4) (natp index) (<= index count))
  (lw-unit-square-pointp (lw-polynomial-line-point (lw-polynomial-square-edge-left (cons -1 -1) 2 edge) (lw-polynomial-square-edge-right (cons -1 -1) 2 edge) count index)))
 :hints (("Goal"
  :use (lw-pnc-parameter (:instance lw-pnc-side-point (parameter (* index (/ count)))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-line-point lw-pnc-left-commutes lw-pnc-left-distributes lw-pnc-fold-constants lw-pnc-times-negative lw-pnc-negative-times lw-pnc-zero-times lw-pnc-minus-one lw-pnc-double-negative lw-pnc-add-cancel lw-pnc-double lw-pnc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-unit-square-line-point-step
 (implies (and (posp count) (natp edge) (< edge 4) (natp index))
  (lw-complex-diskp
   (lw-complex-sub (lw-polynomial-line-point (lw-polynomial-square-edge-left (cons -1 -1) 2 edge) (lw-polynomial-square-edge-right (cons -1 -1) 2 edge) count (+ 1 index))
                   (lw-polynomial-line-point (lw-polynomial-square-edge-left (cons -1 -1) 2 edge) (lw-polynomial-square-edge-right (cons -1 -1) 2 edge) count index))
   (* 2 (/ count))))
 :hints (("Goal"
  :use ((:instance lw-reciprocal-positive (value count)))
  :cases ((equal edge 0) (equal edge 1) (equal edge 2))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-line-point lw-polynomial-square-edge-left lw-polynomial-square-edge-right lw-complex-segment lw-complex-add lw-complex-scale lw-complex-sub lw-complex-diskp lw-diskp lw-complexp lw-pnc-rational-inverse lw-pnc-rational-product lw-pnc-left-commutes lw-pnc-left-distributes lw-pnc-fold-constants lw-pnc-times-negative lw-pnc-negative-times lw-pnc-zero-times lw-pnc-minus-one lw-pnc-double-negative lw-pnc-add-cancel lw-pnc-double lw-pnc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :nonlinearp t :do-not-induct t)))
