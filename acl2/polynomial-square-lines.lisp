(in-package "ACL2")

(include-book "polynomial-grid-perimeter")
(include-book "polynomial-square-refinement")

; Construct the canonical perimeter in linear rather than quadratic space.
; These four sampled lines equal the boundary extracted from the full grid.

(local (defthm lw-psl-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-psl-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-psl-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-psl-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-psl-times-negative (a b) (b a)))
                 :in-theory (disable lw-psl-times-negative)))))

(local (defthm lw-psl-zero-times (equal (* 0 a) 0)))

(local (defthm lw-psl-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-psl-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-psl-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-psl-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-psl-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-psl-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-psl-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-psl-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-psl-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-psl-left-commutes)))))

(defthm lw-complex-identity-polynomial
 (implies (lw-complexp point)
  (equal (lw-complex-polynomial '((0 . 0) (1 . 0)) point 0) point))
 :hints (("Goal"
  :expand ((lw-complex-polynomial '((0 . 0) (1 . 0)) point 0)
           (lw-complex-polynomial '((1 . 0)) point 1)
           (lw-complex-polynomial nil point 2)
           (lw-complex-power point 0) (lw-complex-power point 1))
  :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-complex-mul-zero lw-complex-mul-one lw-complex-add-zero lw-psl-left-commutes lw-psl-left-distributes lw-psl-fold-constants lw-psl-times-negative lw-psl-negative-times lw-psl-zero-times lw-psl-minus-one lw-psl-double-negative lw-psl-add-cancel lw-psl-double lw-psl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-polynomial-identity-path-values
 (implies (lw-ray-pointsp points)
  (equal (lw-polynomial-path-values '((0 . 0) (1 . 0)) points) points))
 :hints (("Goal" :induct (lw-polynomial-path-values '((0 . 0) (1 . 0)) points)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-path-values lw-ray-pointsp lw-complex-identity-polynomial lw-psl-left-commutes lw-psl-left-distributes lw-psl-fold-constants lw-psl-times-negative lw-psl-negative-times lw-psl-zero-times lw-psl-minus-one lw-psl-double-negative lw-psl-add-cancel lw-psl-double lw-psl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defun lw-polynomial-square-line-boundary (coefficients anchor side count)
 (lw-ray-four-path-perimeter
  (lw-polynomial-line-values coefficients
    (lw-polynomial-square-edge-left anchor side 0) (lw-polynomial-square-edge-right anchor side 0)
    count 0 (+ 1 count))
  (lw-polynomial-line-values coefficients
    (lw-polynomial-square-edge-left anchor side 2) (lw-polynomial-square-edge-right anchor side 2)
    count 0 (+ 1 count))
  (lw-ray-reverse-points (lw-polynomial-line-values coefficients
    (lw-polynomial-square-edge-left anchor side 1) (lw-polynomial-square-edge-right anchor side 1)
    count 0 (+ 1 count)))
  (lw-ray-reverse-points (lw-polynomial-line-values coefficients
    (lw-polynomial-square-edge-left anchor side 3) (lw-polynomial-square-edge-right anchor side 3)
    count 0 (+ 1 count)))))

(local (defthm lw-psl-grid-head
 (implies (not (zp remaining))
  (equal (car (lw-polynomial-grid-rows coefficients anchor side count row remaining))
         (lw-polynomial-grid-row coefficients anchor side count row 0 (+ 1 count))))
 :hints (("Goal" :expand ((lw-polynomial-grid-rows coefficients anchor side count row remaining))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-psl-left-commutes lw-psl-left-distributes lw-psl-fold-constants lw-psl-times-negative lw-psl-negative-times lw-psl-zero-times lw-psl-minus-one lw-psl-double-negative lw-psl-add-cancel lw-psl-double lw-psl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-polynomial-square-line-boundary-values
 (implies (and (lw-complexp anchor) (rationalp side) (posp count))
  (equal (lw-polynomial-square-line-boundary coefficients anchor side count)
         (lw-polynomial-path-values coefficients (lw-polynomial-square-boundary anchor side count))))
 :hints (("Goal"
  :use (lw-polynomial-square-boundary-values
        (:instance lw-polynomial-square-edge-as-line (edge 0) (index 0) (remaining (+ 1 count)))
        (:instance lw-polynomial-square-edge-as-line (edge 1) (index 0) (remaining (+ 1 count)))
        (:instance lw-polynomial-square-edge-as-line (edge 2) (index 0) (remaining (+ 1 count)))
        (:instance lw-polynomial-square-edge-as-line (edge 3) (index 0) (remaining (+ 1 count))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-square-line-boundary lw-ray-grid-perimeter lw-ray-four-path-perimeter lw-polynomial-grid lw-psl-grid-head lw-polynomial-grid-rows-last lw-polynomial-grid-left-column lw-polynomial-grid-right-column lw-polynomial-square-edge-values lw-polynomial-square-edge-row lw-polynomial-square-edge-column lw-psl-left-commutes lw-psl-left-distributes lw-psl-fold-constants lw-psl-times-negative lw-psl-negative-times lw-psl-zero-times lw-psl-minus-one lw-psl-double-negative lw-psl-add-cancel lw-psl-double lw-psl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-polynomial-square-domain-lines
 (implies (and (lw-complexp anchor) (rationalp side) (posp count))
  (equal (lw-polynomial-square-line-boundary '((0 . 0) (1 . 0)) anchor side count)
         (lw-polynomial-square-boundary anchor side count)))
 :hints (("Goal"
  :use ((:instance lw-polynomial-square-line-boundary-values (coefficients '((0 . 0) (1 . 0))))
        lw-polynomial-square-boundary-data)
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-identity-path-values lw-psl-left-commutes lw-psl-left-distributes lw-psl-fold-constants lw-psl-times-negative lw-psl-negative-times lw-psl-zero-times lw-psl-minus-one lw-psl-double-negative lw-psl-add-cancel lw-psl-double lw-psl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

