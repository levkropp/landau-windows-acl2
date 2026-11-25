(in-package "ACL2")

(include-book "unit-square-boundary")

; Adjacent side samples have distance 2/count. Reversal and the repeated
; corners assemble the whole canonical boundary with that same step.

(local (defthm lw-uss-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-uss-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-uss-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-uss-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-uss-times-negative (a b) (b a)))
                 :in-theory (disable lw-uss-times-negative)))))

(local (defthm lw-uss-zero-times (equal (* 0 a) 0)))

(local (defthm lw-uss-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-uss-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-uss-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-uss-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-uss-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-uss-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-uss-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-uss-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-uss-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-uss-left-commutes)))))

(defun lw-unit-square-side (count edge)
 (lw-polynomial-line-values '((0 . 0) (1 . 0))
  (lw-polynomial-square-edge-left '(-1 . -1) 2 edge)
  (lw-polynomial-square-edge-right '(-1 . -1) 2 edge) count 0 (+ 1 count)))

(local (defthm lw-uss-rational-inverse
 (implies (rationalp x) (rationalp (/ x))) :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-uss-rational-product
 (implies (and (rationalp x) (rationalp y)) (rationalp (* x y)))
 :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-uss-side-coordinates
 (implies (and (posp count) (natp index) (natp edge) (< edge 4))
  (equal
   (lw-polynomial-line-value '((0 . 0) (1 . 0))
    (lw-polynomial-square-edge-left '(-1 . -1) 2 edge)
    (lw-polynomial-square-edge-right '(-1 . -1) 2 edge) count index)
   (cond ((equal edge 0) (cons (+ -1 (* 2 index (/ count))) -1))
         ((equal edge 1) (cons (+ -1 (* 2 index (/ count))) 1))
         ((equal edge 2) (cons 1 (+ -1 (* 2 index (/ count)))))
         (t (cons -1 (+ -1 (* 2 index (/ count))))))))
 :hints (("Goal"
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-line-value lw-polynomial-line-point lw-complex-identity-polynomial lw-complexp lw-polynomial-square-edge-left lw-polynomial-square-edge-right lw-complex-segment lw-complex-add lw-complex-scale lw-uss-rational-inverse lw-uss-rational-product lw-uss-left-commutes lw-uss-left-distributes lw-uss-fold-constants lw-uss-times-negative lw-uss-negative-times lw-uss-zero-times lw-uss-minus-one lw-uss-double-negative lw-uss-add-cancel lw-uss-double lw-uss-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :cases ((equal edge 0) (equal edge 1) (equal edge 2))))))

(local (defthm lw-uss-side-step
 (implies (and (posp count) (natp index) (natp edge) (< edge 4))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-polynomial-line-value '((0 . 0) (1 . 0))
     (lw-polynomial-square-edge-left '(-1 . -1) 2 edge)
     (lw-polynomial-square-edge-right '(-1 . -1) 2 edge) count (+ 1 index))
    (lw-polynomial-line-value '((0 . 0) (1 . 0))
     (lw-polynomial-square-edge-left '(-1 . -1) 2 edge)
     (lw-polynomial-square-edge-right '(-1 . -1) 2 edge) count index))
   (* 2 (/ count))))
 :hints (("Goal"
  :use ((:instance lw-reciprocal-positive (value count)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-uss-side-coordinates lw-complex-sub lw-complex-diskp lw-complexp lw-diskp lw-uss-rational-inverse lw-uss-rational-product lw-uss-left-commutes lw-uss-left-distributes lw-uss-fold-constants lw-uss-times-negative lw-uss-negative-times lw-uss-zero-times lw-uss-minus-one lw-uss-double-negative lw-uss-add-cancel lw-uss-double lw-uss-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :cases ((equal edge 0) (equal edge 1) (equal edge 2))))))

(local (defthm lw-uss-line-head
 (and
  (equal (consp (lw-polynomial-line-values coefficients left right count index remaining)) (not (zp remaining)))
  (implies (not (zp remaining))
   (and (equal (car (lw-polynomial-line-values coefficients left right count index remaining))
               (lw-polynomial-line-value coefficients left right count index))
        (equal (cdr (lw-polynomial-line-values coefficients left right count index remaining))
               (lw-polynomial-line-values coefficients left right count (+ 1 index) (- remaining 1))))))
 :hints (("Goal" :expand ((lw-polynomial-line-values coefficients left right count index remaining))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-uss-left-commutes lw-uss-left-distributes lw-uss-fold-constants lw-uss-times-negative lw-uss-negative-times lw-uss-zero-times lw-uss-minus-one lw-uss-double-negative lw-uss-add-cancel lw-uss-double lw-uss-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-uss-side-values-step
 (implies (and (posp count) (natp index) (natp remaining) (natp edge) (< edge 4))
  (lw-ray-path-step-check
   (lw-polynomial-line-values '((0 . 0) (1 . 0))
    (lw-polynomial-square-edge-left '(-1 . -1) 2 edge)
    (lw-polynomial-square-edge-right '(-1 . -1) 2 edge) count index remaining)
   (* 2 (/ count))))
 :hints (("Goal" :induct (lw-polynomial-line-values '((0 . 0) (1 . 0))
    (lw-polynomial-square-edge-left '(-1 . -1) 2 edge)
    (lw-polynomial-square-edge-right '(-1 . -1) 2 edge) count index remaining)
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-line-values lw-uss-line-head lw-ray-path-step-check lw-uss-side-step lw-uss-left-commutes lw-uss-left-distributes lw-uss-fold-constants lw-uss-times-negative lw-uss-negative-times lw-uss-zero-times lw-uss-minus-one lw-uss-double-negative lw-uss-add-cancel lw-uss-double lw-uss-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-unit-square-side-step
 (implies (and (posp count) (natp edge) (< edge 4))
  (lw-ray-path-step-check (lw-unit-square-side count edge) (* 2 (/ count))))
 :hints (("Goal" :use ((:instance lw-uss-side-values-step (index 0) (remaining (+ 1 count))))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-unit-square-side lw-uss-left-commutes lw-uss-left-distributes lw-uss-fold-constants lw-uss-times-negative lw-uss-negative-times lw-uss-zero-times lw-uss-minus-one lw-uss-double-negative lw-uss-add-cancel lw-uss-double lw-uss-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-unit-square-side-data
 (implies (and (posp count) (natp edge) (< edge 4))
  (and (lw-ray-pointsp (lw-unit-square-side count edge))
       (consp (lw-unit-square-side count edge))
       (equal (car (lw-unit-square-side count edge)) (lw-polynomial-square-edge-left '(-1 . -1) 2 edge))
       (equal (lw-ray-row-last (lw-unit-square-side count edge)) (lw-polynomial-square-edge-right '(-1 . -1) 2 edge))))
 :hints (("Goal"
  :use ((:instance lw-polynomial-line-values-data
          (coefficients '((0 . 0) (1 . 0)))
          (left (lw-polynomial-square-edge-left '(-1 . -1) 2 edge))
          (right (lw-polynomial-square-edge-right '(-1 . -1) 2 edge))
          (index 0) (remaining (+ 1 count)))
        (:instance lw-polynomial-line-values-endpoints
          (coefficients '((0 . 0) (1 . 0)))
          (left (lw-polynomial-square-edge-left '(-1 . -1) 2 edge))
          (right (lw-polynomial-square-edge-right '(-1 . -1) 2 edge))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-unit-square-side lw-uss-line-head lw-complex-identity-polynomial lw-polynomial-square-edge-left lw-polynomial-square-edge-right (:executable-counterpart lw-complex-coefficientsp) lw-complexp lw-uss-left-commutes lw-uss-left-distributes lw-uss-fold-constants lw-uss-times-negative lw-uss-negative-times lw-uss-zero-times lw-uss-minus-one lw-uss-double-negative lw-uss-add-cancel lw-uss-double lw-uss-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-uss-assembled
 (equal (lw-unit-square-boundary count)
  (append (lw-unit-square-side count 0)
   (append (lw-unit-square-side count 2)
    (append (lw-ray-reverse-points (lw-unit-square-side count 1))
            (lw-ray-reverse-points (lw-unit-square-side count 3))))))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-unit-square-boundary lw-polynomial-square-line-boundary lw-unit-square-side lw-ray-four-path-perimeter lw-uss-left-commutes lw-uss-left-distributes lw-uss-fold-constants lw-uss-times-negative lw-uss-negative-times lw-uss-zero-times lw-uss-minus-one lw-uss-double-negative lw-uss-add-cancel lw-uss-double lw-uss-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-uss-append-head
 (implies (consp left) (equal (car (append left right)) (car left)))
 :hints (("Goal" :expand ((append left right)) :in-theory (union-theories
 '(fold-consts-in-+ lw-uss-left-commutes lw-uss-left-distributes lw-uss-fold-constants lw-uss-times-negative lw-uss-negative-times lw-uss-zero-times lw-uss-minus-one lw-uss-double-negative lw-uss-add-cancel lw-uss-double lw-uss-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-uss-self-difference
 (implies (and (lw-complexp point) (rationalp radius) (<= 0 radius))
  (lw-complex-diskp (lw-complex-sub point point) radius))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-sub lw-complexp lw-complex-diskp lw-diskp lw-uss-left-commutes lw-uss-left-distributes lw-uss-fold-constants lw-uss-times-negative lw-uss-negative-times lw-uss-zero-times lw-uss-minus-one lw-uss-double-negative lw-uss-add-cancel lw-uss-double lw-uss-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-uss-step-radius
 (implies (posp count) (and (rationalp (* 2 (/ count))) (< 0 (* 2 (/ count)))))
 :hints (("Goal" :use ((:instance lw-reciprocal-positive (value count)))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-uss-rational-inverse lw-uss-rational-product lw-uss-left-commutes lw-uss-left-distributes lw-uss-fold-constants lw-uss-times-negative lw-uss-negative-times lw-uss-zero-times lw-uss-minus-one lw-uss-double-negative lw-uss-add-cancel lw-uss-double lw-uss-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-unit-square-boundary-step
 (implies (posp count)
  (lw-ray-path-step-check (lw-unit-square-boundary count) (* 2 (/ count))))
 :hints (("Goal"
  :use (lw-uss-step-radius)
  :in-theory (union-theories
 '(fold-consts-in-+ lw-uss-assembled lw-ray-path-step-append lw-ray-path-step-reverse lw-unit-square-side-step lw-unit-square-side-data lw-ray-step-join-check lw-ray-reverse-points-data lw-ray-reverse-points-endpoints lw-ray-pointsp-append lw-uss-append-head lw-uss-self-difference (:executable-counterpart lw-polynomial-square-edge-left) (:executable-counterpart lw-polynomial-square-edge-right) (:executable-counterpart lw-complexp) lw-uss-left-commutes lw-uss-left-distributes lw-uss-fold-constants lw-uss-times-negative lw-uss-negative-times lw-uss-zero-times lw-uss-minus-one lw-uss-double-negative lw-uss-add-cancel lw-uss-double lw-uss-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

