(in-package "ACL2")

(include-book "unit-square-translated-sides")

; The ray convention gives a half-open-square indicator, including when
; a rational root is exactly on a boundary edge. Product use will add clearance.

(local (defthm lw-uli-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-uli-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-uli-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-uli-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-uli-times-negative (a b) (b a)))
                 :in-theory (disable lw-uli-times-negative)))))

(local (defthm lw-uli-zero-times (equal (* 0 a) 0)))

(local (defthm lw-uli-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-uli-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-uli-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-uli-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-uli-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-uli-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-uli-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-uli-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-uli-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-uli-left-commutes)))))
(defun lw-unit-square-root-index (root)
 (if (and (<= -1 (car root)) (< (car root) 1)
          (<= -1 (cdr root)) (< (cdr root) 1)) 1 0))

(local (defthm lw-uli-assembled
 (equal (lw-unit-square-boundary count)
  (append (lw-unit-square-side count 0)
   (append (lw-unit-square-side count 2)
    (append (lw-ray-reverse-points (lw-unit-square-side count 1))
            (lw-ray-reverse-points (lw-unit-square-side count 3))))))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-unit-square-boundary lw-polynomial-square-line-boundary lw-unit-square-side lw-ray-four-path-perimeter lw-uli-left-commutes lw-uli-left-distributes lw-uli-fold-constants lw-uli-times-negative lw-uli-negative-times lw-uli-zero-times lw-uli-minus-one lw-uli-double-negative lw-uli-add-cancel lw-uli-double lw-uli-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))


(local (defthm lw-uli-translated-assembled
 (equal (lw-ray-translate-points root (lw-unit-square-boundary count))
  (lw-ray-four-path-perimeter
   (lw-ray-translate-points root (lw-unit-square-side count 0)) (lw-ray-translate-points root (lw-unit-square-side count 2))
   (lw-ray-reverse-points (lw-ray-translate-points root (lw-unit-square-side count 1))) (lw-ray-reverse-points (lw-ray-translate-points root (lw-unit-square-side count 3)))))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-uli-assembled lw-ray-translate-append lw-ray-translate-reverse lw-ray-four-path-perimeter lw-uli-left-commutes lw-uli-left-distributes lw-uli-fold-constants lw-uli-times-negative lw-uli-negative-times lw-uli-zero-times lw-uli-minus-one lw-uli-double-negative lw-uli-add-cancel lw-uli-double lw-uli-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
          :do-not-induct t))))

(local (defthm lw-uli-indicator-algebra
 (implies (and (rationalp x) (rationalp y))
  (equal
   (- (if (< x 1) (- (if (< y 1) 1 0) (if (< y -1) 1 0)) 0)
      (if (< x -1) (- (if (< y 1) 1 0) (if (< y -1) 1 0)) 0))
   (if (and (<= -1 x) (< x 1) (<= -1 y) (< y 1)) 1 0)))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-uli-left-commutes lw-uli-left-distributes lw-uli-fold-constants lw-uli-times-negative lw-uli-negative-times lw-uli-zero-times lw-uli-minus-one lw-uli-double-negative lw-uli-add-cancel lw-uli-double lw-uli-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))))

(defthm lw-unit-square-translated-boundary-index
 (implies (and (lw-complexp root) (posp count))
  (equal (lw-ray-polygon-index (lw-ray-translate-points root (lw-unit-square-boundary count)))
         (lw-unit-square-root-index root)))
 :hints (("Goal"
  :use (lw-unit-square-translated-side-indices
        (:instance lw-unit-square-translated-side-data (edge 0))
        (:instance lw-unit-square-translated-side-data (edge 1))
        (:instance lw-unit-square-translated-side-data (edge 2))
        (:instance lw-unit-square-translated-side-data (edge 3))
        (:instance lw-ray-four-path-perimeter-index
          (bottom (lw-ray-translate-points root (lw-unit-square-side count 0))) (right (lw-ray-translate-points root (lw-unit-square-side count 2)))
          (top (lw-ray-reverse-points (lw-ray-translate-points root (lw-unit-square-side count 1)))) (left (lw-ray-reverse-points (lw-ray-translate-points root (lw-unit-square-side count 3)))))
        (:instance lw-uli-indicator-algebra (x (car root)) (y (cdr root))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-uli-translated-assembled lw-unit-square-root-index lw-ray-reverse-points-data lw-ray-reverse-points-endpoints lw-ray-row-index-reverse lw-ray-row-index-integer lw-complexp (:executable-counterpart lw-polynomial-square-edge-left) (:executable-counterpart lw-polynomial-square-edge-right) lw-uli-left-commutes lw-uli-left-distributes lw-uli-fold-constants lw-uli-times-negative lw-uli-negative-times lw-uli-zero-times lw-uli-minus-one lw-uli-double-negative lw-uli-add-cancel lw-uli-double lw-uli-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-unit-square-linear-index-zero-or-one
 (implies (and (lw-complexp root) (posp count))
  (let ((index (lw-ray-polygon-index (lw-ray-translate-points root (lw-unit-square-boundary count)))))
   (and (<= 0 index) (<= index 1) (or (equal index 0) (equal index 1)))))
 :hints (("Goal" :use (lw-unit-square-translated-boundary-index)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-unit-square-root-index lw-uli-left-commutes lw-uli-left-distributes lw-uli-fold-constants lw-uli-times-negative lw-uli-negative-times lw-uli-zero-times lw-uli-minus-one lw-uli-double-negative lw-uli-add-cancel lw-uli-double lw-uli-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
