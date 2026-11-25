(in-package "ACL2")

(include-book "unit-square-axes")

; Exact coordinate, endpoint and crossing data for the linear factor z-root.

(local (defthm lw-uts-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-uts-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-uts-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-uts-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-uts-times-negative (a b) (b a)))
                 :in-theory (disable lw-uts-times-negative)))))

(local (defthm lw-uts-zero-times (equal (* 0 a) 0)))

(local (defthm lw-uts-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-uts-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-uts-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-uts-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-uts-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-uts-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-uts-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-uts-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-uts-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-uts-left-commutes)))))
(defthm lw-unit-square-translated-side-data
 (implies (and (lw-complexp root) (posp count) (natp edge) (< edge 4))
  (let ((points (lw-ray-translate-points root (lw-unit-square-side count edge))))
   (and (lw-ray-pointsp points) (consp points)
        (equal (car points) (lw-complex-sub (lw-polynomial-square-edge-left '(-1 . -1) 2 edge) root))
        (equal (lw-ray-row-last points)
               (lw-complex-sub (lw-polynomial-square-edge-right '(-1 . -1) 2 edge) root)))))
 :hints (("Goal"
  :use (lw-unit-square-side-data
        (:instance lw-ray-translate-points-data (points (lw-unit-square-side count edge))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-translate-points-head lw-ray-translate-row-last lw-uts-left-commutes lw-uts-left-distributes lw-uts-fold-constants lw-uts-times-negative lw-uts-negative-times lw-uts-zero-times lw-uts-minus-one lw-uts-double-negative lw-uts-add-cancel lw-uts-double lw-uts-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-unit-square-translated-side-axes
 (implies (and (lw-complexp root) (posp count))
  (and (lw-ray-fixed-imag-pointsp (lw-ray-translate-points root (lw-unit-square-side count 0)) (- -1 (cdr root)))
       (lw-ray-fixed-imag-pointsp (lw-ray-translate-points root (lw-unit-square-side count 1)) (- 1 (cdr root)))
       (lw-ray-fixed-real-pointsp (lw-ray-translate-points root (lw-unit-square-side count 2)) (- 1 (car root)))
       (lw-ray-fixed-real-pointsp (lw-ray-translate-points root (lw-unit-square-side count 3)) (- -1 (car root)))))
 :hints (("Goal"
  :use (lw-unit-square-side-axes
        (:instance lw-ray-translate-fixed-imag (points (lw-unit-square-side count 0)) (imag -1))
        (:instance lw-ray-translate-fixed-imag (points (lw-unit-square-side count 1)) (imag 1))
        (:instance lw-ray-translate-fixed-real (points (lw-unit-square-side count 2)) (real 1))
        (:instance lw-ray-translate-fixed-real (points (lw-unit-square-side count 3)) (real -1)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-uts-left-commutes lw-uts-left-distributes lw-uts-fold-constants lw-uts-times-negative lw-uts-negative-times lw-uts-zero-times lw-uts-minus-one lw-uts-double-negative lw-uts-add-cancel lw-uts-double lw-uts-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-unit-square-translated-side-indices
 (implies (and (lw-complexp root) (posp count))
  (and (equal (lw-ray-row-index (lw-ray-translate-points root (lw-unit-square-side count 0))) 0)
       (equal (lw-ray-row-index (lw-ray-translate-points root (lw-unit-square-side count 1))) 0)
       (equal (lw-ray-row-index (lw-ray-translate-points root (lw-unit-square-side count 2)))
              (if (< (car root) 1)
               (- (if (< (cdr root) 1) 1 0) (if (< (cdr root) -1) 1 0)) 0))
       (equal (lw-ray-row-index (lw-ray-translate-points root (lw-unit-square-side count 3)))
              (if (< (car root) -1)
               (- (if (< (cdr root) 1) 1 0) (if (< (cdr root) -1) 1 0)) 0))))
 :hints (("Goal"
  :use (lw-unit-square-translated-side-axes
        (:instance lw-unit-square-translated-side-data (edge 0))
        (:instance lw-unit-square-translated-side-data (edge 1))
        (:instance lw-unit-square-translated-side-data (edge 2))
        (:instance lw-unit-square-translated-side-data (edge 3))
        (:instance lw-ray-horizontal-row-zero
          (points (lw-ray-translate-points root (lw-unit-square-side count 0))) (imag (- -1 (cdr root))))
        (:instance lw-ray-horizontal-row-zero
          (points (lw-ray-translate-points root (lw-unit-square-side count 1))) (imag (- 1 (cdr root))))
        (:instance lw-ray-vertical-row-potential
          (points (lw-ray-translate-points root (lw-unit-square-side count 2))) (real (- 1 (car root))))
        (:instance lw-ray-vertical-row-potential
          (points (lw-ray-translate-points root (lw-unit-square-side count 3))) (real (- -1 (car root)))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-upper-indicator lw-complex-sub lw-complexp (:executable-counterpart lw-polynomial-square-edge-left) (:executable-counterpart lw-polynomial-square-edge-right) lw-uts-left-commutes lw-uts-left-distributes lw-uts-fold-constants lw-uts-times-negative lw-uts-negative-times lw-uts-zero-times lw-uts-minus-one lw-uts-double-negative lw-uts-add-cancel lw-uts-double lw-uts-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))
