(in-package "ACL2")

(include-book "unit-square-clearance")
(include-book "unit-square-mesh")

; Computed clearance and safe meshes for every linear factor off the square.

(local (defthm lw-ulb-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ulb-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ulb-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ulb-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ulb-times-negative (a b) (b a)))
                 :in-theory (disable lw-ulb-times-negative)))))

(local (defthm lw-ulb-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ulb-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ulb-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ulb-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ulb-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ulb-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ulb-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ulb-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ulb-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ulb-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ulb-left-commutes)))))
(local (defthm lw-ulb-rational-inverse
 (implies (rationalp x) (rationalp (/ x)))
 :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-ulb-rational-product
 (implies (and (rationalp x) (rationalp y)) (rationalp (* x y)))
 :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-ulb-parameter
 (implies (and (posp count) (natp index) (<= index count))
  (and (rationalp (* index (/ count))) (<= 0 (* index (/ count))) (<= (* index (/ count)) 1)))
 :hints (("Goal"
  :use ((:instance lw-reciprocal-positive (value count))
        (:instance inverse-of-* (x count))
        (:instance lw-ulb-multiply-order (a 0) (b index) (factor (/ count)))
        (:instance lw-ulb-multiply-order (a index) (b count) (factor (/ count))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-ulb-rational-inverse lw-ulb-rational-product lw-ulb-left-commutes lw-ulb-left-distributes lw-ulb-fold-constants lw-ulb-times-negative lw-ulb-negative-times lw-ulb-zero-times lw-ulb-minus-one lw-ulb-double-negative lw-ulb-add-cancel lw-ulb-double lw-ulb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))


(local (defthm lw-ulb-side-point
 (implies (and (natp edge) (< edge 4) (rationalp parameter) (<= 0 parameter) (<= parameter 1))
  (lw-unit-square-pointp
   (lw-complex-segment (lw-polynomial-square-edge-left '(-1 . -1) 2 edge)
                       (lw-polynomial-square-edge-right '(-1 . -1) 2 edge) parameter)))
 :hints (("Goal" :cases ((equal edge 0) (equal edge 1) (equal edge 2))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-unit-square-point-coordinates lw-polynomial-square-edge-left lw-polynomial-square-edge-right lw-complex-segment lw-complex-add lw-complex-scale lw-complexp lw-ulb-left-commutes lw-ulb-left-distributes lw-ulb-fold-constants lw-ulb-times-negative lw-ulb-negative-times lw-ulb-zero-times lw-ulb-minus-one lw-ulb-double-negative lw-ulb-add-cancel lw-ulb-double lw-ulb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
          :do-not-induct t))))

(local (defthm lw-ulb-side-value-point
 (implies (and (natp edge) (< edge 4) (posp count) (natp index) (<= index count))
  (lw-unit-square-pointp
   (lw-polynomial-line-value '((0 . 0) (1 . 0))
    (lw-polynomial-square-edge-left '(-1 . -1) 2 edge)
    (lw-polynomial-square-edge-right '(-1 . -1) 2 edge) count index)))
 :hints (("Goal"
  :use (lw-ulb-parameter (:instance lw-ulb-side-point (parameter (* index (/ count)))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-line-value lw-polynomial-line-point lw-complex-identity-polynomial lw-complex-segment-rational lw-polynomial-square-edge-left lw-polynomial-square-edge-right lw-complexp lw-ulb-left-commutes lw-ulb-left-distributes lw-ulb-fold-constants lw-ulb-times-negative lw-ulb-negative-times lw-ulb-zero-times lw-ulb-minus-one lw-ulb-double-negative lw-ulb-add-cancel lw-ulb-double lw-ulb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(local (defthm lw-ulb-side-values-points
 (implies (and (natp edge) (< edge 4) (posp count) (natp index) (natp remaining)
               (<= (+ index remaining) (+ 1 count)))
  (lw-ray-unit-square-pointsp (lw-polynomial-line-values '((0 . 0) (1 . 0))
    (lw-polynomial-square-edge-left '(-1 . -1) 2 edge)
    (lw-polynomial-square-edge-right '(-1 . -1) 2 edge) count index remaining)))
 :hints (("Goal" :induct (lw-polynomial-line-values '((0 . 0) (1 . 0))
    (lw-polynomial-square-edge-left '(-1 . -1) 2 edge)
    (lw-polynomial-square-edge-right '(-1 . -1) 2 edge) count index remaining)
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-polynomial-line-values) lw-polynomial-line-values lw-ray-unit-square-pointsp lw-ulb-side-value-point lw-ulb-left-commutes lw-ulb-left-distributes lw-ulb-fold-constants lw-ulb-times-negative lw-ulb-negative-times lw-ulb-zero-times lw-ulb-minus-one lw-ulb-double-negative lw-ulb-add-cancel lw-ulb-double lw-ulb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-ulb-points-append
 (implies (and (lw-ray-unit-square-pointsp left) (lw-ray-unit-square-pointsp right))
  (lw-ray-unit-square-pointsp (append left right)))
 :hints (("Goal" :induct (append left right)
          :in-theory (union-theories
 '(fold-consts-in-+ append lw-ray-unit-square-pointsp endp lw-ulb-left-commutes lw-ulb-left-distributes lw-ulb-fold-constants lw-ulb-times-negative lw-ulb-negative-times lw-ulb-zero-times lw-ulb-minus-one lw-ulb-double-negative lw-ulb-add-cancel lw-ulb-double lw-ulb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))
(local (defthm lw-ulb-points-reverse
 (implies (lw-ray-unit-square-pointsp points)
  (lw-ray-unit-square-pointsp (lw-ray-reverse-points points)))
 :hints (("Goal" :induct (lw-ray-reverse-points points)
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-ray-reverse-points) lw-ray-reverse-points lw-ray-unit-square-pointsp lw-ulb-points-append endp lw-ulb-left-commutes lw-ulb-left-distributes lw-ulb-fold-constants lw-ulb-times-negative lw-ulb-negative-times lw-ulb-zero-times lw-ulb-minus-one lw-ulb-double-negative lw-ulb-add-cancel lw-ulb-double lw-ulb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-unit-square-boundary-points
 (implies (posp count) (lw-ray-unit-square-pointsp (lw-unit-square-boundary count)))
 :hints (("Goal"
  :use ((:instance lw-ulb-side-values-points (edge 0) (index 0) (remaining (+ 1 count)))
        (:instance lw-ulb-side-values-points (edge 1) (index 0) (remaining (+ 1 count)))
        (:instance lw-ulb-side-values-points (edge 2) (index 0) (remaining (+ 1 count)))
        (:instance lw-ulb-side-values-points (edge 3) (index 0) (remaining (+ 1 count))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-unit-square-boundary lw-polynomial-square-line-boundary lw-ray-four-path-perimeter lw-ulb-points-append lw-ulb-points-reverse lw-ulb-left-commutes lw-ulb-left-distributes lw-ulb-fold-constants lw-ulb-times-negative lw-ulb-negative-times lw-ulb-zero-times lw-ulb-minus-one lw-ulb-double-negative lw-ulb-add-cancel lw-ulb-double lw-ulb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-unit-square-linear-boundary-annulus
 (implies (and (lw-complexp root) (posp count))
  (let ((points (lw-ray-translate-points root (lw-unit-square-boundary count))))
   (and (lw-ray-pointsp points) (consp points)
        (equal (lw-ray-row-last points) (car points))
        (lw-ray-annulus-pointsp points (lw-unit-square-root-gap root) (lw-unit-square-root-cap root)))))
 :hints (("Goal"
  :use (lw-unit-square-boundary-points lw-unit-square-boundary-data
        (:instance lw-ray-translate-points-data (points (lw-unit-square-boundary count)))
        (:instance lw-ray-unit-square-translate-annulus (points (lw-unit-square-boundary count))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-translate-points-head lw-ray-translate-row-last lw-ulb-left-commutes lw-ulb-left-distributes lw-ulb-fold-constants lw-ulb-times-negative lw-ulb-negative-times lw-ulb-zero-times lw-ulb-minus-one lw-ulb-double-negative lw-ulb-add-cancel lw-ulb-double lw-ulb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defun lw-unit-square-linear-count (root)
 (* 4 (lw-unit-square-mesh-factor (* 1/2 (lw-unit-square-root-gap root)))))

(defthm lw-unit-square-linear-count-data
 (implies (and (lw-complexp root) (not (lw-unit-square-pointp root)))
  (and (posp (lw-unit-square-linear-count root))
       (< 0 (lw-unit-square-root-gap root))
       (<= (* 2 (/ (lw-unit-square-linear-count root))) (* 1/2 (lw-unit-square-root-gap root)))))
 :hints (("Goal"
  :use (lw-unit-square-root-gap-data
        (:instance lw-unit-square-mesh-factor-data (error (* 1/2 (lw-unit-square-root-gap root)))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-unit-square-linear-count lw-ulb-rational-product lw-ulb-left-commutes lw-ulb-left-distributes lw-ulb-fold-constants lw-ulb-times-negative lw-ulb-negative-times lw-ulb-zero-times lw-ulb-minus-one lw-ulb-double-negative lw-ulb-add-cancel lw-ulb-double lw-ulb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-unit-square-linear-boundary-safe
 (implies (and (lw-complexp root) (not (lw-unit-square-pointp root)))
  (lw-ray-safe-polygonp
   (lw-ray-translate-points root (lw-unit-square-boundary (lw-unit-square-linear-count root)))))
 :hints (("Goal"
  :use (lw-unit-square-root-gap-data lw-unit-square-linear-count-data
        (:instance lw-unit-square-linear-boundary-annulus (count (lw-unit-square-linear-count root)))
        (:instance lw-unit-square-boundary-data (count (lw-unit-square-linear-count root)))
        (:instance lw-unit-square-boundary-step (count (lw-unit-square-linear-count root)))
        (:instance lw-ray-translate-path-step
          (points (lw-unit-square-boundary (lw-unit-square-linear-count root)))
          (error (* 2 (/ (lw-unit-square-linear-count root)))))
        (:instance lw-ray-path-step-enlarge
          (points (lw-ray-translate-points root (lw-unit-square-boundary (lw-unit-square-linear-count root))))
          (delta (* 2 (/ (lw-unit-square-linear-count root))))
          (larger (* 1/2 (lw-unit-square-root-gap root))))
        (:instance lw-ray-annulus-closed-polygon-safe
          (points (lw-ray-translate-points root (lw-unit-square-boundary (lw-unit-square-linear-count root))))
          (lower (lw-unit-square-root-gap root)) (upper (lw-unit-square-root-cap root))
          (delta (* 1/2 (lw-unit-square-root-gap root)))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-ulb-rational-inverse lw-ulb-rational-product lw-ulb-left-commutes lw-ulb-left-distributes lw-ulb-fold-constants lw-ulb-times-negative lw-ulb-negative-times lw-ulb-zero-times lw-ulb-minus-one lw-ulb-double-negative lw-ulb-add-cancel lw-ulb-double lw-ulb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-unit-square-leading-linear-index
 (implies (and (lw-complexp root) (not (lw-unit-square-pointp root))
               (lw-complexp leading) (not (equal leading (cons 0 0))))
  (let ((index (lw-ray-polygon-index
                (lw-ray-multiply-points leading
                 (lw-ray-translate-points root (lw-unit-square-boundary (lw-unit-square-linear-count root)))))))
   (and (equal index (lw-unit-square-root-index root)) (<= 0 index) (<= index 1))))
 :hints (("Goal"
  :use (lw-unit-square-linear-boundary-safe lw-unit-square-linear-count-data
        (:instance lw-unit-square-translated-boundary-index (count (lw-unit-square-linear-count root)))
        (:instance lw-ray-polygon-product-invariant (factor leading)
          (points (lw-ray-translate-points root (lw-unit-square-boundary (lw-unit-square-linear-count root))))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-unit-square-root-index lw-ulb-left-commutes lw-ulb-left-distributes lw-ulb-fold-constants lw-ulb-times-negative lw-ulb-negative-times lw-ulb-zero-times lw-ulb-minus-one lw-ulb-double-negative lw-ulb-add-cancel lw-ulb-double lw-ulb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
