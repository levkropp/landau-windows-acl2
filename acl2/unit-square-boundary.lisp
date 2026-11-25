(in-package "ACL2")

(include-book "polynomial-square-lines")
(include-book "ray-path-assembly")
(include-book "ray-power-index")

; Canonical [-1,1]^2 boundary sampled directly along four sides.
; Every vertex is in the annulus 1 <= |z| <= 2.

(local (defthm lw-usb-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-usb-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-usb-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-usb-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-usb-times-negative (a b) (b a)))
                 :in-theory (disable lw-usb-times-negative)))))

(local (defthm lw-usb-zero-times (equal (* 0 a) 0)))

(local (defthm lw-usb-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-usb-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-usb-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-usb-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-usb-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-usb-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-usb-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-usb-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-usb-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-usb-left-commutes)))))

(defun lw-unit-square-boundary (count)
 (lw-polynomial-square-line-boundary '((0 . 0) (1 . 0)) '(-1 . -1) 2 count))

(defthm lw-unit-square-boundary-canonical
 (implies (posp count)
  (equal (lw-unit-square-boundary count)
         (lw-polynomial-square-boundary '(-1 . -1) 2 count)))
 :hints (("Goal"
  :use ((:instance lw-polynomial-square-domain-lines (anchor '(-1 . -1)) (side 2)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-unit-square-boundary (:executable-counterpart lw-complexp) lw-usb-left-commutes lw-usb-left-distributes lw-usb-fold-constants lw-usb-times-negative lw-usb-negative-times lw-usb-zero-times lw-usb-minus-one lw-usb-double-negative lw-usb-add-cancel lw-usb-double lw-usb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-usb-square-nonnegative
 (implies (rationalp x) (<= 0 (* x x)))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-usb-coordinate-annulus
 (implies (and (rationalp x) (rationalp y)
               (<= -1 x) (<= x 1) (<= -1 y) (<= y 1)
               (or (equal x -1) (equal x 1) (equal y -1) (equal y 1)))
  (and (lw-complex-diskp (cons x y) 2)
       (<= 1 (lw-complex-norm-square (cons x y)))))
 :hints (("Goal"
  :use ((:instance lw-usb-square-nonnegative (x x))
        (:instance lw-usb-square-nonnegative (x y))
        (:instance lw-complex-l1-bound (point (cons x y)))
        (:instance lw-complex-disk-enlarge (point (cons x y)) (radius (+ (abs x) (abs y))) (cap 2)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-complexp lw-complex-l1 lw-complex-norm-square abs lw-usb-left-commutes lw-usb-left-distributes lw-usb-fold-constants lw-usb-times-negative lw-usb-negative-times lw-usb-zero-times lw-usb-minus-one lw-usb-double-negative lw-usb-add-cancel lw-usb-double lw-usb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :cases ((equal x -1) (equal x 1) (equal y -1))))))

(local (defthm lw-usb-side-annulus
 (implies (and (natp edge) (< edge 4) (rationalp parameter) (<= 0 parameter) (<= parameter 1))
  (let ((point (lw-complex-segment
          (lw-polynomial-square-edge-left '(-1 . -1) 2 edge)
          (lw-polynomial-square-edge-right '(-1 . -1) 2 edge) parameter)))
   (and (lw-complex-diskp point 2) (<= 1 (lw-complex-norm-square point)))))
 :hints (("Goal"
  :use ((:instance lw-usb-coordinate-annulus
   (x (car (lw-complex-segment
          (lw-polynomial-square-edge-left '(-1 . -1) 2 edge)
          (lw-polynomial-square-edge-right '(-1 . -1) 2 edge) parameter)))
   (y (cdr (lw-complex-segment
          (lw-polynomial-square-edge-left '(-1 . -1) 2 edge)
          (lw-polynomial-square-edge-right '(-1 . -1) 2 edge) parameter)))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-square-edge-left lw-polynomial-square-edge-right lw-complex-segment lw-complex-add lw-complex-scale lw-usb-left-commutes lw-usb-left-distributes lw-usb-fold-constants lw-usb-times-negative lw-usb-negative-times lw-usb-zero-times lw-usb-minus-one lw-usb-double-negative lw-usb-add-cancel lw-usb-double lw-usb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :cases ((equal edge 0) (equal edge 1) (equal edge 2))))))

(local (defthm lw-usb-rational-inverse
 (implies (rationalp x) (rationalp (/ x)))
 :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-usb-rational-product
 (implies (and (rationalp x) (rationalp y)) (rationalp (* x y)))
 :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-usb-parameter
 (implies (and (posp count) (natp index) (<= index count))
  (and (rationalp (* index (/ count))) (<= 0 (* index (/ count))) (<= (* index (/ count)) 1)))
 :hints (("Goal"
  :use ((:instance lw-reciprocal-positive (value count))
        (:instance inverse-of-* (x count))
        (:instance lw-usb-multiply-order (a 0) (b index) (factor (/ count)))
        (:instance lw-usb-multiply-order (a index) (b count) (factor (/ count))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-usb-rational-inverse lw-usb-rational-product lw-usb-left-commutes lw-usb-left-distributes lw-usb-fold-constants lw-usb-times-negative lw-usb-negative-times lw-usb-zero-times lw-usb-minus-one lw-usb-double-negative lw-usb-add-cancel lw-usb-double lw-usb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-usb-side-value-annulus
 (implies (and (natp edge) (< edge 4) (posp count) (natp index) (<= index count))
  (let ((point (lw-polynomial-line-value '((0 . 0) (1 . 0))
          (lw-polynomial-square-edge-left '(-1 . -1) 2 edge)
          (lw-polynomial-square-edge-right '(-1 . -1) 2 edge) count index)))
   (and (lw-complex-diskp point 2) (<= 1 (lw-complex-norm-square point)))))
 :hints (("Goal"
  :use (lw-usb-parameter
        (:instance lw-usb-side-annulus (parameter (* index (/ count)))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-line-value lw-polynomial-line-point lw-complex-identity-polynomial lw-complex-segment-rational lw-polynomial-square-edge-left lw-polynomial-square-edge-right lw-complexp lw-usb-left-commutes lw-usb-left-distributes lw-usb-fold-constants lw-usb-times-negative lw-usb-negative-times lw-usb-zero-times lw-usb-minus-one lw-usb-double-negative lw-usb-add-cancel lw-usb-double lw-usb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-usb-side-values-annulus
 (implies (and (natp edge) (< edge 4) (posp count) (natp index) (natp remaining)
               (<= (+ index remaining) (+ 1 count)))
  (lw-ray-annulus-pointsp
   (lw-polynomial-line-values '((0 . 0) (1 . 0))
    (lw-polynomial-square-edge-left '(-1 . -1) 2 edge)
    (lw-polynomial-square-edge-right '(-1 . -1) 2 edge)
    count index remaining) 1 2))
 :hints (("Goal" :induct (lw-polynomial-line-values '((0 . 0) (1 . 0))
    (lw-polynomial-square-edge-left '(-1 . -1) 2 edge)
    (lw-polynomial-square-edge-right '(-1 . -1) 2 edge) count index remaining)
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-line-values lw-ray-annulus-pointsp lw-usb-side-value-annulus lw-usb-left-commutes lw-usb-left-distributes lw-usb-fold-constants lw-usb-times-negative lw-usb-negative-times lw-usb-zero-times lw-usb-minus-one lw-usb-double-negative lw-usb-add-cancel lw-usb-double lw-usb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-unit-square-boundary-annulus
 (implies (posp count) (lw-ray-annulus-pointsp (lw-unit-square-boundary count) 1 2))
 :hints (("Goal"
  :use ((:instance lw-usb-side-values-annulus (edge 0) (index 0) (remaining (+ 1 count)))
        (:instance lw-usb-side-values-annulus (edge 1) (index 0) (remaining (+ 1 count)))
        (:instance lw-usb-side-values-annulus (edge 2) (index 0) (remaining (+ 1 count)))
        (:instance lw-usb-side-values-annulus (edge 3) (index 0) (remaining (+ 1 count))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-unit-square-boundary lw-polynomial-square-line-boundary lw-ray-four-path-perimeter lw-ray-annulus-append lw-ray-annulus-reverse lw-usb-left-commutes lw-usb-left-distributes lw-usb-fold-constants lw-usb-times-negative lw-usb-negative-times lw-usb-zero-times lw-usb-minus-one lw-usb-double-negative lw-usb-add-cancel lw-usb-double lw-usb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-unit-square-boundary-data
 (implies (posp count)
  (and (lw-ray-pointsp (lw-unit-square-boundary count))
       (consp (lw-unit-square-boundary count))
       (equal (lw-ray-row-last (lw-unit-square-boundary count)) (car (lw-unit-square-boundary count)))
       (equal (len (lw-unit-square-boundary count)) (* 4 (+ 1 count)))))
 :hints (("Goal"
  :use ((:instance lw-polynomial-square-boundary-data (anchor '(-1 . -1)) (side 2)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-unit-square-boundary-canonical (:executable-counterpart lw-complexp) lw-usb-left-commutes lw-usb-left-distributes lw-usb-fold-constants lw-usb-times-negative lw-usb-negative-times lw-usb-zero-times lw-usb-minus-one lw-usb-double-negative lw-usb-add-cancel lw-usb-double lw-usb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-unit-square-coarse-certificate
 (and (lw-polynomial-square-boundary-check '((0 . 0) (1 . 0)) '(-1 . -1) 2 4)
      (equal (lw-ray-polygon-index (lw-unit-square-boundary 4)) 1)))

(defthm lw-unit-square-boundary-index
 (implies (posp factor)
  (equal (lw-ray-polygon-index (lw-unit-square-boundary (* 4 factor))) 1))
 :hints (("Goal"
  :use (lw-unit-square-coarse-certificate
        (:instance lw-polynomial-square-refinement-index
          (coefficients '((0 . 0) (1 . 0))) (anchor '(-1 . -1)) (side 2) (coarse 4))
        (:instance lw-polynomial-grid-boundary-as-polygon
          (coefficients '((0 . 0) (1 . 0))) (anchor '(-1 . -1)) (side 2) (count 4))
        (:instance lw-polynomial-grid-boundary-as-polygon
          (coefficients '((0 . 0) (1 . 0))) (anchor '(-1 . -1)) (side 2) (count (* 4 factor)))
        (:instance lw-polynomial-square-boundary-data (anchor '(-1 . -1)) (side 2) (count 4))
        (:instance lw-polynomial-square-boundary-data (anchor '(-1 . -1)) (side 2) (count (* 4 factor))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-unit-square-boundary-canonical lw-polynomial-identity-path-values (:executable-counterpart lw-complex-coefficientsp) (:executable-counterpart lw-complexp) lw-usb-left-commutes lw-usb-left-distributes lw-usb-fold-constants lw-usb-times-negative lw-usb-negative-times lw-usb-zero-times lw-usb-minus-one lw-usb-double-negative lw-usb-add-cancel lw-usb-double lw-usb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

