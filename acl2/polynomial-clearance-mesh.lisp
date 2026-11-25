(in-package "ACL2")

(include-book "euler-square-polynomial-check")

; Compute an integer-multiple mesh from coefficients and a supplied positive margin.

(local (defthm lw-pcm-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pcm-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pcm-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pcm-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pcm-times-negative (a b) (b a)))
                 :in-theory (disable lw-pcm-times-negative)))))

(local (defthm lw-pcm-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pcm-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pcm-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pcm-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pcm-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pcm-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pcm-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-pcm-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pcm-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pcm-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-pcm-left-commutes)))))

(local (defthm lw-pcm-product-rational
 (implies (and (rationalp a) (rationalp b)) (rationalp (* a b)))
 :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-pcm-inverse-rational
 (implies (rationalp a) (rationalp (/ a))) :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-pcm-division-enlarge
 (implies (and (rationalp numerator) (<= 0 numerator)
               (rationalp divisor) (< 0 divisor) (rationalp larger) (<= divisor larger)
               (rationalp bound) (<= 0 bound)
               (<= (* numerator (/ divisor)) bound))
  (<= (* numerator (/ larger)) bound))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance lw-pcm-multiply-order (a (* numerator (/ divisor))) (b bound) (factor divisor))
        (:instance lw-pcm-inverse-factor (coefficient numerator))
        (:instance lw-pcm-multiply-order (a divisor) (b larger) (factor bound))
        (:instance lw-positive-division-bound (divisor larger)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-pcm-product-rational lw-pcm-inverse-rational lw-pcm-left-commutes lw-pcm-left-distributes lw-pcm-fold-constants lw-pcm-times-negative lw-pcm-negative-times lw-pcm-zero-times lw-pcm-minus-one lw-pcm-double-negative lw-pcm-add-cancel lw-pcm-double lw-pcm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))))

(defun lw-polynomial-clearance-count (coefficients anchor side coarse clearance)
 (* coarse (lw-polynomial-root-count coefficients anchor side clearance)))

(defthm lw-polynomial-clearance-count-data
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor) (rationalp side) (< 0 side)
               (posp coarse) (rationalp clearance) (< 0 clearance))
  (and (posp (lw-polynomial-clearance-count coefficients anchor side coarse clearance)) (<= (* 2 (lw-polynomial-grid-step side (lw-polynomial-clearance-count coefficients anchor side coarse clearance)) (lw-polynomial-lipschitz-cap coefficients (lw-polynomial-grid-radius anchor side))) clearance)))
 :hints (("Goal"
  :use ((:instance lw-polynomial-root-count-data (epsilon clearance)) lw-polynomial-grid-radius-data
        (:instance lw-polynomial-lipschitz-cap-data (bound (lw-polynomial-grid-radius anchor side)))
        (:instance lw-pcm-positive-product (a coarse) (b (lw-polynomial-root-count coefficients anchor side clearance)))
        (:instance lw-pcm-multiply-order (a 1) (b coarse) (factor (lw-polynomial-root-count coefficients anchor side clearance)))
        (:instance lw-pcm-division-enlarge (numerator (* 2 side (lw-polynomial-lipschitz-cap coefficients (lw-polynomial-grid-radius anchor side))))
          (divisor (lw-polynomial-root-count coefficients anchor side clearance)) (larger (* coarse (lw-polynomial-root-count coefficients anchor side clearance))) (bound clearance)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-clearance-count lw-polynomial-grid-step lw-pcm-product-rational lw-pcm-left-commutes lw-pcm-left-distributes lw-pcm-fold-constants lw-pcm-times-negative lw-pcm-negative-times lw-pcm-zero-times lw-pcm-minus-one lw-pcm-double-negative lw-pcm-add-cancel lw-pcm-double lw-pcm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-polynomial-clearance-edge-cap-data
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor) (rationalp side) (< 0 side)
               (posp coarse) (rationalp clearance) (< 0 clearance))
  (and (rationalp (lw-polynomial-edge-cap coefficients (lw-polynomial-grid-radius anchor side) (lw-polynomial-grid-step side (lw-polynomial-clearance-count coefficients anchor side coarse clearance)))) (<= 0 (lw-polynomial-edge-cap coefficients (lw-polynomial-grid-radius anchor side) (lw-polynomial-grid-step side (lw-polynomial-clearance-count coefficients anchor side coarse clearance)))) (< (lw-polynomial-edge-cap coefficients (lw-polynomial-grid-radius anchor side) (lw-polynomial-grid-step side (lw-polynomial-clearance-count coefficients anchor side coarse clearance))) clearance)))
 :hints (("Goal"
  :use (lw-polynomial-clearance-count-data lw-polynomial-grid-radius-data
        (:instance lw-polynomial-grid-step-data (count (lw-polynomial-clearance-count coefficients anchor side coarse clearance)))
        (:instance lw-polynomial-lipschitz-cap-data (bound (lw-polynomial-grid-radius anchor side)))
        (:instance lw-pcm-multiply-order (a 0) (b (lw-polynomial-lipschitz-cap coefficients (lw-polynomial-grid-radius anchor side))) (factor (lw-polynomial-grid-step side (lw-polynomial-clearance-count coefficients anchor side coarse clearance)))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-edge-cap lw-pcm-product-rational lw-pcm-left-commutes lw-pcm-left-distributes lw-pcm-fold-constants lw-pcm-times-negative lw-pcm-negative-times lw-pcm-zero-times lw-pcm-minus-one lw-pcm-double-negative lw-pcm-add-cancel lw-pcm-double lw-pcm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(local (defthm lw-pcm-contained-type
 (implies (lw-square-containsp anchor side point) (lw-complexp point))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-square-containsp lw-pcm-left-commutes lw-pcm-left-distributes lw-pcm-fold-constants lw-pcm-times-negative lw-pcm-negative-times lw-pcm-zero-times lw-pcm-minus-one lw-pcm-double-negative lw-pcm-add-cancel lw-pcm-double lw-pcm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))))

(local (defthm lw-pcm-norm-lower
 (implies (and (lw-complexp point) (rationalp radius) (<= 0 radius)
               (rationalp clearance) (< 0 clearance) (< radius clearance) (not (lw-complex-diskp point clearance)))
  (< (* radius radius) (lw-complex-norm-square point)))
 :rule-classes nil
 :hints (("Goal" :use ((:instance lw-complex-disk-norm-square (radius clearance)))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-pcm-left-commutes lw-pcm-left-distributes lw-pcm-fold-constants lw-pcm-times-negative lw-pcm-negative-times lw-pcm-zero-times lw-pcm-minus-one lw-pcm-double-negative lw-pcm-add-cancel lw-pcm-double lw-pcm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :nonlinearp t))))

(defthm lw-polynomial-clearance-edge-check
 (implies (and (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor) (rationalp side) (< 0 side)
               (posp coarse) (rationalp clearance) (< 0 clearance))
               (natp edge) (< edge 4) (natp index) (< index (lw-polynomial-clearance-count coefficients anchor side coarse clearance))
               (not (lw-complex-diskp (lw-polynomial-line-value coefficients (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) (lw-polynomial-clearance-count coefficients anchor side coarse clearance) index) clearance)))
  (lw-polynomial-edge-check coefficients (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) (lw-polynomial-clearance-count coefficients anchor side coarse clearance) index) (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) (lw-polynomial-clearance-count coefficients anchor side coarse clearance) (+ 1 index)) (lw-polynomial-grid-radius anchor side) (lw-polynomial-grid-step side (lw-polynomial-clearance-count coefficients anchor side coarse clearance))))
 :hints (("Goal"
  :use (lw-polynomial-clearance-count-data lw-polynomial-clearance-edge-cap-data lw-polynomial-grid-radius-data
        (:instance lw-polynomial-grid-step-data (count (lw-polynomial-clearance-count coefficients anchor side coarse clearance)))
        (:instance lw-polynomial-square-line-point-contained (count (lw-polynomial-clearance-count coefficients anchor side coarse clearance)))
        (:instance lw-polynomial-square-line-point-contained (count (lw-polynomial-clearance-count coefficients anchor side coarse clearance)) (index (+ 1 index)))
        (:instance lw-square-contained-in-disk (point (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) (lw-polynomial-clearance-count coefficients anchor side coarse clearance) index)))
        (:instance lw-square-contained-in-disk (point (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) (lw-polynomial-clearance-count coefficients anchor side coarse clearance) (+ 1 index))))
        (:instance lw-polynomial-square-line-step-exact (count (lw-polynomial-clearance-count coefficients anchor side coarse clearance)))
        (:instance lw-pcm-norm-lower (point (lw-complex-polynomial coefficients (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) (lw-polynomial-clearance-count coefficients anchor side coarse clearance) index) 0)) (radius (lw-polynomial-edge-cap coefficients (lw-polynomial-grid-radius anchor side) (lw-polynomial-grid-step side (lw-polynomial-clearance-count coefficients anchor side coarse clearance)))) (clearance clearance)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-edge-check lw-polynomial-line-value lw-complex-polynomial-rational lw-pcm-contained-type lw-pcm-left-commutes lw-pcm-left-distributes lw-pcm-fold-constants lw-pcm-times-negative lw-pcm-negative-times lw-pcm-zero-times lw-pcm-minus-one lw-pcm-double-negative lw-pcm-add-cancel lw-pcm-double lw-pcm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))
