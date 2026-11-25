(in-package "ACL2")

(include-book "ray-crossing")

; Positive changes of radial length preserve crossings. A determinant-zero
; edge with positive dot product has endpoints on the same nonzero ray.

(local (defthm lw-rps-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-rps-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-rps-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-rps-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-rps-times-negative (a b) (b a)))
                 :in-theory (disable lw-rps-times-negative)))))

(local (defthm lw-rps-zero-times (equal (* 0 a) 0)))

(local (defthm lw-rps-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-rps-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-rps-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-rps-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-rps-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-rps-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-rps-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-rps-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-rps-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-rps-left-commutes)))))

(defthm lw-complex-det-scales
 (implies (and (lw-complexp a) (lw-complexp b)
               (rationalp s) (rationalp t0))
  (equal (lw-complex-det (lw-complex-scale s a) (lw-complex-scale t0 b))
         (* s t0 (lw-complex-det a b))))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complexp lw-complex-det lw-complex-scale lw-rps-left-commutes lw-rps-left-distributes lw-rps-fold-constants lw-rps-times-negative lw-rps-negative-times lw-rps-zero-times lw-rps-minus-one lw-rps-double-negative lw-rps-add-cancel lw-rps-double lw-rps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-rps-positive-scale-sign
 (implies (and (rationalp s) (< 0 s) (rationalp x))
  (and (equal (< 0 (* s x)) (< 0 x))
       (equal (< (* s x) 0) (< x 0))
       (equal (<= (* s x) 0) (<= x 0))))
 :hints (("Goal" :cases ((< 0 x) (< x 0)) :nonlinearp t))))

(local (defthm lw-rps-positive-product-sign
 (implies (and (rationalp s) (< 0 s) (rationalp t0) (< 0 t0) (rationalp x))
  (and (equal (< 0 (* s t0 x)) (< 0 x))
       (equal (< (* s t0 x) 0) (< x 0))))
 :hints (("Goal" :cases ((< 0 x) (< x 0)) :nonlinearp t))))

(local (defthm lw-rps-scale-imaginary
 (equal (cdr (lw-complex-scale factor point)) (* factor (cdr point)))
 :hints (("Goal" :in-theory (enable lw-complex-scale)))))

(defthm lw-ray-crossing-positive-scales
 (implies (and (lw-complexp a) (lw-complexp b)
               (rationalp s) (< 0 s) (rationalp t0) (< 0 t0))
  (equal (lw-ray-crossing (lw-complex-scale s a) (lw-complex-scale t0 b))
         (lw-ray-crossing a b)))
 :hints (("Goal"
  :use (lw-complex-orientation-rational)
  :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-crossing lw-complex-det-scales lw-rps-scale-imaginary lw-complexp lw-rps-positive-scale-sign lw-rps-positive-product-sign lw-rps-left-commutes lw-rps-left-distributes lw-rps-fold-constants lw-rps-times-negative lw-rps-negative-times lw-rps-zero-times lw-rps-minus-one lw-rps-double-negative lw-rps-add-cancel lw-rps-double lw-rps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-rps-dot-det-identity
 (implies (and (lw-complexp a) (lw-complexp b))
  (equal (lw-complex-scale (lw-complex-norm-square a) b)
   (lw-complex-add (lw-complex-scale (lw-complex-dot a b) a)
    (lw-complex-scale (lw-complex-det a b) (cons (- (cdr a)) (car a))))))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complexp lw-complex-det lw-complex-dot lw-complex-norm-square lw-complex-scale lw-complex-add lw-rps-left-commutes lw-rps-left-distributes lw-rps-fold-constants lw-rps-times-negative lw-rps-negative-times lw-rps-zero-times lw-rps-minus-one lw-rps-double-negative lw-rps-add-cancel lw-rps-double lw-rps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-rps-det-dot-reconstruction
 (implies (and (lw-complexp a) (lw-complexp b) (equal (lw-complex-det a b) 0))
  (equal (lw-complex-scale (lw-complex-norm-square a) b)
         (lw-complex-scale (lw-complex-dot a b) a)))
 :hints (("Goal" :use (lw-rps-dot-det-identity)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-complexp lw-complex-scale lw-complex-add lw-rps-left-commutes lw-rps-left-distributes lw-rps-fold-constants lw-rps-times-negative lw-rps-negative-times lw-rps-zero-times lw-rps-minus-one lw-rps-double-negative lw-rps-add-cancel lw-rps-double lw-rps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-rps-pair
 (implies (consp point) (equal (cons (car point) (cdr point)) point))))

(local (defthm lw-rps-scale-inverse
 (implies (and (lw-complexp point) (rationalp factor) (not (equal factor 0)))
  (equal (lw-complex-scale (/ factor) (lw-complex-scale factor point)) point))
 :hints (("Goal"
  :use ((:instance lw-rps-inverse-factor (divisor factor) (coefficient (car point)))
        (:instance lw-rps-inverse-factor (divisor factor) (coefficient (cdr point))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-complexp lw-complex-scale lw-rps-pair lw-rps-left-commutes lw-rps-left-distributes lw-rps-fold-constants lw-rps-times-negative lw-rps-negative-times lw-rps-zero-times lw-rps-minus-one lw-rps-double-negative lw-rps-add-cancel lw-rps-double lw-rps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-rps-scale-compose
 (implies (and (lw-complexp point) (rationalp a) (rationalp b))
  (equal (lw-complex-scale a (lw-complex-scale b point))
         (lw-complex-scale (* a b) point)))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complexp lw-complex-scale lw-rps-left-commutes lw-rps-left-distributes lw-rps-fold-constants lw-rps-times-negative lw-rps-negative-times lw-rps-zero-times lw-rps-minus-one lw-rps-double-negative lw-rps-add-cancel lw-rps-double lw-rps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-rps-dot-positive-nonzero
 (implies (and (lw-complexp a) (lw-complexp b) (< 0 (lw-complex-dot a b)))
  (not (equal a (cons 0 0))))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-dot lw-rps-left-commutes lw-rps-left-distributes lw-rps-fold-constants lw-rps-times-negative lw-rps-negative-times lw-rps-zero-times lw-rps-minus-one lw-rps-double-negative lw-rps-add-cancel lw-rps-double lw-rps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-rps-positive-inverse
 (implies (and (rationalp x) (< 0 x)) (< 0 (/ x)))
 :hints (("Goal" :use ((:instance inverse-of-*))
          :in-theory (disable inverse-of-*) :nonlinearp t))
 :rule-classes nil))

(defthm lw-complex-same-ray-factor
 (implies (and (lw-complexp a) (lw-complexp b)
               (equal (lw-complex-det a b) 0) (< 0 (lw-complex-dot a b)))
  (let ((factor (* (lw-complex-dot a b) (/ (lw-complex-norm-square a)))))
   (and (rationalp factor) (< 0 factor) (equal (lw-complex-scale factor a) b))))
 :hints (("Goal"
  :use (lw-rps-det-dot-reconstruction lw-rps-dot-positive-nonzero
        (:instance lw-complex-norm-square-positive (point a))
        (:instance lw-complex-norm-square-valid (point a))
        (:instance lw-complex-orientation-rational)
        (:instance lw-rps-positive-inverse (x (lw-complex-norm-square a)))
        (:instance lw-rps-positive-product
          (a (lw-complex-dot a b)) (b (/ (lw-complex-norm-square a))))
        (:instance lw-rps-scale-inverse (point b) (factor (lw-complex-norm-square a)))
        (:instance lw-rps-scale-compose
          (point a) (a (/ (lw-complex-norm-square a))) (b (lw-complex-dot a b))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-rps-left-commutes lw-rps-left-distributes lw-rps-fold-constants lw-rps-times-negative lw-rps-negative-times lw-rps-zero-times lw-rps-minus-one lw-rps-double-negative lw-rps-add-cancel lw-rps-double lw-rps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-ray-crossing-same-ray-endpoint
 (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c)
               (equal (lw-complex-det a b) 0) (< 0 (lw-complex-dot a b)))
  (and (equal (lw-ray-crossing a c) (lw-ray-crossing b c))
       (equal (lw-ray-crossing c a) (lw-ray-crossing c b))))
 :hints (("Goal"
  :use (lw-complex-same-ray-factor
        (:instance lw-ray-crossing-positive-scales
          (s (* (lw-complex-dot a b) (/ (lw-complex-norm-square a))))
          (t0 1) (b c))
        (:instance lw-ray-crossing-positive-scales
          (a c) (b a) (s 1)
          (t0 (* (lw-complex-dot a b) (/ (lw-complex-norm-square a))))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-scale lw-complexp lw-rps-pair lw-rps-left-commutes lw-rps-left-distributes lw-rps-fold-constants lw-rps-times-negative lw-rps-negative-times lw-rps-zero-times lw-rps-minus-one lw-rps-double-negative lw-rps-add-cancel lw-rps-double lw-rps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

