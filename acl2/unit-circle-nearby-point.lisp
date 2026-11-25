(in-package "ACL2")

(include-book "unit-circle-charts")
(include-book "pole-resolvents")
(include-book "cauchy-orbits")
(include-book "complex-exp")

; The same rational chart formula also projects an interior point close
; to the circle. Its error is at most the defect of the squared norm.
(defun lw-unit-circle-nearby-point (point)
  (lw-complex-scale (lw-unit-circle-sign point)
    (lw-phase-rotation (lw-unit-circle-parameter point))))

(local (defthm lw-ucn-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ucn-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ucn-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ucn-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ucn-times-negative (a b) (b a)))
                 :in-theory (disable lw-ucn-times-negative)))))

(local (defthm lw-ucn-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ucn-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ucn-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ucn-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ucn-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ucn-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ucn-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ucn-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ucn-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ucn-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ucn-left-commutes)))))
(local
 (defthm lw-ucn-pair
   (implies (and (rationalp x) (rationalp y)) (lw-complexp (cons x y)))
   :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-complexp consp lw-ucn-left-commutes lw-ucn-left-distributes lw-ucn-fold-constants lw-ucn-times-negative lw-ucn-negative-times lw-ucn-zero-times lw-ucn-minus-one lw-ucn-double-negative lw-ucn-add-cancel lw-ucn-double lw-ucn-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local
 (defthm lw-ucn-cayley
   (implies (rationalp parameter)
            (equal (lw-phase-rotation parameter)
                   (lw-complex-mul (cons 2 parameter) (lw-complex-reciprocal (cons 2 (- parameter))))))
   :hints (("Goal" :in-theory
            (enable lw-phase-rotation lw-phase-denominator lw-complex-reciprocal
                    lw-complex-norm-square lw-complex-conjugate lw-complex-scale lw-complex-mul)))))

(local
 (defthm lw-ucn-cross-coordinates
   (implies (and (rationalp x) (rationalp y) (rationalp parameter) (<= 0 x)
                (equal (* (+ 1 x) parameter) (* 2 y))
                (<= (+ (* x x) (* y y)) 1))
            (equal (lw-complex-sub (cons 2 parameter) (lw-complex-mul (cons x y) (cons 2 (- parameter))))
                   (cons (- (- 2 (* 2 x)) (* parameter y)) 0)))
   :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-complex-mul lw-complex-sub cons-equal lw-ucn-left-commutes lw-ucn-left-distributes lw-ucn-fold-constants lw-ucn-times-negative lw-ucn-negative-times lw-ucn-zero-times lw-ucn-minus-one lw-ucn-double-negative lw-ucn-add-cancel lw-ucn-double lw-ucn-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
                   :do-not-induct t))))

(local
 (defthm lw-ucn-equality-times
   (implies (equal a b) (equal (* a factor) (* b factor)))
   :rule-classes nil))

(local
 (defthm lw-ucn-cross-identity
   (implies (and (rationalp x) (rationalp y) (rationalp parameter)
                 (equal (* (+ 1 x) parameter) (* 2 y)))
            (equal (* (+ 1 x) (- (- 2 (* 2 x)) (* parameter y)))
                   (* 2 (- 1 (+ (* x x) (* y y))))))
   :hints (("Goal"
            :use ((:instance lw-ucn-equality-times
                    (a (* (+ 1 x) parameter)) (b (* 2 y)) (factor y)))
            :in-theory (union-theories
 '(fold-consts-in-+ consp lw-ucn-left-commutes lw-ucn-left-distributes lw-ucn-fold-constants lw-ucn-times-negative lw-ucn-negative-times lw-ucn-zero-times lw-ucn-minus-one lw-ucn-double-negative lw-ucn-add-cancel lw-ucn-double lw-ucn-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-ucn-remove-positive-factor
   (implies (and (rationalp x) (<= 0 x) (rationalp value) (rationalp cap)
                 (<= 0 cap) (equal (* (+ 1 x) value) cap))
            (and (<= 0 value) (<= value cap)))
   :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ consp lw-ucn-left-commutes lw-ucn-left-distributes lw-ucn-fold-constants lw-ucn-times-negative lw-ucn-negative-times lw-ucn-zero-times lw-ucn-minus-one lw-ucn-double-negative lw-ucn-add-cancel lw-ucn-double lw-ucn-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :nonlinearp t :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-ucn-cross-bound
   (implies (and (rationalp x) (rationalp y) (rationalp parameter) (<= 0 x)
                (equal (* (+ 1 x) parameter) (* 2 y))
                (<= (+ (* x x) (* y y)) 1))
            (and (<= 0 (- (- 2 (* 2 x)) (* parameter y))) (<= (- (- 2 (* 2 x)) (* parameter y)) (* 2 (- 1 (+ (* x x) (* y y)))))))
   :hints (("Goal"
            :use (lw-ucn-cross-identity
                  (:instance lw-ucn-remove-positive-factor
                    (value (- (- 2 (* 2 x)) (* parameter y)))
                    (cap (* 2 (- 1 (+ (* x x) (* y y)))))))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) consp lw-ucn-left-commutes lw-ucn-left-distributes lw-ucn-fold-constants lw-ucn-times-negative lw-ucn-negative-times lw-ucn-zero-times lw-ucn-minus-one lw-ucn-double-negative lw-ucn-add-cancel lw-ucn-double lw-ucn-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-ucn-real-disk
   (implies (and (rationalp x) (rationalp cap) (<= 0 x) (<= x cap))
            (lw-complex-diskp (cons x 0) cap))
   :hints (("Goal"
            :use ((:instance lw-complex-disk-norm-square (point (cons x 0)) (radius cap)))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-ucn-pair lw-complex-norm-square lw-ucn-left-commutes lw-ucn-left-distributes lw-ucn-fold-constants lw-ucn-times-negative lw-ucn-negative-times lw-ucn-zero-times lw-ucn-minus-one lw-ucn-double-negative lw-ucn-add-cancel lw-ucn-double lw-ucn-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :nonlinearp t :do-not-induct t))))

(local
 (defthm lw-ucn-cayley-denominator
   (implies (rationalp parameter)
            (and (not (equal (cons 2 (- parameter)) (cons 0 0)))
                 (lw-complex-diskp (lw-complex-reciprocal (cons 2 (- parameter))) 1/2)))
   :hints (("Goal"
            :cases ((< parameter 0))
            :use ((:instance lw-complex-reciprocal-disk-bound (point (cons 2 (- parameter))) (lower 2))
                  (:instance lw-ucn-multiply-order (a 0) (b parameter) (factor parameter))
                  (:instance lw-ucn-multiply-order (a 0) (b (- parameter)) (factor (- parameter))))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-ucn-pair lw-complex-norm-square cons-equal lw-ucn-left-commutes lw-ucn-left-distributes lw-ucn-fold-constants lw-ucn-times-negative lw-ucn-negative-times lw-ucn-zero-times lw-ucn-minus-one lw-ucn-double-negative lw-ucn-add-cancel lw-ucn-double lw-ucn-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :nonlinearp t :do-not-induct t))))

(local
 (defthm lw-ucn-cayley-difference
   (implies (and (lw-complexp point) (lw-complexp numerator) (lw-complexp denominator)
                 (not (equal denominator (cons 0 0))))
            (equal (lw-complex-sub (lw-complex-mul numerator (lw-complex-reciprocal denominator)) point)
                   (lw-complex-mul (lw-complex-sub numerator (lw-complex-mul point denominator))
                                   (lw-complex-reciprocal denominator))))
   :hints (("Goal"
            :use ((:instance lw-complex-sub-products-right
                    (a numerator) (b (lw-complex-mul point denominator)) (weight (lw-complex-reciprocal denominator)))
                  (:instance lw-complex-reciprocal-inverse (point denominator)))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-complex-mul-associative lw-complex-mul-one lw-complex-ring-rational lw-complex-reciprocal-rational lw-ucn-left-commutes lw-ucn-left-distributes lw-ucn-fold-constants lw-ucn-times-negative lw-ucn-negative-times lw-ucn-zero-times lw-ucn-minus-one lw-ucn-double-negative lw-ucn-add-cancel lw-ucn-double lw-ucn-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))))

(local
 (defthm lw-ucn-half-disk
   (implies (and (rationalp x) (rationalp y) (rationalp parameter) (<= 0 x)
                (equal (* (+ 1 x) parameter) (* 2 y))
                (<= (+ (* x x) (* y y)) 1))
            (lw-complex-diskp (lw-complex-sub (lw-phase-rotation parameter) (cons x y)) (- 1 (+ (* x x) (* y y)))))
   :hints (("Goal"
            :use (lw-ucn-cross-bound
                  (:instance lw-complex-mul-disk
                    (left (cons (- (- 2 (* 2 x)) (* parameter y)) 0)) (radius (* 2 (- 1 (+ (* x x) (* y y)))))
                    (right (lw-complex-reciprocal (cons 2 (- parameter)))) (other-radius 1/2)))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-ucn-pair lw-ucn-cayley lw-ucn-cayley-denominator lw-ucn-cayley-difference lw-ucn-cross-coordinates lw-ucn-real-disk lw-complex-reciprocal-rational lw-ucn-left-commutes lw-ucn-left-distributes lw-ucn-fold-constants lw-ucn-times-negative lw-ucn-negative-times lw-ucn-zero-times lw-ucn-minus-one lw-ucn-double-negative lw-ucn-add-cancel lw-ucn-double lw-ucn-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))))

(local
 (defthm lw-ucn-parameter-identity
   (implies (and (rationalp x) (<= 0 x) (rationalp y))
            (equal (* (+ 1 x) (* 2 y (/ (+ 1 x)))) (* 2 y)))
   :hints (("Goal" :use ((:instance lw-ucn-inverse-factor (divisor (+ 1 x)) (coefficient (* 2 y))))
                   :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) consp lw-ucn-left-commutes lw-ucn-left-distributes lw-ucn-fold-constants lw-ucn-times-negative lw-ucn-negative-times lw-ucn-zero-times lw-ucn-minus-one lw-ucn-double-negative lw-ucn-add-cancel lw-ucn-double lw-ucn-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
                   :do-not-induct t))))

(local
 (defthm lw-ucn-negative-point
   (implies (and (rationalp x) (rationalp y))
            (equal (lw-complex-scale -1 (cons x y)) (cons (- x) (- y))))
   :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-complex-scale lw-ucn-left-commutes lw-ucn-left-distributes lw-ucn-fold-constants lw-ucn-times-negative lw-ucn-negative-times lw-ucn-zero-times lw-ucn-minus-one lw-ucn-double-negative lw-ucn-add-cancel lw-ucn-double lw-ucn-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local
 (defthm lw-ucn-scale-sign-norm
   (implies (and (lw-complexp point) (or (equal sign 1) (equal sign -1)))
            (equal (lw-complex-norm-square (lw-complex-scale sign point))
                   (lw-complex-norm-square point)))
   :hints (("Goal" :cases ((equal sign 1))
                   :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-complexp lw-complex-norm-square lw-complex-scale consp lw-ucn-left-commutes lw-ucn-left-distributes lw-ucn-fold-constants lw-ucn-times-negative lw-ucn-negative-times lw-ucn-zero-times lw-ucn-minus-one lw-ucn-double-negative lw-ucn-add-cancel lw-ucn-double lw-ucn-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local
 (defthm lw-ucn-negate-difference
   (implies (and (lw-complexp point) (lw-complexp value))
            (equal
             (lw-complex-scale -1 (lw-complex-sub value (cons (- (car point)) (- (cdr point)))))
             (lw-complex-sub (lw-complex-scale -1 value) point)))
   :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complexp lw-complex-sub lw-complex-scale consp lw-ucn-left-commutes lw-ucn-left-distributes lw-ucn-fold-constants lw-ucn-times-negative lw-ucn-negative-times lw-ucn-zero-times lw-ucn-minus-one lw-ucn-double-negative lw-ucn-add-cancel lw-ucn-double lw-ucn-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local
 (defthm lw-ucn-coordinate-data
   (implies (lw-complexp point)
            (and (rationalp (car point)) (rationalp (cdr point))
                 (equal (lw-complex-norm-square point) (+ (* (car point) (car point)) (* (cdr point) (cdr point))))))
   :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complexp lw-complex-norm-square consp lw-ucn-left-commutes lw-ucn-left-distributes lw-ucn-fold-constants lw-ucn-times-negative lw-ucn-negative-times lw-ucn-zero-times lw-ucn-minus-one lw-ucn-double-negative lw-ucn-add-cancel lw-ucn-double lw-ucn-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))
   :rule-classes nil))

(defthm lw-unit-circle-nearby-point-data
  (implies (lw-complex-diskp point 1)
           (and (lw-complexp (lw-unit-circle-nearby-point point))
                (equal (lw-complex-norm-square (lw-unit-circle-nearby-point point)) 1)
                (lw-complex-diskp (lw-complex-sub (lw-unit-circle-nearby-point point) point)
                  (- 1 (lw-complex-norm-square point)))))
  :hints (("Goal"
           :cases ((< (car point) 0))
           :use (lw-ucn-coordinate-data
                 (:instance lw-complex-disk-norm-square (radius 1))
                 (:instance lw-ucn-half-disk (x (car point)) (y (cdr point))
                   (parameter (* 2 (cdr point) (/ (+ 1 (car point))))))
                 (:instance lw-ucn-half-disk (x (- (car point))) (y (- (cdr point)))
                   (parameter (* 2 (- (cdr point)) (/ (+ 1 (- (car point)))))))
                 (:instance lw-complex-scale-disk (factor -1)
                   (point (lw-complex-sub
                     (lw-phase-rotation (* 2 (- (cdr point)) (/ (+ 1 (- (car point))))))
                     (cons (- (car point)) (- (cdr point)))))
                   (radius (- 1 (lw-complex-norm-square point)))))
           :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-unit-circle-nearby-point lw-unit-circle-sign lw-unit-circle-parameter lw-phase-rotation-rational lw-cayley-norm-square-one lw-ucn-negate-difference abs lw-complex-scale-one lw-ucn-scale-sign-norm lw-ucn-negative-point lw-ucn-parameter-identity lw-complex-scale-rational lw-complex-sub-scales lw-complex-ring-rational cons-car-cdr consp lw-ucn-left-commutes lw-ucn-left-distributes lw-ucn-fold-constants lw-ucn-times-negative lw-ucn-negative-times lw-ucn-zero-times lw-ucn-minus-one lw-ucn-double-negative lw-ucn-add-cancel lw-ucn-double lw-ucn-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm lw-ucn-square-scale
   (implies (and (lw-complexp point) (rationalp factor))
            (equal (lw-complex-norm-square (lw-complex-scale factor point))
                   (* factor factor (lw-complex-norm-square point))))
   :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-complexp lw-complex-norm-square lw-complex-scale consp lw-ucn-left-commutes lw-ucn-left-distributes lw-ucn-fold-constants lw-ucn-times-negative lw-ucn-negative-times lw-ucn-zero-times lw-ucn-minus-one lw-ucn-double-negative lw-ucn-add-cancel lw-ucn-double lw-ucn-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
                   :do-not-induct t))))

(local
 (defthm lw-ucn-cancel-scaled-defect
   (implies (and (rationalp radius) (< 0 radius) (rationalp norm))
            (equal (* radius (- 1 (* (/ radius) (/ radius) norm)))
                   (- radius (* (/ radius) norm))))
   :hints (("Goal"
            :use ((:instance lw-ucn-inverse-factor (divisor radius) (coefficient (* (/ radius) norm))))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) consp lw-ucn-left-commutes lw-ucn-left-distributes lw-ucn-fold-constants lw-ucn-times-negative lw-ucn-negative-times lw-ucn-zero-times lw-ucn-minus-one lw-ucn-double-negative lw-ucn-add-cancel lw-ucn-double lw-ucn-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))))

(local
 (defthm lw-ucn-scale-inverse
   (implies (and (lw-complexp point) (rationalp radius) (< 0 radius))
            (equal (lw-complex-scale radius (lw-complex-scale (/ radius) point)) point))
   :hints (("Goal"
            :use ((:instance inverse-of-* (x radius)))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-complex-scale-compose lw-complex-scale-one lw-ucn-left-commutes lw-ucn-left-distributes lw-ucn-fold-constants lw-ucn-times-negative lw-ucn-negative-times lw-ucn-zero-times lw-ucn-minus-one lw-ucn-double-negative lw-ucn-add-cancel lw-ucn-double lw-ucn-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))))

(local
 (defthm lw-ucn-radius-inverse
   (implies (and (rationalp radius) (< 0 radius))
            (and (equal (* radius (/ radius)) 1)
                 (equal (* (/ radius) radius) 1)))
   :hints (("Goal" :use ((:instance inverse-of-* (x radius)))
                   :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) consp lw-ucn-left-commutes lw-ucn-left-distributes lw-ucn-fold-constants lw-ucn-times-negative lw-ucn-negative-times lw-ucn-zero-times lw-ucn-minus-one lw-ucn-double-negative lw-ucn-add-cancel lw-ucn-double lw-ucn-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defun lw-circle-nearby-unit-point (point radius)
  (lw-unit-circle-nearby-point (lw-complex-scale (/ radius) point)))

(defthm lw-circle-nearby-unit-point-data
  (implies (and (lw-complex-diskp point radius) (< 0 radius))
           (and (lw-complexp (lw-circle-nearby-unit-point point radius))
                (equal (lw-complex-norm-square (lw-circle-nearby-unit-point point radius)) 1)
                (lw-complex-diskp
                 (lw-complex-sub (lw-complex-scale radius (lw-circle-nearby-unit-point point radius)) point)
                 (- radius (* (/ radius) (lw-complex-norm-square point))))))
  :hints (("Goal"
           :use ((:instance lw-complex-disk-data)
                 (:instance lw-complex-scale-disk (factor (/ radius)))
                 (:instance lw-unit-circle-nearby-point-data (point (lw-complex-scale (/ radius) point)))
                 (:instance lw-complex-scale-disk
                   (factor radius) (point (lw-complex-sub (lw-unit-circle-nearby-point (lw-complex-scale (/ radius) point)) (lw-complex-scale (/ radius) point))) (radius (- 1 (lw-complex-norm-square (lw-complex-scale (/ radius) point)))))
                 (:instance lw-complex-sub-scales (factor radius) (a (lw-unit-circle-nearby-point (lw-complex-scale (/ radius) point))) (b (lw-complex-scale (/ radius) point)))
                 (:instance lw-ucn-cancel-scaled-defect (norm (lw-complex-norm-square point))))
           :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-circle-nearby-unit-point lw-ucn-radius-inverse lw-ucn-scale-inverse lw-ucn-square-scale lw-reciprocal-positive lw-complex-scale-rational lw-complex-norm-square-valid abs lw-ucn-left-commutes lw-ucn-left-distributes lw-ucn-fold-constants lw-ucn-times-negative lw-ucn-negative-times lw-ucn-zero-times lw-ucn-minus-one lw-ucn-double-negative lw-ucn-add-cancel lw-ucn-double lw-ucn-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
