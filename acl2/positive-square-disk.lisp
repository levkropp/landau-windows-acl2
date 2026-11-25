; A computed disk inside Re(s)>0 encloses any positive rational square.
(in-package "ACL2")
(include-book "square-cells")
(local (in-theory (disable lw-complexp lw-complex-sub lw-complex-add lw-complex-mul
 lw-complex-diskp lw-complex-norm-square lw-square-containsp)))
(local (defthm lw-psd-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-psd-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-psd-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-psd-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-psd-times-negative (a b) (b a)))
                 :in-theory (disable lw-psd-times-negative)))))

(local (defthm lw-psd-zero-times (equal (* 0 a) 0)))

(local (defthm lw-psd-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-psd-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-psd-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-psd-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-psd-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-psd-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-psd-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-psd-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-psd-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-psd-left-commutes)))))
(defun lw-positive-squarep (anchor side)
 (and (lw-complexp anchor) (< 0 (car anchor)) (rationalp side) (< 0 side)))
(defun lw-positive-square-center-rate (anchor side)
 (+ (car anchor) side 1 (* side side (/ (car anchor)))))
(defun lw-positive-square-center-height (anchor side) (+ (cdr anchor) (/ side 2)))
(defun lw-positive-square-disk-radius (anchor side)
 (- (lw-positive-square-center-rate anchor side) (/ (car anchor) 2)))
(defun lw-positive-square-center (anchor side)
 (cons (lw-positive-square-center-rate anchor side) (lw-positive-square-center-height anchor side)))
(defun lw-positive-square-offset (anchor side point)
 (lw-complex-sub point (lw-positive-square-center anchor side)))
(defun lw-positive-square-translation (anchor side)
 (cons (- (lw-positive-square-center-rate anchor side)) (- (lw-positive-square-center-height anchor side))))
(local (in-theory (disable lw-positive-squarep lw-positive-square-center-rate lw-positive-square-center-height
 lw-positive-square-disk-radius lw-positive-square-center lw-positive-square-offset lw-positive-square-translation)))

(local (defthm lw-psd-center-data
 (implies (lw-positive-squarep anchor side)
 (let ((rate (lw-positive-square-center-rate anchor side)) (x (car anchor)))
 (and (rationalp rate) (< 0 rate) (<= (+ x side) rate)
      (<= (+ (* x x) (* side side)) (* rate x)))))
 :hints (("Goal"
 :use ((:instance lw-reciprocal-positive (value (car anchor)))
       (:instance lw-psd-positive-product (a side) (b side))
       (:instance lw-psd-positive-product (a (* side side)) (b (/ (car anchor))))
       (:instance lw-psd-inverse-factor (divisor (car anchor)) (coefficient (* side side))))
 :in-theory (union-theories
 '(lw-positive-squarep lw-positive-square-center-rate lw-complexp lw-psd-inverse-factor lw-psd-left-commutes lw-psd-left-distributes lw-psd-fold-constants lw-psd-times-negative lw-psd-negative-times lw-psd-zero-times lw-psd-minus-one lw-psd-double-negative lw-psd-add-cancel lw-psd-double lw-psd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp t :do-not-induct t)) :rule-classes nil))

(local (defthm lw-psd-radius-budget
 (implies (and (rationalp rate) (rationalp x) (< 0 x) (rationalp side) (< 0 side)
 (<= (+ x side) rate) (<= (+ (* x x) (* side side)) (* rate x)))
 (let ((radius (- rate (/ x 2))))
 (and (< 0 radius) (< radius rate)
      (<= (+ (* (- rate x) (- rate x)) (* 1/4 side side)) (* radius radius)))))
 :hints (("Goal" :in-theory (union-theories
 '( lw-psd-left-commutes lw-psd-left-distributes lw-psd-fold-constants lw-psd-times-negative lw-psd-negative-times lw-psd-zero-times lw-psd-minus-one lw-psd-double-negative lw-psd-add-cancel lw-psd-double lw-psd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :nonlinearp t)) :rule-classes nil))

(defthm lw-positive-square-disk-data
 (implies (lw-positive-squarep anchor side)
 (let ((rate (lw-positive-square-center-rate anchor side))
       (height (lw-positive-square-center-height anchor side))
       (radius (lw-positive-square-disk-radius anchor side)))
 (and (rationalp rate) (< 0 rate) (rationalp height)
      (rationalp radius) (< 0 radius) (< radius rate)
      (<= (+ (car anchor) side) rate)
      (<= (+ (* (- rate (car anchor)) (- rate (car anchor))) (* 1/4 side side)) (* radius radius)))))
 :hints (("Goal"
 :use (lw-psd-center-data
       (:instance lw-psd-radius-budget (rate (lw-positive-square-center-rate anchor side)) (x (car anchor))))
 :in-theory (union-theories
 '(lw-positive-squarep lw-positive-square-center-height lw-positive-square-disk-radius lw-complexp lw-psd-left-commutes lw-psd-left-distributes lw-psd-fold-constants lw-psd-times-negative lw-psd-negative-times lw-psd-zero-times lw-psd-minus-one lw-psd-double-negative lw-psd-add-cancel lw-psd-double lw-psd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(local (defthm lw-psd-square-interval
 (implies (and (rationalp value) (rationalp cap) (<= 0 cap) (<= (- cap) value) (<= value cap))
 (<= (* value value) (* cap cap)))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defthm lw-positive-square-offset-in-disk
 (implies (and (lw-positive-squarep anchor side) (lw-square-containsp anchor side point))
 (lw-complex-diskp (lw-positive-square-offset anchor side point) (lw-positive-square-disk-radius anchor side)))
 :hints (("Goal"
 :use (lw-positive-square-disk-data
       (:instance lw-psd-square-interval
        (value (- (car point) (lw-positive-square-center-rate anchor side)))
        (cap (- (lw-positive-square-center-rate anchor side) (car anchor))))
       (:instance lw-psd-square-interval
        (value (- (cdr point) (lw-positive-square-center-height anchor side))) (cap (/ side 2)))
       (:instance lw-complex-disk-norm-square
        (point (lw-positive-square-offset anchor side point)) (radius (lw-positive-square-disk-radius anchor side))))
 :in-theory (union-theories
 '(lw-positive-squarep lw-square-containsp lw-positive-square-offset lw-positive-square-center lw-positive-square-center-height lw-complexp lw-complex-sub lw-complex-norm-square lw-psd-left-commutes lw-psd-left-distributes lw-psd-fold-constants lw-psd-times-negative lw-psd-negative-times lw-psd-zero-times lw-psd-minus-one lw-psd-double-negative lw-psd-add-cancel lw-psd-double lw-psd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-positive-square-point-data
 (implies (and (lw-positive-squarep anchor side) (lw-square-containsp anchor side point))
 (and (lw-complexp point) (< 0 (car point))))
 :hints (("Goal" :in-theory (union-theories
 '(lw-positive-squarep lw-square-containsp lw-psd-left-commutes lw-psd-left-distributes lw-psd-fold-constants lw-psd-times-negative lw-psd-negative-times lw-psd-zero-times lw-psd-minus-one lw-psd-double-negative lw-psd-add-cancel lw-psd-double lw-psd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-positive-square-coordinate-recovery
 (implies (and (lw-positive-squarep anchor side) (lw-complexp point))
 (let ((offset (lw-positive-square-offset anchor side point)))
 (and (lw-complexp (lw-positive-square-center anchor side))
      (lw-complexp (lw-positive-square-translation anchor side))
      (lw-complexp offset)
      (equal (+ (lw-positive-square-center-rate anchor side) (car offset)) (car point))
      (equal (+ (lw-positive-square-center-height anchor side) (cdr offset)) (cdr point)))))
 :hints (("Goal" :use lw-positive-square-disk-data
 :in-theory (union-theories
 '(lw-positive-square-offset lw-positive-square-center lw-positive-square-translation lw-complex-sub lw-complexp lw-psd-left-commutes lw-psd-left-distributes lw-psd-fold-constants lw-psd-times-negative lw-psd-negative-times lw-psd-zero-times lw-psd-minus-one lw-psd-double-negative lw-psd-add-cancel lw-psd-double lw-psd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-positive-square-affine-point
 (implies (and (lw-positive-squarep anchor side) (lw-complexp point))
 (equal (lw-complex-add (lw-positive-square-translation anchor side) (lw-complex-mul (cons 1 0) point))
        (lw-positive-square-offset anchor side point)))
 :hints (("Goal" :use lw-positive-square-disk-data
 :in-theory (union-theories
 '(lw-positive-square-offset lw-positive-square-center lw-positive-square-translation lw-complex-add lw-complex-mul lw-complex-sub lw-complexp lw-psd-left-commutes lw-psd-left-distributes lw-psd-fold-constants lw-psd-times-negative lw-psd-negative-times lw-psd-zero-times lw-psd-minus-one lw-psd-double-negative lw-psd-add-cancel lw-psd-double lw-psd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
