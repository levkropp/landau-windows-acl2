(in-package "ACL2")

(include-book "polygon-product-index")
(include-book "complex-exp-multiply")

; Rational global annulus and step budgets generate every half-plane
; check needed for multiplicative winding, including the product diagonal.

(local (defthm lw-ppb2-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ppb2-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ppb2-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ppb2-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ppb2-times-negative (a b) (b a)))
                 :in-theory (disable lw-ppb2-times-negative)))))

(local (defthm lw-ppb2-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ppb2-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ppb2-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ppb2-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ppb2-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ppb2-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ppb2-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ppb2-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ppb2-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ppb2-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ppb2-left-commutes)))))

(defun lw-ray-annulus-pointsp (points lower upper)
 (if (endp points) (equal points nil)
  (and (lw-complex-diskp (car points) upper)
       (<= (* lower lower) (lw-complex-norm-square (car points)))
       (lw-ray-annulus-pointsp (cdr points) lower upper))))

(defun lw-ray-path-step-check (points delta)
 (if (or (endp points) (endp (cdr points))) t
  (and (lw-complex-diskp (lw-complex-sub (cadr points) (car points)) delta)
       (lw-ray-path-step-check (cdr points) delta))))

(defun lw-ray-product-step-budget (lower-left upper-left lower-right upper-right)
 (* 1/4 lower-left lower-right (/ (+ 1 upper-left upper-right))))

(local (defthm lw-ppb2-square-gap
 (implies (and (rationalp x) (<= 0 x) (rationalp y) (< x y))
          (< (* x x) (* y y)))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ppb2-inverse-positive
 (implies (and (rationalp x) (< 0 x)) (< 0 (/ x)))
 :hints (("Goal" :use ((:instance inverse-of-*))
          :in-theory (disable inverse-of-*) :nonlinearp t)) :rule-classes nil))

(defthm lw-ray-product-step-budget-valid
 (implies (and (rationalp lower-left) (< 0 lower-left)
               (rationalp lower-right) (< 0 lower-right)
               (rationalp upper-left) (<= 0 upper-left)
               (rationalp upper-right) (<= 0 upper-right))
  (let ((delta (lw-ray-product-step-budget lower-left upper-left lower-right upper-right)))
   (and (rationalp delta) (< 0 delta)
        (< (+ (* delta upper-left) (* delta upper-right)) (* lower-left lower-right)))))
 :hints (("Goal"
  :use ((:instance lw-ppb2-inverse-positive (x (+ 1 upper-left upper-right)))
        (:instance lw-ppb2-positive-product (a lower-left) (b lower-right))
        (:instance lw-ppb2-positive-product
          (a (* 1/4 lower-left lower-right)) (b (/ (+ 1 upper-left upper-right))))
        (:instance lw-ppb2-inverse-factor
          (divisor (+ 1 upper-left upper-right)) (coefficient (* 1/4 lower-left lower-right))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-product-step-budget lw-ppb2-left-commutes lw-ppb2-left-distributes lw-ppb2-fold-constants lw-ppb2-times-negative lw-ppb2-negative-times lw-ppb2-zero-times lw-ppb2-minus-one lw-ppb2-double-negative lw-ppb2-add-cancel lw-ppb2-double lw-ppb2-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :nonlinearp t)))

(defthm lw-ray-annulus-data
 (implies (lw-ray-annulus-pointsp points lower upper) (lw-ray-pointsp points))
 :hints (("Goal" :induct (lw-ray-annulus-pointsp points lower upper)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-annulus-pointsp lw-ray-pointsp lw-complex-disk-data lw-ppb2-left-commutes lw-ppb2-left-distributes lw-ppb2-fold-constants lw-ppb2-times-negative lw-ppb2-negative-times lw-ppb2-zero-times lw-ppb2-minus-one lw-ppb2-double-negative lw-ppb2-add-cancel lw-ppb2-double lw-ppb2-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-ray-annulus-first
 (implies (and (consp points) (lw-ray-annulus-pointsp points lower upper))
  (and (lw-complex-diskp (car points) upper)
       (lw-complexp (car points))
       (<= (* lower lower) (lw-complex-norm-square (car points)))
       (lw-ray-annulus-pointsp (cdr points) lower upper)))
 :hints (("Goal" :expand ((lw-ray-annulus-pointsp points lower upper))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-disk-data lw-ppb2-left-commutes lw-ppb2-left-distributes lw-ppb2-fold-constants lw-ppb2-times-negative lw-ppb2-negative-times lw-ppb2-zero-times lw-ppb2-minus-one lw-ppb2-double-negative lw-ppb2-add-cancel lw-ppb2-double lw-ppb2-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-ppb2-product-norm-lower
 (implies (and (lw-complexp a) (lw-complexp b)
               (rationalp lower-left) (< 0 lower-left)
               (rationalp lower-right) (< 0 lower-right)
               (<= (* lower-left lower-left) (lw-complex-norm-square a))
               (<= (* lower-right lower-right) (lw-complex-norm-square b)))
  (<= (* lower-left lower-right lower-left lower-right)
      (lw-complex-norm-square (lw-complex-mul a b))))
 :hints (("Goal"
  :use ((:instance lw-complex-norm-square-valid (point a))
        (:instance lw-complex-norm-square-valid (point b))
        (:instance lw-ppb2-multiply-order
          (a (* lower-left lower-left)) (b (lw-complex-norm-square a))
          (factor (lw-complex-norm-square b)))
        (:instance lw-ppb2-multiply-order
          (a (* lower-right lower-right)) (b (lw-complex-norm-square b))
          (factor (* lower-left lower-left))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-norm-square-product lw-ppb2-left-commutes lw-ppb2-left-distributes lw-ppb2-fold-constants lw-ppb2-times-negative lw-ppb2-negative-times lw-ppb2-zero-times lw-ppb2-minus-one lw-ppb2-double-negative lw-ppb2-add-cancel lw-ppb2-double lw-ppb2-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ppb2-product-near-halfplane
 (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c) (lw-complexp d)
               (lw-complex-diskp b right-cap) (lw-complex-diskp c left-cap)
               (lw-complex-diskp (lw-complex-sub a c) left-error)
               (lw-complex-diskp (lw-complex-sub b d) right-error)
               (rationalp radius)
               (equal radius (+ (* right-cap left-error) (* left-cap right-error)))
               (< (* radius radius) (lw-complex-norm-square (lw-complex-mul c d))))
  (lw-complex-positive-halfplanep (lw-complex-mul c d) (lw-complex-mul a b)))
 :hints (("Goal"
  :use (lw-complex-mul-difference-bound
        (:instance lw-complex-disk-positive-halfplane
          (anchor (lw-complex-mul c d)) (point (lw-complex-mul a b))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-ring-rational lw-ppb2-left-commutes lw-ppb2-left-distributes lw-ppb2-fold-constants lw-ppb2-times-negative lw-ppb2-negative-times lw-ppb2-zero-times lw-ppb2-minus-one lw-ppb2-double-negative lw-ppb2-add-cancel lw-ppb2-double lw-ppb2-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))) :rule-classes nil))

(local (defthm lw-ppb2-self-difference
 (implies (and (lw-complexp point) (rationalp delta) (<= 0 delta))
          (lw-complex-diskp (lw-complex-sub point point) delta))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complexp lw-complex-sub lw-complex-diskp lw-diskp lw-ppb2-left-commutes lw-ppb2-left-distributes lw-ppb2-fold-constants lw-ppb2-times-negative lw-ppb2-negative-times lw-ppb2-zero-times lw-ppb2-minus-one lw-ppb2-double-negative lw-ppb2-add-cancel lw-ppb2-double lw-ppb2-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-ray-product-cell-from-budgets
 (implies (and (lw-complexp a0) (lw-complexp a1) (lw-complexp b0) (lw-complexp b1)
               (rationalp lower-left) (< 0 lower-left) (rationalp lower-right) (< 0 lower-right)
               (rationalp upper-left) (<= 0 upper-left) (rationalp upper-right) (<= 0 upper-right)
               (rationalp delta) (<= 0 delta)
               (lw-complex-diskp a0 upper-left) (lw-complex-diskp a1 upper-left)
               (lw-complex-diskp b0 upper-right) (lw-complex-diskp b1 upper-right)
               (<= (* lower-left lower-left) (lw-complex-norm-square a0))
               (<= (* lower-right lower-right) (lw-complex-norm-square b0))
               (lw-complex-diskp (lw-complex-sub a1 a0) delta)
               (lw-complex-diskp (lw-complex-sub b1 b0) delta)
               (< (+ (* delta upper-left) (* delta upper-right)) (* lower-left lower-right)))
  (let ((anchor (lw-complex-mul b0 a0)))
   (and (lw-complex-positive-halfplanep anchor anchor)
        (lw-complex-positive-halfplanep anchor (lw-complex-mul b0 a1))
        (lw-complex-positive-halfplanep anchor (lw-complex-mul b1 a1))
        (lw-complex-positive-halfplanep anchor (lw-complex-mul b1 a0)))))
 :hints (("Goal"
  :use ((:instance lw-ppb2-product-norm-lower (a b0) (b a0)
          (lower-left lower-right) (lower-right lower-left))
        (:instance lw-ppb2-square-gap
          (x (+ (* delta upper-left) (* delta upper-right))) (y (* lower-left lower-right)))
        (:instance lw-ppb2-product-near-halfplane (a b0) (b a0) (c b0) (d a0)
          (left-cap upper-right) (right-cap upper-left) (left-error delta) (right-error delta)
          (radius (+ (* delta upper-left) (* delta upper-right))))
        (:instance lw-ppb2-product-near-halfplane (a b0) (b a1) (c b0) (d a0)
          (left-cap upper-right) (right-cap upper-left) (left-error delta) (right-error delta)
          (radius (+ (* delta upper-left) (* delta upper-right))))
        (:instance lw-ppb2-product-near-halfplane (a b1) (b a1) (c b0) (d a0)
          (left-cap upper-right) (right-cap upper-left) (left-error delta) (right-error delta)
          (radius (+ (* delta upper-left) (* delta upper-right))))
        (:instance lw-ppb2-product-near-halfplane (a b1) (b a0) (c b0) (d a0)
          (left-cap upper-right) (right-cap upper-left) (left-error delta) (right-error delta)
          (radius (+ (* delta upper-left) (* delta upper-right)))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-ppb2-self-difference lw-ppb2-left-commutes lw-ppb2-left-distributes lw-ppb2-fold-constants lw-ppb2-times-negative lw-ppb2-negative-times lw-ppb2-zero-times lw-ppb2-minus-one lw-ppb2-double-negative lw-ppb2-add-cancel lw-ppb2-double lw-ppb2-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :nonlinearp t :do-not-induct t)))

(defthm lw-ray-product-strip-from-budgets
 (implies (and (lw-ray-annulus-pointsp points lower-left upper-left)
               (lw-complex-diskp bottom upper-right) (lw-complex-diskp top upper-right)
               (<= (* lower-right lower-right) (lw-complex-norm-square bottom))
               (rationalp lower-left) (< 0 lower-left) (rationalp lower-right) (< 0 lower-right)
               (rationalp upper-left) (<= 0 upper-left) (rationalp upper-right) (<= 0 upper-right)
               (rationalp delta) (<= 0 delta) (lw-ray-path-step-check points delta)
               (lw-complex-diskp (lw-complex-sub top bottom) delta)
               (< (+ (* delta upper-left) (* delta upper-right)) (* lower-left lower-right)))
  (lw-ray-product-strip-check points bottom top))
 :hints (("Goal" :induct (lw-ray-path-step-check points delta)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-product-strip-check lw-ray-path-step-check lw-ray-annulus-pointsp lw-ray-annulus-first lw-complex-disk-data lw-ppb2-left-commutes lw-ppb2-left-distributes lw-ppb2-fold-constants lw-ppb2-times-negative lw-ppb2-negative-times lw-ppb2-zero-times lw-ppb2-minus-one lw-ppb2-double-negative lw-ppb2-add-cancel lw-ppb2-double lw-ppb2-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) )
         (and stable-under-simplificationp
          '(:use ((:instance lw-ray-product-cell-from-budgets
                    (a0 (car points)) (a1 (cadr points)) (b0 bottom) (b1 top)))
            :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-annulus-first lw-complex-disk-data lw-ppb2-left-commutes lw-ppb2-left-distributes lw-ppb2-fold-constants lw-ppb2-times-negative lw-ppb2-negative-times lw-ppb2-zero-times lw-ppb2-minus-one lw-ppb2-double-negative lw-ppb2-add-cancel lw-ppb2-double lw-ppb2-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

