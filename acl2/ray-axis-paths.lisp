(in-package "ACL2")

(include-book "ray-axis-crossings")

; Axis-aligned path sums telescope to their endpoint potentials.

(local (defthm lw-rap-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-rap-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-rap-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-rap-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-rap-times-negative (a b) (b a)))
                 :in-theory (disable lw-rap-times-negative)))))

(local (defthm lw-rap-zero-times (equal (* 0 a) 0)))

(local (defthm lw-rap-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-rap-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-rap-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-rap-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-rap-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-rap-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-rap-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-rap-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-rap-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-rap-left-commutes)))))
(defun lw-ray-fixed-real-pointsp (points real)
 (declare (xargs :measure (acl2-count points) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (endp points) (equal points nil)
  (and (lw-complexp (car points)) (equal (car (car points)) real)
       (lw-ray-fixed-real-pointsp (cdr points) real))))
(defun lw-ray-fixed-imag-pointsp (points imag)
 (declare (xargs :measure (acl2-count points) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (endp points) (equal points nil)
  (and (lw-complexp (car points)) (equal (cdr (car points)) imag)
       (lw-ray-fixed-imag-pointsp (cdr points) imag))))

(defthm lw-ray-fixed-real-data
 (implies (lw-ray-fixed-real-pointsp points real) (lw-ray-pointsp points))
 :hints (("Goal" :induct (lw-ray-fixed-real-pointsp points real)
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-ray-fixed-real-pointsp) lw-ray-fixed-real-pointsp lw-ray-pointsp endp lw-rap-left-commutes lw-rap-left-distributes lw-rap-fold-constants lw-rap-times-negative lw-rap-negative-times lw-rap-zero-times lw-rap-minus-one lw-rap-double-negative lw-rap-add-cancel lw-rap-double lw-rap-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))
(defthm lw-ray-fixed-imag-data
 (implies (lw-ray-fixed-imag-pointsp points imag) (lw-ray-pointsp points))
 :hints (("Goal" :induct (lw-ray-fixed-imag-pointsp points imag)
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-ray-fixed-imag-pointsp) lw-ray-fixed-imag-pointsp lw-ray-pointsp endp lw-rap-left-commutes lw-rap-left-distributes lw-rap-fold-constants lw-rap-times-negative lw-rap-negative-times lw-rap-zero-times lw-rap-minus-one lw-rap-double-negative lw-rap-add-cancel lw-rap-double lw-rap-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-ray-vertical-path-potential
 (implies (and (lw-complexp current) (equal (car current) real)
               (lw-ray-fixed-real-pointsp points real))
  (equal (lw-ray-path-index current points)
   (if (< 0 real)
    (- (lw-ray-upper-indicator (lw-ray-path-last current points))
       (lw-ray-upper-indicator current)) 0)))
 :hints (("Goal" :induct (lw-ray-path-index current points)
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-ray-path-index) lw-ray-path-index lw-ray-path-last lw-ray-fixed-real-pointsp lw-ray-crossing-vertical-potential (:type-prescription lw-ray-upper-indicator) endp lw-rap-left-commutes lw-rap-left-distributes lw-rap-fold-constants lw-rap-times-negative lw-rap-negative-times lw-rap-zero-times lw-rap-minus-one lw-rap-double-negative lw-rap-add-cancel lw-rap-double lw-rap-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-ray-horizontal-path-zero
 (implies (and (lw-complexp current) (equal (cdr current) imag)
               (lw-ray-fixed-imag-pointsp points imag))
  (equal (lw-ray-path-index current points) 0))
 :hints (("Goal" :induct (lw-ray-path-index current points)
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-ray-path-index) lw-ray-path-index lw-ray-fixed-imag-pointsp lw-ray-crossing-horizontal-zero endp lw-rap-left-commutes lw-rap-left-distributes lw-rap-fold-constants lw-rap-times-negative lw-rap-negative-times lw-rap-zero-times lw-rap-minus-one lw-rap-double-negative lw-rap-add-cancel lw-rap-double lw-rap-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-ray-vertical-row-potential
 (implies (and (consp points) (lw-ray-fixed-real-pointsp points real))
  (equal (lw-ray-row-index points)
   (if (< 0 real)
    (- (lw-ray-upper-indicator (lw-ray-row-last points))
       (lw-ray-upper-indicator (car points))) 0)))
 :hints (("Goal"
  :use ((:instance lw-ray-vertical-path-potential (current (car points)) (points (cdr points))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-fixed-real-pointsp lw-ray-row-index lw-ray-row-last endp lw-rap-left-commutes lw-rap-left-distributes lw-rap-fold-constants lw-rap-times-negative lw-rap-negative-times lw-rap-zero-times lw-rap-minus-one lw-rap-double-negative lw-rap-add-cancel lw-rap-double lw-rap-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-ray-horizontal-row-zero
 (implies (lw-ray-fixed-imag-pointsp points imag) (equal (lw-ray-row-index points) 0))
 :hints (("Goal"
  :use ((:instance lw-ray-horizontal-path-zero (current (car points)) (points (cdr points))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-fixed-imag-pointsp lw-ray-row-index (:executable-counterpart lw-ray-path-index) endp lw-rap-left-commutes lw-rap-left-distributes lw-rap-fold-constants lw-rap-times-negative lw-rap-negative-times lw-rap-zero-times lw-rap-minus-one lw-rap-double-negative lw-rap-add-cancel lw-rap-double lw-rap-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))
