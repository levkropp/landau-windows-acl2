; Bounded indexed slices and closure identities for finite polygon values.
(in-package "ACL2")
(include-book "polygon-homotopy")
(local (in-theory (disable lw-ray-pointsp lw-ray-row-index lw-ray-row-last lw-ray-polygon-index
 lw-ray-close-polygon lw-ray-path-index lw-ray-path-last lw-ray-crossing lw-complexp)))
(local (defthm lw-psi-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-psi-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-psi-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-psi-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-psi-times-negative (a b) (b a)))
                 :in-theory (disable lw-psi-times-negative)))))

(local (defthm lw-psi-zero-times (equal (* 0 a) 0)))

(local (defthm lw-psi-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-psi-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-psi-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-psi-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-psi-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-psi-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-psi-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-psi-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-psi-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-psi-left-commutes)))))
(defun lw-ray-indexed-slice (values index remaining)
 (declare (xargs :measure (nfix remaining) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (zp remaining) nil
 (cons (nth index values) (lw-ray-indexed-slice values (+ 1 index) (- remaining 1)))))
(local (in-theory (disable lw-ray-indexed-slice)))

(local (defthm lw-psi-length-natural
 (natp (len values))
 :hints (("Goal" :induct (len values) :in-theory (union-theories
 '(len endp lw-psi-left-commutes lw-psi-left-distributes lw-psi-fold-constants lw-psi-times-negative lw-psi-negative-times lw-psi-zero-times lw-psi-minus-one lw-psi-double-negative lw-psi-add-cancel lw-psi-double lw-psi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))
 :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-psi-nth-zero
 (equal (nth 0 values) (car values))
 :hints (("Goal" :expand ((nth 0 values)) :in-theory (union-theories
 '(nth lw-psi-left-commutes lw-psi-left-distributes lw-psi-fold-constants lw-psi-times-negative lw-psi-negative-times lw-psi-zero-times lw-psi-minus-one lw-psi-double-negative lw-psi-add-cancel lw-psi-double lw-psi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-psi-nth-shift
 (implies (natp index) (equal (nth (+ 1 index) values) (nth index (cdr values))))
 :hints (("Goal" :in-theory (union-theories
 '(nth fold-consts-in-+ lw-psi-left-commutes lw-psi-left-distributes lw-psi-fold-constants lw-psi-times-negative lw-psi-negative-times lw-psi-zero-times lw-psi-minus-one lw-psi-double-negative lw-psi-add-cancel lw-psi-double lw-psi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-ray-indexed-slice-shape
 (implies (natp remaining)
 (and (true-listp (lw-ray-indexed-slice values index remaining))
      (equal (len (lw-ray-indexed-slice values index remaining)) remaining)))
 :hints (("Goal" :induct (lw-ray-indexed-slice values index remaining)
 :in-theory (union-theories
 '(lw-ray-indexed-slice len true-listp lw-psi-left-commutes lw-psi-left-distributes lw-psi-fold-constants lw-psi-times-negative lw-psi-negative-times lw-psi-zero-times lw-psi-minus-one lw-psi-double-negative lw-psi-add-cancel lw-psi-double lw-psi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-ray-indexed-slice-shift
 (implies (natp index)
 (equal (lw-ray-indexed-slice values (+ 1 index) remaining)
        (lw-ray-indexed-slice (cdr values) index remaining)))
 :hints (("Goal" :induct (lw-ray-indexed-slice values index remaining)
 :in-theory (union-theories
 '(lw-ray-indexed-slice lw-psi-nth-shift fold-consts-in-+ lw-psi-left-commutes lw-psi-left-distributes lw-psi-fold-constants lw-psi-times-negative lw-psi-negative-times lw-psi-zero-times lw-psi-minus-one lw-psi-double-negative lw-psi-add-cancel lw-psi-double lw-psi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-ray-indexed-slice-full
 (implies (true-listp values)
 (equal (lw-ray-indexed-slice values 0 (len values)) values))
 :hints (("Goal" :induct (len values)
 :in-theory (union-theories
 '(lw-ray-indexed-slice lw-ray-indexed-slice-shift lw-psi-nth-zero len true-listp endp fold-consts-in-+ lw-psi-left-commutes lw-psi-left-distributes lw-psi-fold-constants lw-psi-times-negative lw-psi-negative-times lw-psi-zero-times lw-psi-minus-one lw-psi-double-negative lw-psi-add-cancel lw-psi-double lw-psi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-ray-indexed-slice-tail
 (implies (and (true-listp values) (consp values))
 (equal (lw-ray-indexed-slice values 1 (- (len values) 1)) (cdr values)))
 :hints (("Goal"
 :use ((:instance lw-ray-indexed-slice-full (values (cdr values)))
       (:instance lw-ray-indexed-slice-shift (index 0) (remaining (- (len values) 1))))
 :in-theory (union-theories
 '(lw-psi-length-natural true-listp len lw-psi-nth-zero fold-consts-in-+ lw-psi-left-commutes lw-psi-left-distributes lw-psi-fold-constants lw-psi-times-negative lw-psi-negative-times lw-psi-zero-times lw-psi-minus-one lw-psi-double-negative lw-psi-add-cancel lw-psi-double lw-psi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-ray-polygon-index-close
 (implies (lw-ray-pointsp points)
 (equal (lw-ray-polygon-index (lw-ray-close-polygon points)) (lw-ray-polygon-index points)))
 :hints (("Goal"
 :use (lw-ray-close-polygon-data lw-ray-close-polygon-last lw-ray-close-polygon-index
       (:instance lw-ray-crossing-self (point (car points))))
 :in-theory (union-theories
 '(lw-ray-polygon-index lw-ray-row-index lw-ray-row-last lw-ray-pointsp lw-ray-close-polygon endp lw-psi-left-commutes lw-psi-left-distributes lw-psi-fold-constants lw-psi-times-negative lw-psi-negative-times lw-psi-zero-times lw-psi-minus-one lw-psi-double-negative lw-psi-add-cancel lw-psi-double lw-psi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

