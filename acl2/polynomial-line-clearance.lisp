(in-package "ACL2")

(include-book "polynomial-edge-clearance")

; A checked finite line supplies one positive clearance for all its subedges.

(local (defthm lw-plc2-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-plc2-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-plc2-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-plc2-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-plc2-times-negative (a b) (b a)))
                 :in-theory (disable lw-plc2-times-negative)))))

(local (defthm lw-plc2-zero-times (equal (* 0 a) 0)))

(local (defthm lw-plc2-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-plc2-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-plc2-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-plc2-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-plc2-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-plc2-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-plc2-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-plc2-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-plc2-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-plc2-left-commutes)))))
(defun lw-polynomial-line-clearance (coefficients left right count index remaining bound radius)
 (declare (xargs :measure (nfix remaining) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (zp remaining) 1
  (let ((head (lw-polynomial-edge-clearance coefficients (lw-polynomial-line-point left right count index) (lw-polynomial-line-point left right count (+ 1 index)) bound radius))
        (tail (lw-polynomial-line-clearance coefficients left right count (+ 1 index) (- remaining 1) bound radius)))
   (if (< head tail) head tail))))

(defthm lw-polynomial-line-clearance-data
 (implies (lw-polynomial-line-check coefficients left right count index remaining bound radius)
  (and (rationalp (lw-polynomial-line-clearance coefficients left right count index remaining bound radius))
       (< 0 (lw-polynomial-line-clearance coefficients left right count index remaining bound radius))))
 :hints (("Goal" :induct (lw-polynomial-line-clearance coefficients left right count index remaining bound radius)
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-polynomial-line-clearance) lw-polynomial-line-clearance lw-polynomial-line-check lw-plc2-left-commutes lw-plc2-left-distributes lw-plc2-fold-constants lw-plc2-times-negative lw-plc2-negative-times lw-plc2-zero-times lw-plc2-minus-one lw-plc2-double-negative lw-plc2-add-cancel lw-plc2-double lw-plc2-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
         (and stable-under-simplificationp
          '(:use ((:instance lw-polynomial-edge-clearance-data (left (lw-polynomial-line-point left right count index)) (right (lw-polynomial-line-point left right count (+ 1 index)))))
            :do-not-induct t))))

(local (defun lw-plc2-select-induct (index remaining position)
 (declare (xargs :measure (nfix remaining) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (or (zp remaining) (equal index position)) nil
  (lw-plc2-select-induct (+ 1 index) (- remaining 1) position))))

(defthm lw-polynomial-line-clearance-select
 (implies (and (lw-polynomial-line-check coefficients left right count index remaining bound radius)
               (natp index) (posp remaining) (natp position) (<= index position) (< position (+ index remaining)))
  (and (lw-polynomial-edge-check coefficients (lw-polynomial-line-point left right count position) (lw-polynomial-line-point left right count (+ 1 position)) bound radius)
       (<= (lw-polynomial-line-clearance coefficients left right count index remaining bound radius) (lw-polynomial-edge-clearance coefficients (lw-polynomial-line-point left right count position) (lw-polynomial-line-point left right count (+ 1 position)) bound radius))))
 :hints (("Goal" :induct (lw-plc2-select-induct index remaining position)
          :expand ((lw-polynomial-line-clearance coefficients left right count index remaining bound radius)
                   (lw-polynomial-line-check coefficients left right count index remaining bound radius))
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-plc2-select-induct) lw-plc2-left-commutes lw-plc2-left-distributes lw-plc2-fold-constants lw-plc2-times-negative lw-plc2-negative-times lw-plc2-zero-times lw-plc2-minus-one lw-plc2-double-negative lw-plc2-add-cancel lw-plc2-double lw-plc2-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
         (and stable-under-simplificationp
          '(:use (lw-polynomial-line-clearance-data
                  (:instance lw-polynomial-line-clearance-data (index (+ 1 index)) (remaining (- remaining 1)))
                  (:instance lw-polynomial-edge-clearance-data (left (lw-polynomial-line-point left right count index)) (right (lw-polynomial-line-point left right count (+ 1 index)))))
            :do-not-induct t))))

(defthm lw-polynomial-line-segment-excludes-clearance
 (implies (and (lw-polynomial-line-check coefficients left right count index remaining bound radius)
               (natp index) (posp remaining) (natp position) (<= index position) (< position (+ index remaining))
               (rationalp parameter) (<= 0 parameter) (<= parameter 1))
  (not (lw-complex-diskp
   (lw-complex-polynomial coefficients (lw-complex-segment (lw-polynomial-line-point left right count position) (lw-polynomial-line-point left right count (+ 1 position)) parameter) 0)
   (lw-polynomial-line-clearance coefficients left right count index remaining bound radius))))
 :hints (("Goal"
  :use (lw-polynomial-line-clearance-data lw-polynomial-line-clearance-select
        (:instance lw-polynomial-edge-clearance-data (left (lw-polynomial-line-point left right count position)) (right (lw-polynomial-line-point left right count (+ 1 position))))
        (:instance lw-polynomial-edge-excludes-clearance (left (lw-polynomial-line-point left right count position)) (right (lw-polynomial-line-point left right count (+ 1 position))))
        (:instance lw-complex-disk-enlarge
          (point (lw-complex-polynomial coefficients (lw-complex-segment (lw-polynomial-line-point left right count position) (lw-polynomial-line-point left right count (+ 1 position)) parameter) 0))
          (radius (lw-polynomial-line-clearance coefficients left right count index remaining bound radius)) (cap (lw-polynomial-edge-clearance coefficients (lw-polynomial-line-point left right count position) (lw-polynomial-line-point left right count (+ 1 position)) bound radius))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-plc2-left-commutes lw-plc2-left-distributes lw-plc2-fold-constants lw-plc2-times-negative lw-plc2-negative-times lw-plc2-zero-times lw-plc2-minus-one lw-plc2-double-negative lw-plc2-add-cancel lw-plc2-double lw-plc2-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
