; Finite polygon index stability from pointwise perturbation and an edge budget.
(in-package "ACL2")
(include-book "polygon-homotopy")
(local (in-theory (disable lw-complexp lw-complex-sub lw-complex-diskp
 lw-ray-pointsp lw-ray-row-near-check lw-ray-row-avoids lw-ray-close-polygon
 lw-ray-polygon-index lw-ray-polygon-homotopy-check)))
(local (defthm lw-ppb-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ppb-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ppb-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ppb-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ppb-times-negative (a b) (b a)))
                 :in-theory (disable lw-ppb-times-negative)))))

(local (defthm lw-ppb-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ppb-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ppb-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ppb-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ppb-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ppb-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ppb-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ppb-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ppb-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ppb-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ppb-left-commutes)))))
(defun lw-ray-pointwise-nearp (left right delta)
 (if (or (endp left) (endp right))
     (and (equal left nil) (equal right nil))
 (and (lw-complexp (car left)) (lw-complexp (car right))
      (lw-complex-diskp (lw-complex-sub (car right) (car left)) delta)
      (lw-ray-pointwise-nearp (cdr left) (cdr right) delta))))
(local (in-theory (disable lw-ray-pointwise-nearp)))

(defthm lw-ray-pointwise-near-data
 (implies (lw-ray-pointwise-nearp left right delta)
 (and (lw-ray-pointsp left) (lw-ray-pointsp right)
      (equal (len left) (len right))
      (equal (consp left) (consp right))))
 :hints (("Goal" :induct (lw-ray-pointwise-nearp left right delta)
 :in-theory (union-theories
 '(lw-ray-pointwise-nearp lw-ray-pointsp endp len lw-ppb-left-commutes lw-ppb-left-distributes lw-ppb-fold-constants lw-ppb-times-negative lw-ppb-negative-times lw-ppb-zero-times lw-ppb-minus-one lw-ppb-double-negative lw-ppb-add-cancel lw-ppb-double lw-ppb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-ray-pointwise-near-append
 (implies (and (lw-ray-pointwise-nearp left right delta)
               (lw-ray-pointwise-nearp left-tail right-tail delta))
 (lw-ray-pointwise-nearp (append left left-tail) (append right right-tail) delta))
 :hints (("Goal" :induct (lw-ray-pointwise-nearp left right delta)
 :in-theory (union-theories
 '(lw-ray-pointwise-nearp append endp lw-ppb-left-commutes lw-ppb-left-distributes lw-ppb-fold-constants lw-ppb-times-negative lw-ppb-negative-times lw-ppb-zero-times lw-ppb-minus-one lw-ppb-double-negative lw-ppb-add-cancel lw-ppb-double lw-ppb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-ray-pointwise-near-close
 (implies (lw-ray-pointwise-nearp left right delta)
 (lw-ray-pointwise-nearp (lw-ray-close-polygon left) (lw-ray-close-polygon right) delta))
 :hints (("Goal"
 :use ((:instance lw-ray-pointwise-near-data)
       (:instance lw-ray-pointwise-near-append
        (left (cdr left)) (right (cdr right))
        (left-tail (list (car left))) (right-tail (list (car right)))))
 :in-theory (union-theories
 '(lw-ray-pointwise-nearp lw-ray-close-polygon append endp cons lw-ppb-left-commutes lw-ppb-left-distributes lw-ppb-fold-constants lw-ppb-times-negative lw-ppb-negative-times lw-ppb-zero-times lw-ppb-minus-one lw-ppb-double-negative lw-ppb-add-cancel lw-ppb-double lw-ppb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-ray-pointwise-near-enlarge
 (implies (and (lw-ray-pointwise-nearp left right delta)
               (rationalp delta) (<= 0 delta) (rationalp cap) (<= delta cap))
 (lw-ray-pointwise-nearp left right cap))
 :hints (("Goal" :induct (lw-ray-pointwise-nearp left right delta)
 :in-theory (union-theories
 '(lw-ray-pointwise-nearp endp lw-ppb-left-commutes lw-ppb-left-distributes lw-ppb-fold-constants lw-ppb-times-negative lw-ppb-negative-times lw-ppb-zero-times lw-ppb-minus-one lw-ppb-double-negative lw-ppb-add-cancel lw-ppb-double lw-ppb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) )
 (and stable-under-simplificationp
 '(:use ((:instance lw-complex-disk-enlarge
          (point (lw-complex-sub (car right) (car left))) (radius delta)))
   :do-not-induct t))))

(defthm lw-ray-pointwise-near-row-check
 (implies (and (lw-ray-pointwise-nearp bottom top delta)
               (lw-ray-row-near-check bottom bottom beta)
               (rationalp beta) (<= 0 beta) (rationalp delta) (<= 0 delta))
 (lw-ray-row-near-check bottom top (+ beta delta)))
 :hints (("Goal" :induct (lw-ray-pointwise-nearp bottom top delta)
 :in-theory (union-theories
 '(lw-ray-pointwise-nearp lw-ray-row-near-check endp lw-ppb-left-commutes lw-ppb-left-distributes lw-ppb-fold-constants lw-ppb-times-negative lw-ppb-negative-times lw-ppb-zero-times lw-ppb-minus-one lw-ppb-double-negative lw-ppb-add-cancel lw-ppb-double lw-ppb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) )
 (and stable-under-simplificationp
 '(:use ((:instance lw-complex-disk-enlarge
          (point (lw-complex-sub (cadr bottom) (car bottom))) (radius beta) (cap (+ beta delta)))
         (:instance lw-complex-disk-enlarge
          (point (lw-complex-sub (car top) (car bottom))) (radius delta) (cap (+ beta delta)))
         (:instance lw-complex-difference-triangle
          (left (cadr top)) (middle (cadr bottom)) (right (car bottom))
          (radius delta) (other-radius beta)))
   :do-not-induct t))))

(defthm lw-ray-row-near-enlarge
 (implies (and (lw-ray-row-near-check bottom top radius)
               (rationalp radius) (<= 0 radius) (rationalp cap) (<= radius cap))
 (lw-ray-row-near-check bottom top cap))
 :hints (("Goal" :induct (lw-ray-row-near-check bottom top radius)
 :in-theory (union-theories
 '(lw-ray-row-near-check endp lw-ppb-left-commutes lw-ppb-left-distributes lw-ppb-fold-constants lw-ppb-times-negative lw-ppb-negative-times lw-ppb-zero-times lw-ppb-minus-one lw-ppb-double-negative lw-ppb-add-cancel lw-ppb-double lw-ppb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) )
 (and stable-under-simplificationp
 '(:use ((:instance lw-complex-disk-enlarge
          (point (lw-complex-sub (cadr bottom) (car bottom))))
         (:instance lw-complex-disk-enlarge
          (point (lw-complex-sub (cadr top) (car bottom))))
         (:instance lw-complex-disk-enlarge
          (point (lw-complex-sub (car top) (car bottom)))))
   :do-not-induct t))))

(defthm lw-ray-row-avoids-shrink
 (implies (and (lw-ray-row-avoids points cap)
               (rationalp radius) (<= 0 radius) (rationalp cap) (<= radius cap))
 (lw-ray-row-avoids points radius))
 :hints (("Goal" :induct (lw-ray-row-avoids points cap)
 :in-theory (union-theories
 '(lw-ray-row-avoids endp lw-ppb-left-commutes lw-ppb-left-distributes lw-ppb-fold-constants lw-ppb-times-negative lw-ppb-negative-times lw-ppb-zero-times lw-ppb-minus-one lw-ppb-double-negative lw-ppb-add-cancel lw-ppb-double lw-ppb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) )
 (and stable-under-simplificationp
 '(:use ((:instance lw-complex-disk-enlarge (point (car points))))
   :do-not-induct t))))

(defthm lw-ray-polygon-pointwise-perturbation
 (implies (and (consp bottom)
               (lw-ray-pointwise-nearp bottom top delta)
               (rationalp beta) (<= 0 beta) (rationalp delta) (<= 0 delta) (< 0 (+ beta delta))
               (lw-ray-row-avoids bottom (+ beta delta))
               (lw-ray-row-near-check (lw-ray-close-polygon bottom) (lw-ray-close-polygon bottom) beta))
 (equal (lw-ray-polygon-index bottom) (lw-ray-polygon-index top)))
 :hints (("Goal"
 :use ((:instance lw-ray-pointwise-near-data (left bottom) (right top))
       (:instance lw-ray-pointwise-near-close (left bottom) (right top))
       (:instance lw-ray-pointwise-near-row-check
        (bottom (lw-ray-close-polygon bottom)) (top (lw-ray-close-polygon top)))
       (:instance lw-ray-polygon-homotopy-invariant (epsilon (+ beta delta))))
 :in-theory (union-theories
 '(lw-ray-polygon-homotopy-check lw-ppb-left-commutes lw-ppb-left-distributes lw-ppb-fold-constants lw-ppb-times-negative lw-ppb-negative-times lw-ppb-zero-times lw-ppb-minus-one lw-ppb-double-negative lw-ppb-add-cancel lw-ppb-double lw-ppb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

