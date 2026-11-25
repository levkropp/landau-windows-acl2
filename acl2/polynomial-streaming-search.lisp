(in-package "ACL2")

(include-book "polynomial-approximate-root")

; Search rows on demand. The equality theorem connects this executable search
; to the full finite grid used in the winding proof.

(local (defthm lw-pss-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pss-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pss-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pss-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pss-times-negative (a b) (b a)))
                 :in-theory (disable lw-pss-times-negative)))))

(local (defthm lw-pss-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pss-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pss-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pss-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pss-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pss-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pss-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-pss-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pss-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pss-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-pss-left-commutes)))))
(defun lw-polynomial-grid-small-search (coefficients anchor side count row remaining epsilon)
 (declare (xargs :measure (nfix remaining) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (zp remaining) nil
  (let ((column (lw-ray-row-small-search
                 (lw-polynomial-grid-row coefficients anchor side count row 0 (+ 1 count)) epsilon)))
   (if (natp column) (cons 0 column)
    (let ((address (lw-polynomial-grid-small-search
                   coefficients anchor side count (+ 1 row) (- remaining 1) epsilon)))
     (if (consp address) (cons (+ 1 (car address)) (cdr address)) nil))))))

(defthm lw-polynomial-grid-small-search-agrees
 (equal (lw-polynomial-grid-small-search coefficients anchor side count row remaining epsilon)
        (lw-ray-grid-small-search
         (lw-polynomial-grid-rows coefficients anchor side count row remaining) epsilon))
 :hints (("Goal" :induct (lw-polynomial-grid-small-search coefficients anchor side count row remaining epsilon)
          :expand ((lw-polynomial-grid-rows coefficients anchor side count row remaining))
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-polynomial-grid-small-search) lw-polynomial-grid-small-search lw-polynomial-grid-rows lw-ray-grid-small-search endp lw-pss-left-commutes lw-pss-left-distributes lw-pss-fold-constants lw-pss-times-negative lw-pss-negative-times lw-pss-zero-times lw-pss-minus-one lw-pss-double-negative lw-pss-add-cancel lw-pss-double lw-pss-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defun lw-polynomial-global-root-address-fast (coefficients epsilon)
 (lw-polynomial-grid-small-search (lw-polynomial-outer-coefficients coefficients)
  (cons -1 -1) 2 (lw-polynomial-global-root-count coefficients epsilon) 0
  (+ 1 (lw-polynomial-global-root-count coefficients epsilon)) epsilon))

(defun lw-polynomial-global-root-point-fast (coefficients epsilon)
 (let ((address (lw-polynomial-global-root-address-fast coefficients epsilon)))
  (lw-complex-scale (lw-polynomial-leading-radius coefficients)
   (lw-polynomial-grid-point (cons -1 -1) 2 (lw-polynomial-global-root-count coefficients epsilon)
                            (car address) (cdr address)))))

(defthm lw-polynomial-global-root-address-fast-agrees
 (equal (lw-polynomial-global-root-address-fast coefficients epsilon)
        (lw-polynomial-global-root-address coefficients epsilon))
 :hints (("Goal"
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-global-root-address-fast lw-polynomial-global-root-address lw-polynomial-global-root-grid lw-polynomial-grid lw-polynomial-grid-small-search-agrees lw-pss-left-commutes lw-pss-left-distributes lw-pss-fold-constants lw-pss-times-negative lw-pss-negative-times lw-pss-zero-times lw-pss-minus-one lw-pss-double-negative lw-pss-add-cancel lw-pss-double lw-pss-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-polynomial-global-root-point-fast-agrees
 (equal (lw-polynomial-global-root-point-fast coefficients epsilon)
        (lw-polynomial-global-root-point coefficients epsilon))
 :hints (("Goal"
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-global-root-point-fast lw-polynomial-global-root-point lw-polynomial-global-root-unit-point lw-polynomial-global-root-address-fast-agrees lw-pss-left-commutes lw-pss-left-distributes lw-pss-fold-constants lw-pss-times-negative lw-pss-negative-times lw-pss-zero-times lw-pss-minus-one lw-pss-double-negative lw-pss-add-cancel lw-pss-double lw-pss-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-polynomial-approximate-root-fast
 (implies (and (lw-complex-coefficientsp coefficients) (consp coefficients) (consp (cdr coefficients))
               (not (equal (lw-polynomial-leading coefficients) (cons 0 0)))
               (rationalp epsilon) (< 0 epsilon))
  (and (consp (lw-polynomial-global-root-address-fast coefficients epsilon))
       (lw-complexp (lw-polynomial-global-root-point-fast coefficients epsilon))
       (lw-complex-diskp (lw-polynomial-global-root-point-fast coefficients epsilon)
                         (* 2 (lw-polynomial-leading-radius coefficients)))
       (lw-complex-diskp
        (lw-complex-polynomial coefficients (lw-polynomial-global-root-point-fast coefficients epsilon) 0) epsilon)))
 :hints (("Goal" :use (lw-polynomial-approximate-root)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-global-root-address-fast-agrees lw-polynomial-global-root-point-fast-agrees lw-pss-left-commutes lw-pss-left-distributes lw-pss-fold-constants lw-pss-times-negative lw-pss-negative-times lw-pss-zero-times lw-pss-minus-one lw-pss-double-negative lw-pss-add-cancel lw-pss-double lw-pss-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
          :do-not-induct t)))
