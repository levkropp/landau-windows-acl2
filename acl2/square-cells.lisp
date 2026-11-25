; Computed rational cell locations and uniform square geometry.
(in-package "ACL2")
(include-book "polynomial-grid")
(local (in-theory (disable lw-complexp lw-complex-sub lw-complex-l1 lw-complex-diskp
 lw-polynomial-grid-point lw-polynomial-grid-step lw-polynomial-grid-radius)))
(local (defthm lw-sqc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-sqc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-sqc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-sqc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-sqc-times-negative (a b) (b a)))
                 :in-theory (disable lw-sqc-times-negative)))))

(local (defthm lw-sqc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-sqc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-sqc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-sqc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-sqc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-sqc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-sqc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-sqc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-sqc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-sqc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-sqc-left-commutes)))))
(defun lw-axis-cell-index (start step count value)
 (declare (xargs :measure (nfix count) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (or (zp count) (<= value (+ start step))) 0
 (+ 1 (lw-axis-cell-index (+ start step) step (- count 1) value))))
(defun lw-square-containsp (anchor side point)
 (and (lw-complexp anchor) (lw-complexp point) (rationalp side) (< 0 side)
      (<= (car anchor) (car point)) (<= (car point) (+ (car anchor) side))
      (<= (cdr anchor) (cdr point)) (<= (cdr point) (+ (cdr anchor) side))))
(defun lw-square-cell-containsp (anchor side count row column point)
 (and (lw-complexp anchor) (lw-complexp point) (rationalp side) (< 0 side) (posp count)
      (natp row) (< row count) (natp column) (< column count)
      (let ((base (lw-polynomial-grid-point anchor side count row column))
            (step (lw-polynomial-grid-step side count)))
       (and (<= (car base) (car point)) (<= (car point) (+ (car base) step))
            (<= (cdr base) (cdr point)) (<= (cdr point) (+ (cdr base) step))))))
(defun lw-square-cell-address (anchor side count point)
 (cons (lw-axis-cell-index (cdr anchor) (lw-polynomial-grid-step side count) count (cdr point))
       (lw-axis-cell-index (car anchor) (lw-polynomial-grid-step side count) count (car point))))
(local (in-theory (disable lw-axis-cell-index lw-square-containsp lw-square-cell-containsp lw-square-cell-address)))

(defthm lw-axis-cell-index-natural
 (natp (lw-axis-cell-index start step count value))
 :hints (("Goal" :induct (lw-axis-cell-index start step count value) :in-theory (union-theories
 '(lw-axis-cell-index lw-sqc-left-commutes lw-sqc-left-distributes lw-sqc-fold-constants lw-sqc-times-negative lw-sqc-negative-times lw-sqc-zero-times lw-sqc-minus-one lw-sqc-double-negative lw-sqc-add-cancel lw-sqc-double lw-sqc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))
 :rule-classes (:rewrite :type-prescription))

(defthm lw-axis-cell-index-cover
 (implies (and (rationalp start) (rationalp step) (< 0 step) (posp count) (rationalp value)
 (<= start value) (<= value (+ start (* count step))))
 (let ((index (lw-axis-cell-index start step count value)))
 (and (natp index) (< index count)
      (<= (+ start (* index step)) value) (<= value (+ start (* (+ 1 index) step))))))
 :hints (("Goal" :induct (lw-axis-cell-index start step count value)
 :in-theory (union-theories
 '(lw-axis-cell-index lw-axis-cell-index-natural fold-consts-in-+ lw-sqc-left-commutes lw-sqc-left-distributes lw-sqc-fold-constants lw-sqc-times-negative lw-sqc-negative-times lw-sqc-zero-times lw-sqc-minus-one lw-sqc-double-negative lw-sqc-add-cancel lw-sqc-double lw-sqc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))) :rule-classes nil)

(local (defthm lw-sqc-abs-interval
 (implies (and (rationalp left) (rationalp right) (rationalp side) (<= 0 side)
 (<= left right) (<= right (+ left side)))
 (<= (abs right) (+ (abs left) side)))
 :hints (("Goal" :cases ((<= 0 left) (<= 0 right))
 :in-theory (union-theories
 '(abs lw-sqc-left-commutes lw-sqc-left-distributes lw-sqc-fold-constants lw-sqc-times-negative lw-sqc-negative-times lw-sqc-zero-times lw-sqc-minus-one lw-sqc-double-negative lw-sqc-add-cancel lw-sqc-double lw-sqc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))) :rule-classes nil))

(defthm lw-square-contained-in-disk
 (implies (lw-square-containsp anchor side point)
 (lw-complex-diskp point (lw-polynomial-grid-radius anchor side)))
 :hints (("Goal"
 :use (lw-polynomial-grid-radius-data
       (:instance lw-sqc-abs-interval (left (car anchor)) (right (car point)))
       (:instance lw-sqc-abs-interval (left (cdr anchor)) (right (cdr point)))
       (:instance lw-complex-l1-bound)
       (:instance lw-complex-disk-enlarge (radius (lw-complex-l1 point)) (cap (lw-polynomial-grid-radius anchor side))))
 :in-theory (union-theories
 '(lw-square-containsp lw-polynomial-grid-radius lw-complex-l1 lw-complexp lw-sqc-left-commutes lw-sqc-left-distributes lw-sqc-fold-constants lw-sqc-times-negative lw-sqc-negative-times lw-sqc-zero-times lw-sqc-minus-one lw-sqc-double-negative lw-sqc-add-cancel lw-sqc-double lw-sqc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-square-cell-address-cover
 (implies (and (lw-square-containsp anchor side point) (posp count))
 (let ((address (lw-square-cell-address anchor side count point)))
 (and (consp address) (natp (car address)) (< (car address) count)
      (natp (cdr address)) (< (cdr address) count)
      (lw-square-cell-containsp anchor side count (car address) (cdr address) point))))
 :hints (("Goal"
 :use (lw-polynomial-grid-step-data
       (:instance inverse-of-* (x count))
       (:instance lw-axis-cell-index-cover (start (car anchor)) (step (lw-polynomial-grid-step side count)) (value (car point)))
       (:instance lw-axis-cell-index-cover (start (cdr anchor)) (step (lw-polynomial-grid-step side count)) (value (cdr point))))
 :in-theory (union-theories
 '(lw-square-containsp lw-square-cell-containsp lw-square-cell-address lw-polynomial-grid-point lw-polynomial-grid-step lw-complexp lw-sqc-inverse-factor fold-consts-in-+ lw-sqc-left-commutes lw-sqc-left-distributes lw-sqc-fold-constants lw-sqc-times-negative lw-sqc-negative-times lw-sqc-zero-times lw-sqc-minus-one lw-sqc-double-negative lw-sqc-add-cancel lw-sqc-double lw-sqc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defun lw-square-radius (anchor side) (+ (lw-complex-l1 anchor) (* 2 side)))
(local (in-theory (disable lw-square-radius)))

(defthm lw-square-radius-data
 (implies (and (lw-complexp anchor) (rationalp side) (< 0 side))
 (and (rationalp (lw-square-radius anchor side)) (< 0 (lw-square-radius anchor side))))
 :hints (("Goal" :use ((:instance lw-complex-l1-bound (point anchor)))
 :in-theory (union-theories
 '(lw-square-radius lw-sqc-left-commutes lw-sqc-left-distributes lw-sqc-fold-constants lw-sqc-times-negative lw-sqc-negative-times lw-sqc-zero-times lw-sqc-minus-one lw-sqc-double-negative lw-sqc-add-cancel lw-sqc-double lw-sqc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-square-contained-in-tight-disk
 (implies (lw-square-containsp anchor side point)
 (lw-complex-diskp point (lw-square-radius anchor side)))
 :hints (("Goal"
 :use (lw-square-radius-data
       (:instance lw-sqc-abs-interval (left (car anchor)) (right (car point)))
       (:instance lw-sqc-abs-interval (left (cdr anchor)) (right (cdr point)))
       (:instance lw-complex-l1-bound)
       (:instance lw-complex-disk-enlarge (radius (lw-complex-l1 point)) (cap (lw-square-radius anchor side))))
 :in-theory (union-theories
 '(lw-square-containsp lw-square-radius lw-complex-l1 lw-complexp lw-sqc-left-commutes lw-sqc-left-distributes lw-sqc-fold-constants lw-sqc-times-negative lw-sqc-negative-times lw-sqc-zero-times lw-sqc-minus-one lw-sqc-double-negative lw-sqc-add-cancel lw-sqc-double lw-sqc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-square-cell-in-square
 (implies (lw-square-cell-containsp anchor side count row column point)
 (lw-square-containsp anchor side point))
 :hints (("Goal"
 :use (lw-polynomial-grid-step-data
       (:instance lw-polynomial-grid-point-bounds)
       (:instance lw-polynomial-grid-point-bounds (row (+ 1 row)) (column (+ 1 column))))
 :in-theory (union-theories
 '(lw-square-containsp lw-square-cell-containsp lw-polynomial-grid-point lw-complexp fold-consts-in-+ lw-sqc-left-commutes lw-sqc-left-distributes lw-sqc-fold-constants lw-sqc-times-negative lw-sqc-negative-times lw-sqc-zero-times lw-sqc-minus-one lw-sqc-double-negative lw-sqc-add-cancel lw-sqc-double lw-sqc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(local (defthm lw-sqc-rectangle-distance
 (implies (and (lw-complexp left) (lw-complexp right) (rationalp step) (<= 0 step)
 (<= (car left) (car right)) (<= (car right) (+ (car left) step))
 (<= (cdr left) (cdr right)) (<= (cdr right) (+ (cdr left) step)))
 (lw-complex-diskp (lw-complex-sub right left) (* 2 step)))
 :hints (("Goal"
 :use ((:instance lw-complex-l1-bound (point (lw-complex-sub right left)))
       (:instance lw-complex-disk-enlarge (point (lw-complex-sub right left)) (radius (lw-complex-l1 (lw-complex-sub right left))) (cap (* 2 step))))
 :in-theory (union-theories
 '(lw-complexp lw-complex-sub lw-complex-l1 abs lw-sqc-left-commutes lw-sqc-left-distributes lw-sqc-fold-constants lw-sqc-times-negative lw-sqc-negative-times lw-sqc-zero-times lw-sqc-minus-one lw-sqc-double-negative lw-sqc-add-cancel lw-sqc-double lw-sqc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes nil))

(defthm lw-square-cell-distance
 (implies (lw-square-cell-containsp anchor side count row column point)
 (lw-complex-diskp (lw-complex-sub point (lw-polynomial-grid-point anchor side count row column))
                  (* 2 (lw-polynomial-grid-step side count))))
 :hints (("Goal"
 :use (lw-polynomial-grid-point-rational lw-polynomial-grid-step-data
       (:instance lw-sqc-rectangle-distance (left (lw-polynomial-grid-point anchor side count row column))
        (right point) (step (lw-polynomial-grid-step side count))))
 :in-theory (union-theories
 '(lw-square-cell-containsp lw-sqc-left-commutes lw-sqc-left-distributes lw-sqc-fold-constants lw-sqc-times-negative lw-sqc-negative-times lw-sqc-zero-times lw-sqc-minus-one lw-sqc-double-negative lw-sqc-add-cancel lw-sqc-double lw-sqc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
