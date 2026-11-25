; Complete finite cell covers of polynomial small-value regions.
(in-package "ACL2")
(include-book "polynomial-cell-clearance")
(local (in-theory (disable lw-complexp lw-complex-diskp lw-complex-polynomial
 lw-polynomial-cell-activep lw-polynomial-cell-variation lw-square-containsp
 lw-square-cell-containsp lw-square-cell-address)))
(local (defthm lw-psc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-psc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-psc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-psc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-psc-times-negative (a b) (b a)))
                 :in-theory (disable lw-psc-times-negative)))))

(local (defthm lw-psc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-psc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-psc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-psc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-psc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-psc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-psc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-psc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-psc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-psc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-psc-left-commutes)))))
(defun lw-square-address-listp (addresses count)
 (if (endp addresses) (equal addresses nil)
 (and (consp (car addresses)) (natp (caar addresses)) (< (caar addresses) count)
      (natp (cdar addresses)) (< (cdar addresses) count)
      (lw-square-address-listp (cdr addresses) count))))
(defun lw-polynomial-active-coverp (coefficients anchor side count epsilon addresses)
 (if (endp addresses) (equal addresses nil)
 (and (lw-polynomial-cell-activep coefficients anchor side count epsilon (caar addresses) (cdar addresses))
      (lw-polynomial-active-coverp coefficients anchor side count epsilon (cdr addresses)))))
(defun lw-square-cover-containsp (anchor side count point addresses)
 (if (endp addresses) nil
 (or (lw-square-cell-containsp anchor side count (caar addresses) (cdar addresses) point)
     (lw-square-cover-containsp anchor side count point (cdr addresses)))))
(defun lw-polynomial-sublevel-cover-row (coefficients anchor side count epsilon row column remaining)
 (declare (xargs :measure (nfix remaining) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (zp remaining) nil
 (let ((tail (lw-polynomial-sublevel-cover-row coefficients anchor side count epsilon row (+ 1 column) (- remaining 1))))
 (if (lw-polynomial-cell-activep coefficients anchor side count epsilon row column)
     (cons (cons row column) tail) tail))))
(defun lw-polynomial-sublevel-cover-rows (coefficients anchor side count epsilon row remaining)
 (declare (xargs :measure (nfix remaining) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (zp remaining) nil
 (append (lw-polynomial-sublevel-cover-row coefficients anchor side count epsilon row 0 count)
         (lw-polynomial-sublevel-cover-rows coefficients anchor side count epsilon (+ 1 row) (- remaining 1)))))
(defun lw-polynomial-sublevel-cover (coefficients anchor side count epsilon)
 (lw-polynomial-sublevel-cover-rows coefficients anchor side count epsilon 0 count))
(local (in-theory (disable lw-square-address-listp lw-polynomial-active-coverp lw-square-cover-containsp
 lw-polynomial-sublevel-cover-row lw-polynomial-sublevel-cover-rows lw-polynomial-sublevel-cover)))

(local (defthm lw-psc-length-natural (natp (len points))
 :hints (("Goal" :induct (len points) :in-theory (union-theories
 '(len endp lw-psc-left-commutes lw-psc-left-distributes lw-psc-fold-constants lw-psc-times-negative lw-psc-negative-times lw-psc-zero-times lw-psc-minus-one lw-psc-double-negative lw-psc-add-cancel lw-psc-double lw-psc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))
 :rule-classes (:rewrite :type-prescription)))
(local (defthm lw-psc-length-append
 (equal (len (append left right)) (+ (len left) (len right)))
 :hints (("Goal" :induct (append left right)
 :in-theory (union-theories
 '(append len lw-psc-length-natural endp lw-psc-left-commutes lw-psc-left-distributes lw-psc-fold-constants lw-psc-times-negative lw-psc-negative-times lw-psc-zero-times lw-psc-minus-one lw-psc-double-negative lw-psc-add-cancel lw-psc-double lw-psc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))
(local (defthm lw-psc-member-append
 (iff (member-equal address (append left right))
 (or (member-equal address left) (member-equal address right)))
 :hints (("Goal" :induct (append left right)
 :in-theory (union-theories
 '(append member-equal iff endp lw-psc-left-commutes lw-psc-left-distributes lw-psc-fold-constants lw-psc-times-negative lw-psc-negative-times lw-psc-zero-times lw-psc-minus-one lw-psc-double-negative lw-psc-add-cancel lw-psc-double lw-psc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))
(local (defthm lw-psc-addresses-append
 (implies (and (lw-square-address-listp left count) (lw-square-address-listp right count))
 (lw-square-address-listp (append left right) count))
 :hints (("Goal" :induct (append left right)
 :in-theory (union-theories
 '(append lw-square-address-listp endp lw-psc-left-commutes lw-psc-left-distributes lw-psc-fold-constants lw-psc-times-negative lw-psc-negative-times lw-psc-zero-times lw-psc-minus-one lw-psc-double-negative lw-psc-add-cancel lw-psc-double lw-psc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))
(local (defthm lw-psc-active-append
 (implies (and (lw-polynomial-active-coverp coefficients anchor side count epsilon left)
               (lw-polynomial-active-coverp coefficients anchor side count epsilon right))
 (lw-polynomial-active-coverp coefficients anchor side count epsilon (append left right)))
 :hints (("Goal" :induct (append left right)
 :in-theory (union-theories
 '(append lw-polynomial-active-coverp endp lw-psc-left-commutes lw-psc-left-distributes lw-psc-fold-constants lw-psc-times-negative lw-psc-negative-times lw-psc-zero-times lw-psc-minus-one lw-psc-double-negative lw-psc-add-cancel lw-psc-double lw-psc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-polynomial-sublevel-cover-row-data
 (implies (and (posp count) (natp row) (< row count) (natp column) (natp remaining) (<= (+ column remaining) count))
 (and (lw-square-address-listp (lw-polynomial-sublevel-cover-row coefficients anchor side count epsilon row column remaining) count)
      (lw-polynomial-active-coverp coefficients anchor side count epsilon
       (lw-polynomial-sublevel-cover-row coefficients anchor side count epsilon row column remaining))
      (<= (len (lw-polynomial-sublevel-cover-row coefficients anchor side count epsilon row column remaining)) remaining)))
 :hints (("Goal" :induct (lw-polynomial-sublevel-cover-row coefficients anchor side count epsilon row column remaining)
 :in-theory (union-theories
 '(lw-polynomial-sublevel-cover-row lw-square-address-listp lw-polynomial-active-coverp len lw-psc-length-natural fold-consts-in-+ endp lw-psc-left-commutes lw-psc-left-distributes lw-psc-fold-constants lw-psc-times-negative lw-psc-negative-times lw-psc-zero-times lw-psc-minus-one lw-psc-double-negative lw-psc-add-cancel lw-psc-double lw-psc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))
 :rule-classes nil)

(defthm lw-polynomial-sublevel-cover-rows-data
 (implies (and (posp count) (natp row) (natp remaining) (<= (+ row remaining) count))
 (and (lw-square-address-listp (lw-polynomial-sublevel-cover-rows coefficients anchor side count epsilon row remaining) count)
      (lw-polynomial-active-coverp coefficients anchor side count epsilon
       (lw-polynomial-sublevel-cover-rows coefficients anchor side count epsilon row remaining))
      (<= (len (lw-polynomial-sublevel-cover-rows coefficients anchor side count epsilon row remaining)) (* remaining count))))
 :hints (("Goal" :induct (lw-polynomial-sublevel-cover-rows coefficients anchor side count epsilon row remaining)
 :in-theory (union-theories
 '(lw-polynomial-sublevel-cover-rows lw-psc-addresses-append lw-psc-active-append lw-psc-length-append lw-psc-length-natural lw-square-address-listp lw-polynomial-active-coverp len endp fold-consts-in-+ lw-psc-left-commutes lw-psc-left-distributes lw-psc-fold-constants lw-psc-times-negative lw-psc-negative-times lw-psc-zero-times lw-psc-minus-one lw-psc-double-negative lw-psc-add-cancel lw-psc-double lw-psc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
 (and stable-under-simplificationp
 '(:use ((:instance lw-polynomial-sublevel-cover-row-data (column 0) (remaining count))) :do-not-induct t)))
 :rule-classes nil)

(defthm lw-polynomial-sublevel-cover-data
 (implies (posp count)
 (and (lw-square-address-listp (lw-polynomial-sublevel-cover coefficients anchor side count epsilon) count)
      (lw-polynomial-active-coverp coefficients anchor side count epsilon
       (lw-polynomial-sublevel-cover coefficients anchor side count epsilon))
      (<= (len (lw-polynomial-sublevel-cover coefficients anchor side count epsilon)) (* count count))))
 :hints (("Goal" :use ((:instance lw-polynomial-sublevel-cover-rows-data (row 0) (remaining count)))
 :in-theory (union-theories
 '(lw-polynomial-sublevel-cover lw-psc-left-commutes lw-psc-left-distributes lw-psc-fold-constants lw-psc-times-negative lw-psc-negative-times lw-psc-zero-times lw-psc-minus-one lw-psc-double-negative lw-psc-add-cancel lw-psc-double lw-psc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(local (defthm lw-psc-row-member-data
 (implies (and (natp row) (natp column) (natp remaining)
 (member-equal address (lw-polynomial-sublevel-cover-row coefficients anchor side count epsilon row column remaining)))
 (and (consp address) (equal (car address) row) (natp (cdr address))
      (<= column (cdr address)) (< (cdr address) (+ column remaining))
      (lw-polynomial-cell-activep coefficients anchor side count epsilon row (cdr address))))
 :hints (("Goal" :induct (lw-polynomial-sublevel-cover-row coefficients anchor side count epsilon row column remaining)
 :in-theory (union-theories
 '(lw-polynomial-sublevel-cover-row member-equal fold-consts-in-+ endp lw-psc-left-commutes lw-psc-left-distributes lw-psc-fold-constants lw-psc-times-negative lw-psc-negative-times lw-psc-zero-times lw-psc-minus-one lw-psc-double-negative lw-psc-add-cancel lw-psc-double lw-psc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-psc-row-member-complete
 (implies (and (natp row) (natp column) (natp remaining) (natp target)
 (<= column target) (< target (+ column remaining))
 (lw-polynomial-cell-activep coefficients anchor side count epsilon row target))
 (member-equal (cons row target) (lw-polynomial-sublevel-cover-row coefficients anchor side count epsilon row column remaining)))
 :hints (("Goal" :induct (lw-polynomial-sublevel-cover-row coefficients anchor side count epsilon row column remaining)
 :in-theory (union-theories
 '(lw-polynomial-sublevel-cover-row member-equal fold-consts-in-+ endp lw-psc-left-commutes lw-psc-left-distributes lw-psc-fold-constants lw-psc-times-negative lw-psc-negative-times lw-psc-zero-times lw-psc-minus-one lw-psc-double-negative lw-psc-add-cancel lw-psc-double lw-psc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-psc-rows-member-data
 (implies (and (posp count) (natp row) (natp remaining)
 (member-equal address (lw-polynomial-sublevel-cover-rows coefficients anchor side count epsilon row remaining)))
 (and (consp address) (natp (car address)) (<= row (car address)) (< (car address) (+ row remaining))
      (natp (cdr address)) (< (cdr address) count)
      (lw-polynomial-cell-activep coefficients anchor side count epsilon (car address) (cdr address))))
 :hints (("Goal" :induct (lw-polynomial-sublevel-cover-rows coefficients anchor side count epsilon row remaining)
 :in-theory (union-theories
 '(lw-polynomial-sublevel-cover-rows lw-psc-member-append member-equal fold-consts-in-+ endp lw-psc-left-commutes lw-psc-left-distributes lw-psc-fold-constants lw-psc-times-negative lw-psc-negative-times lw-psc-zero-times lw-psc-minus-one lw-psc-double-negative lw-psc-add-cancel lw-psc-double lw-psc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
 (and stable-under-simplificationp
 '(:use ((:instance lw-psc-row-member-data (column 0) (remaining count))) :do-not-induct t)))
 :rule-classes nil))

(local (defthm lw-psc-rows-member-complete
 (implies (and (posp count) (natp row) (natp remaining) (natp target-row) (natp target-column)
 (<= row target-row) (< target-row (+ row remaining)) (< target-column count)
 (lw-polynomial-cell-activep coefficients anchor side count epsilon target-row target-column))
 (member-equal (cons target-row target-column)
 (lw-polynomial-sublevel-cover-rows coefficients anchor side count epsilon row remaining)))
 :hints (("Goal" :induct (lw-polynomial-sublevel-cover-rows coefficients anchor side count epsilon row remaining)
 :in-theory (union-theories
 '(lw-polynomial-sublevel-cover-rows lw-psc-member-append member-equal fold-consts-in-+ endp lw-psc-left-commutes lw-psc-left-distributes lw-psc-fold-constants lw-psc-times-negative lw-psc-negative-times lw-psc-zero-times lw-psc-minus-one lw-psc-double-negative lw-psc-add-cancel lw-psc-double lw-psc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
 (and stable-under-simplificationp
 '(:cases ((equal target-row row))
 :use ((:instance lw-psc-row-member-complete (column 0) (remaining count) (target target-column))) :do-not-induct t)))
 :rule-classes nil))

(defthm lw-polynomial-sublevel-cover-member-data
 (implies (and (posp count) (member-equal address (lw-polynomial-sublevel-cover coefficients anchor side count epsilon)))
 (and (consp address) (natp (car address)) (< (car address) count)
      (natp (cdr address)) (< (cdr address) count)
      (lw-polynomial-cell-activep coefficients anchor side count epsilon (car address) (cdr address))))
 :hints (("Goal" :use ((:instance lw-psc-rows-member-data (row 0) (remaining count)))
 :in-theory (union-theories
 '(lw-polynomial-sublevel-cover lw-psc-left-commutes lw-psc-left-distributes lw-psc-fold-constants lw-psc-times-negative lw-psc-negative-times lw-psc-zero-times lw-psc-minus-one lw-psc-double-negative lw-psc-add-cancel lw-psc-double lw-psc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-polynomial-sublevel-cover-member
 (implies (and (posp count) (natp row) (< row count) (natp column) (< column count))
 (iff (member-equal (cons row column) (lw-polynomial-sublevel-cover coefficients anchor side count epsilon))
      (lw-polynomial-cell-activep coefficients anchor side count epsilon row column)))
 :hints (("Goal"
 :use ((:instance lw-psc-rows-member-data (row 0) (remaining count) (address (cons row column)))
       (:instance lw-psc-rows-member-complete (row 0) (remaining count) (target-row row) (target-column column)))
 :in-theory (union-theories
 '(lw-polynomial-sublevel-cover iff lw-psc-left-commutes lw-psc-left-distributes lw-psc-fold-constants lw-psc-times-negative lw-psc-negative-times lw-psc-zero-times lw-psc-minus-one lw-psc-double-negative lw-psc-add-cancel lw-psc-double lw-psc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-square-cover-member-contains
 (implies (and (member-equal address addresses)
 (lw-square-cell-containsp anchor side count (car address) (cdr address) point))
 (lw-square-cover-containsp anchor side count point addresses))
 :hints (("Goal" :induct (member-equal address addresses)
 :in-theory (union-theories
 '(member-equal lw-square-cover-containsp endp lw-psc-left-commutes lw-psc-left-distributes lw-psc-fold-constants lw-psc-times-negative lw-psc-negative-times lw-psc-zero-times lw-psc-minus-one lw-psc-double-negative lw-psc-add-cancel lw-psc-double lw-psc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-square-cover-in-square
 (implies (lw-square-cover-containsp anchor side count point addresses)
 (lw-square-containsp anchor side point))
 :hints (("Goal" :induct (lw-square-cover-containsp anchor side count point addresses)
 :in-theory (union-theories
 '(lw-square-cover-containsp endp lw-psc-left-commutes lw-psc-left-distributes lw-psc-fold-constants lw-psc-times-negative lw-psc-negative-times lw-psc-zero-times lw-psc-minus-one lw-psc-double-negative lw-psc-add-cancel lw-psc-double lw-psc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
 (and stable-under-simplificationp
 '(:use ((:instance lw-square-cell-in-square (row (caar addresses)) (column (cdar addresses)))) :do-not-induct t))))

(defthm lw-polynomial-active-cover-value-bound
 (implies (and (lw-complex-coefficientsp coefficients) (rationalp epsilon) (<= 0 epsilon)
 (lw-polynomial-active-coverp coefficients anchor side count epsilon addresses)
 (lw-square-cover-containsp anchor side count point addresses))
 (lw-complex-diskp (lw-complex-polynomial coefficients point 0)
 (+ epsilon (* 2 (lw-polynomial-cell-variation coefficients anchor side count)))))
 :hints (("Goal" :induct (lw-square-cover-containsp anchor side count point addresses)
 :in-theory (union-theories
 '(lw-square-cover-containsp lw-polynomial-active-coverp endp lw-psc-left-commutes lw-psc-left-distributes lw-psc-fold-constants lw-psc-times-negative lw-psc-negative-times lw-psc-zero-times lw-psc-minus-one lw-psc-double-negative lw-psc-add-cancel lw-psc-double lw-psc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
 (and stable-under-simplificationp
 '(:use ((:instance lw-polynomial-active-cell-value-bound (row (caar addresses)) (column (cdar addresses)))) :do-not-induct t))))

(defthm lw-polynomial-sublevel-cover-complete
 (implies (and (lw-complex-coefficientsp coefficients) (lw-square-containsp anchor side point)
 (posp count) (rationalp epsilon) (<= 0 epsilon)
 (lw-complex-diskp (lw-complex-polynomial coefficients point 0) epsilon))
 (and (member-equal (lw-square-cell-address anchor side count point)
                   (lw-polynomial-sublevel-cover coefficients anchor side count epsilon))
      (lw-square-cover-containsp anchor side count point
                   (lw-polynomial-sublevel-cover coefficients anchor side count epsilon))))
 :hints (("Goal"
 :use (lw-square-cell-address-cover
       (:instance lw-polynomial-small-value-forces-active
        (row (car (lw-square-cell-address anchor side count point))) (column (cdr (lw-square-cell-address anchor side count point))))
       (:instance lw-polynomial-sublevel-cover-member
        (row (car (lw-square-cell-address anchor side count point))) (column (cdr (lw-square-cell-address anchor side count point))))
       (:instance lw-square-cover-member-contains
        (address (lw-square-cell-address anchor side count point))
        (addresses (lw-polynomial-sublevel-cover coefficients anchor side count epsilon))))
 :in-theory (union-theories
 '(lw-square-cell-address  lw-psc-left-commutes lw-psc-left-distributes lw-psc-fold-constants lw-psc-times-negative lw-psc-negative-times lw-psc-zero-times lw-psc-minus-one lw-psc-double-negative lw-psc-add-cancel lw-psc-double lw-psc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-polynomial-sublevel-cover-value-bound
 (implies (and (lw-complex-coefficientsp coefficients) (posp count) (rationalp epsilon) (<= 0 epsilon)
 (lw-square-cover-containsp anchor side count point
 (lw-polynomial-sublevel-cover coefficients anchor side count epsilon)))
 (lw-complex-diskp (lw-complex-polynomial coefficients point 0)
 (+ epsilon (* 2 (lw-polynomial-cell-variation coefficients anchor side count)))))
 :hints (("Goal" :use (lw-polynomial-sublevel-cover-data
       (:instance lw-polynomial-active-cover-value-bound
        (addresses (lw-polynomial-sublevel-cover coefficients anchor side count epsilon))))
 :in-theory (union-theories
 '( lw-psc-left-commutes lw-psc-left-distributes lw-psc-fold-constants lw-psc-times-negative lw-psc-negative-times lw-psc-zero-times lw-psc-minus-one lw-psc-double-negative lw-psc-add-cancel lw-psc-double lw-psc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
