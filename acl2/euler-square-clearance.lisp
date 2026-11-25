; Generated nonzero charts and denominator bounds outside a computed Euler cover.
(in-package "ACL2")
(include-book "euler-square-cover")
(include-book "euler-nonzero-neighborhood")
(local (in-theory (disable lw-complexp lw-complex-diskp lw-complex-l1 lw-complex-reciprocal lw-complex-norm-square
 lw-complex-euler-continuation-value lw-euler-square-domainp lw-square-containsp lw-square-cover-containsp
 lw-euler-square-cover lw-euler-square-cover-count lw-euler-value-clearance-check lw-euler-value-clearance-size
 lw-euler-value-clearance-lower lw-euler-neighborhood-radius)))
(local (defthm lw-esx-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-esx-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-esx-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-esx-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-esx-times-negative (a b) (b a)))
                 :in-theory (disable lw-esx-times-negative)))))

(local (defthm lw-esx-zero-times (equal (* 0 a) 0)))

(local (defthm lw-esx-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-esx-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-esx-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-esx-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-esx-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-esx-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-esx-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-esx-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-esx-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-esx-left-commutes)))))
(defun lw-euler-square-uncoveredp (rate height anchor side width error point)
 (and (lw-euler-square-domainp rate height anchor side) (lw-square-containsp anchor side point)
      (rationalp width) (< 0 width) (rationalp error) (< 0 error)
      (not (lw-square-cover-containsp anchor side
       (lw-euler-square-cover-count rate height anchor side width error) point
       (lw-euler-square-cover rate height anchor side width error)))))
(defun lw-euler-square-regular-radius (rate height anchor side width error point)
 (declare (ignore anchor side width))
 (lw-euler-neighborhood-radius (+ rate (car point)) (+ height (cdr point))
                              (/ (+ rate (car point)) 2) (/ error 64)))
(local (in-theory (disable lw-euler-square-uncoveredp lw-euler-square-regular-radius)))

(local (defthm lw-esx-not-small-l1
 (implies (and (lw-complexp value) (rationalp error) (< 0 error)
 (not (lw-complex-diskp value (/ error 2))))
 (< (/ error 2) (lw-complex-l1 value)))
 :hints (("Goal"
 :use ((:instance lw-complex-l1-bound (point value))
       (:instance lw-complex-disk-enlarge (point value) (radius (lw-complex-l1 value)) (cap (/ error 2))))
 :in-theory (union-theories
 '( lw-esx-left-commutes lw-esx-left-distributes lw-esx-fold-constants lw-esx-times-negative lw-esx-negative-times lw-esx-zero-times lw-esx-minus-one lw-esx-double-negative lw-esx-add-cancel lw-esx-double lw-esx-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)) :rule-classes nil))

(defthm lw-euler-square-uncovered-check
 (implies (lw-euler-square-uncoveredp rate height anchor side width error point)
 (and (lw-euler-value-clearance-check (+ rate (car point)) (+ height (cdr point)) (/ error 64))
      (<= (/ error 8)
       (lw-euler-value-clearance-lower (+ rate (car point)) (+ height (cdr point)) (/ error 64)))))
 :hints (("Goal"
 :use ((:instance lw-euler-square-cover-complement (value-error (/ error 64)))
       lw-euler-square-point-data
       (:instance lw-complex-euler-continuation-value-rational
        (rate (+ rate (car point))) (height (+ height (cdr point))) (error (/ error 64)))
       (:instance lw-esx-not-small-l1
        (value (lw-complex-euler-continuation-value (+ rate (car point)) (+ height (cdr point)) (/ error 64)))))
 :in-theory (union-theories
 '(lw-euler-square-uncoveredp lw-euler-value-clearance-check lw-euler-value-clearance-size lw-euler-value-clearance-lower lw-esx-left-commutes lw-esx-left-distributes lw-esx-fold-constants lw-esx-times-negative lw-esx-negative-times lw-esx-zero-times lw-esx-minus-one lw-esx-double-negative lw-esx-add-cancel lw-esx-double lw-esx-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(local (defthm lw-esx-square-order
 (implies (and (rationalp a) (rationalp b) (<= 0 a) (<= a b))
 (<= (* a a) (* b b)))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defthm lw-euler-square-uncovered-denominator-clearance
 (implies (and (lw-euler-square-uncoveredp rate height anchor side width error point)
 (rationalp request) (< 0 request) (<= request (/ error 32)))
 (let ((value (lw-complex-euler-continuation-value (+ rate (car point)) (+ height (cdr point)) request)))
 (and (lw-complexp value) (not (equal value (cons 0 0)))
      (<= (* (/ error 8) (/ error 8)) (lw-complex-norm-square value))
      (lw-complex-diskp (lw-complex-reciprocal value) (/ (/ error 8))))))
 :hints (("Goal"
 :use (lw-euler-square-uncovered-check
       (:instance lw-euler-value-clearance-data
        (rate (+ rate (car point))) (height (+ height (cdr point))) (anchor-error (/ error 64)))
       (:instance lw-complex-euler-value-clearance
        (rate (+ rate (car point))) (height (+ height (cdr point))) (anchor-error (/ error 64)))
       (:instance lw-esx-square-order (a (/ error 8))
        (b (lw-euler-value-clearance-lower (+ rate (car point)) (+ height (cdr point)) (/ error 64))))
       (:instance lw-complex-reciprocal-disk-bound
        (point (lw-complex-euler-continuation-value (+ rate (car point)) (+ height (cdr point)) request))
        (lower (/ error 8))))
 :in-theory (union-theories
 '(lw-euler-square-uncoveredp lw-esx-left-commutes lw-esx-left-distributes lw-esx-fold-constants lw-esx-times-negative lw-esx-negative-times lw-esx-zero-times lw-esx-minus-one lw-esx-double-negative lw-esx-add-cancel lw-esx-double lw-esx-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-square-regular-radius-data
 (implies (lw-euler-square-uncoveredp rate height anchor side width error point)
 (let ((radius (lw-euler-square-regular-radius rate height anchor side width error point)))
 (and (rationalp radius) (< 0 radius) (<= radius 1) (<= radius (/ (+ rate (car point)) 4)))))
 :hints (("Goal"
 :use (lw-euler-square-uncovered-check lw-euler-square-point-data
       (:instance lw-euler-neighborhood-data
        (rate (+ rate (car point))) (height (+ height (cdr point))) (outer-radius (/ (+ rate (car point)) 2))
        (anchor-error (/ error 64))))
 :in-theory (union-theories
 '(lw-euler-square-domainp lw-square-containsp lw-complexp lw-euler-square-uncoveredp lw-euler-square-regular-radius lw-esx-left-commutes lw-esx-left-distributes lw-esx-fold-constants lw-esx-times-negative lw-esx-negative-times lw-esx-zero-times lw-esx-minus-one lw-esx-double-negative lw-esx-add-cancel lw-esx-double lw-esx-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-square-regular-shifted-check
 (implies (and (lw-euler-square-uncoveredp rate height anchor side width error point)
 (lw-complex-diskp offset (lw-euler-square-regular-radius rate height anchor side width error point)))
 (and (lw-euler-value-clearance-check (+ rate (car point) (car offset)) (+ height (cdr point) (cdr offset)) (/ error 128))
      (<= (/ error 16)
       (lw-euler-value-clearance-lower (+ rate (car point) (car offset)) (+ height (cdr point) (cdr offset)) (/ error 128)))))
 :hints (("Goal"
 :use (lw-euler-square-uncovered-check lw-euler-square-point-data
       (:instance lw-euler-neighborhood-shifted-check
        (rate (+ rate (car point))) (height (+ height (cdr point))) (outer-radius (/ (+ rate (car point)) 2))
        (anchor-error (/ error 64)) (point offset)))
 :in-theory (union-theories
 '(lw-euler-square-domainp lw-square-containsp lw-complexp lw-euler-square-uncoveredp lw-euler-square-regular-radius lw-euler-value-clearance-lower lw-esx-left-commutes lw-esx-left-distributes lw-esx-fold-constants lw-esx-times-negative lw-esx-negative-times lw-esx-zero-times lw-esx-minus-one lw-esx-double-negative lw-esx-add-cancel lw-esx-double lw-esx-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))
