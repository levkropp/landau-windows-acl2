; Rational orientation and half-plane arithmetic for finite winding counts.
(in-package "ACL2")
(include-book "complex-geometric")
(local (in-theory (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-scale
 lw-complex-mul lw-complex-diskp lw-diskp lw-complex-norm-square)))
(local (defthm lw-cor-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-cor-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-cor-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-cor-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-cor-times-negative (a b) (b a)))
                 :in-theory (disable lw-cor-times-negative)))))

(local (defthm lw-cor-zero-times (equal (* 0 a) 0)))

(local (defthm lw-cor-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-cor-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-cor-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-cor-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-cor-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-cor-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-cor-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cor-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cor-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-cor-left-commutes)))))
(defun lw-complex-det (a b)
 (- (* (car a) (cdr b)) (* (cdr a) (car b))))
(defun lw-complex-dot (a b)
 (+ (* (car a) (car b)) (* (cdr a) (cdr b))))
(defun lw-complex-positive-halfplanep (anchor point)
 (and (lw-complexp anchor) (lw-complexp point) (< 0 (lw-complex-dot anchor point))))

(local (in-theory (disable lw-complex-det lw-complex-dot lw-complex-positive-halfplanep)))

(defthm lw-complex-orientation-rational
 (implies (and (lw-complexp a) (lw-complexp b))
 (and (rationalp (lw-complex-det a b)) (rationalp (lw-complex-dot a b))))
 :hints (("Goal" :in-theory (union-theories
 '(lw-complexp lw-complex-det lw-complex-dot lw-cor-left-commutes lw-cor-left-distributes lw-cor-fold-constants lw-cor-times-negative lw-cor-negative-times lw-cor-zero-times lw-cor-minus-one lw-cor-double-negative lw-cor-add-cancel lw-cor-double lw-cor-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-complex-det-reverse
 (implies (and (lw-complexp a) (lw-complexp b))
 (equal (lw-complex-det b a) (- (lw-complex-det a b))))
 :hints (("Goal" :in-theory (union-theories
 '(lw-complexp lw-complex-det lw-cor-left-commutes lw-cor-left-distributes lw-cor-fold-constants lw-cor-times-negative lw-cor-negative-times lw-cor-zero-times lw-cor-minus-one lw-cor-double-negative lw-cor-add-cancel lw-cor-double lw-cor-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-complex-dot-commutative
 (implies (and (lw-complexp a) (lw-complexp b))
 (equal (lw-complex-dot b a) (lw-complex-dot a b)))
 :hints (("Goal" :in-theory (union-theories
 '(lw-complexp lw-complex-dot lw-cor-left-commutes lw-cor-left-distributes lw-cor-fold-constants lw-cor-times-negative lw-cor-negative-times lw-cor-zero-times lw-cor-minus-one lw-cor-double-negative lw-cor-add-cancel lw-cor-double lw-cor-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-complex-dot-self
 (implies (lw-complexp point)
 (equal (lw-complex-dot point point) (lw-complex-norm-square point)))
 :hints (("Goal" :in-theory (union-theories
 '(lw-complexp lw-complex-dot lw-complex-norm-square lw-cor-left-commutes lw-cor-left-distributes lw-cor-fold-constants lw-cor-times-negative lw-cor-negative-times lw-cor-zero-times lw-cor-minus-one lw-cor-double-negative lw-cor-add-cancel lw-cor-double lw-cor-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-complex-det-self
 (implies (lw-complexp point) (equal (lw-complex-det point point) 0))
 :hints (("Goal" :in-theory (union-theories
 '(lw-complexp lw-complex-det lw-cor-left-commutes lw-cor-left-distributes lw-cor-fold-constants lw-cor-times-negative lw-cor-negative-times lw-cor-zero-times lw-cor-minus-one lw-cor-double-negative lw-cor-add-cancel lw-cor-double lw-cor-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-complex-det-y-relation
 (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c))
 (equal (+ (* (cdr a) (lw-complex-det b c))
           (* (cdr b) (lw-complex-det c a))
           (* (cdr c) (lw-complex-det a b))) 0))
 :hints (("Goal" :in-theory (union-theories
 '(lw-complexp lw-complex-det lw-cor-left-commutes lw-cor-left-distributes lw-cor-fold-constants lw-cor-times-negative lw-cor-negative-times lw-cor-zero-times lw-cor-minus-one lw-cor-double-negative lw-cor-add-cancel lw-cor-double lw-cor-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))
 :rule-classes nil)

(defthm lw-complex-det-dot-relation
 (implies (and (lw-complexp h) (lw-complexp a) (lw-complexp b) (lw-complexp c))
 (equal (+ (* (lw-complex-dot h a) (lw-complex-det b c))
           (* (lw-complex-dot h b) (lw-complex-det c a))
           (* (lw-complex-dot h c) (lw-complex-det a b))) 0))
 :hints (("Goal" :in-theory (union-theories
 '(lw-complexp lw-complex-det lw-complex-dot lw-cor-left-commutes lw-cor-left-distributes lw-cor-fold-constants lw-cor-times-negative lw-cor-negative-times lw-cor-zero-times lw-cor-minus-one lw-cor-double-negative lw-cor-add-cancel lw-cor-double lw-cor-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))
 :rule-classes nil)

(defthm lw-complex-dot-norm-difference
 (implies (and (lw-complexp a) (lw-complexp b))
 (equal (* 2 (lw-complex-dot a b))
 (+ (lw-complex-norm-square a) (lw-complex-norm-square b) (- (lw-complex-norm-square (lw-complex-sub a b))))))
 :hints (("Goal" :in-theory (union-theories
 '(lw-complexp lw-complex-det lw-complex-dot lw-complex-norm-square lw-complex-sub lw-cor-left-commutes lw-cor-left-distributes lw-cor-fold-constants lw-cor-times-negative lw-cor-negative-times lw-cor-zero-times lw-cor-minus-one lw-cor-double-negative lw-cor-add-cancel lw-cor-double lw-cor-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))
 :rule-classes nil)

(defthm lw-complex-disk-positive-dot
 (implies (and (lw-complexp anchor) (rationalp radius)
 (< (* radius radius) (lw-complex-norm-square anchor))
 (lw-complex-diskp (lw-complex-sub point anchor) radius) (lw-complexp point))
 (< 0 (lw-complex-dot anchor point)))
 :hints (("Goal"
 :use ((:instance lw-complex-disk-norm-square (point (lw-complex-sub point anchor)))
       (:instance lw-complex-norm-square-valid)
       (:instance lw-complex-dot-norm-difference (a point) (b anchor))
       (:instance lw-complex-dot-commutative (a point) (b anchor)))
 :in-theory (union-theories
 '( lw-cor-left-commutes lw-cor-left-distributes lw-cor-fold-constants lw-cor-times-negative lw-cor-negative-times lw-cor-zero-times lw-cor-minus-one lw-cor-double-negative lw-cor-add-cancel lw-cor-double lw-cor-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-complex-disk-positive-halfplane
 (implies (and (lw-complexp anchor) (lw-complexp point) (rationalp radius)
 (< (* radius radius) (lw-complex-norm-square anchor))
 (lw-complex-diskp (lw-complex-sub point anchor) radius))
 (lw-complex-positive-halfplanep anchor point))
 :hints (("Goal" :use (lw-complex-disk-positive-dot)
 :in-theory (union-theories
 '(lw-complex-positive-halfplanep lw-cor-left-commutes lw-cor-left-distributes lw-cor-fold-constants lw-cor-times-negative lw-cor-negative-times lw-cor-zero-times lw-cor-minus-one lw-cor-double-negative lw-cor-add-cancel lw-cor-double lw-cor-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

