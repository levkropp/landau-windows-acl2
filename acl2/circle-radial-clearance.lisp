(in-package "ACL2")

(include-book "circle-finite-radius-selection")

(defun lw-circle-radial-clearance (radius gap)
  (/ gap (+ 1 gap (* 4 radius))))

(local (defthm lw-crg-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-crg-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-crg-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-crg-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-crg-times-negative (a b) (b a)))
                 :in-theory (disable lw-crg-times-negative)))))

(local (defthm lw-crg-zero-times (equal (* 0 a) 0)))

(local (defthm lw-crg-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-crg-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-crg-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-crg-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-crg-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-crg-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-crg-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-crg-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-crg-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-crg-left-commutes)))))

(defthm lw-circle-radial-clearance-budget
   (implies (and (rationalp radius) (< 0 radius)
                 (rationalp gap) (< 0 gap))
            (let ((delta (lw-circle-radial-clearance radius gap)))
              (and (rationalp delta) (< 0 delta) (< delta 1)
                   (< (* (+ radius delta) (+ radius delta)) (+ (* radius radius) gap))
                   (implies (<= gap (* radius radius))
                            (and (< (* 4 delta) radius)
                                 (<= (- (* radius radius) gap) (* (- radius (* 2 delta)) (- radius (* 2 delta))))
                                 (< (* (- radius delta) (- radius delta)) (* radius radius)))))))
   :hints (("Goal"
            :use ((:instance lw-crg-inverse-factor (divisor (+ 1 gap (* 4 radius))) (coefficient gap))
                  (:instance lw-crg-positive-product (a (+ gap (* 4 radius))) (b (lw-circle-radial-clearance radius gap)))
                  (:instance lw-crg-positive-product (a (+ gap (* 2 radius))) (b (lw-circle-radial-clearance radius gap)))
                  (:instance lw-crg-positive-product (a (+ 1 gap)) (b (lw-circle-radial-clearance radius gap)))
                  (:instance lw-crg-positive-product (a radius) (b (- (* 4 (lw-circle-radial-clearance radius gap)) radius)))
                  (:instance lw-crg-positive-product (a (lw-circle-radial-clearance radius gap)) (b (- (* 2 radius) (lw-circle-radial-clearance radius gap))))
                  (:instance lw-crg-multiply-order (a 0) (b (lw-circle-radial-clearance radius gap)) (factor (lw-circle-radial-clearance radius gap)))
                  (:instance lw-crg-multiply-order (a (lw-circle-radial-clearance radius gap)) (b 1) (factor (lw-circle-radial-clearance radius gap))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-radial-clearance lw-reciprocal-positive
              lw-crg-left-commutes lw-crg-left-distributes lw-crg-fold-constants
              lw-crg-times-negative lw-crg-negative-times lw-crg-zero-times
              lw-crg-minus-one lw-crg-double-negative lw-crg-add-cancel lw-crg-double lw-crg-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t :nonlinearp t))
   :rule-classes nil)

(local
 (defthm lw-crg-translate
   (implies (and (lw-complexp root) (lw-complexp point))
            (and (equal (lw-complex-add root (lw-complex-sub point root)) point)
                 (equal (lw-complex-sub point (lw-complex-sub point root)) root)))
   :hints (("Goal" :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complexp lw-complex-add lw-complex-sub
              lw-crg-left-commutes lw-crg-left-distributes lw-crg-fold-constants
              lw-crg-times-negative lw-crg-negative-times lw-crg-zero-times
              lw-crg-minus-one lw-crg-double-negative lw-crg-add-cancel lw-crg-double lw-crg-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defthm lw-crg-offset-cancel
   (implies (and (rationalp radius) (rationalp delta))
            (equal (+ radius delta (- (* 2 delta))) (+ radius (- delta))))
   :hints (("Goal" :nonlinearp t))
   :rule-classes nil))

(defthm lw-circle-radial-clearance-valid
  (implies (and (lw-complexp root) (lw-complexp point)
                (rationalp radius) (< 0 radius) (rationalp gap) (< 0 gap)
                (equal (lw-complex-norm-square point) (* radius radius))
                (or (<= (+ (lw-complex-norm-square root) gap) (* radius radius))
                    (<= (+ (* radius radius) gap) (lw-complex-norm-square root))))
           (and (rationalp (lw-circle-radial-clearance radius gap)) (< 0 (lw-circle-radial-clearance radius gap))
                (< (* (lw-circle-radial-clearance radius gap) (lw-circle-radial-clearance radius gap)) (lw-complex-norm-square (lw-complex-sub point root)))))
  :hints (("Goal"
           :cases ((<= (lw-complex-norm-square (lw-complex-sub point root)) (* (lw-circle-radial-clearance radius gap) (lw-circle-radial-clearance radius gap))))
           :use (lw-circle-radial-clearance-budget lw-crg-translate
                 (:instance lw-crg-offset-cancel (delta (lw-circle-radial-clearance radius gap)))
                 (:instance lw-complex-norm-square-valid (point root))
                 (:instance lw-complex-ring-rational (left point) (right root))
                 (:instance lw-complex-disk-norm-square (point (lw-complex-sub point root)) (radius (lw-circle-radial-clearance radius gap)))
                 (:instance lw-complex-disk-norm-square (radius radius))
                 (:instance lw-complex-disk-norm-square (point root) (radius (+ radius (lw-circle-radial-clearance radius gap))))
                 (:instance lw-complex-disk-norm-square (point root) (radius (- radius (* 2 (lw-circle-radial-clearance radius gap)))))
                 (:instance lw-complex-disk-norm-square (radius (- radius (lw-circle-radial-clearance radius gap))))
                 (:instance lw-complex-add-disk
                   (left root) (right (lw-complex-sub point root)) (radius (- radius (* 2 (lw-circle-radial-clearance radius gap)))) (other-radius (lw-circle-radial-clearance radius gap)))
                 (:instance lw-complex-sub-disk
                   (left point) (right (lw-complex-sub point root)) (radius radius) (other-radius (lw-circle-radial-clearance radius gap))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)

              lw-crg-left-commutes lw-crg-left-distributes lw-crg-fold-constants
              lw-crg-times-negative lw-crg-negative-times lw-crg-zero-times
              lw-crg-minus-one lw-crg-double-negative lw-crg-add-cancel lw-crg-double lw-crg-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t :nonlinearp t))
  :rule-classes nil)

(local
 (defthm lw-crg-listed-root
   (implies (and (lw-circle-radial-bracket-clear roots radius radius gap)
                 (member-equal root roots))
            (or (<= (+ (lw-complex-norm-square root) gap) (* radius radius))
                (<= (+ (* radius radius) gap) (lw-complex-norm-square root))))
   :hints (("Goal" :induct (lw-circle-radial-bracket-clear roots radius radius gap)
                   :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-radial-bracket-clear member-equal endp
              lw-crg-left-commutes lw-crg-left-distributes lw-crg-fold-constants
              lw-crg-times-negative lw-crg-negative-times lw-crg-zero-times
              lw-crg-minus-one lw-crg-double-negative lw-crg-add-cancel lw-crg-double lw-crg-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                   :do-not '(generalize fertilize)))
   :rule-classes nil))

(defthm lw-circle-radial-clearance-for-root
  (implies (and (lw-complexp root) (lw-complexp point)
                (rationalp radius) (< 0 radius) (rationalp gap) (< 0 gap)
                (equal (lw-complex-norm-square point) (* radius radius))
                (lw-circle-radial-bracket-clear roots radius radius gap)
                (member-equal root roots))
           (< (* (lw-circle-radial-clearance radius gap) (lw-circle-radial-clearance radius gap)) (lw-complex-norm-square (lw-complex-sub point root))))
  :hints (("Goal" :use (lw-crg-listed-root lw-circle-radial-clearance-valid)
                   :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)

              lw-crg-left-commutes lw-crg-left-distributes lw-crg-fold-constants
              lw-crg-times-negative lw-crg-negative-times lw-crg-zero-times
              lw-crg-minus-one lw-crg-double-negative lw-crg-add-cancel lw-crg-double lw-crg-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                   :do-not-induct t))
  :rule-classes nil)
