(in-package "ACL2")

(include-book "ray-power-samples")

; Assemble annulus and step certificates along concatenated and reversed
; finite paths. Joins use the actual last and first values.

(local (defthm lw-rpa-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-rpa-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-rpa-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-rpa-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-rpa-times-negative (a b) (b a)))
                 :in-theory (disable lw-rpa-times-negative)))))

(local (defthm lw-rpa-zero-times (equal (* 0 a) 0)))

(local (defthm lw-rpa-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-rpa-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-rpa-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-rpa-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-rpa-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-rpa-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-rpa-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-rpa-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-rpa-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-rpa-left-commutes)))))

(defun lw-ray-step-join-check (left right delta)
 (or (endp left) (endp right)
     (lw-complex-diskp (lw-complex-sub (car right) (lw-ray-row-last left)) delta)))

(defthm lw-ray-annulus-append
 (implies (and (lw-ray-annulus-pointsp left lower upper)
               (lw-ray-annulus-pointsp right lower upper))
  (lw-ray-annulus-pointsp (append left right) lower upper))
 :hints (("Goal" :induct (append left right)
          :in-theory (union-theories
 '(fold-consts-in-+ append lw-ray-annulus-pointsp lw-rpa-left-commutes lw-rpa-left-distributes lw-rpa-fold-constants lw-rpa-times-negative lw-rpa-negative-times lw-rpa-zero-times lw-rpa-minus-one lw-rpa-double-negative lw-rpa-add-cancel lw-rpa-double lw-rpa-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-ray-annulus-reverse
 (implies (lw-ray-annulus-pointsp points lower upper)
  (lw-ray-annulus-pointsp (lw-ray-reverse-points points) lower upper))
 :hints (("Goal" :induct (lw-ray-reverse-points points)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-reverse-points lw-ray-annulus-pointsp lw-ray-annulus-append lw-rpa-left-commutes lw-rpa-left-distributes lw-rpa-fold-constants lw-rpa-times-negative lw-rpa-negative-times lw-rpa-zero-times lw-rpa-minus-one lw-rpa-double-negative lw-rpa-add-cancel lw-rpa-double lw-rpa-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-rpa-last-tail
 (implies (and (consp points) (consp (cdr points)))
  (equal (lw-ray-row-last points) (lw-ray-row-last (cdr points))))
 :hints (("Goal" :expand ((lw-ray-path-last (car points) (cdr points)))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-row-last lw-rpa-left-commutes lw-rpa-left-distributes lw-rpa-fold-constants lw-rpa-times-negative lw-rpa-negative-times lw-rpa-zero-times lw-rpa-minus-one lw-rpa-double-negative lw-rpa-add-cancel lw-rpa-double lw-rpa-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-rpa-last-single
 (implies (and (consp points) (equal (cdr points) nil))
  (equal (lw-ray-row-last points) (car points)))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-row-last lw-ray-path-last lw-rpa-left-commutes lw-rpa-left-distributes lw-rpa-fold-constants lw-rpa-times-negative lw-rpa-negative-times lw-rpa-zero-times lw-rpa-minus-one lw-rpa-double-negative lw-rpa-add-cancel lw-rpa-double lw-rpa-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-rpa-append-head
 (and (equal (consp (append left right)) (or (consp left) (consp right)))
      (equal (car (append left right)) (if (consp left) (car left) (car right)))
      (implies (consp left) (equal (cdr (append left right)) (append (cdr left) right))))
 :hints (("Goal" :expand ((append left right)) :in-theory (union-theories
 '(fold-consts-in-+ lw-rpa-left-commutes lw-rpa-left-distributes lw-rpa-fold-constants lw-rpa-times-negative lw-rpa-negative-times lw-rpa-zero-times lw-rpa-minus-one lw-rpa-double-negative lw-rpa-add-cancel lw-rpa-double lw-rpa-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-ray-path-step-append
 (implies (and (lw-ray-pointsp left) (lw-ray-pointsp right)
               (lw-ray-path-step-check left delta) (lw-ray-path-step-check right delta)
               (lw-ray-step-join-check left right delta))
  (lw-ray-path-step-check (append left right) delta))
 :hints (("Goal" :induct (append left right)
          :in-theory (union-theories
 '(fold-consts-in-+ append lw-rpa-append-head lw-ray-path-step-check lw-ray-step-join-check lw-ray-pointsp lw-rpa-last-tail lw-rpa-last-single lw-rpa-left-commutes lw-rpa-left-distributes lw-rpa-fold-constants lw-rpa-times-negative lw-rpa-negative-times lw-rpa-zero-times lw-rpa-minus-one lw-rpa-double-negative lw-rpa-add-cancel lw-rpa-double lw-rpa-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-ray-path-step-reverse
 (implies (and (lw-ray-pointsp points) (rationalp delta) (<= 0 delta)
               (lw-ray-path-step-check points delta))
  (lw-ray-path-step-check (lw-ray-reverse-points points) delta))
 :hints (("Goal" :induct (lw-ray-reverse-points points)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-reverse-points lw-ray-pointsp lw-ray-path-step-check lw-rpa-left-commutes lw-rpa-left-distributes lw-rpa-fold-constants lw-rpa-times-negative lw-rpa-negative-times lw-rpa-zero-times lw-rpa-minus-one lw-rpa-double-negative lw-rpa-add-cancel lw-rpa-double lw-rpa-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) )
         (and stable-under-simplificationp
          '(:use ((:instance lw-ray-path-step-append
                    (left (lw-ray-reverse-points (cdr points))) (right (list (car points))))
                  (:instance lw-complex-difference-symmetric
                    (left (cadr points)) (right (car points)) (radius delta)))
            :in-theory (union-theories
 '(fold-consts-in-+ append (:executable-counterpart lw-ray-reverse-points) lw-ray-pointsp lw-ray-path-step-check lw-ray-step-join-check lw-ray-reverse-points-data lw-ray-reverse-points-endpoints lw-rpa-left-commutes lw-rpa-left-distributes lw-rpa-fold-constants lw-rpa-times-negative lw-rpa-negative-times lw-rpa-zero-times lw-rpa-minus-one lw-rpa-double-negative lw-rpa-add-cancel lw-rpa-double lw-rpa-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

