(in-package "ACL2")

(include-book "ray-axis-paths")
(include-book "ray-path-assembly")

; Translation of finite paths for the linear factor z-root.

(local (defthm lw-rtr-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-rtr-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-rtr-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-rtr-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-rtr-times-negative (a b) (b a)))
                 :in-theory (disable lw-rtr-times-negative)))))

(local (defthm lw-rtr-zero-times (equal (* 0 a) 0)))

(local (defthm lw-rtr-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-rtr-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-rtr-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-rtr-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-rtr-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-rtr-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-rtr-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-rtr-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-rtr-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-rtr-left-commutes)))))
(defun lw-ray-translate-points (root points)
 (declare (xargs :measure (acl2-count points) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (endp points) nil
  (cons (lw-complex-sub (car points) root) (lw-ray-translate-points root (cdr points)))))

(defthm lw-ray-translate-points-data
 (implies (and (lw-complexp root) (lw-ray-pointsp points))
  (and (lw-ray-pointsp (lw-ray-translate-points root points))
       (equal (len (lw-ray-translate-points root points)) (len points))
       (equal (consp (lw-ray-translate-points root points)) (consp points))))
 :hints (("Goal" :induct (lw-ray-translate-points root points)
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-ray-translate-points) lw-ray-translate-points lw-ray-pointsp lw-complex-ring-rational len endp lw-rtr-left-commutes lw-rtr-left-distributes lw-rtr-fold-constants lw-rtr-times-negative lw-rtr-negative-times lw-rtr-zero-times lw-rtr-minus-one lw-rtr-double-negative lw-rtr-add-cancel lw-rtr-double lw-rtr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-ray-translate-path-last
 (equal (lw-ray-path-last (lw-complex-sub current root) (lw-ray-translate-points root points))
        (lw-complex-sub (lw-ray-path-last current points) root))
 :hints (("Goal" :induct (lw-ray-path-last current points)
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-ray-path-last) lw-ray-path-last lw-ray-translate-points endp lw-rtr-left-commutes lw-rtr-left-distributes lw-rtr-fold-constants lw-rtr-times-negative lw-rtr-negative-times lw-rtr-zero-times lw-rtr-minus-one lw-rtr-double-negative lw-rtr-add-cancel lw-rtr-double lw-rtr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-ray-translate-append
 (equal (lw-ray-translate-points root (append left right))
        (append (lw-ray-translate-points root left) (lw-ray-translate-points root right)))
 :hints (("Goal" :induct (append left right)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-translate-points append endp lw-rtr-left-commutes lw-rtr-left-distributes lw-rtr-fold-constants lw-rtr-times-negative lw-rtr-negative-times lw-rtr-zero-times lw-rtr-minus-one lw-rtr-double-negative lw-rtr-add-cancel lw-rtr-double lw-rtr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-ray-translate-reverse
 (equal (lw-ray-translate-points root (lw-ray-reverse-points points))
        (lw-ray-reverse-points (lw-ray-translate-points root points)))
 :hints (("Goal" :induct (lw-ray-reverse-points points)
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-ray-reverse-points) lw-ray-reverse-points lw-ray-translate-points lw-ray-translate-append append endp lw-rtr-left-commutes lw-rtr-left-distributes lw-rtr-fold-constants lw-rtr-times-negative lw-rtr-negative-times lw-rtr-zero-times lw-rtr-minus-one lw-rtr-double-negative lw-rtr-add-cancel lw-rtr-double lw-rtr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-ray-translate-fixed-real
 (implies (and (lw-complexp root) (lw-ray-fixed-real-pointsp points real))
  (lw-ray-fixed-real-pointsp (lw-ray-translate-points root points) (- real (car root))))
 :hints (("Goal" :induct (lw-ray-translate-points root points)
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-ray-translate-points) lw-ray-translate-points lw-ray-fixed-real-pointsp lw-complexp lw-complex-sub endp lw-rtr-left-commutes lw-rtr-left-distributes lw-rtr-fold-constants lw-rtr-times-negative lw-rtr-negative-times lw-rtr-zero-times lw-rtr-minus-one lw-rtr-double-negative lw-rtr-add-cancel lw-rtr-double lw-rtr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-ray-translate-fixed-imag
 (implies (and (lw-complexp root) (lw-ray-fixed-imag-pointsp points imag))
  (lw-ray-fixed-imag-pointsp (lw-ray-translate-points root points) (- imag (cdr root))))
 :hints (("Goal" :induct (lw-ray-translate-points root points)
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-ray-translate-points) lw-ray-translate-points lw-ray-fixed-imag-pointsp lw-complexp lw-complex-sub endp lw-rtr-left-commutes lw-rtr-left-distributes lw-rtr-fold-constants lw-rtr-times-negative lw-rtr-negative-times lw-rtr-zero-times lw-rtr-minus-one lw-rtr-double-negative lw-rtr-add-cancel lw-rtr-double lw-rtr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-ray-translate-points-head
 (implies (consp points)
  (equal (car (lw-ray-translate-points root points)) (lw-complex-sub (car points) root)))
 :hints (("Goal" :expand ((lw-ray-translate-points root points)) :in-theory (union-theories
 '(fold-consts-in-+ lw-rtr-left-commutes lw-rtr-left-distributes lw-rtr-fold-constants lw-rtr-times-negative lw-rtr-negative-times lw-rtr-zero-times lw-rtr-minus-one lw-rtr-double-negative lw-rtr-add-cancel lw-rtr-double lw-rtr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-ray-translate-row-last
 (implies (consp points)
  (equal (lw-ray-row-last (lw-ray-translate-points root points))
         (lw-complex-sub (lw-ray-row-last points) root)))
 :hints (("Goal" :expand ((lw-ray-translate-points root points))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-row-last lw-ray-translate-path-last lw-rtr-left-commutes lw-rtr-left-distributes lw-rtr-fold-constants lw-rtr-times-negative lw-rtr-negative-times lw-rtr-zero-times lw-rtr-minus-one lw-rtr-double-negative lw-rtr-add-cancel lw-rtr-double lw-rtr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
