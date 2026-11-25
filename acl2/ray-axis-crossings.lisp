(in-package "ACL2")

(include-book "polygon-paths")

; Exact crossing potentials for vertical and horizontal rational edges.

(local (defthm lw-rax-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-rax-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-rax-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-rax-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-rax-times-negative (a b) (b a)))
                 :in-theory (disable lw-rax-times-negative)))))

(local (defthm lw-rax-zero-times (equal (* 0 a) 0)))

(local (defthm lw-rax-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-rax-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-rax-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-rax-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-rax-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-rax-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-rax-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-rax-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-rax-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-rax-left-commutes)))))
(defun lw-ray-upper-indicator (point) (if (< 0 (cdr point)) 1 0))

(defthm lw-ray-crossing-vertical-potential
 (implies (and (lw-complexp a) (lw-complexp b) (equal (car a) (car b)))
  (equal (lw-ray-crossing a b)
         (if (< 0 (car a))
          (- (lw-ray-upper-indicator b) (lw-ray-upper-indicator a)) 0)))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complexp lw-complex-det lw-ray-crossing lw-ray-upper-indicator lw-rax-left-commutes lw-rax-left-distributes lw-rax-fold-constants lw-rax-times-negative lw-rax-negative-times lw-rax-zero-times lw-rax-minus-one lw-rax-double-negative lw-rax-add-cancel lw-rax-double lw-rax-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
          :nonlinearp t :do-not-induct t)))

(defthm lw-ray-crossing-horizontal-zero
 (implies (equal (cdr a) (cdr b)) (equal (lw-ray-crossing a b) 0))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-crossing lw-rax-left-commutes lw-rax-left-distributes lw-rax-fold-constants lw-rax-times-negative lw-rax-negative-times lw-rax-zero-times lw-rax-minus-one lw-rax-double-negative lw-rax-add-cancel lw-rax-double lw-rax-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
