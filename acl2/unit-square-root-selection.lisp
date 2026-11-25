(in-package "ACL2")

(include-book "polynomial-factor-paths")

; Select the unit weights contributing to the finite square factor count.

(local (defthm lw-urs-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-urs-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-urs-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-urs-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-urs-times-negative (a b) (b a)))
                 :in-theory (disable lw-urs-times-negative)))))

(local (defthm lw-urs-zero-times (equal (* 0 a) 0)))

(local (defthm lw-urs-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-urs-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-urs-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-urs-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-urs-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-urs-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-urs-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-urs-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-urs-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-urs-left-commutes)))))

(defun lw-unit-square-inside-roots (roots)
 (declare (xargs :measure (acl2-count roots) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (endp roots) nil
  (if (equal (lw-unit-square-root-index (car roots)) 1)
   (cons (car roots) (lw-unit-square-inside-roots (cdr roots)))
   (lw-unit-square-inside-roots (cdr roots)))))

(defun lw-unit-square-open-rootsp (roots)
 (declare (xargs :measure (acl2-count roots) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (endp roots) (equal roots nil)
  (and (lw-complexp (car roots))
       (< -1 (caar roots)) (< (caar roots) 1)
       (< -1 (cdar roots)) (< (cdar roots) 1)
       (lw-unit-square-open-rootsp (cdr roots)))))

(local (in-theory (disable lw-unit-square-inside-roots lw-unit-square-open-rootsp)))

(local (defthm lw-urs-length-natural
 (natp (len roots)) :rule-classes (:rewrite :type-prescription)))
(local (defthm lw-urs-count-natural
 (natp (lw-unit-square-factor-count roots))
 :hints (("Goal" :use (lw-unit-square-factor-count-data) :in-theory (union-theories
 '(fold-consts-in-+ lw-urs-left-commutes lw-urs-left-distributes lw-urs-fold-constants lw-urs-times-negative lw-urs-negative-times lw-urs-zero-times lw-urs-minus-one lw-urs-double-negative lw-urs-add-cancel lw-urs-double lw-urs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))
 :rule-classes (:rewrite :type-prescription)))

(defthm lw-unit-square-inside-roots-length
 (equal (len (lw-unit-square-inside-roots roots)) (lw-unit-square-factor-count roots))
 :hints (("Goal" :induct (lw-unit-square-inside-roots roots)
  :in-theory (union-theories
 '(lw-urs-length-natural lw-urs-count-natural fold-consts-in-+ (:induction lw-unit-square-inside-roots) lw-unit-square-inside-roots lw-unit-square-root-index lw-unit-square-factor-count len endp lw-urs-left-commutes lw-urs-left-distributes lw-urs-fold-constants lw-urs-times-negative lw-urs-negative-times lw-urs-zero-times lw-urs-minus-one lw-urs-double-negative lw-urs-add-cancel lw-urs-double lw-urs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-unit-square-inside-roots-valid
 (implies (lw-ray-pointsp roots) (lw-ray-pointsp (lw-unit-square-inside-roots roots)))
 :hints (("Goal" :induct (lw-unit-square-inside-roots roots)
  :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-unit-square-inside-roots) lw-unit-square-inside-roots lw-ray-pointsp endp lw-urs-left-commutes lw-urs-left-distributes lw-urs-fold-constants lw-urs-times-negative lw-urs-negative-times lw-urs-zero-times lw-urs-minus-one lw-urs-double-negative lw-urs-add-cancel lw-urs-double lw-urs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-urs-counted-root-interior
 (implies (and (lw-complexp root) (not (lw-unit-square-pointp root)) (equal (lw-unit-square-root-index root) 1))
  (and (< -1 (car root)) (< (car root) 1) (< -1 (cdr root)) (< (cdr root) 1)))
 :hints (("Goal"
  :in-theory (union-theories
 '(fold-consts-in-+ lw-unit-square-root-index lw-unit-square-pointp lw-complex-square-radius lw-complexp max abs lw-urs-left-commutes lw-urs-left-distributes lw-urs-fold-constants lw-urs-times-negative lw-urs-negative-times lw-urs-zero-times lw-urs-minus-one lw-urs-double-negative lw-urs-add-cancel lw-urs-double lw-urs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))))

(defthm lw-unit-square-inside-roots-interior
 (implies (lw-unit-square-roots-awayp roots)
  (lw-unit-square-open-rootsp (lw-unit-square-inside-roots roots)))
 :hints (("Goal" :induct (lw-unit-square-inside-roots roots)
  :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-unit-square-inside-roots) lw-unit-square-inside-roots lw-unit-square-open-rootsp lw-unit-square-roots-awayp lw-urs-counted-root-interior endp lw-urs-left-commutes lw-urs-left-distributes lw-urs-fold-constants lw-urs-times-negative lw-urs-negative-times lw-urs-zero-times lw-urs-minus-one lw-urs-double-negative lw-urs-add-cancel lw-urs-double lw-urs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))
