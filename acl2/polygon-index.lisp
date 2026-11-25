; Finite polygon winding as an integer sum of rational ray crossings.
(in-package "ACL2")
(include-book "ray-crossing")
(local (in-theory (disable lw-complexp lw-complex-det lw-complex-dot lw-complex-positive-halfplanep lw-ray-crossing lw-ray-triangle-index)))
(local (defthm lw-pwi-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pwi-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pwi-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pwi-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pwi-times-negative (a b) (b a)))
                 :in-theory (disable lw-pwi-times-negative)))))

(local (defthm lw-pwi-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pwi-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pwi-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pwi-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pwi-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pwi-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pwi-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-pwi-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pwi-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pwi-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-pwi-left-commutes)))))
(defun lw-ray-pointsp (points)
 (if (endp points) (equal points nil)
 (and (lw-complexp (car points)) (lw-ray-pointsp (cdr points)))))
(defun lw-ray-halfplane-points (h points)
 (if (endp points) (equal points nil)
 (and (lw-complex-positive-halfplanep h (car points)) (lw-ray-halfplane-points h (cdr points)))))
(defun lw-ray-path-index (current points)
 (if (endp points) 0
 (+ (lw-ray-crossing current (car points)) (lw-ray-path-index (car points) (cdr points)))))
(defun lw-ray-path-last (current points)
 (if (endp points) current (lw-ray-path-last (car points) (cdr points))))
(defun lw-ray-polygon-index (points)
 (if (endp points) 0
 (+ (lw-ray-path-index (car points) (cdr points))
    (lw-ray-crossing (lw-ray-path-last (car points) (cdr points)) (car points)))))
(defun lw-ray-quadrilateral-index (a b c d)
 (+ (lw-ray-crossing a b) (lw-ray-crossing b c) (lw-ray-crossing c d) (lw-ray-crossing d a)))

(local (in-theory (disable lw-ray-pointsp lw-ray-halfplane-points lw-ray-path-index lw-ray-path-last lw-ray-polygon-index lw-ray-quadrilateral-index)))

(local (defthm lw-pwi-length-natural (natp (len points))
 :hints (("Goal" :induct (len points) :in-theory (union-theories
 '(len endp lw-pwi-left-commutes lw-pwi-left-distributes lw-pwi-fold-constants lw-pwi-times-negative lw-pwi-negative-times lw-pwi-zero-times lw-pwi-minus-one lw-pwi-double-negative lw-pwi-add-cancel lw-pwi-double lw-pwi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-ray-path-index-integer
 (integerp (lw-ray-path-index current points))
 :hints (("Goal" :induct (lw-ray-path-index current points)
 :in-theory (union-theories
 '(lw-ray-path-index endp lw-pwi-left-commutes lw-pwi-left-distributes lw-pwi-fold-constants lw-pwi-times-negative lw-pwi-negative-times lw-pwi-zero-times lw-pwi-minus-one lw-pwi-double-negative lw-pwi-add-cancel lw-pwi-double lw-pwi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
 (and stable-under-simplificationp
 '(:use ((:instance lw-ray-crossing-data (a current) (b (car points)))) :do-not-induct t)))
 :rule-classes (:rewrite :type-prescription))

(defthm lw-ray-path-index-bounds
 (and (<= (- (len points)) (lw-ray-path-index current points))
      (<= (lw-ray-path-index current points) (len points)))
 :hints (("Goal" :induct (lw-ray-path-index current points)
 :in-theory (union-theories
 '(lw-ray-path-index len endp lw-pwi-left-commutes lw-pwi-left-distributes lw-pwi-fold-constants lw-pwi-times-negative lw-pwi-negative-times lw-pwi-zero-times lw-pwi-minus-one lw-pwi-double-negative lw-pwi-add-cancel lw-pwi-double lw-pwi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
 (and stable-under-simplificationp
 '(:use ((:instance lw-ray-crossing-data (a current) (b (car points)))) :do-not-induct t))))

(defthm lw-ray-path-index-append
 (equal (lw-ray-path-index current (append prefix suffix))
 (+ (lw-ray-path-index current prefix) (lw-ray-path-index (lw-ray-path-last current prefix) suffix)))
 :hints (("Goal" :induct (lw-ray-path-index current prefix)
 :in-theory (union-theories
 '(lw-ray-path-index-integer lw-ray-path-index lw-ray-path-last append endp lw-pwi-left-commutes lw-pwi-left-distributes lw-pwi-fold-constants lw-pwi-times-negative lw-pwi-negative-times lw-pwi-zero-times lw-pwi-minus-one lw-pwi-double-negative lw-pwi-add-cancel lw-pwi-double lw-pwi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
 (and stable-under-simplificationp
 '(:use ((:instance lw-ray-crossing-data (a current) (b (car prefix)))
         (:instance lw-ray-path-index-integer (current (car prefix)) (points (cdr prefix)))
         (:instance lw-ray-path-index-integer (current (lw-ray-path-last (car prefix) (cdr prefix))) (points suffix)))
 :do-not-induct t))))

(defthm lw-ray-path-last-append
 (equal (lw-ray-path-last current (append prefix suffix))
 (lw-ray-path-last (lw-ray-path-last current prefix) suffix))
 :hints (("Goal" :induct (lw-ray-path-last current prefix)
 :in-theory (union-theories
 '(lw-ray-path-last append endp lw-pwi-left-commutes lw-pwi-left-distributes lw-pwi-fold-constants lw-pwi-times-negative lw-pwi-negative-times lw-pwi-zero-times lw-pwi-minus-one lw-pwi-double-negative lw-pwi-add-cancel lw-pwi-double lw-pwi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))


(defthm lw-ray-halfplane-points-data
 (implies (lw-ray-halfplane-points h points)
 (and (true-listp points) (lw-ray-pointsp points)))
 :hints (("Goal" :induct (lw-ray-halfplane-points h points)
 :in-theory (union-theories
 '(lw-ray-halfplane-points lw-ray-pointsp lw-complex-positive-halfplanep true-listp endp lw-pwi-left-commutes lw-pwi-left-distributes lw-pwi-fold-constants lw-pwi-times-negative lw-pwi-negative-times lw-pwi-zero-times lw-pwi-minus-one lw-pwi-double-negative lw-pwi-add-cancel lw-pwi-double lw-pwi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))
(defthm lw-ray-path-last-halfplane
 (implies (and (lw-complex-positive-halfplanep h current) (lw-ray-halfplane-points h points))
 (lw-complex-positive-halfplanep h (lw-ray-path-last current points)))
 :hints (("Goal" :induct (lw-ray-path-last current points)
 :in-theory (union-theories
 '(lw-ray-path-last lw-ray-halfplane-points endp lw-pwi-left-commutes lw-pwi-left-distributes lw-pwi-fold-constants lw-pwi-times-negative lw-pwi-negative-times lw-pwi-zero-times lw-pwi-minus-one lw-pwi-double-negative lw-pwi-add-cancel lw-pwi-double lw-pwi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))
(defthm lw-ray-path-halfplane-potential
 (implies (and (lw-complex-positive-halfplanep h current) (lw-ray-halfplane-points h points))
 (equal (lw-ray-path-index current points)
 (- (lw-ray-crossing h (lw-ray-path-last current points)) (lw-ray-crossing h current))))
 :hints (("Goal" :induct (lw-ray-path-index current points)
 :in-theory (union-theories
 '(lw-ray-path-index lw-ray-path-last lw-ray-halfplane-points endp lw-ray-halfplane-potential lw-pwi-left-commutes lw-pwi-left-distributes lw-pwi-fold-constants lw-pwi-times-negative lw-pwi-negative-times lw-pwi-zero-times lw-pwi-minus-one lw-pwi-double-negative lw-pwi-add-cancel lw-pwi-double lw-pwi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
 (and stable-under-simplificationp
 '(:use ((:instance lw-ray-crossing-data (a h) (b current))
         (:instance lw-ray-crossing-data (a h) (b (car points)))
         (:instance lw-ray-crossing-data (a h) (b (lw-ray-path-last (car points) (cdr points)))))
 :do-not-induct t))))

(defthm lw-ray-polygon-index-integer
 (integerp (lw-ray-polygon-index points))
 :hints (("Goal"
 :use ((:instance lw-ray-path-index-integer (current (car points)) (points (cdr points)))
       (:instance lw-ray-crossing-data (a (lw-ray-path-last (car points) (cdr points))) (b (car points))))
 :in-theory (union-theories
 '(lw-ray-polygon-index endp lw-pwi-left-commutes lw-pwi-left-distributes lw-pwi-fold-constants lw-pwi-times-negative lw-pwi-negative-times lw-pwi-zero-times lw-pwi-minus-one lw-pwi-double-negative lw-pwi-add-cancel lw-pwi-double lw-pwi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))
 :rule-classes (:rewrite :type-prescription))

(defthm lw-ray-polygon-index-bounds
 (and (<= (- (len points)) (lw-ray-polygon-index points)) (<= (lw-ray-polygon-index points) (len points)))
 :hints (("Goal"
 :use ((:instance lw-ray-path-index-bounds (current (car points)) (points (cdr points)))
       (:instance lw-ray-crossing-data (a (lw-ray-path-last (car points) (cdr points))) (b (car points))))
 :in-theory (union-theories
 '(lw-ray-polygon-index len endp lw-pwi-left-commutes lw-pwi-left-distributes lw-pwi-fold-constants lw-pwi-times-negative lw-pwi-negative-times lw-pwi-zero-times lw-pwi-minus-one lw-pwi-double-negative lw-pwi-add-cancel lw-pwi-double lw-pwi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-ray-polygon-halfplane-zero
 (implies (lw-ray-halfplane-points h points) (equal (lw-ray-polygon-index points) 0))
 :hints (("Goal"
 :use ((:instance lw-ray-path-halfplane-potential (current (car points)) (points (cdr points)))
       (:instance lw-ray-path-last-halfplane (current (car points)) (points (cdr points)))
       (:instance lw-ray-halfplane-potential (a (lw-ray-path-last (car points) (cdr points))) (b (car points)))
       (:instance lw-ray-crossing-data (a h) (b (car points)))
       (:instance lw-ray-crossing-data (a h) (b (lw-ray-path-last (car points) (cdr points)))))
 :in-theory (union-theories
 '(lw-ray-polygon-index lw-ray-halfplane-points endp lw-pwi-left-commutes lw-pwi-left-distributes lw-pwi-fold-constants lw-pwi-times-negative lw-pwi-negative-times lw-pwi-zero-times lw-pwi-minus-one lw-pwi-double-negative lw-pwi-add-cancel lw-pwi-double lw-pwi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-ray-quadrilateral-decomposition
 (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c) (lw-complexp d))
 (equal (lw-ray-quadrilateral-index a b c d)
 (+ (lw-ray-triangle-index a b c) (lw-ray-triangle-index a c d))))
 :hints (("Goal"
 :use ((:instance lw-ray-crossing-reverse (a a) (b c))
       lw-ray-crossing-data
       (:instance lw-ray-crossing-data (a b) (b c))
       (:instance lw-ray-crossing-data (a c) (b d))
       (:instance lw-ray-crossing-data (a d) (b a))
       (:instance lw-ray-crossing-data (a a) (b c)))
 :in-theory (union-theories
 '(lw-ray-quadrilateral-index lw-ray-triangle-index lw-pwi-left-commutes lw-pwi-left-distributes lw-pwi-fold-constants lw-pwi-times-negative lw-pwi-negative-times lw-pwi-zero-times lw-pwi-minus-one lw-pwi-double-negative lw-pwi-add-cancel lw-pwi-double lw-pwi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-ray-quadrilateral-halfplane-zero
 (implies (and (lw-complex-positive-halfplanep h a) (lw-complex-positive-halfplanep h b)
               (lw-complex-positive-halfplanep h c) (lw-complex-positive-halfplanep h d))
 (equal (lw-ray-quadrilateral-index a b c d) 0))
 :hints (("Goal"
 :use (lw-ray-quadrilateral-decomposition
       lw-ray-triangle-halfplane-zero
       (:instance lw-ray-triangle-halfplane-zero (a a) (b c) (c d)))
 :in-theory (union-theories
 '(lw-complex-positive-halfplanep lw-pwi-left-commutes lw-pwi-left-distributes lw-pwi-fold-constants lw-pwi-times-negative lw-pwi-negative-times lw-pwi-zero-times lw-pwi-minus-one lw-pwi-double-negative lw-pwi-add-cancel lw-pwi-double lw-pwi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))


