; Concatenation and reversal of finite rational polygon paths.
(in-package "ACL2")
(include-book "grid-index")
(local (in-theory (disable lw-complexp lw-ray-crossing lw-ray-path-index lw-ray-path-last
 lw-ray-row-index lw-ray-row-last lw-ray-polygon-index lw-ray-pointsp)))
(local (defthm lw-ppt-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ppt-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ppt-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ppt-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ppt-times-negative (a b) (b a)))
                 :in-theory (disable lw-ppt-times-negative)))))

(local (defthm lw-ppt-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ppt-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ppt-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ppt-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ppt-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ppt-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ppt-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ppt-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ppt-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ppt-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ppt-left-commutes)))))
(defun lw-ray-reverse-points (points)
 (if (endp points) nil
 (append (lw-ray-reverse-points (cdr points)) (list (car points)))))
(local (in-theory (disable lw-ray-reverse-points)))

(local (defthm lw-ppt-append-head
 (and (equal (consp (append left right)) (or (consp left) (consp right)))
      (equal (car (append left right)) (if (consp left) (car left) (car right))))
 :hints (("Goal" :expand ((append left right)) :in-theory (union-theories
 '(append endp lw-ppt-left-commutes lw-ppt-left-distributes lw-ppt-fold-constants lw-ppt-times-negative lw-ppt-negative-times lw-ppt-zero-times lw-ppt-minus-one lw-ppt-double-negative lw-ppt-add-cancel lw-ppt-double lw-ppt-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-ppt-length-natural (natp (len points))
 :hints (("Goal" :induct (len points) :in-theory (union-theories
 '(len endp lw-ppt-left-commutes lw-ppt-left-distributes lw-ppt-fold-constants lw-ppt-times-negative lw-ppt-negative-times lw-ppt-zero-times lw-ppt-minus-one lw-ppt-double-negative lw-ppt-add-cancel lw-ppt-double lw-ppt-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))
 :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-ppt-length-append
 (equal (len (append left right)) (+ (len left) (len right)))
 :hints (("Goal" :induct (append left right)
 :in-theory (union-theories
 '(append len endp lw-ppt-length-natural lw-ppt-left-commutes lw-ppt-left-distributes lw-ppt-fold-constants lw-ppt-times-negative lw-ppt-negative-times lw-ppt-zero-times lw-ppt-minus-one lw-ppt-double-negative lw-ppt-add-cancel lw-ppt-double lw-ppt-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-ray-pointsp-append
 (implies (and (lw-ray-pointsp left) (lw-ray-pointsp right))
 (lw-ray-pointsp (append left right)))
 :hints (("Goal" :induct (append left right)
 :in-theory (union-theories
 '(append lw-ray-pointsp endp lw-ppt-left-commutes lw-ppt-left-distributes lw-ppt-fold-constants lw-ppt-times-negative lw-ppt-negative-times lw-ppt-zero-times lw-ppt-minus-one lw-ppt-double-negative lw-ppt-add-cancel lw-ppt-double lw-ppt-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-ray-row-index-integer
 (integerp (lw-ray-row-index row))
 :hints (("Goal" :in-theory (union-theories
 '(lw-ray-row-index lw-ray-path-index-integer lw-ppt-left-commutes lw-ppt-left-distributes lw-ppt-fold-constants lw-ppt-times-negative lw-ppt-negative-times lw-ppt-zero-times lw-ppt-minus-one lw-ppt-double-negative lw-ppt-add-cancel lw-ppt-double lw-ppt-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))
 :rule-classes (:rewrite :type-prescription))

(defthm lw-ray-row-index-cons
 (equal (lw-ray-row-index (cons current points))
 (if (endp points) 0 (+ (lw-ray-crossing current (car points)) (lw-ray-row-index points))))
 :hints (("Goal"
 :use ((:instance lw-ray-crossing-data (a current) (b (car points))))
 :in-theory (union-theories
 '(lw-ray-row-index lw-ray-path-index lw-ray-path-index-integer endp lw-ppt-left-commutes lw-ppt-left-distributes lw-ppt-fold-constants lw-ppt-times-negative lw-ppt-negative-times lw-ppt-zero-times lw-ppt-minus-one lw-ppt-double-negative lw-ppt-add-cancel lw-ppt-double lw-ppt-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-ppt-empty-row-index
 (implies (endp points) (equal (lw-ray-row-index points) 0))
 :hints (("Goal" :in-theory (union-theories
 '(lw-ray-row-index lw-ray-path-index endp lw-ppt-left-commutes lw-ppt-left-distributes lw-ppt-fold-constants lw-ppt-times-negative lw-ppt-negative-times lw-ppt-zero-times lw-ppt-minus-one lw-ppt-double-negative lw-ppt-add-cancel lw-ppt-double lw-ppt-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-ray-row-index-append
 (implies (and (consp left) (consp right))
 (equal (lw-ray-row-index (append left right))
 (+ (lw-ray-row-index left)
    (lw-ray-crossing (lw-ray-row-last left) (car right))
    (lw-ray-row-index right))))
 :hints (("Goal"
 :use ((:instance lw-ray-path-index-append (current (car left)) (prefix (cdr left)) (suffix right))
       (:instance lw-ray-crossing-data (a (lw-ray-row-last left)) (b (car right))))
 :expand ((append left right))
 :in-theory (union-theories
 '(lw-ray-row-index lw-ray-row-last lw-ray-path-index lw-ray-path-index-integer endp lw-ppt-left-commutes lw-ppt-left-distributes lw-ppt-fold-constants lw-ppt-times-negative lw-ppt-negative-times lw-ppt-zero-times lw-ppt-minus-one lw-ppt-double-negative lw-ppt-add-cancel lw-ppt-double lw-ppt-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-ray-row-last-append
 (implies (consp right)
 (equal (lw-ray-row-last (append left right)) (lw-ray-row-last right)))
 :hints (("Goal" :cases ((consp left))
 :use ((:instance lw-ray-path-last-append (current (car left)) (prefix (cdr left)) (suffix right)))
 :expand ((append left right))
 :in-theory (union-theories
 '(lw-ray-row-last lw-ray-path-last endp lw-ppt-left-commutes lw-ppt-left-distributes lw-ppt-fold-constants lw-ppt-times-negative lw-ppt-negative-times lw-ppt-zero-times lw-ppt-minus-one lw-ppt-double-negative lw-ppt-add-cancel lw-ppt-double lw-ppt-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-ray-reverse-points-data
 (and (equal (consp (lw-ray-reverse-points points)) (consp points))
      (equal (len (lw-ray-reverse-points points)) (len points))
      (implies (lw-ray-pointsp points) (lw-ray-pointsp (lw-ray-reverse-points points))))
 :hints (("Goal" :induct (lw-ray-reverse-points points)
 :in-theory (union-theories
 '(lw-ray-reverse-points lw-ray-pointsp lw-ray-pointsp-append lw-ppt-length-append lw-ppt-length-natural lw-ppt-append-head len endp lw-ppt-left-commutes lw-ppt-left-distributes lw-ppt-fold-constants lw-ppt-times-negative lw-ppt-negative-times lw-ppt-zero-times lw-ppt-minus-one lw-ppt-double-negative lw-ppt-add-cancel lw-ppt-double lw-ppt-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-ray-reverse-points-endpoints
 (implies (consp points)
 (and (equal (car (lw-ray-reverse-points points)) (lw-ray-row-last points))
      (equal (lw-ray-row-last (lw-ray-reverse-points points)) (car points))))
 :hints (("Goal" :induct (lw-ray-reverse-points points)
 :in-theory (union-theories
 '(lw-ray-reverse-points lw-ray-reverse-points-data lw-ppt-append-head lw-ray-row-last-append lw-ray-row-last lw-ray-path-last endp lw-ppt-left-commutes lw-ppt-left-distributes lw-ppt-fold-constants lw-ppt-times-negative lw-ppt-negative-times lw-ppt-zero-times lw-ppt-minus-one lw-ppt-double-negative lw-ppt-add-cancel lw-ppt-double lw-ppt-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-ppt-row-step
 (implies (consp points)
 (equal (lw-ray-row-index points)
 (if (endp (cdr points)) 0
 (+ (lw-ray-crossing (car points) (cadr points)) (lw-ray-row-index (cdr points))))))
 :hints (("Goal" :in-theory (union-theories
 '(lw-ray-row-index lw-ray-path-index lw-ray-path-index-integer endp lw-ppt-left-commutes lw-ppt-left-distributes lw-ppt-fold-constants lw-ppt-times-negative lw-ppt-negative-times lw-ppt-zero-times lw-ppt-minus-one lw-ppt-double-negative lw-ppt-add-cancel lw-ppt-double lw-ppt-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))
 :rule-classes nil))

(defthm lw-ray-row-index-reverse
 (implies (lw-ray-pointsp points)
 (equal (lw-ray-row-index (lw-ray-reverse-points points)) (- (lw-ray-row-index points))))
 :hints (("Goal" :induct (lw-ray-reverse-points points)
 :expand ((lw-ray-reverse-points points))
 :in-theory (union-theories
 '(append (:executable-counterpart lw-ray-reverse-points) (:induction lw-ray-reverse-points) lw-ppt-append-head lw-ppt-empty-row-index lw-ray-row-index-cons lw-ray-row-index-integer lw-ray-reverse-points-data lw-ray-reverse-points-endpoints lw-ray-row-index-append lw-ray-path-index-integer lw-ray-row-last lw-ray-path-last lw-ray-pointsp endp lw-ppt-left-commutes lw-ppt-left-distributes lw-ppt-fold-constants lw-ppt-times-negative lw-ppt-negative-times lw-ppt-zero-times lw-ppt-minus-one lw-ppt-double-negative lw-ppt-add-cancel lw-ppt-double lw-ppt-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
 (and stable-under-simplificationp
 '(:use ((:instance lw-ppt-row-step (points points))
         (:instance lw-ray-crossing-reverse (a (car points)) (b (cadr points)))
         (:instance lw-ray-crossing-data (a (car points)) (b (cadr points)))
         (:instance lw-ray-crossing-data (a (cadr points)) (b (car points))))
 :do-not-induct t))))

(local (defthm lw-ppt-last-complex
 (implies (and (lw-complexp current) (lw-ray-pointsp points))
 (lw-complexp (lw-ray-path-last current points)))
 :hints (("Goal" :induct (lw-ray-path-last current points)
 :in-theory (union-theories
 '(lw-ray-pointsp lw-ray-path-last endp lw-ppt-left-commutes lw-ppt-left-distributes lw-ppt-fold-constants lw-ppt-times-negative lw-ppt-negative-times lw-ppt-zero-times lw-ppt-minus-one lw-ppt-double-negative lw-ppt-add-cancel lw-ppt-double lw-ppt-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-ray-row-last-complex
 (implies (and (consp points) (lw-ray-pointsp points))
 (lw-complexp (lw-ray-row-last points)))
 :hints (("Goal" :use ((:instance lw-ppt-last-complex (current (car points)) (points (cdr points))))
 :in-theory (union-theories
 '(lw-ray-row-last lw-ray-pointsp endp lw-ppt-left-commutes lw-ppt-left-distributes lw-ppt-fold-constants lw-ppt-times-negative lw-ppt-negative-times lw-ppt-zero-times lw-ppt-minus-one lw-ppt-double-negative lw-ppt-add-cancel lw-ppt-double lw-ppt-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-ray-polygon-index-reverse
 (implies (lw-ray-pointsp points)
 (equal (lw-ray-polygon-index (lw-ray-reverse-points points)) (- (lw-ray-polygon-index points))))
 :hints (("Goal"
 :use (lw-ray-row-index-reverse lw-ray-row-last-complex lw-ray-reverse-points-endpoints
       (:instance lw-ray-crossing-reverse (a (lw-ray-row-last points)) (b (car points)))
       (:instance lw-ray-crossing-data (a (lw-ray-row-last points)) (b (car points))))
 :in-theory (union-theories
 '(lw-ray-polygon-index lw-ray-row-index lw-ray-row-last lw-ray-reverse-points-endpoints lw-ray-reverse-points-data lw-ray-pointsp lw-ray-path-index-integer endp lw-ppt-left-commutes lw-ppt-left-distributes lw-ppt-fold-constants lw-ppt-times-negative lw-ppt-negative-times lw-ppt-zero-times lw-ppt-minus-one lw-ppt-double-negative lw-ppt-add-cancel lw-ppt-double lw-ppt-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))
