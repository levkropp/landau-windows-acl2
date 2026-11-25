; Shape, exact access and closure of actual native Euler polygon values.
(in-package "ACL2")
(include-book "euler-native-polygon-index")
(include-book "polygon-slices")
(local (in-theory (disable lw-euler-native-path-values lw-euler-native-polygon-index
 lw-complex-euler-continuation-value lw-euler-positive-square-model
 lw-ray-pointwise-nearp lw-ray-pointsp lw-square-point-listp lw-polynomial-path-values
 lw-ray-close-polygon lw-ray-polygon-index)))
(local (defthm lw-npa-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-npa-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-npa-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-npa-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-npa-times-negative (a b) (b a)))
                 :in-theory (disable lw-npa-times-negative)))))

(local (defthm lw-npa-zero-times (equal (* 0 a) 0)))

(local (defthm lw-npa-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-npa-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-npa-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-npa-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-npa-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-npa-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-npa-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-npa-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-npa-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-npa-left-commutes)))))
(local (defthm lw-npa-nth-zero
 (equal (nth 0 points) (car points))
 :hints (("Goal" :expand ((nth 0 points)) :in-theory (union-theories
 '(nth lw-npa-left-commutes lw-npa-left-distributes lw-npa-fold-constants lw-npa-times-negative lw-npa-negative-times lw-npa-zero-times lw-npa-minus-one lw-npa-double-negative lw-npa-add-cancel lw-npa-double lw-npa-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-euler-native-path-values-shape
 (and (true-listp (lw-euler-native-path-values points error))
      (equal (consp (lw-euler-native-path-values points error)) (consp points))
      (equal (len (lw-euler-native-path-values points error)) (len points)))
 :hints (("Goal" :induct (lw-euler-native-path-values points error)
 :in-theory (union-theories
 '(lw-euler-native-path-values true-listp len endp lw-npa-left-commutes lw-npa-left-distributes lw-npa-fold-constants lw-npa-times-negative lw-npa-negative-times lw-npa-zero-times lw-npa-minus-one lw-npa-double-negative lw-npa-add-cancel lw-npa-double lw-npa-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-euler-native-path-values-append
 (equal (lw-euler-native-path-values (append left right) error)
        (append (lw-euler-native-path-values left error) (lw-euler-native-path-values right error)))
 :hints (("Goal" :induct (append left right)
 :in-theory (union-theories
 '(lw-euler-native-path-values append endp lw-npa-left-commutes lw-npa-left-distributes lw-npa-fold-constants lw-npa-times-negative lw-npa-negative-times lw-npa-zero-times lw-npa-minus-one lw-npa-double-negative lw-npa-add-cancel lw-npa-double lw-npa-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-euler-native-path-values-close
 (equal (lw-euler-native-path-values (lw-ray-close-polygon points) error)
        (lw-ray-close-polygon (lw-euler-native-path-values points error)))
 :hints (("Goal"
 :use ((:instance lw-euler-native-path-values-append
        (left (cdr points)) (right (list (car points)))))
 :expand ((lw-euler-native-path-values points error))
 :in-theory (union-theories
 '(lw-euler-native-path-values lw-ray-close-polygon append endp cons lw-npa-left-commutes lw-npa-left-distributes lw-npa-fold-constants lw-npa-times-negative lw-npa-negative-times lw-npa-zero-times lw-npa-minus-one lw-npa-double-negative lw-npa-add-cancel lw-npa-double lw-npa-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-euler-native-path-values-nth
 (implies (and (natp index) (< index (len points)))
 (equal (nth index (lw-euler-native-path-values points error))
        (lw-complex-euler-continuation-value (car (nth index points)) (cdr (nth index points)) error)))
 :hints (("Goal" :induct (nth index points)
 :in-theory (union-theories
 '(lw-euler-native-path-values nth lw-npa-nth-zero len endp fold-consts-in-+ lw-npa-left-commutes lw-npa-left-distributes lw-npa-fold-constants lw-npa-times-negative lw-npa-negative-times lw-npa-zero-times lw-npa-minus-one lw-npa-double-negative lw-npa-add-cancel lw-npa-double lw-npa-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-euler-native-path-values-data
 (implies (and (lw-positive-squarep anchor side) (lw-square-point-listp anchor side points)
               (rationalp error) (< 0 error))
 (lw-ray-pointsp (lw-euler-native-path-values points error)))
 :hints (("Goal"
 :use ((:instance lw-euler-native-path-model-near (base-target 0) (base-error 1) (value-error error))
       (:instance lw-ray-pointwise-near-data
        (left (lw-polynomial-path-values (lw-euler-positive-square-model anchor side 0 1) points))
        (right (lw-euler-native-path-values points error)) (delta (* 1/4 (+ 1 error)))))
 :in-theory (union-theories
 '( lw-npa-left-commutes lw-npa-left-distributes lw-npa-fold-constants lw-npa-times-negative lw-npa-negative-times lw-npa-zero-times lw-npa-minus-one lw-npa-double-negative lw-npa-add-cancel lw-npa-double lw-npa-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-native-polygon-index-close
 (implies (and (lw-positive-squarep anchor side) (lw-square-point-listp anchor side points)
               (rationalp error) (< 0 error))
 (equal (lw-euler-native-polygon-index (lw-ray-close-polygon points) error)
        (lw-euler-native-polygon-index points error)))
 :hints (("Goal" :use (lw-euler-native-path-values-data
       (:instance lw-ray-polygon-index-close (points (lw-euler-native-path-values points error))))
 :in-theory (union-theories
 '(lw-euler-native-polygon-index lw-euler-native-path-values-close lw-npa-left-commutes lw-npa-left-distributes lw-npa-fold-constants lw-npa-times-negative lw-npa-negative-times lw-npa-zero-times lw-npa-minus-one lw-npa-double-negative lw-npa-add-cancel lw-npa-double lw-npa-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

