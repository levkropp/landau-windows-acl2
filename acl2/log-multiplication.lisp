(in-package "ACL2")

(include-book "log-partitions")

; Product logarithms from exact scaling and concatenation of rational
; rectangle partitions. All three logarithm requests are independent.

(local (in-theory (disable lw-log-bounds lw-log-count lw-log-rectangles
                          lw-uniform-log-partition lw-positive-partitionp
                          lw-partition-end lw-log-partition-lower lw-log-partition-upper)))

(local (defthm lw-lgm-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-lgm-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-lgm-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-lgm-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-lgm-times-negative (a b) (b a)))
                 :in-theory (disable lw-lgm-times-negative)))))

(local (defthm lw-lgm-zero-times (equal (* 0 a) 0)))

(local (defthm lw-lgm-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-lgm-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-lgm-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-lgm-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-lgm-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-lgm-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-lgm-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-lgm-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-lgm-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-lgm-left-commutes)))))

(local (defthm lw-lgm-cancel-equality
 (implies (and (rationalp factor) (< 0 factor) (rationalp a) (rationalp b)
               (equal (* factor a) (* factor b)))
  (equal a b))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-lgm-inverse-product
 (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b))
  (equal (/ (* a b)) (* (/ a) (/ b))))
 :hints (("Goal"
  :use ((:instance inverse-of-* (x a)) (:instance inverse-of-* (x b))
        (:instance inverse-of-* (x (* a b)))
        (:instance lw-lgm-cancel-equality
         (factor (* a b)) (a (/ (* a b))) (b (* (/ a) (/ b)))))
  :in-theory (disable inverse-of-*) :nonlinearp t))
 :rule-classes nil))

(local (defthm lw-lgm-scaled-ratio
 (implies (and (rationalp factor) (< 0 factor) (rationalp numerator)
               (rationalp divisor) (< 0 divisor))
  (equal (* factor numerator (/ (* factor divisor))) (* numerator (/ divisor))))
 :hints (("Goal"
  :use ((:instance lw-lgm-inverse-product (a factor) (b divisor))
        (:instance inverse-of-* (x factor)))
  :in-theory (disable inverse-of-*) :nonlinearp t :do-not-induct t))))

(defun lw-scale-log-partition (factor endpoints)
 (if (endp endpoints) nil
  (cons (* factor (car endpoints))
        (lw-scale-log-partition factor (cdr endpoints)))))

(defthm lw-scaled-log-partition-valid
 (implies (and (rationalp factor) (< 0 factor) (lw-positive-partitionp start endpoints))
  (lw-positive-partitionp (* factor start) (lw-scale-log-partition factor endpoints)))
 :hints (("Goal" :induct (lw-positive-partitionp start endpoints)
                 :in-theory (enable lw-positive-partitionp lw-scale-log-partition)
                 :nonlinearp t)))

(defthm lw-scaled-log-partition-end
 (implies (and (rationalp factor) (< 0 factor) (lw-positive-partitionp start endpoints))
  (equal (lw-partition-end (* factor start) (lw-scale-log-partition factor endpoints))
         (* factor (lw-partition-end start endpoints))))
 :hints (("Goal" :induct (lw-positive-partitionp start endpoints)
                 :in-theory (enable lw-positive-partitionp lw-partition-end lw-scale-log-partition))))

(defthm lw-scaled-log-partition-sums
 (implies (and (rationalp factor) (< 0 factor) (lw-positive-partitionp start endpoints))
  (and
   (equal (lw-log-partition-lower (* factor start) (lw-scale-log-partition factor endpoints))
          (lw-log-partition-lower start endpoints))
   (equal (lw-log-partition-upper (* factor start) (lw-scale-log-partition factor endpoints))
          (lw-log-partition-upper start endpoints))))
 :hints (("Goal" :induct (lw-positive-partitionp start endpoints)
                 :in-theory (enable lw-positive-partitionp lw-log-partition-lower
                                    lw-log-partition-upper lw-scale-log-partition))))

(local (in-theory (disable lw-scale-log-partition binary-append)))

(local (defthm lw-lgm-grid-data
 (implies (and (rationalp value) (< 1 value) (rationalp error) (< 0 error))
  (and (lw-positive-partitionp 1 (lw-uniform-log-partition 1 (/ (- value 1) (lw-log-count value error)) (lw-log-count value error)))
       (true-listp (lw-uniform-log-partition 1 (/ (- value 1) (lw-log-count value error)) (lw-log-count value error)))
       (equal (lw-partition-end 1 (lw-uniform-log-partition 1 (/ (- value 1) (lw-log-count value error)) (lw-log-count value error))) value)
       (equal (lw-log-partition-lower 1 (lw-uniform-log-partition 1 (/ (- value 1) (lw-log-count value error)) (lw-log-count value error))) (car (lw-log-bounds value error)))
       (equal (lw-log-partition-upper 1 (lw-uniform-log-partition 1 (/ (- value 1) (lw-log-count value error)) (lw-log-count value error))) (cdr (lw-log-bounds value error)))))
 :hints (("Goal"
  :use ((:instance lw-log-count-positive (epsilon error))
        (:instance lw-log-step-positive (epsilon error))
        (:instance lw-log-grid-endpoint (epsilon error))
        (:instance lw-uniform-log-partition-valid
         (start 1) (step (/ (- value 1) (lw-log-count value error))) (count (lw-log-count value error)))
        (:instance lw-uniform-log-partition-end
         (start 1) (step (/ (- value 1) (lw-log-count value error))) (count (lw-log-count value error)))
        (:instance lw-uniform-log-partition-sums
         (start 1) (step (/ (- value 1) (lw-log-count value error))) (count (lw-log-count value error))))
  :in-theory (e/d (lw-log-bounds)
    (lw-log-count-positive lw-log-step-positive lw-log-grid-endpoint
     lw-uniform-log-partition-valid lw-uniform-log-partition-end lw-uniform-log-partition-sums))
  :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-lgm-product-grid-data
 (implies (and (rationalp left) (< 1 left) (rationalp right) (< 1 right)
               (rationalp left-error) (< 0 left-error)
               (rationalp right-error) (< 0 right-error))
  (and (lw-positive-partitionp 1 (append (lw-uniform-log-partition 1 (/ (- left 1) (lw-log-count left left-error)) (lw-log-count left left-error)) (lw-scale-log-partition left (lw-uniform-log-partition 1 (/ (- right 1) (lw-log-count right right-error)) (lw-log-count right right-error)))))
       (equal (lw-partition-end 1 (append (lw-uniform-log-partition 1 (/ (- left 1) (lw-log-count left left-error)) (lw-log-count left left-error)) (lw-scale-log-partition left (lw-uniform-log-partition 1 (/ (- right 1) (lw-log-count right right-error)) (lw-log-count right right-error))))) (* left right))
       (equal (lw-log-partition-lower 1 (append (lw-uniform-log-partition 1 (/ (- left 1) (lw-log-count left left-error)) (lw-log-count left left-error)) (lw-scale-log-partition left (lw-uniform-log-partition 1 (/ (- right 1) (lw-log-count right right-error)) (lw-log-count right right-error)))))
              (+ (car (lw-log-bounds left left-error)) (car (lw-log-bounds right right-error))))
       (equal (lw-log-partition-upper 1 (append (lw-uniform-log-partition 1 (/ (- left 1) (lw-log-count left left-error)) (lw-log-count left left-error)) (lw-scale-log-partition left (lw-uniform-log-partition 1 (/ (- right 1) (lw-log-count right right-error)) (lw-log-count right right-error)))))
              (+ (cdr (lw-log-bounds left left-error)) (cdr (lw-log-bounds right right-error))))))
 :hints (("Goal"
  :use ((:instance lw-lgm-grid-data (value left) (error left-error))
        (:instance lw-lgm-grid-data (value right) (error right-error))
        (:instance lw-scaled-log-partition-valid (factor left) (start 1) (endpoints (lw-uniform-log-partition 1 (/ (- right 1) (lw-log-count right right-error)) (lw-log-count right right-error))))
        (:instance lw-scaled-log-partition-end (factor left) (start 1) (endpoints (lw-uniform-log-partition 1 (/ (- right 1) (lw-log-count right right-error)) (lw-log-count right right-error))))
        (:instance lw-scaled-log-partition-sums (factor left) (start 1) (endpoints (lw-uniform-log-partition 1 (/ (- right 1) (lw-log-count right right-error)) (lw-log-count right right-error))))
        (:instance lw-positive-partition-append (start 1)
         (prefix (lw-uniform-log-partition 1 (/ (- left 1) (lw-log-count left left-error)) (lw-log-count left left-error))) (suffix (lw-scale-log-partition left (lw-uniform-log-partition 1 (/ (- right 1) (lw-log-count right right-error)) (lw-log-count right right-error)))))
        (:instance lw-partition-end-append (start 1)
         (prefix (lw-uniform-log-partition 1 (/ (- left 1) (lw-log-count left left-error)) (lw-log-count left left-error))) (suffix (lw-scale-log-partition left (lw-uniform-log-partition 1 (/ (- right 1) (lw-log-count right right-error)) (lw-log-count right right-error)))))
        (:instance lw-log-partition-append-sums (start 1)
         (prefix (lw-uniform-log-partition 1 (/ (- left 1) (lw-log-count left left-error)) (lw-log-count left left-error))) (suffix (lw-scale-log-partition left (lw-uniform-log-partition 1 (/ (- right 1) (lw-log-count right right-error)) (lw-log-count right right-error))))))
  :in-theory (disable lw-scaled-log-partition-valid lw-scaled-log-partition-end
                      lw-scaled-log-partition-sums lw-positive-partition-append
                      lw-partition-end-append lw-log-partition-append-sums)
  :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-lgm-product-above-one
 (implies (and (rationalp left) (< 1 left) (rationalp right) (< 1 right))
  (and (rationalp (* left right)) (< 1 (* left right))))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defthm lw-log-bounds-product-overlap
 (implies (and (rationalp left) (< 1 left) (rationalp right) (< 1 right)
               (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error)
               (rationalp product-error) (< 0 product-error))
  (and (<= (car (lw-log-bounds (* left right) product-error))
           (+ (cdr (lw-log-bounds left left-error)) (cdr (lw-log-bounds right right-error))))
       (<= (+ (car (lw-log-bounds left left-error)) (car (lw-log-bounds right right-error)))
           (cdr (lw-log-bounds (* left right) product-error)))))
 :hints (("Goal"
  :use (lw-lgm-product-above-one lw-lgm-product-grid-data
        (:instance lw-lgm-grid-data (value (* left right)) (error product-error))
        (:instance lw-log-partitions-compare (start 1)
         (left (append (lw-uniform-log-partition 1 (/ (- left 1) (lw-log-count left left-error)) (lw-log-count left left-error)) (lw-scale-log-partition left (lw-uniform-log-partition 1 (/ (- right 1) (lw-log-count right right-error)) (lw-log-count right right-error))))) (right (lw-uniform-log-partition 1 (/ (- (* left right) 1) (lw-log-count (* left right) product-error)) (lw-log-count (* left right) product-error))))
        (:instance lw-log-partitions-compare (start 1)
         (right (append (lw-uniform-log-partition 1 (/ (- left 1) (lw-log-count left left-error)) (lw-log-count left left-error)) (lw-scale-log-partition left (lw-uniform-log-partition 1 (/ (- right 1) (lw-log-count right right-error)) (lw-log-count right right-error))))) (left (lw-uniform-log-partition 1 (/ (- (* left right) 1) (lw-log-count (* left right) product-error)) (lw-log-count (* left right) product-error)))))
  :in-theory (disable lw-log-partitions-compare)
  :do-not-induct t)))

(defthm lw-log-lower-multiplication
 (implies (and (rationalp left) (< 1 left) (rationalp right) (< 1 right)
               (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error)
               (rationalp product-error) (< 0 product-error))
  (<= (abs (- (+ (car (lw-log-bounds left left-error)) (car (lw-log-bounds right right-error)))
              (car (lw-log-bounds (* left right) product-error))))
      (+ left-error right-error product-error)))
 :hints (("Goal"
  :use (lw-lgm-product-above-one lw-log-bounds-product-overlap
        (:instance lw-log-bounds-width (value left) (epsilon left-error))
        (:instance lw-log-bounds-width (value right) (epsilon right-error))
        (:instance lw-log-bounds-width (value (* left right)) (epsilon product-error))
        (:instance lw-log-bounds-interval (value left) (epsilon left-error))
        (:instance lw-log-bounds-interval (value right) (epsilon right-error))
        (:instance lw-log-bounds-interval (value (* left right)) (epsilon product-error)))
  :in-theory (e/d (lw-intervalp)
    (lw-log-bounds-product-overlap lw-log-bounds-width lw-log-bounds-interval))
  :nonlinearp nil :do-not-induct t)))


