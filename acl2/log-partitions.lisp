(in-package "ACL2")

(include-book "log-growth")

(local (defthm lw-partition-multiply-left-commutes
         (equal (* left (* middle right)) (* middle (* left right)))
         :hints (("Goal" :use ((:instance associativity-of-* (x left) (y middle) (z right))
                              (:instance associativity-of-* (x middle) (y left) (z right))
                              (:instance commutativity-of-* (x left) (y middle)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-partition-times-negation
         (implies (and (rationalp left) (rationalp right))
                  (equal (* left (- right)) (- (* left right))))
         :hints (("Goal" :use ((:instance distributivity
                                (x left) (y right) (z (- right))))
                         :in-theory (disable distributivity)))))

(local (defthm lw-partition-multiply-inequality
         (implies (and (rationalp left) (rationalp right) (<= left right)
                       (rationalp factor) (<= 0 factor))
                  (<= (* left factor) (* right factor)))
         :hints (("Goal" :nonlinearp t))
         :rule-classes nil))

(defun lw-positive-partitionp (start endpoints)
  (and (rationalp start) (< 0 start)
       (if (consp endpoints)
           (and (rationalp (car endpoints)) (< start (car endpoints))
                (lw-positive-partitionp (car endpoints) (cdr endpoints)))
         (equal endpoints nil))))

(defun lw-partition-end (start endpoints)
  (if (endp endpoints) start
    (lw-partition-end (car endpoints) (cdr endpoints))))

(defun lw-log-partition-lower (start endpoints)
  (if (endp endpoints) 0
    (+ (/ (- (car endpoints) start) (car endpoints))
       (lw-log-partition-lower (car endpoints) (cdr endpoints)))))

(defun lw-log-partition-upper (start endpoints)
  (if (endp endpoints) 0
    (+ (/ (- (car endpoints) start) start)
       (lw-log-partition-upper (car endpoints) (cdr endpoints)))))

(defthm lw-partition-end-bounds
  (implies (lw-positive-partitionp start endpoints)
           (and (rationalp (lw-partition-end start endpoints))
                (<= start (lw-partition-end start endpoints))
                (implies (consp endpoints) (< start (lw-partition-end start endpoints)))))
  :hints (("Goal" :induct (lw-positive-partitionp start endpoints))))

(defthm lw-log-partition-types
  (implies (lw-positive-partitionp start endpoints)
           (and (rationalp (lw-log-partition-lower start endpoints))
                (rationalp (lw-log-partition-upper start endpoints))
                (<= 0 (lw-log-partition-lower start endpoints))
                (<= 0 (lw-log-partition-upper start endpoints))))
  :hints (("Goal" :induct (lw-positive-partitionp start endpoints)
                  :in-theory (disable distributivity) :nonlinearp t)
          (and stable-under-simplificationp
               '(:use ((:instance lw-partition-multiply-inequality
                          (left 0) (right (- (car endpoints) start)) (factor (/ start)))
                        (:instance lw-partition-multiply-inequality
                          (left 0) (right (- (car endpoints) start)) (factor (/ (car endpoints)))))
                 :in-theory (disable distributivity lw-log-partition-lower lw-log-partition-upper)
                 :nonlinearp t))))

(defthm lw-log-partition-lower-rational
  (implies (lw-positive-partitionp start endpoints)
           (rationalp (lw-log-partition-lower start endpoints)))
  :hints (("Goal" :use (lw-log-partition-types)
                  :in-theory (disable lw-positive-partitionp lw-log-partition-lower
                                      lw-log-partition-upper lw-log-partition-types)))
  :rule-classes (:rewrite :type-prescription))

(defthm lw-log-partition-upper-rational
  (implies (lw-positive-partitionp start endpoints)
           (rationalp (lw-log-partition-upper start endpoints)))
  :hints (("Goal" :use (lw-log-partition-types)
                  :in-theory (disable lw-positive-partitionp lw-log-partition-lower
                                      lw-log-partition-upper lw-log-partition-types)))
  :rule-classes (:rewrite :type-prescription))

(local
 (defthm lw-partition-cell-compare
   (implies (and (rationalp start) (< 0 start) (rationalp end) (<= start end))
            (<= (/ (- end start) end) (/ (- end start) start)))
   :hints (("Goal" :use ((:instance lw-reciprocal-antitone (left start) (right end))
                         (:instance lw-partition-multiply-inequality
                           (left (/ end)) (right (/ start)) (factor (- end start))))
                   :in-theory (disable lw-reciprocal-antitone)))
   :rule-classes nil))

(local
 (defthm lw-partition-lower-split
   (implies (and (rationalp start) (< 0 start) (rationalp cut) (<= start cut)
                 (rationalp end) (<= cut end))
            (<= (/ (- end start) end)
                (+ (/ (- cut start) cut) (/ (- end cut) end))))
   :hints (("Goal" :use ((:instance lw-reciprocal-antitone (left cut) (right end))
                         (:instance lw-partition-multiply-inequality
                           (left (/ end)) (right (/ cut)) (factor (- cut start))))
                   :in-theory (disable lw-reciprocal-antitone)))
   :rule-classes nil))

(local
 (defthm lw-partition-upper-split
   (implies (and (rationalp start) (< 0 start) (rationalp cut) (<= start cut)
                 (rationalp end) (<= cut end))
            (<= (+ (/ (- cut start) start) (/ (- end cut) cut))
                (/ (- end start) start)))
   :hints (("Goal" :use ((:instance lw-reciprocal-antitone (left start) (right cut))
                         (:instance lw-partition-multiply-inequality
                           (left (/ cut)) (right (/ start)) (factor (- end cut))))
                   :in-theory (disable lw-reciprocal-antitone)))
   :rule-classes nil))

(local
 (defun lw-log-partition-comparison-induction (start left right)
   (declare (xargs :measure (+ (acl2-count left) (acl2-count right))))
   (if (or (endp left) (endp right)) (list start left right)
     (if (< (car left) (car right))
         (lw-log-partition-comparison-induction (car left) (cdr left) right)
       (if (< (car right) (car left))
           (lw-log-partition-comparison-induction (car right) left (cdr right))
         (lw-log-partition-comparison-induction (car left) (cdr left) (cdr right)))))))

; Any lower rectangle sum lies below any upper rectangle sum on the same
; rational interval, even when their mesh points do not align.
(defthm lw-log-partitions-compare
  (implies (and (lw-positive-partitionp start left)
                (lw-positive-partitionp start right)
                (equal (lw-partition-end start left) (lw-partition-end start right)))
           (<= (lw-log-partition-lower start left) (lw-log-partition-upper start right)))
  :hints (("Goal" :induct (lw-log-partition-comparison-induction start left right)
                  :do-not '(generalize eliminate-destructors))
          (and stable-under-simplificationp
               '(:use ((:instance lw-partition-end-bounds (endpoints left))
                        (:instance lw-partition-end-bounds (endpoints right))
                        (:instance lw-log-partition-types (endpoints left))
                        (:instance lw-log-partition-types (endpoints right))
                        (:instance lw-partition-cell-compare (end (car left)))
                        (:instance lw-partition-cell-compare (end (car right)))
                        (:instance lw-partition-lower-split (cut (car right)) (end (car left)))
                        (:instance lw-partition-upper-split (cut (car left)) (end (car right))))
                 :expand ((lw-positive-partitionp start left)
                          (lw-positive-partitionp start right)
                          (lw-positive-partitionp (car left) right)
                          (lw-positive-partitionp (car right) left)
                          (lw-partition-end start left) (lw-partition-end start right)
                          (lw-partition-end (car left) right) (lw-partition-end (car right) left)
                          (lw-log-partition-lower start left) (lw-log-partition-upper start right)
                          (lw-log-partition-lower (car right) left)
                          (lw-log-partition-upper (car left) right))
                 :in-theory (disable lw-partition-end-bounds lw-log-partition-types)))))

(defun lw-uniform-log-partition (start step count)
  (declare (xargs :measure (nfix count)))
  (if (zp count) nil
    (cons (+ start step) (lw-uniform-log-partition (+ start step) step (- count 1)))))

(defthm lw-uniform-log-partition-valid
  (implies (and (rationalp start) (< 0 start) (rationalp step) (< 0 step))
           (lw-positive-partitionp start (lw-uniform-log-partition start step count)))
  :hints (("Goal" :induct (lw-uniform-log-partition start step count))))

(defthm lw-uniform-log-partition-end
  (implies (and (rationalp start) (rationalp step) (natp count))
           (equal (lw-partition-end start (lw-uniform-log-partition start step count))
                  (+ start (* count step))))
  :hints (("Goal" :induct (lw-uniform-log-partition start step count))))

(defthm lw-uniform-log-partition-sums
  (implies (and (rationalp start) (< 0 start) (rationalp step) (< 0 step) (natp count))
           (and (equal (lw-log-partition-lower start (lw-uniform-log-partition start step count))
                       (car (lw-log-rectangles start step count)))
                (equal (lw-log-partition-upper start (lw-uniform-log-partition start step count))
                       (cdr (lw-log-rectangles start step count)))))
  :hints (("Goal" :induct (lw-uniform-log-partition start step count))))

(defthm lw-log-rectangles-compare
  (implies (and (rationalp start) (< 0 start)
                (rationalp left-step) (< 0 left-step) (natp left-count)
                (rationalp right-step) (< 0 right-step) (natp right-count)
                (equal (* left-count left-step) (* right-count right-step)))
           (<= (car (lw-log-rectangles start left-step left-count))
               (cdr (lw-log-rectangles start right-step right-count))))
  :hints (("Goal" :use ((:instance lw-log-partitions-compare
                          (left (lw-uniform-log-partition start left-step left-count))
                          (right (lw-uniform-log-partition start right-step right-count))))
                  :in-theory (disable lw-uniform-log-partition lw-log-partitions-compare
                                      lw-log-rectangles lw-positive-partitionp))))

(defthm lw-log-bounds-overlap
  (implies (and (rationalp value) (< 1 value)
                (rationalp left-error) (< 0 left-error)
                (rationalp right-error) (< 0 right-error))
           (<= (car (lw-log-bounds value left-error)) (cdr (lw-log-bounds value right-error))))
  :hints (("Goal" :use ((:instance lw-log-rectangles-compare
                          (start 1)
                          (left-step (/ (- value 1) (lw-log-count value left-error)))
                          (left-count (lw-log-count value left-error))
                          (right-step (/ (- value 1) (lw-log-count value right-error)))
                          (right-count (lw-log-count value right-error)))
                        (:instance lw-log-step-positive (epsilon left-error))
                        (:instance lw-log-step-positive (epsilon right-error))
                        (:instance lw-log-grid-endpoint (epsilon left-error))
                        (:instance lw-log-grid-endpoint (epsilon right-error)))
                  :in-theory (disable lw-log-rectangles lw-log-count lw-log-rectangles-compare
                                      lw-log-step-positive lw-log-grid-endpoint))))

(defthm lw-positive-partition-true-list
  (implies (lw-positive-partitionp start endpoints) (true-listp endpoints)))

(defthm lw-positive-partition-append
  (implies (and (lw-positive-partitionp start prefix)
                (lw-positive-partitionp (lw-partition-end start prefix) suffix))
           (lw-positive-partitionp start (append prefix suffix)))
  :hints (("Goal" :induct (lw-positive-partitionp start prefix))))

(defthm lw-partition-end-append
  (implies (true-listp prefix)
           (equal (lw-partition-end start (append prefix suffix))
                  (lw-partition-end (lw-partition-end start prefix) suffix))))

(defthm lw-log-partition-append-sums
  (implies (and (lw-positive-partitionp start prefix)
                (lw-positive-partitionp (lw-partition-end start prefix) suffix))
           (and (equal (lw-log-partition-lower start (append prefix suffix))
                       (+ (lw-log-partition-lower start prefix)
                          (lw-log-partition-lower (lw-partition-end start prefix) suffix)))
                (equal (lw-log-partition-upper start (append prefix suffix))
                       (+ (lw-log-partition-upper start prefix)
                          (lw-log-partition-upper (lw-partition-end start prefix) suffix)))))
  :hints (("Goal" :induct (lw-positive-partitionp start prefix))))

(defthm lw-positive-partition-append-single
  (implies (and (lw-positive-partitionp start endpoints) (rationalp end)
                (< (lw-partition-end start endpoints) end))
           (lw-positive-partitionp start (append endpoints (list end))))
  :hints (("Goal" :induct (lw-positive-partitionp start endpoints))))

(defthm lw-partition-end-append-single
  (equal (lw-partition-end start (append endpoints (list end))) end))

(defthm lw-log-upper-append-single
  (implies (and (lw-positive-partitionp start endpoints) (rationalp end)
                (< (lw-partition-end start endpoints) end))
           (equal (lw-log-partition-upper start (append endpoints (list end)))
                  (+ (lw-log-partition-upper start endpoints)
                     (/ (- end (lw-partition-end start endpoints))
                        (lw-partition-end start endpoints)))))
  :hints (("Goal" :induct (lw-positive-partitionp start endpoints))))

(defthm lw-log-lower-append-monotone
  (implies (and (lw-positive-partitionp start endpoints) (rationalp end)
                (< (lw-partition-end start endpoints) end))
           (<= (lw-log-partition-lower start endpoints)
               (lw-log-partition-lower start (append endpoints (list end)))))
  :hints (("Goal" :induct (lw-positive-partitionp start endpoints))
          (and stable-under-simplificationp
               '(:use ((:instance lw-log-partition-types (endpoints (list end))))
                 :in-theory (disable lw-log-partition-types)))))

(defthm lw-log-rectangles-ordered-compare
  (implies (and (rationalp start) (< 0 start)
                (rationalp left-step) (< 0 left-step) (natp left-count)
                (rationalp right-step) (< 0 right-step) (natp right-count)
                (<= (* left-count left-step) (* right-count right-step)))
           (<= (car (lw-log-rectangles start left-step left-count))
               (cdr (lw-log-rectangles start right-step right-count))))
  :hints (("Goal" :cases ((equal (* left-count left-step) (* right-count right-step)))
                  :use (lw-log-rectangles-compare
                        (:instance lw-log-partitions-compare
                          (left (append (lw-uniform-log-partition start left-step left-count)
                                         (list (+ start (* right-count right-step)))))
                          (right (lw-uniform-log-partition start right-step right-count)))
                        (:instance lw-log-lower-append-monotone
                          (endpoints (lw-uniform-log-partition start left-step left-count))
                          (end (+ start (* right-count right-step)))))
                  :in-theory (disable lw-uniform-log-partition lw-log-partitions-compare
                                      lw-log-rectangles lw-positive-partitionp lw-log-rectangles-compare
                                      lw-log-lower-append-monotone)
                  :nonlinearp t)))

(defthm lw-log-bounds-monotone-overlap
  (implies (and (rationalp left) (rationalp right) (< 1 left) (<= left right)
                (rationalp left-error) (< 0 left-error)
                (rationalp right-error) (< 0 right-error))
           (<= (car (lw-log-bounds left left-error)) (cdr (lw-log-bounds right right-error))))
  :hints (("Goal" :use ((:instance lw-log-rectangles-ordered-compare
                          (start 1)
                          (left-step (/ (- left 1) (lw-log-count left left-error)))
                          (left-count (lw-log-count left left-error))
                          (right-step (/ (- right 1) (lw-log-count right right-error)))
                          (right-count (lw-log-count right right-error)))
                        (:instance lw-log-step-positive (value left) (epsilon left-error))
                        (:instance lw-log-step-positive (value right) (epsilon right-error))
                        (:instance lw-log-grid-endpoint (value left) (epsilon left-error))
                        (:instance lw-log-grid-endpoint (value right) (epsilon right-error)))
                  :in-theory (disable lw-log-rectangles lw-log-count lw-log-rectangles-ordered-compare
                                      lw-log-step-positive lw-log-grid-endpoint))))

(defthm lw-log-rectangles-growth-compare
  (implies (and (rationalp start) (< 0 start)
                (rationalp left-step) (< 0 left-step) (natp left-count)
                (rationalp right-step) (< 0 right-step) (natp right-count)
                (< (* left-count left-step) (* right-count right-step)))
           (<= (car (lw-log-rectangles start right-step right-count))
               (+ (cdr (lw-log-rectangles start left-step left-count))
                  (/ (- (* right-count right-step) (* left-count left-step))
                     (+ start (* left-count left-step))))))
  :hints (("Goal" :use ((:instance lw-log-partitions-compare
                          (left (lw-uniform-log-partition start right-step right-count))
                          (right (append (lw-uniform-log-partition start left-step left-count)
                                         (list (+ start (* right-count right-step)))))))
                  :in-theory (disable lw-uniform-log-partition lw-log-partitions-compare
                                      lw-log-rectangles lw-positive-partitionp))))

(defthm lw-log-bounds-growth-compare
  (implies (and (rationalp left) (rationalp right) (< 1 left) (< left right)
                (rationalp left-error) (< 0 left-error)
                (rationalp right-error) (< 0 right-error))
           (<= (car (lw-log-bounds right right-error))
               (+ (cdr (lw-log-bounds left left-error)) (/ (- right left) left))))
  :hints (("Goal" :use ((:instance lw-log-rectangles-growth-compare
                          (start 1)
                          (left-step (/ (- left 1) (lw-log-count left left-error)))
                          (left-count (lw-log-count left left-error))
                          (right-step (/ (- right 1) (lw-log-count right right-error)))
                          (right-count (lw-log-count right right-error)))
                        (:instance lw-log-step-positive (value left) (epsilon left-error))
                        (:instance lw-log-step-positive (value right) (epsilon right-error))
                        (:instance lw-log-grid-endpoint (value left) (epsilon left-error))
                        (:instance lw-log-grid-endpoint (value right) (epsilon right-error)))
                  :in-theory (disable lw-log-rectangles lw-log-count lw-log-rectangles-growth-compare
                                      lw-log-step-positive lw-log-grid-endpoint))))

(defthm lw-log-bounds-lipschitz-budget
  (implies (and (rationalp left) (rationalp right) (< 1 left) (<= left right)
                (rationalp left-error) (< 0 left-error)
                (rationalp right-error) (< 0 right-error))
           (<= (- (cdr (lw-log-bounds right right-error)) (car (lw-log-bounds left left-error)))
               (+ (- right left) left-error right-error)))
  :hints (("Goal" :cases ((equal left right))
                  :use (lw-log-bounds-growth-compare
                        (:instance lw-log-bounds-overlap (value left)
                          (left-error right-error) (right-error left-error))
                        (:instance lw-log-bounds-width (value left) (epsilon left-error))
                        (:instance lw-log-bounds-width (value right) (epsilon right-error))
                        (:instance lw-log-bounds-interval (value left) (epsilon left-error))
                        (:instance lw-log-bounds-interval (value right) (epsilon right-error))
                        (:instance lw-reciprocal-antitone (left 1) (right left))
                        (:instance lw-partition-multiply-inequality
                          (left (/ left)) (right 1) (factor (- right left))))
                  :in-theory (disable lw-log-bounds lw-log-bounds-growth-compare
                                      lw-log-bounds-overlap lw-log-bounds-width lw-log-bounds-interval
                                      lw-log-bounds-monotone-overlap lw-reciprocal-antitone))))

(defthm lw-log-bounds-cross-budget
  (implies (and (rationalp left) (rationalp right) (< 1 left) (< 1 right)
                (rationalp left-error) (< 0 left-error)
                (rationalp right-error) (< 0 right-error))
           (<= (- (cdr (lw-log-bounds right right-error)) (car (lw-log-bounds left left-error)))
               (+ (abs (- right left)) left-error right-error)))
  :hints (("Goal" :cases ((<= left right))
                  :use (lw-log-bounds-lipschitz-budget
                        (:instance lw-log-bounds-monotone-overlap
                          (left right) (right left) (left-error right-error) (right-error left-error))
                        (:instance lw-log-bounds-width (value left) (epsilon left-error))
                        (:instance lw-log-bounds-width (value right) (epsilon right-error))
                        (:instance lw-log-bounds-interval (value left) (epsilon left-error))
                        (:instance lw-log-bounds-interval (value right) (epsilon right-error)))
                  :in-theory (disable lw-log-bounds lw-log-bounds-lipschitz-budget
                                      lw-log-bounds-monotone-overlap lw-log-bounds-width
                                      lw-log-bounds-interval))))

(defthm lw-log-enclosed-values-lipschitz
  (implies (and (rationalp left) (rationalp right) (< 1 left) (< 1 right)
                (rationalp left-error) (< 0 left-error)
                (rationalp right-error) (< 0 right-error)
                (lw-contains (lw-log-bounds left left-error) left-value)
                (lw-contains (lw-log-bounds right right-error) right-value))
           (<= (abs (- right-value left-value))
               (+ (abs (- right left)) left-error right-error)))
  :hints (("Goal" :use (lw-log-bounds-cross-budget
                        (:instance lw-log-bounds-cross-budget
                          (left right) (right left) (left-error right-error) (right-error left-error)))
                  :in-theory (disable lw-log-bounds lw-log-bounds-cross-budget))))

(defthm lw-log-lower-cauchy
  (implies (and (rationalp value) (< 1 value)
                (rationalp left-error) (< 0 left-error)
                (rationalp right-error) (< 0 right-error))
           (<= (abs (- (car (lw-log-bounds value left-error))
                       (car (lw-log-bounds value right-error))))
               (+ left-error right-error)))
  :hints (("Goal" :use ((:instance lw-log-enclosed-values-lipschitz
                          (left value) (right value)
                          (left-value (car (lw-log-bounds value right-error)))
                          (right-value (car (lw-log-bounds value left-error)))
                          (left-error right-error) (right-error left-error))
                        (:instance lw-log-bounds-interval (epsilon left-error))
                        (:instance lw-log-bounds-interval (epsilon right-error)))
                  :in-theory (disable lw-log-bounds lw-log-enclosed-values-lipschitz
                                      lw-log-bounds-interval))))

(defthm lw-log-bounds-lower-coarse
  (implies (and (rationalp value) (< 1 value) (rationalp epsilon) (< 0 epsilon))
           (and (<= 0 (car (lw-log-bounds value epsilon)))
                (<= (car (lw-log-bounds value epsilon)) (- value 1))))
  :hints (("Goal" :use ((:instance lw-log-partitions-compare
                          (start 1)
                          (left (lw-uniform-log-partition 1 (/ (- value 1) (lw-log-count value epsilon))
                                                           (lw-log-count value epsilon)))
                          (right (list value)))
                        (:instance lw-log-rectangles-nonnegative
                          (start 1) (step (/ (- value 1) (lw-log-count value epsilon)))
                          (count (lw-log-count value epsilon)))
                        lw-log-step-positive lw-log-grid-endpoint)
                  :in-theory (disable lw-uniform-log-partition lw-log-partitions-compare
                                      lw-log-rectangles lw-log-count lw-log-rectangles-nonnegative
                                      lw-log-step-positive))))

(defthm lw-log-bounds-one-sided-transport
  (implies (and (rationalp left) (rationalp right) (< 1 left) (< 1 right)
                (rationalp left-error) (< 0 left-error)
                (rationalp right-error) (< 0 right-error))
           (<= (- (car (lw-log-bounds right right-error)) (cdr (lw-log-bounds left left-error)))
               (abs (- right left))))
  :hints (("Goal" :cases ((< left right))
                  :use (lw-log-bounds-growth-compare
                        (:instance lw-log-bounds-monotone-overlap
                          (left right) (right left) (left-error right-error) (right-error left-error))
                        (:instance lw-log-bounds-interval (value left) (epsilon left-error))
                        (:instance lw-log-bounds-interval (value right) (epsilon right-error))
                        (:instance lw-reciprocal-antitone (left 1) (right left))
                        (:instance lw-partition-multiply-inequality
                          (left (/ left)) (right 1) (factor (- right left))))
                  :in-theory (disable lw-log-bounds lw-log-bounds-growth-compare
                                      lw-log-bounds-monotone-overlap lw-log-bounds-interval
                                      lw-reciprocal-antitone))))

(assert-event (and (lw-positive-partitionp 1 '(2 3 5))
                   (lw-positive-partitionp 1 '(3/2 4 5))
                   (<= (lw-log-partition-lower 1 '(2 3 5))
                       (lw-log-partition-upper 1 '(3/2 4 5)))))
(assert-event (<= (abs (- (car (lw-log-bounds 2 1/100))
                          (car (lw-log-bounds 2 1/20))))
                  (+ 1/100 1/20)))
