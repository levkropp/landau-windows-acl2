(in-package "ACL2")

(include-book "log-partitions")
(include-book "euler-bounds")

(defthm lw-harmonic-successor
  (implies (natp count)
           (equal (lw-harmonic (+ 1 count)) (+ (/ (+ 1 count)) (lw-harmonic count))))
  :hints (("Goal" :expand ((lw-harmonic (+ 1 count))) :in-theory (disable lw-harmonic))))

(defthm lw-log-unit-lower
  (implies (and (posp start) (natp count))
           (equal (car (lw-log-rectangles start 1 count))
                  (- (lw-harmonic (+ start count)) (lw-harmonic start))))
  :hints (("Goal" :induct (lw-log-rectangles start 1 count)
                  :in-theory (disable lw-harmonic))
          (and stable-under-simplificationp
               '(:use ((:instance lw-harmonic-successor (count start)))
                 :in-theory (disable lw-harmonic lw-harmonic-successor lw-log-rectangles)))))

(defthm lw-log-unit-upper
  (implies (and (posp start) (natp count))
           (equal (cdr (lw-log-rectangles start 1 count))
                  (+ (- (lw-harmonic (+ start count)) (lw-harmonic start))
                     (/ start) (- (/ (+ start count))))))
  :hints (("Goal" :use (lw-log-unit-lower
                        (:instance lw-log-rectangles-width (step 1))
                        (:instance lw-log-rectangles-interval (step 1)))
                  :in-theory (disable lw-log-rectangles lw-harmonic lw-log-unit-lower
                                      lw-log-rectangles-width lw-log-rectangles-interval))))

; Comparing a log partition followed by the integer partition from m to n
; against any other log partition gives both harmonic/log tail inequalities.
(defthm lw-harmonic-log-tail-bounds
  (implies (and (integerp small) (<= 2 small) (integerp large) (<= small large)
                (rationalp small-error) (< 0 small-error)
                (rationalp large-error) (< 0 large-error))
           (and (<= (+ (car (lw-log-bounds small small-error))
                        (- (lw-harmonic large) (lw-harmonic small)))
                    (cdr (lw-log-bounds large large-error)))
                (<= (car (lw-log-bounds large large-error))
                    (+ (cdr (lw-log-bounds small small-error))
                       (- (lw-harmonic large) (lw-harmonic small))
                       (/ small) (- (/ large))))))
  :hints (("Goal"
           :use ((:instance lw-log-partitions-compare
                   (start 1)
                   (left (append
                          (lw-uniform-log-partition 1 (/ (- small 1) (lw-log-count small small-error))
                                                    (lw-log-count small small-error))
                          (lw-uniform-log-partition small 1 (- large small))))
                   (right (lw-uniform-log-partition 1 (/ (- large 1) (lw-log-count large large-error))
                                                     (lw-log-count large large-error))))
                 (:instance lw-log-partitions-compare
                   (start 1)
                   (left (lw-uniform-log-partition 1 (/ (- large 1) (lw-log-count large large-error))
                                                    (lw-log-count large large-error)))
                   (right (append
                           (lw-uniform-log-partition 1 (/ (- small 1) (lw-log-count small small-error))
                                                     (lw-log-count small small-error))
                           (lw-uniform-log-partition small 1 (- large small)))))
                 (:instance lw-log-step-positive (value small) (epsilon small-error))
                 (:instance lw-log-step-positive (value large) (epsilon large-error))
                 (:instance lw-log-grid-endpoint (value small) (epsilon small-error))
                 (:instance lw-log-grid-endpoint (value large) (epsilon large-error)))
           :in-theory (disable lw-uniform-log-partition lw-log-rectangles lw-log-count
                               lw-positive-partitionp lw-log-partitions-compare lw-harmonic
                               lw-log-step-positive))))

(defthm lw-euler-log-enclosures-overlap
  (implies (and (integerp left-count) (<= 2 left-count)
                (integerp right-count) (<= 2 right-count)
                (rationalp left-error) (< 0 left-error)
                (rationalp right-error) (< 0 right-error))
           (<= (car (lw-euler-from-log left-count (lw-log-bounds left-count left-error)))
               (cdr (lw-euler-from-log right-count (lw-log-bounds right-count right-error)))))
  :hints (("Goal" :cases ((<= left-count right-count))
                  :use ((:instance lw-harmonic-log-tail-bounds
                          (small left-count) (large right-count)
                          (small-error left-error) (large-error right-error))
                        (:instance lw-harmonic-log-tail-bounds
                          (small right-count) (large left-count)
                          (small-error right-error) (large-error left-error))
                        (:instance lw-log-bounds-interval (value left-count) (epsilon left-error))
                        (:instance lw-log-bounds-interval (value right-count) (epsilon right-error)))
                  :in-theory (disable lw-log-bounds lw-harmonic lw-harmonic-log-tail-bounds
                                      lw-log-bounds-interval))))

(defthm lw-euler-count-at-least-three
  (implies (and (rationalp epsilon) (< 0 epsilon)) (<= 3 (lw-euler-count epsilon)))
  :hints (("Goal" :use ((:instance lw-denominator-at-least-one (value epsilon))
                        (:instance rational-implies1 (x epsilon)))
                  :in-theory (disable lw-denominator-at-least-one))))

(defthm lw-euler-bounds-overlap
  (implies (and (rationalp left-error) (< 0 left-error)
                (rationalp right-error) (< 0 right-error))
           (<= (car (lw-euler-bounds left-error)) (cdr (lw-euler-bounds right-error))))
  :hints (("Goal" :use ((:instance lw-euler-log-enclosures-overlap
                          (left-count (lw-euler-count left-error)) (left-error (/ left-error 2))
                          (right-count (lw-euler-count right-error)) (right-error (/ right-error 2)))
                        (:instance lw-euler-count-at-least-three (epsilon left-error))
                        (:instance lw-euler-count-at-least-three (epsilon right-error)))
                  :in-theory (disable lw-euler-count lw-euler-from-log lw-log-bounds
                                      lw-euler-log-enclosures-overlap lw-euler-count-at-least-three))))

(defthm lw-euler-enclosed-values-cauchy
  (implies (and (rationalp left-error) (< 0 left-error)
                (rationalp right-error) (< 0 right-error)
                (lw-contains (lw-euler-bounds left-error) left-value)
                (lw-contains (lw-euler-bounds right-error) right-value))
           (<= (abs (- right-value left-value)) (+ left-error right-error)))
  :hints (("Goal" :use (lw-euler-bounds-overlap
                        (:instance lw-euler-bounds-overlap (left-error right-error) (right-error left-error))
                        (:instance lw-euler-bounds-width (epsilon left-error))
                        (:instance lw-euler-bounds-width (epsilon right-error)))
                  :in-theory (disable lw-euler-bounds lw-euler-bounds-overlap lw-euler-bounds-width))))

(defthm lw-euler-lower-cauchy
  (implies (and (rationalp left-error) (< 0 left-error)
                (rationalp right-error) (< 0 right-error))
           (<= (abs (- (car (lw-euler-bounds left-error)) (car (lw-euler-bounds right-error))))
               (+ left-error right-error)))
  :hints (("Goal" :use ((:instance lw-euler-enclosed-values-cauchy
                          (left-value (car (lw-euler-bounds right-error)))
                          (right-value (car (lw-euler-bounds left-error)))
                          (left-error right-error) (right-error left-error))
                        (:instance lw-euler-bounds-interval (epsilon left-error))
                        (:instance lw-euler-bounds-interval (epsilon right-error)))
                  :in-theory (disable lw-euler-bounds lw-euler-enclosed-values-cauchy
                                      lw-euler-bounds-interval))))

(local (defthm lw-ec-harmonic-one (equal (lw-harmonic 1) 1)))

(defthm lw-euler-log-enclosure-coarse
  (implies (and (integerp count) (<= 2 count) (rationalp epsilon) (< 0 epsilon))
           (let ((bounds (lw-euler-from-log count (lw-log-bounds count epsilon))))
             (and (<= (- epsilon) (car bounds)) (<= (cdr bounds) (+ 1 epsilon)))))
  :hints (("Goal"
           :use ((:instance lw-log-rectangles-compare
                   (start 1) (left-step 1) (left-count (- count 1))
                   (right-step (/ (- count 1) (lw-log-count count epsilon)))
                   (right-count (lw-log-count count epsilon)))
                 (:instance lw-log-rectangles-compare
                   (start 1) (right-step 1) (right-count (- count 1))
                   (left-step (/ (- count 1) (lw-log-count count epsilon)))
                   (left-count (lw-log-count count epsilon)))
                 (:instance lw-log-step-positive (value count))
                 (:instance lw-log-grid-endpoint (value count))
                 (:instance lw-log-bounds-width (value count))
                 (:instance lw-log-bounds-interval (value count)))
           :in-theory (disable lw-log-rectangles lw-log-count lw-harmonic
                               lw-log-rectangles-compare lw-log-step-positive
                               lw-log-grid-endpoint
                               lw-log-rectangles-width lw-log-rectangles-interval
                               lw-log-bounds-width lw-log-bounds-interval))))

(defthm lw-euler-bounds-coarse
  (implies (and (rationalp epsilon) (< 0 epsilon) (<= epsilon 1))
           (and (<= -1 (car (lw-euler-bounds epsilon)))
                (<= (cdr (lw-euler-bounds epsilon)) 2)))
  :hints (("Goal" :use ((:instance lw-euler-log-enclosure-coarse
                          (count (lw-euler-count epsilon)) (epsilon (/ epsilon 2)))
                        lw-euler-count-at-least-three)
                  :in-theory (disable lw-euler-count lw-log-bounds lw-euler-from-log
                                      lw-euler-log-enclosure-coarse lw-euler-count-at-least-three))))

(assert-event (<= (abs (- (car (lw-euler-bounds 1/2)) (car (lw-euler-bounds 1/4)))) 3/4))
