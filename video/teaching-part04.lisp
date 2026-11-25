; Part Four imports the actual project evaluator.  prepare_part_four.py
; mirrors this relative layout in video/.tools/acl2-part04/ and certifies
; all dependency sources there, without writing to the project proof tree.
(in-package "ACL2")
(include-book "../acl2/signal-bounds")

(defthm video-prime-power-examples
  (and (equal (lw-prime-power-data 16) '(2 . 4))
       (equal (lw-prime-power-data 13) '(13 . 1))
       (not (lw-prime-power-data 6))
       (not (lw-prime-power-data 1)))
  :rule-classes nil)

(defthm video-log2-four-rectangles
  (equal (lw-log-rectangles 1 1/4 4) '(533/840 . 319/420))
  :rule-classes nil)

(defthm video-ramp-padding-zero
  (implies (and (rationalp value) (<= 1 value)
                (posp index) (<= value index))
           (equal (lw-ramp value index) 0))
  :hints (("Goal" :use ((:instance lw-positive-division-bound
                          (numerator value) (divisor index) (bound 1)))))
  :rule-classes nil)

(defthm video-smoothed-example
  (equal (lw-smoothed-sum-bounds 9/2 9 1)
         (lw-interval-add
           (lw-interval-scale 11/8 (lw-log-bounds 2 1))
           (lw-interval-scale 1/2 (lw-log-bounds 3 1))))
  :rule-classes nil)

(defthm video-gz-width-budget
  (<= (lw-interval-width (lw-gz-bounds-raw 9/2 9 1/202)) 1/4)
  :hints (("Goal" :use ((:instance lw-gz-bounds-raw-width
                          (value 9/2) (count 9) (epsilon 1/202)))
                  :in-theory (disable lw-gz-bounds-raw-width
                                      lw-gz-bounds-raw lw-interval-width)))
  :rule-classes nil)

(defthm video-gz-two-positive
  (< 0 (car (lw-gz-bounds-raw 2 2 1)))
  :rule-classes nil)

(assert-event (and (lw-primep 2) (lw-primep 13)
                   (not (lw-primep 1)) (not (lw-primep 4))))
(assert-event (equal (lw-prime-power-data 81) '(3 . 4)))
(assert-event (equal (lw-mangoldt-bounds 16 1) (lw-log-bounds 2 1)))
(assert-event (equal (lw-mangoldt-bounds 6 1) '(0 . 0)))
(assert-event (equal (lw-log-bounds 2 1) '(7/12 . 5/6)))
(assert-event (equal (lw-ramp 9/2 2) 5/4))
(assert-event (equal (lw-ramp 9/2 3) 1/2))
(assert-event (equal (lw-ramp 9/2 4) 1/8))
(assert-event (equal (lw-ramp 4 4) 0))
(assert-event (equal (lw-signal-count 9/2) 9))
(assert-event (equal (lw-smoothed-sum-bounds 9/2 9 1)
                     (lw-smoothed-sum-bounds 9/2 12 1)))
(assert-event (equal (lw-harmonic 4) 25/12))
(assert-event (equal (lw-gz-bounds-raw 2 2 1)
                     '(38114/45045 . 229381/90090)))
(assert-event (equal (lw-euler-bounds 1) '(23099/90090 . 77153/90090)))
(assert-event (equal (lw-smoothed-sum-bounds 9/2 9 1)
                     '(12661/10080 . 3061/1680)))
(assert-event (equal (lw-log-bounds 2 1/4) '(1627/2520 . 1879/2520)))
