; Part Two: isolated teaching copy of the interval kernel and its guarantees.
; The five lw-* definitions match acl2/interval-search.lisp verbatim.
(in-package "ACL2")

(defun lw-intervalp (bounds)
  (and (consp bounds)
       (rationalp (car bounds))
       (rationalp (cdr bounds))
       (<= (car bounds) (cdr bounds))))

(defun lw-contains (bounds value)
  (and (lw-intervalp bounds)
       (rationalp value)
       (<= (car bounds) value)
       (<= value (cdr bounds))))

(defun lw-interval-add (left right)
  (cons (+ (car left) (car right))
        (+ (cdr left) (cdr right))))

(defun lw-interval-sub (left right)
  (cons (- (car left) (cdr right))
        (- (cdr left) (car right))))

(defun lw-interval-scale (coefficient bounds)
  (if (<= 0 coefficient)
      (cons (* coefficient (car bounds)) (* coefficient (cdr bounds)))
    (cons (* coefficient (cdr bounds)) (* coefficient (car bounds)))))

(defthm lw-contains-add
  (implies (and (lw-contains left left-value)
                (lw-contains right right-value))
           (lw-contains
             (lw-interval-add left right)
             (+ left-value right-value)))
  :rule-classes nil)

(defthm lw-contains-sub
  (implies (and (lw-contains left left-value)
                (lw-contains right right-value))
           (lw-contains
             (lw-interval-sub left right)
             (- left-value right-value)))
  :rule-classes nil)

(defthm lw-contains-scale
  (implies (and (rationalp coefficient)
                (lw-contains bounds value))
           (lw-contains
             (lw-interval-scale coefficient bounds)
             (* coefficient value)))
  :hints (("Goal" :nonlinearp t))
  :rule-classes nil)

(defthm lw-lower-gt-of-margin
  (implies (and (lw-contains bounds value)
                (rationalp threshold)
                (rationalp error)
                (<= (- (cdr bounds) (car bounds)) error)
                (< (+ threshold error) value))
           (< threshold (car bounds)))
  :rule-classes nil)

(defthm video-rational-sum-example
  (equal (+ 1/3 1/6) 1/2)
  :rule-classes nil)

(defthm video-interval-add-width
  (implies (and (lw-intervalp left) (lw-intervalp right))
           (equal (- (cdr (lw-interval-add left right))
                     (car (lw-interval-add left right)))
                  (+ (- (cdr left) (car left))
                     (- (cdr right) (car right)))))
  :rule-classes nil)

(defthm video-interval-sub-width
  (implies (and (lw-intervalp left) (lw-intervalp right))
           (equal (- (cdr (lw-interval-sub left right))
                     (car (lw-interval-sub left right)))
                  (+ (- (cdr left) (car left))
                     (- (cdr right) (car right)))))
  :rule-classes nil)

(defthm video-positive-lower-sound
  (implies (and (lw-contains bounds value) (< 0 (car bounds)))
           (< 0 value))
  :rule-classes nil)

(assert-event (and (equal 4/6 2/3) (<= 1/2 2/3) (<= 2/3 3/4)))
(assert-event (equal (- 1/3 333/1000) 1/3000))
(assert-event (equal (* 3 333/1000) 999/1000))
(assert-event (equal (cons 1/2 3/4) '(1/2 . 3/4)))
(assert-event (equal (lw-interval-add '(1/2 . 3/4) '(1/4 . 1/3))
                     '(3/4 . 13/12)))
(assert-event (equal (lw-interval-sub '(1/2 . 3/4) '(1/4 . 1/3))
                     '(1/6 . 1/2)))
(assert-event (equal (lw-interval-scale 2 '(1/2 . 3/4)) '(1 . 3/2)))
(assert-event (equal (lw-interval-scale -2 '(1/2 . 3/4)) '(-3/2 . -1)))
(assert-event (equal (lw-interval-sub (lw-interval-scale 2 '(99/100 . 101/100))
                                     '(199/100 . 201/100))
                     '(-3/100 . 3/100)))
(assert-event (equal (lw-interval-sub (lw-interval-scale 2 '(1001/1000 . 1003/1000))
                                     '(1999/1000 . 2001/1000))
                     '(1/1000 . 7/1000)))
(assert-event (lw-contains '(3/20 . 1/4) 1/5))
(assert-event (equal (- 1/4 3/20) 1/10))
(assert-event (and (< (* 7 7) (* 2 5 5)) (< (* 2 2 2) (* 3 3))))
