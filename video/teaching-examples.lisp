; Teaching examples for Part Zero. Independent of the Landau proof books.
(in-package "ACL2")

(defun video-odd-sum (n)
  (if (zp n)
      0
    (+ (video-odd-sum (1- n)) (- (* 2 n) 1))))

(defthm video-zero-plus-n
  (implies (natp n) (equal (+ 0 n) n))
  :rule-classes nil)

(defthm video-add-successor
  (implies (and (natp x) (natp y))
           (equal (+ x (+ 1 y)) (+ 1 (+ x y))))
  :rule-classes nil)

(defthm video-multiply-successor
  (implies (and (natp x) (natp y))
           (equal (* x (+ 1 y)) (+ (* x y) x)))
  :rule-classes nil)

(defthm video-order-witness
  (implies (and (natp x) (natp y) (<= x y))
           (and (natp (- y x)) (equal (+ x (- y x)) y)))
  :rule-classes nil)

(defthm video-odd-sum-next
  (implies (natp n)
           (equal (video-odd-sum (+ 1 n))
                  (+ (video-odd-sum n) (* 2 n) 1)))
  :rule-classes nil)

(defthm video-odd-sum-square
  (implies (natp n)
           (equal (video-odd-sum n) (* n n)))
  :hints (("Goal" :induct (video-odd-sum n)))
  :rule-classes nil)

(assert-event (equal (+ 2 (+ 1 1)) 4))
(assert-event (not (equal (+ 1 (+ 1 1)) 4)))
