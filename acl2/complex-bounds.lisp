(in-package "ACL2")

(include-book "mellin-sums")

(local (defthm lw-cb-multiply-left-commutes
         (equal (* left (* middle right)) (* middle (* left right)))
         :hints (("Goal" :use ((:instance associativity-of-* (x left) (y middle) (z right))
                              (:instance associativity-of-* (x middle) (y left) (z right))
                              (:instance commutativity-of-* (x left) (y middle)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-cb-times-negation
         (implies (and (rationalp left) (rationalp right))
                  (equal (* left (- right)) (- (* left right))))
         :hints (("Goal" :use ((:instance distributivity (x left) (y right) (z (- right))))
                         :in-theory (disable distributivity)))))

(local (defthm lw-cb-zero-product (equal (* 0 value) 0)))
(local (defthm lw-cb-minus-one-product
         (implies (rationalp value) (equal (* -1 value) (- value)))))
(local (defthm lw-cb-add-cancel
         (implies (and (rationalp value) (rationalp rest))
                  (equal (+ value (- value) rest) rest))))

(local (defthm lw-cb-square-nonnegative
         (implies (rationalp value) (<= 0 (* value value)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cb-multiply-order
         (implies (and (rationalp left) (rationalp right) (<= left right)
                       (rationalp factor) (<= 0 factor))
                  (<= (* left factor) (* right factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defun lw-complexp (point) (and (consp point) (rationalp (car point)) (rationalp (cdr point))))
(defun lw-complex-add (left right) (cons (+ (car left) (car right)) (+ (cdr left) (cdr right))))
(defun lw-complex-sub (left right) (cons (- (car left) (car right)) (- (cdr left) (cdr right))))
(defun lw-complex-scale (factor point) (cons (* factor (car point)) (* factor (cdr point))))
(defun lw-complex-mul (left right)
  (cons (- (* (car left) (car right)) (* (cdr left) (cdr right)))
        (+ (* (car left) (cdr right)) (* (cdr left) (car right)))))
(defun lw-complex-diskp (point radius) (and (lw-complexp point) (lw-diskp (car point) (cdr point) radius)))

(defthm lw-complex-disk-data
  (implies (lw-complex-diskp point radius)
           (and (lw-complexp point) (rationalp radius) (<= 0 radius)))
  :rule-classes (:rewrite :forward-chaining))

(defthm lw-complex-operations-rational
  (implies (and (lw-complexp left) (lw-complexp right) (rationalp factor))
           (and (lw-complexp (lw-complex-add left right))
                (lw-complexp (lw-complex-sub left right))
                (lw-complexp (lw-complex-scale factor left))
                (lw-complexp (lw-complex-mul left right)))))

(defthm lw-complex-add-disk
  (implies (and (lw-complex-diskp left radius) (lw-complex-diskp right other-radius))
           (lw-complex-diskp (lw-complex-add left right) (+ radius other-radius)))
  :hints (("Goal" :use ((:instance lw-disk-add
                          (x (car left)) (y (cdr left)) (u (car right)) (v (cdr right))))
                  :in-theory (disable lw-diskp lw-disk-add))))

(local
 (defthm lw-cb-mul-norm-identity
   (implies (and (rationalp x) (rationalp y) (rationalp u) (rationalp v))
            (equal (+ (* (- (* x u) (* y v)) (- (* x u) (* y v)))
                      (* (+ (* x v) (* y u)) (+ (* x v) (* y u))))
                   (* (+ (* x x) (* y y)) (+ (* u u) (* v v)))))
   :rule-classes nil))

(defthm lw-complex-mul-disk
  (implies (and (lw-complex-diskp left radius) (lw-complex-diskp right other-radius))
           (lw-complex-diskp (lw-complex-mul left right) (* radius other-radius)))
  :hints (("Goal"
           :use ((:instance lw-cb-mul-norm-identity (x (car left)) (y (cdr left)) (u (car right)) (v (cdr right)))
                 (:instance lw-cb-square-nonnegative (value (car right)))
                 (:instance lw-cb-square-nonnegative (value (cdr right)))
                 (:instance lw-cb-multiply-order
                   (left (+ (* (car left) (car left)) (* (cdr left) (cdr left)))) (right (* radius radius))
                   (factor (+ (* (car right) (car right)) (* (cdr right) (cdr right)))))
                 (:instance lw-cb-multiply-order
                   (left (+ (* (car right) (car right)) (* (cdr right) (cdr right)))) (right (* other-radius other-radius))
                   (factor (* radius radius))))
           :nonlinearp t)))

(defthm lw-complex-scale-disk
  (implies (and (lw-complex-diskp point radius) (rationalp factor))
           (lw-complex-diskp (lw-complex-scale factor point) (* (abs factor) radius)))
  :hints (("Goal" :use ((:instance lw-cb-multiply-order
                          (left (+ (* (car point) (car point)) (* (cdr point) (cdr point))))
                          (right (* radius radius)) (factor (* factor factor))))
                  :cases ((<= 0 factor)) :nonlinearp t)))

(defthm lw-complex-disk-enlarge
  (implies (and (lw-complex-diskp point radius) (rationalp cap) (<= radius cap))
           (lw-complex-diskp point cap))
  :hints (("Goal" :use ((:instance lw-disk-enlarge (real (car point)) (imag (cdr point))))
                  :in-theory (disable lw-diskp lw-disk-enlarge))))

(defthm lw-complex-difference-symmetric
  (implies (and (lw-complexp left) (lw-complexp right)
                (lw-complex-diskp (lw-complex-sub left right) radius))
           (lw-complex-diskp (lw-complex-sub right left) radius))
  :hints (("Goal" :nonlinearp t))
  :rule-classes nil)

(defthm lw-complex-sub-telescope
  (implies (and (lw-complexp left) (lw-complexp middle) (lw-complexp right))
           (equal (lw-complex-sub left right)
                  (lw-complex-add (lw-complex-sub left middle) (lw-complex-sub middle right))))
  :rule-classes nil)

(defthm lw-complex-difference-triangle
  (implies (and (lw-complexp left) (lw-complexp middle) (lw-complexp right)
                (lw-complex-diskp (lw-complex-sub left middle) radius)
                (lw-complex-diskp (lw-complex-sub middle right) other-radius))
           (lw-complex-diskp (lw-complex-sub left right) (+ radius other-radius)))
  :hints (("Goal" :use (lw-complex-sub-telescope
                        (:instance lw-complex-add-disk
                          (left (lw-complex-sub left middle)) (right (lw-complex-sub middle right))))
                  :in-theory (disable lw-complex-diskp lw-complexp lw-complex-sub lw-complex-add
                                      lw-complex-add-disk lw-complex-disk-enlarge lw-disk-enlarge))))

(defun lw-complex-power (point index)
  (declare (xargs :measure (nfix index)))
  (if (zp index) (cons 1 0)
    (lw-complex-mul point (lw-complex-power point (- index 1)))))

(defthm lw-complex-power-rational
  (implies (lw-complexp point) (lw-complexp (lw-complex-power point index))))

(local (defthm lw-cb-power-zero
         (implies (zp index) (equal (lw-complex-power point index) (cons 1 0)))))

(defthm lw-complex-unit-power
  (implies (lw-complex-diskp point 1) (lw-complex-diskp (lw-complex-power point index) 1))
  :hints (("Goal" :induct (lw-complex-power point index)
                  :in-theory (disable lw-complex-mul lw-complex-diskp lw-complex-disk-enlarge))
          (and stable-under-simplificationp
               '(:use ((:instance lw-complex-mul-disk (left point)
                          (right (lw-complex-power point (- index 1))) (radius 1) (other-radius 1)))
                 :in-theory (disable lw-complex-mul lw-complex-diskp lw-complex-disk-enlarge lw-complex-mul-disk)))))

(local
 (defthm lw-cb-power-difference-step
   (implies (and (lw-complexp left) (lw-complexp right) (posp index))
            (equal (lw-complex-sub (lw-complex-power left index) (lw-complex-power right index))
                   (lw-complex-add
                    (lw-complex-mul left (lw-complex-sub (lw-complex-power left (- index 1))
                                                        (lw-complex-power right (- index 1))))
                    (lw-complex-mul (lw-complex-sub left right) (lw-complex-power right (- index 1))))))
   :hints (("Goal" :expand ((lw-complex-power left index) (lw-complex-power right index))
                   :use ((:instance lw-complex-power-rational (point left) (index (- index 1)))
                         (:instance lw-complex-power-rational (point right) (index (- index 1))))
                   :in-theory (disable lw-complex-power lw-complex-power-rational)))
   :rule-classes nil))

(defthm lw-complex-power-difference
  (implies (and (lw-complex-diskp left 1) (lw-complex-diskp right 1)
                (lw-complex-diskp (lw-complex-sub left right) error) (natp index))
           (lw-complex-diskp (lw-complex-sub (lw-complex-power left index) (lw-complex-power right index))
                             (* index error)))
  :hints (("Goal" :induct (lw-complex-power left index)
                  :in-theory (disable lw-complex-diskp lw-complex-mul lw-complex-sub
                                      (:definition lw-complex-power)
                                      lw-complex-disk-enlarge lw-disk-enlarge))
          (and stable-under-simplificationp
               '(:use (lw-cb-power-difference-step
                       (:instance lw-complex-disk-data (point left) (radius 1))
                       (:instance lw-complex-disk-data (point right) (radius 1))
                       (:instance lw-complex-disk-data (point (lw-complex-sub left right)) (radius error))
                       (:instance lw-complex-unit-power (point right) (index (- index 1)))
                       (:instance lw-complex-mul-disk (radius 1) (other-radius (* (- index 1) error))
                         (right (lw-complex-sub (lw-complex-power left (- index 1)) (lw-complex-power right (- index 1)))))
                       (:instance lw-complex-mul-disk (left (lw-complex-sub left right)) (radius error)
                         (right (lw-complex-power right (- index 1))) (other-radius 1))
                       (:instance lw-complex-add-disk
                         (left (lw-complex-mul left (lw-complex-sub (lw-complex-power left (- index 1))
                                                                  (lw-complex-power right (- index 1)))))
                         (right (lw-complex-mul (lw-complex-sub left right) (lw-complex-power right (- index 1))))
                         (radius (* (- index 1) error)) (other-radius error)))
                 :in-theory (disable lw-complex-diskp lw-complex-mul lw-complex-sub lw-complex-add
                                     lw-complex-power lw-complex-mul-disk lw-complex-add-disk
                                     lw-complex-disk-data lw-complex-unit-power lw-complex-disk-enlarge lw-disk-enlarge)))))

(defthm lw-complex-mul-associative
  (implies (and (lw-complexp left) (lw-complexp middle) (lw-complexp right))
           (equal (lw-complex-mul (lw-complex-mul left middle) right)
                  (lw-complex-mul left (lw-complex-mul middle right)))))

(defthm lw-complex-mul-one
  (implies (lw-complexp point)
           (and (equal (lw-complex-mul (cons 1 0) point) point)
                (equal (lw-complex-mul point (cons 1 0)) point))))

(defthm lw-complex-power-add
  (implies (and (lw-complexp point) (natp left) (natp right))
           (equal (lw-complex-power point (+ left right))
                  (lw-complex-mul (lw-complex-power point left) (lw-complex-power point right))))
  :hints (("Goal" :induct (lw-complex-power point left)
                  :in-theory (disable lw-complex-mul lw-complexp))))

(local (defun lw-cb-countdown (index)
         (declare (xargs :measure (nfix index)))
         (if (zp index) 0 (lw-cb-countdown (- index 1)))))

(defthm lw-complex-power-power
  (implies (and (lw-complexp point) (natp inner) (natp outer))
           (equal (lw-complex-power (lw-complex-power point inner) outer)
                  (lw-complex-power point (* inner outer))))
  :hints (("Goal" :induct (lw-cb-countdown outer)
                  :in-theory (disable lw-complex-mul lw-complexp lw-complex-power-add))
          (and stable-under-simplificationp
               '(:use ((:instance lw-complex-power-add (left inner) (right (* inner (- outer 1)))))
                 :in-theory (disable lw-complex-mul lw-complexp lw-complex-power lw-complex-power-add)
                 :nonlinearp t))))

; R_n(z) = z^n - 1 - n*(z-1), evaluated by a recurrence that exposes
; its quadratic error without assuming a logarithm or an exponential.
(defun lw-complex-power-remainder (point index)
  (declare (xargs :measure (nfix index)))
  (if (zp index) (cons 0 0)
    (lw-complex-add
     (lw-complex-mul point (lw-complex-power-remainder point (- index 1)))
     (lw-complex-scale (- index 1)
                       (lw-complex-mul (lw-complex-sub point (cons 1 0))
                                       (lw-complex-sub point (cons 1 0)))))))

(defthm lw-complex-power-remainder-rational
  (implies (lw-complexp point) (lw-complexp (lw-complex-power-remainder point index))))

(defthm lw-complex-power-remainder-identity
  (implies (and (lw-complexp point) (natp index))
           (equal (lw-complex-power-remainder point index)
                  (lw-complex-sub (lw-complex-sub (lw-complex-power point index) (cons 1 0))
                                  (lw-complex-scale index (lw-complex-sub point (cons 1 0))))))
  :hints (("Goal" :induct (lw-complex-power-remainder point index)
                  :in-theory (disable lw-complex-power))
          (and stable-under-simplificationp
               '(:expand ((lw-complex-power point index))
                 :use ((:instance lw-complex-power-rational (index (- index 1))))
                 :in-theory (disable lw-complex-power lw-complex-power-rational)))))

(defun lw-quadratic-radius (index error)
  (* 1/2 (nfix index) (- (nfix index) 1) error error))

(local (defthm lw-cb-quadratic-zero
         (implies (zp index) (equal (lw-quadratic-radius index error) 0))))

(local
 (defthm lw-cb-remainder-radius-step
   (implies (and (rationalp error) (posp index))
            (equal (+ (lw-quadratic-radius (- index 1) error) (* (- index 1) error error))
                   (lw-quadratic-radius index error)))
   :rule-classes nil))

(defthm lw-complex-power-quadratic-bound
  (implies (and (lw-complex-diskp point 1)
                (lw-complex-diskp (lw-complex-sub point (cons 1 0)) error) (natp index))
           (lw-complex-diskp (lw-complex-power-remainder point index) (lw-quadratic-radius index error)))
  :hints (("Goal" :induct (lw-complex-power-remainder point index)
                  :in-theory (disable lw-complex-diskp lw-complex-add lw-complex-mul lw-complex-scale
                                      lw-quadratic-radius lw-complex-power-remainder-identity lw-complex-disk-enlarge lw-disk-enlarge))
          (and stable-under-simplificationp
               '(:use (lw-cb-remainder-radius-step
                       (:instance lw-complex-disk-data (radius 1))
                       (:instance lw-complex-disk-data (point (lw-complex-sub point (cons 1 0))) (radius error))
                       (:instance lw-complex-mul-disk (left point)
                         (right (lw-complex-power-remainder point (- index 1)))
                         (radius 1) (other-radius (lw-quadratic-radius (- index 1) error)))
                       (:instance lw-complex-mul-disk
                         (left (lw-complex-sub point (cons 1 0))) (right (lw-complex-sub point (cons 1 0)))
                         (radius error) (other-radius error))
                       (:instance lw-complex-scale-disk (factor (- index 1))
                         (point (lw-complex-mul (lw-complex-sub point (cons 1 0)) (lw-complex-sub point (cons 1 0))))
                         (radius (* error error)))
                       (:instance lw-complex-add-disk
                         (left (lw-complex-mul point (lw-complex-power-remainder point (- index 1))))
                         (radius (lw-quadratic-radius (- index 1) error))
                         (right (lw-complex-scale (- index 1)
                                 (lw-complex-mul (lw-complex-sub point (cons 1 0)) (lw-complex-sub point (cons 1 0)))))
                         (other-radius (* (- index 1) error error))))
                 :in-theory (disable lw-complex-diskp lw-complex-disk-data lw-complex-add lw-complex-mul
                                     lw-quadratic-radius
                                     lw-complex-scale lw-complex-power-remainder lw-complex-power-remainder-identity
                                     lw-complex-mul-disk lw-complex-add-disk lw-complex-scale-disk
                                     lw-complex-disk-enlarge lw-disk-enlarge)))))

(assert-event
 (and (equal (lw-complex-power (cons 0 1) 4) (cons 1 0))
      (lw-complex-diskp (lw-complex-power (cons 3/5 4/5) 7) 1)))
