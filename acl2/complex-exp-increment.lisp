(in-package "ACL2")

(include-book "complex-exp-multiply")
(include-book "exp-continuity")

; Uniform first-order increments for the actual rational complex
; exponential evaluator. These estimates feed finite telescoping
; quadrature identities, without an assumed analytic integral formula.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-power lw-rational-power
                 lw-complex-l1 lw-complex-exp-value lw-complex-exp-cap
                 lw-complex-exp-term lw-complex-exp-sum lw-exp-term lw-exp-sum
                 lw-exp-bounds lw-exp-lipschitz-cap lw-exp-index
                 lw-complex-disk-enlarge lw-disk-enlarge)))

(local (defthm lw-cei-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-cei-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-cei-times-negative
         (implies (and (rationalp a) (rationalp b)) (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-cei-negative-times
         (implies (and (rationalp a) (rationalp b)) (equal (* (- a) b) (- (* a b))))))
(local (defthm lw-cei-zero-times (equal (* 0 a) 0)))
(local (defthm lw-cei-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))
(local (defthm lw-cei-double-negative (implies (rationalp a) (equal (- (- a)) a))))
(local (defthm lw-cei-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))
(local (defthm lw-cei-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(defthm lw-complex-l1-scale
  (implies (and (lw-complexp point) (rationalp factor))
           (equal (lw-complex-l1 (lw-complex-scale factor point))
                  (* (abs factor) (lw-complex-l1 point))))
  :hints (("Goal" :cases ((<= 0 factor) (<= 0 (car point)) (<= 0 (cdr point)))
                  :in-theory (enable lw-complexp lw-complex-l1 lw-complex-scale)
                  :nonlinearp t :do-not-induct t)))

(defun lw-complex-exp-uniform-cap (argument-cap)
  (+ 1 (lw-exp-lipschitz-cap argument-cap)))

(defthm lw-complex-exp-uniform-cap-data
  (implies (and (rationalp argument-cap) (<= 0 argument-cap))
           (and (rationalp (lw-complex-exp-uniform-cap argument-cap))
                (<= 1 (lw-complex-exp-uniform-cap argument-cap))))
  :hints (("Goal" :use ((:instance lw-exp-lipschitz-cap-valid (cap argument-cap)))
                  :in-theory (disable lw-exp-lipschitz-cap-valid))))

(defthm lw-complex-exp-cap-uniform
  (implies (and (lw-complexp point) (rationalp argument-cap)
                (<= 0 argument-cap) (<= (lw-complex-l1 point) argument-cap))
           (<= (lw-complex-exp-cap point) (lw-complex-exp-uniform-cap argument-cap)))
  :hints (("Goal"
           :use ((:instance lw-complex-l1-bound)
                 (:instance lw-exp-bounds-width (value (lw-complex-l1 point)) (epsilon 1))
                 (:instance lw-exp-bounds-monotone-overlap
                   (left (lw-complex-l1 point)) (right argument-cap)
                   (left-error 1) (right-error 1)))
           :in-theory (e/d (lw-complex-exp-cap lw-exp-lipschitz-cap)
                           (lw-complex-l1-bound lw-exp-bounds-width
                            lw-exp-bounds-monotone-overlap))
           :do-not-induct t)))

(local (in-theory (disable lw-complex-exp-uniform-cap)))

(defthm lw-complex-exp-value-uniform-bound
  (implies (and (lw-complexp point) (rationalp argument-cap)
                (<= 0 argument-cap) (<= (lw-complex-l1 point) argument-cap)
                (rationalp error) (< 0 error))
           (lw-complex-diskp (lw-complex-exp-value point error)
                             (lw-complex-exp-uniform-cap argument-cap)))
  :hints (("Goal"
           :use (lw-complex-exp-cap-uniform lw-complex-exp-value-cap
                 (:instance lw-complex-disk-enlarge
                   (point (lw-complex-exp-value point error)) (radius (lw-complex-exp-cap point))
                   (cap (lw-complex-exp-uniform-cap argument-cap))))
           :in-theory (disable lw-complex-exp-cap-uniform lw-complex-exp-value-cap)
           :do-not-induct t)))

(local (defthm lw-cei-linear-prefix
         (implies (lw-complexp point)
                  (equal (lw-complex-exp-sum point 1) (lw-complex-add (cons 1 0) point)))
         :hints (("Goal"
                  :expand ((lw-complex-exp-sum point 1) (lw-complex-exp-sum point 0)
                           (lw-complex-exp-term point 1) (lw-complex-exp-term point 0))
                  :in-theory (disable lw-complex-exp-sum-real lw-complex-exp-term-real)))))

(local (defthm lw-cei-second-term
         (implies (and (rationalp radius) (<= 0 radius))
                  (equal (* 2 (lw-exp-term radius 2)) (* radius radius)))
         :hints (("Goal" :expand ((lw-exp-term radius 2) (lw-exp-term radius 1)
                                  (lw-exp-term radius 0))))))

(defthm lw-complex-exp-first-order-error
  (implies (and (lw-complex-diskp point radius) (<= radius 1)
                (rationalp error) (< 0 error))
           (lw-complex-diskp
            (lw-complex-sub (lw-complex-exp-value point error)
                            (lw-complex-add (cons 1 0) point))
            (+ (* radius radius) error)))
  :hints (("Goal"
           :use ((:instance lw-complex-exp-prefix-error (small 1))
                 (:instance lw-complex-difference-symmetric
                   (left (lw-complex-exp-sum point 1)) (right (lw-complex-exp-value point error))
                   (radius (+ (* radius radius) error))))
           :in-theory (disable lw-complex-exp-prefix-error)
           :do-not-induct t)))

(local (defthm lw-cei-product-linear-error
         (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp step))
                  (equal
                   (lw-complex-sub (lw-complex-mul a b)
                     (lw-complex-add a (lw-complex-mul step a)))
                   (lw-complex-mul a
                     (lw-complex-sub b (lw-complex-add (cons 1 0) step)))))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-add lw-complex-sub
                                          lw-complex-mul)))
         :rule-classes nil))

(defthm lw-complex-exp-increment-error
  (implies
   (and (lw-complexp left) (lw-complexp right)
        (rationalp left-cap) (<= 0 left-cap) (<= (lw-complex-l1 left) left-cap)
        (rationalp right-cap) (<= 0 right-cap) (<= (lw-complex-l1 right) right-cap)
        (lw-complex-diskp right radius) (<= radius 1)
        (rationalp error) (< 0 error))
   (lw-complex-diskp
    (lw-complex-sub (lw-complex-exp-value (lw-complex-add left right) error)
      (lw-complex-add (lw-complex-exp-value left error)
        (lw-complex-mul right (lw-complex-exp-value left error))))
    (+ (* (lw-complex-exp-uniform-cap left-cap) radius radius)
       (* (+ (lw-complex-exp-uniform-cap right-cap)
             (* 2 (lw-complex-exp-uniform-cap left-cap)) 2) error))))
  :hints (("Goal"
           :use ((:instance lw-complex-exp-value-multiplication
                   (left-error error) (right-error error) (sum-error error))
                 (:instance lw-complex-difference-symmetric
                   (left (lw-complex-mul (lw-complex-exp-value left error)
                                         (lw-complex-exp-value right error)))
                   (right (lw-complex-exp-value (lw-complex-add left right) error))
                   (radius (+ (* (lw-complex-exp-cap right) error)
                              (* (lw-complex-exp-cap left) error) (* 2 error))))
                 (:instance lw-complex-exp-first-order-error (point right))
                 (:instance lw-complex-exp-value-uniform-bound (point left) (argument-cap left-cap))
                 (:instance lw-complex-exp-cap-uniform (point left) (argument-cap left-cap))
                 (:instance lw-complex-exp-cap-uniform (point right) (argument-cap right-cap))
                 (:instance lw-cei-product-linear-error
                   (a (lw-complex-exp-value left error)) (b (lw-complex-exp-value right error))
                   (step right))
                 (:instance lw-complex-mul-disk
                   (left (lw-complex-exp-value left error))
                   (radius (lw-complex-exp-uniform-cap left-cap))
                   (right (lw-complex-sub (lw-complex-exp-value right error)
                            (lw-complex-add (cons 1 0) right)))
                   (other-radius (+ (* radius radius) error)))
                 (:instance lw-complex-difference-triangle
                   (left (lw-complex-exp-value (lw-complex-add left right) error))
                   (middle (lw-complex-mul (lw-complex-exp-value left error)
                                           (lw-complex-exp-value right error)))
                   (right (lw-complex-add (lw-complex-exp-value left error)
                            (lw-complex-mul right (lw-complex-exp-value left error))))
                   (radius (+ (* (lw-complex-exp-cap right) error)
                              (* (lw-complex-exp-cap left) error) (* 2 error)))
                   (other-radius (* (lw-complex-exp-uniform-cap left-cap)
                                    (+ (* radius radius) error))))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-complex-sub (lw-complex-exp-value (lw-complex-add left right) error)
                     (lw-complex-add (lw-complex-exp-value left error)
                       (lw-complex-mul right (lw-complex-exp-value left error)))))
                   (radius (+ (* (lw-complex-exp-cap right) error)
                              (* (lw-complex-exp-cap left) error) (* 2 error)
                              (* (lw-complex-exp-uniform-cap left-cap)
                                 (+ (* radius radius) error))))
                   (cap (+ (* (lw-complex-exp-uniform-cap left-cap) radius radius)
                     (* (+ (lw-complex-exp-uniform-cap right-cap)
                           (* 2 (lw-complex-exp-uniform-cap left-cap)) 2) error)))))
           :in-theory (disable lw-complex-exp-value-multiplication lw-complex-exp-first-order-error
                               lw-complex-exp-value-uniform-bound lw-complex-exp-cap-uniform
                               lw-complex-difference-triangle lw-complex-mul-disk
                               lw-complex-sub-add-first lw-complex-mul-subtract
                               lw-complex-mul-commutative lw-complex-mul-left-commutes)
           :nonlinearp t :do-not-induct t)))
