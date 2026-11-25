(in-package "ACL2")

(include-book "finite-dirichlet-convolution")
(include-book "mangoldt-divisor-log")
(include-book "dirichlet-product")
(include-book "dirichlet-term-transport")

; Concrete finite Dirichlet hyperbolas with the repository's Mangoldt
; and complex-power evaluators. The rational tables are constructed
; here, not supplied as analytic hypotheses.

(local (in-theory (disable lw-divides lw-primep lw-prime-factors lw-prime-power-data
 lw-mangoldt-bounds lw-mangoldt-divisor-sum lw-log-bounds lw-log-count lw-log-rectangles
 lw-complexp lw-complex-add lw-complex-sub lw-complex-scale lw-complex-diskp lw-diskp
 lw-complex-log-ramp-independent-exp lw-dirichlet-coefficient lw-dirichlet-node
 lw-dirichlet-hyperbola-sum lw-dirichlet-divisor-transform lw-divisor-coefficient-sum
 lw-mangoldt-divisor-factor-sum)))

(local (defthm lw-mdc-zero-scale
 (equal (lw-complex-scale 0 point) (cons 0 0))
 :hints (("Goal" :in-theory (enable lw-complex-scale)))))

(local (defthm lw-mdc-mangoldt-rational
 (implies (and (rationalp error) (< 0 error))
  (rationalp (car (lw-mangoldt-bounds value error))))
 :hints (("Goal" :use ((:instance lw-mangoldt-bounds-interval (epsilon error)))
                 :in-theory (e/d (lw-intervalp) (lw-mangoldt-bounds-interval))))
 :rule-classes (:rewrite :type-prescription)))

(defthm lw-mangoldt-divisor-sum-rational
 (implies (and (rationalp error) (< 0 error))
  (rationalp (lw-mangoldt-divisor-sum value limit error)))
 :hints (("Goal" :induct (lw-mangoldt-divisor-sum value limit error)
                 :in-theory (enable lw-mangoldt-divisor-sum)))
 :rule-classes (:rewrite :type-prescription))

(defun lw-dirichlet-sample (rate height index log-error node-error)
 (if (equal index 1) (cons 1 0)
   (if (and (rationalp index) (< 1 index))
       (lw-complex-log-ramp-independent-exp rate height index log-error node-error)
     (cons 0 0))))

(defthm lw-dirichlet-sample-rational
 (implies (and (rationalp rate) (rationalp height) (rationalp log-error) (< 0 log-error)
               (rationalp node-error) (< 0 node-error))
  (lw-complexp (lw-dirichlet-sample rate height index log-error node-error)))
 :hints (("Goal" :in-theory (enable lw-complexp))))

(defthm lw-dirichlet-sample-unit-cap
 (implies (and (rationalp rate) (<= 0 rate) (rationalp height)
               (rationalp log-error) (< 0 log-error)
               (rationalp node-error) (< 0 node-error) (<= node-error 1))
  (lw-complex-diskp (lw-dirichlet-sample rate height index log-error node-error) 2))
 :hints (("Goal"
  :use ((:instance lw-complex-log-ramp-independent-exp-unit-cap (error node-error)))
  :in-theory (e/d (lw-complex-diskp lw-complexp lw-diskp)
                  (lw-complex-log-ramp-independent-exp-unit-cap))
  :do-not-induct t)))

(local (in-theory (disable lw-dirichlet-sample)))

(defun lw-mangoldt-dirichlet-weights (count error)
 (declare (xargs :measure (nfix count)))
 (if (zp count) nil
   (acons count (car (lw-mangoldt-bounds count error))
          (lw-mangoldt-dirichlet-weights (- count 1) error))))

(defthm lw-mangoldt-dirichlet-weight-lookup
 (implies (and (natp count) (posp index) (<= index count) (rationalp error) (< 0 error))
  (equal (lw-dirichlet-coefficient (lw-mangoldt-dirichlet-weights count error) index)
         (car (lw-mangoldt-bounds index error))))
 :hints (("Goal" :induct (lw-mangoldt-dirichlet-weights count error)
                 :in-theory (enable lw-dirichlet-coefficient))))

(defun lw-dirichlet-sample-table (rate height count log-error node-error)
 (declare (xargs :measure (nfix count)))
 (if (zp count) nil
   (acons count (lw-dirichlet-sample rate height count log-error node-error)
          (lw-dirichlet-sample-table rate height (- count 1) log-error node-error))))

(local (defthm lw-mdc-normalize-node
 (implies (lw-complexp point)
  (equal (cons (rfix (car point)) (rfix (cdr point))) point))
 :hints (("Goal" :in-theory (enable lw-complexp)))))

(local (defthm lw-mdc-sample-components
 (implies (and (rationalp rate) (rationalp height) (rationalp log-error) (< 0 log-error)
               (rationalp node-error) (< 0 node-error))
  (and (rationalp (car (lw-dirichlet-sample rate height index log-error node-error)))
       (rationalp (cdr (lw-dirichlet-sample rate height index log-error node-error)))))
 :hints (("Goal" :use (lw-dirichlet-sample-rational)
                 :in-theory (e/d (lw-complexp) (lw-dirichlet-sample-rational))))))

(defthm lw-dirichlet-sample-table-lookup
 (implies (and (natp count) (posp index) (<= index count)
               (rationalp rate) (rationalp height) (rationalp log-error) (< 0 log-error)
               (rationalp node-error) (< 0 node-error))
  (equal (lw-dirichlet-node (lw-dirichlet-sample-table rate height count log-error node-error) index)
         (lw-dirichlet-sample rate height index log-error node-error)))
 :hints (("Goal" :induct (lw-dirichlet-sample-table rate height count log-error node-error)
                 :in-theory (enable lw-dirichlet-node))))

(local (in-theory (disable lw-mangoldt-dirichlet-weights lw-dirichlet-sample-table)))

(defthm lw-mangoldt-table-divisor-coefficients
 (implies (and (natp total) (natp limit) (<= limit total) (rationalp error) (< 0 error))
  (equal (lw-divisor-coefficient-sum value limit (lw-mangoldt-dirichlet-weights total error))
         (lw-mangoldt-divisor-sum value limit error)))
 :hints (("Goal" :induct (lw-mangoldt-divisor-sum value limit error)
                 :in-theory (enable lw-mangoldt-divisor-sum lw-divisor-coefficient-sum))))

(local (defthm lw-mdc-divisor-one
 (equal (lw-mangoldt-divisor-sum 1 1 error) 0)
 :hints (("Goal" :in-theory (enable lw-mangoldt-divisor-sum lw-mangoldt-bounds)))))

(defun lw-complex-mangoldt-divisor-transform (rate height count log-error error node-error)
 (declare (xargs :measure (nfix count)))
 (if (or (zp count) (equal count 1)) (cons 0 0)
   (lw-complex-add
    (lw-complex-scale (lw-mangoldt-divisor-sum count count error)
                      (lw-dirichlet-sample rate height count log-error node-error))
    (lw-complex-mangoldt-divisor-transform rate height (- count 1) log-error error node-error))))

(defthm lw-complex-mangoldt-divisor-transform-rational
 (implies (and (rationalp rate) (rationalp height) (rationalp log-error) (< 0 log-error)
               (rationalp error) (< 0 error) (rationalp node-error) (< 0 node-error))
  (lw-complexp (lw-complex-mangoldt-divisor-transform rate height count log-error error node-error))))

(defthm lw-mangoldt-table-divisor-transform
 (implies (and (natp total) (natp count) (<= count total)
               (rationalp rate) (rationalp height) (rationalp log-error) (< 0 log-error)
               (rationalp error) (< 0 error) (rationalp node-error) (< 0 node-error))
  (equal (lw-dirichlet-divisor-transform
          count (lw-mangoldt-dirichlet-weights total error)
          (lw-dirichlet-sample-table rate height total log-error node-error))
         (lw-complex-mangoldt-divisor-transform rate height count log-error error node-error)))
 :hints (("Goal" :induct (lw-complex-mangoldt-divisor-transform rate height count log-error error node-error)
                 :in-theory (enable lw-dirichlet-divisor-transform))))

(defun lw-complex-mangoldt-hyperbola (rate height count log-error error node-error)
 (lw-dirichlet-hyperbola-sum
  count count count (lw-mangoldt-dirichlet-weights count error)
  (lw-dirichlet-sample-table rate height count log-error node-error)))

(defthm lw-complex-mangoldt-hyperbola-reindex
 (implies (and (natp count) (rationalp rate) (rationalp height)
               (rationalp log-error) (< 0 log-error) (rationalp error) (< 0 error)
               (rationalp node-error) (< 0 node-error))
  (equal (lw-complex-mangoldt-hyperbola rate height count log-error error node-error)
         (lw-complex-mangoldt-divisor-transform rate height count log-error error node-error)))
 :hints (("Goal"
  :use ((:instance lw-dirichlet-full-hyperbola-divisors
         (limit count) (weights (lw-mangoldt-dirichlet-weights count error))
         (nodes (lw-dirichlet-sample-table rate height count log-error node-error))))
  :in-theory (disable lw-dirichlet-full-hyperbola-divisors
                      lw-complex-mangoldt-divisor-transform)
  :do-not-induct t)))

(local (defthm lw-mdc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-mdc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-mdc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-mdc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-mdc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-mdc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-mdc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-mdc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-mdc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-mdc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-mdc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-mdc-left-commutes)))))

(local (defthm lw-mdc-left-distributes
 (equal (* (+ a b) c) (+ (* a c) (* b c)))
 :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                 :in-theory (disable distributivity)))))

(local (defthm lw-mdc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-mdc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-mdc-times-negative (a b) (b a)))
                 :in-theory (disable lw-mdc-times-negative)))))

(local (defthm lw-mdc-scale-difference
 (implies (and (rationalp a) (rationalp b) (lw-complexp point))
  (equal (lw-complex-sub (lw-complex-scale a point) (lw-complex-scale b point))
         (lw-complex-scale (- a b) point)))
 :hints (("Goal" :in-theory (enable lw-complexp lw-complex-sub lw-complex-scale)))))

(local (defthm lw-mdc-scale-error
 (implies (and (rationalp a) (rationalp b) (rationalp budget) (<= 0 budget)
               (<= (abs (- a b)) budget) (lw-complex-diskp point 2))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-scale a point) (lw-complex-scale b point)) (* 2 budget)))
 :hints (("Goal"
  :use ((:instance lw-complex-scale-disk (factor (- a b)) (radius 2))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-scale (- a b) point)) (radius (* 2 (abs (- a b)))) (cap (* 2 budget))))
  :in-theory (disable lw-complex-scale-disk lw-complex-disk-enlarge)
  :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-mdc-log-rational
 (implies (and (rationalp value) (<= 1 value) (rationalp error) (< 0 error))
  (rationalp (car (lw-log-bounds value error))))
 :hints (("Goal" :use ((:instance lw-log-bounds-interval (epsilon error)))
                 :in-theory (e/d (lw-intervalp) (lw-log-bounds-interval))))
 :rule-classes (:rewrite :type-prescription)))

(defun lw-mangoldt-convolution-cost (count)
 (declare (xargs :measure (nfix count)))
 (if (or (zp count) (equal count 1)) 0
   (+ (+ 1 (* 3 (len (lw-prime-factors count))))
      (lw-mangoldt-convolution-cost (- count 1)))))

(defthm lw-mangoldt-convolution-cost-natural
 (natp (lw-mangoldt-convolution-cost count))
 :rule-classes (:rewrite :type-prescription))

(defun lw-complex-log-dirichlet-sum (rate height count log-error error node-error)
 (declare (xargs :measure (nfix count)))
 (if (or (zp count) (equal count 1)) (cons 0 0)
   (lw-complex-add
    (lw-complex-scale (car (lw-log-bounds count error))
                      (lw-dirichlet-sample rate height count log-error node-error))
    (lw-complex-log-dirichlet-sum rate height (- count 1) log-error error node-error))))

(defthm lw-complex-log-dirichlet-sum-rational
 (implies (and (rationalp rate) (rationalp height) (rationalp log-error) (< 0 log-error)
               (rationalp error) (< 0 error) (rationalp node-error) (< 0 node-error))
  (lw-complexp (lw-complex-log-dirichlet-sum rate height count log-error error node-error))))

(defthm lw-complex-mangoldt-divisor-transform-error
 (implies (and (natp count) (rationalp rate) (<= 0 rate) (rationalp height)
               (rationalp log-error) (< 0 log-error) (rationalp error) (< 0 error)
               (rationalp node-error) (< 0 node-error) (<= node-error 1))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-complex-mangoldt-divisor-transform rate height count log-error error node-error)
    (lw-complex-log-dirichlet-sum rate height count log-error error node-error))
   (* 2 (lw-mangoldt-convolution-cost count) error)))
 :hints (("Goal"
  :induct (lw-complex-mangoldt-divisor-transform rate height count log-error error node-error)
  :in-theory (disable lw-complex-sub-add-first lw-complex-sub-add-cancel lw-mdc-scale-difference))
  (and stable-under-simplificationp
   '(:use ((:instance lw-mangoldt-divisor-log-error (value count) (log-error error))
           (:instance lw-dirichlet-sample-unit-cap (index count))
           (:instance lw-mdc-scale-error
            (a (lw-mangoldt-divisor-sum count count error))
            (b (car (lw-log-bounds count error)))
            (budget (* (+ 1 (* 3 (len (lw-prime-factors count)))) error))
            (point (lw-dirichlet-sample rate height count log-error node-error)))
           (:instance lw-complex-add-disk
            (left (lw-complex-sub
             (lw-complex-scale (lw-mangoldt-divisor-sum count count error)
                               (lw-dirichlet-sample rate height count log-error node-error))
             (lw-complex-scale (car (lw-log-bounds count error))
                               (lw-dirichlet-sample rate height count log-error node-error))))
            (right (lw-complex-sub
             (lw-complex-mangoldt-divisor-transform rate height (- count 1) log-error error node-error)
             (lw-complex-log-dirichlet-sum rate height (- count 1) log-error error node-error)))
            (radius (* 2 (+ 1 (* 3 (len (lw-prime-factors count)))) error))
            (other-radius (* 2 (lw-mangoldt-convolution-cost (- count 1)) error))))
     :in-theory (disable lw-complex-mangoldt-divisor-transform lw-complex-log-dirichlet-sum
                         lw-mangoldt-divisor-log-error lw-dirichlet-sample-unit-cap
                         lw-complex-add-disk lw-mdc-scale-difference
                         lw-complex-sub-add-first lw-complex-sub-add-cancel)
     :nonlinearp nil :do-not-induct t))))

(defun lw-mangoldt-convolution-precision (count error)
 (/ error (+ 1 (* 2 (lw-mangoldt-convolution-cost count)))))

(local (defthm lw-mdc-precision-algebra
 (implies (and (rationalp cost) (<= 0 cost) (rationalp error) (< 0 error))
  (let ((request (/ error (+ 1 (* 2 cost)))))
   (and (rationalp request) (< 0 request) (<= (* 2 cost request) error))))
 :hints (("Goal"
  :use ((:instance lw-positive-division-bound
         (numerator (* 2 cost error)) (divisor (+ 1 (* 2 cost))) (bound error)))
  :nonlinearp t :do-not-induct t))
 :rule-classes nil))

(defthm lw-mangoldt-convolution-precision-valid
 (implies (and (rationalp error) (< 0 error))
  (and (rationalp (lw-mangoldt-convolution-precision count error))
       (< 0 (lw-mangoldt-convolution-precision count error))
       (<= (* 2 (lw-mangoldt-convolution-cost count)
                (lw-mangoldt-convolution-precision count error)) error)))
 :hints (("Goal" :use ((:instance lw-mdc-precision-algebra
                       (cost (lw-mangoldt-convolution-cost count))))))
 :rule-classes :rewrite)

(defthm lw-complex-mangoldt-hyperbola-computed-log-error
 (implies (and (natp count) (rationalp rate) (<= 0 rate) (rationalp height)
               (rationalp log-error) (< 0 log-error) (rationalp error) (< 0 error)
               (rationalp node-error) (< 0 node-error) (<= node-error 1))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-complex-mangoldt-hyperbola
     rate height count log-error (lw-mangoldt-convolution-precision count error) node-error)
    (lw-complex-log-dirichlet-sum
     rate height count log-error (lw-mangoldt-convolution-precision count error) node-error))
   error))
 :hints (("Goal"
  :use (lw-mangoldt-convolution-precision-valid
        (:instance lw-complex-mangoldt-divisor-transform-error
         (error (lw-mangoldt-convolution-precision count error)))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub
          (lw-complex-mangoldt-divisor-transform
           rate height count log-error (lw-mangoldt-convolution-precision count error) node-error)
          (lw-complex-log-dirichlet-sum
           rate height count log-error (lw-mangoldt-convolution-precision count error) node-error)))
         (radius (* 2 (lw-mangoldt-convolution-cost count)
                      (lw-mangoldt-convolution-precision count error))) (cap error)))
  :in-theory (disable lw-complex-mangoldt-divisor-transform-error
                      lw-mangoldt-convolution-precision-valid lw-mangoldt-convolution-precision
                      lw-complex-mangoldt-divisor-transform lw-complex-log-dirichlet-sum
                      lw-complex-disk-enlarge)
  :do-not-induct t)))



