(in-package "ACL2")

(include-book "hyperbola-majorants")
(include-book "dirichlet-hyperbola-product")
(include-book "dirichlet-cubic-decay")
(include-book "dirichlet-series")

; Exact rectangle/hyperbola splitting and absolute bounds for the
; omitted products of the actual computed Dirichlet samples.

(local (in-theory (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul
 lw-complex-scale lw-complex-diskp lw-diskp lw-dirichlet-sample
 lw-dirichlet-coefficient lw-dirichlet-node lw-dirichlet-sample-table
 lw-mangoldt-dirichlet-weights lw-mangoldt-bounds lw-prime-power-data
 lw-dirichlet-hyperbola-product-row lw-dirichlet-hyperbola-product-sum
 lw-complex-mangoldt-product-hyperbola lw-complex-log-dirichlet-sum
 lw-complex-log-ramp-independent-exp lw-dirichlet-cubic-node-cost
 lw-exp-lipschitz-cap lw-complex-scale-product lw-complex-sub-add
 lw-complex-sub-add-first lw-complex-sub-add-cancel
 lw-hyperbola-tail-row-majorant lw-hyperbola-tail-majorant)))

(local (defthm lw-dht-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-dht-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-dht-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-dht-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-dht-times-negative (a b) (b a)))
                 :in-theory (disable lw-dht-times-negative)))))

(local (defthm lw-dht-zero-times (equal (* 0 a) 0)))

(local (defthm lw-dht-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-dht-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-dht-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-dht-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-dht-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-dht-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-dht-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-dht-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-dht-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-dht-left-commutes)))))

(local (defthm lw-dht-zero-scale
 (equal (lw-complex-scale 0 point) (cons 0 0))
 :hints (("Goal" :in-theory (enable lw-complex-scale)))))

(local (defthm lw-dht-mul-zero
 (implies (lw-complexp point)
  (and (equal (lw-complex-mul point (cons 0 0)) (cons 0 0))
       (equal (lw-complex-mul (cons 0 0) point) (cons 0 0))))
 :hints (("Goal" :in-theory (enable lw-complexp lw-complex-mul)))))

(local (defthm lw-dht-mul-add-right
 (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c))
  (equal (lw-complex-mul a (lw-complex-add b c))
         (lw-complex-add (lw-complex-mul a b) (lw-complex-mul a c))))
 :hints (("Goal" :in-theory (enable lw-complexp lw-complex-add lw-complex-mul)))))

(local (defthm lw-dht-pull-scale-right
 (implies (and (rationalp factor) (lw-complexp a) (lw-complexp b))
  (equal (lw-complex-mul a (lw-complex-scale factor b))
         (lw-complex-scale factor (lw-complex-mul a b))))
 :hints (("Goal" :in-theory (enable lw-complexp lw-complex-mul lw-complex-scale)))))

(local (defthm lw-dht-pull-scale-left
 (implies (and (rationalp factor) (lw-complexp a) (lw-complexp b))
  (equal (lw-complex-mul (lw-complex-scale factor a) b)
         (lw-complex-scale factor (lw-complex-mul a b))))
 :hints (("Goal" :in-theory (enable lw-complexp lw-complex-mul lw-complex-scale)))))

(defun lw-dirichlet-weighted-prefix (count weights nodes)
 (declare (xargs :measure (nfix count)))
 (if (zp count) (cons 0 0)
   (lw-complex-add
    (lw-complex-scale (lw-dirichlet-coefficient weights count) (lw-dirichlet-node nodes count))
    (lw-dirichlet-weighted-prefix (- count 1) weights nodes))))

(defun lw-dirichlet-node-prefix (count nodes)
 (declare (xargs :measure (nfix count)))
 (if (zp count) (cons 0 0)
   (lw-complex-add (lw-dirichlet-node nodes count) (lw-dirichlet-node-prefix (- count 1) nodes))))

(defthm lw-dirichlet-weighted-prefix-rational
 (lw-complexp (lw-dirichlet-weighted-prefix count weights nodes)))

(defthm lw-dirichlet-node-prefix-rational
 (lw-complexp (lw-dirichlet-node-prefix count nodes)))

(defun lw-dirichlet-hyperbola-tail-row (divisor bound cutoff weights nodes)
 (declare (xargs :measure (nfix bound)))
 (if (zp bound) (cons 0 0)
   (lw-complex-add
    (if (< cutoff (* divisor bound))
        (lw-complex-scale (lw-dirichlet-coefficient weights divisor)
         (lw-complex-mul (lw-dirichlet-node nodes divisor) (lw-dirichlet-node nodes bound)))
      (cons 0 0))
    (lw-dirichlet-hyperbola-tail-row divisor (- bound 1) cutoff weights nodes))))

(defun lw-dirichlet-hyperbola-tail-sum (left bound cutoff weights nodes)
 (declare (xargs :measure (nfix left)))
 (if (zp left) (cons 0 0)
   (lw-complex-add
    (lw-dirichlet-hyperbola-tail-row left bound cutoff weights nodes)
    (lw-dirichlet-hyperbola-tail-sum (- left 1) bound cutoff weights nodes))))

(defthm lw-dirichlet-hyperbola-tail-row-rational
 (lw-complexp (lw-dirichlet-hyperbola-tail-row divisor bound cutoff weights nodes)))

(defthm lw-dirichlet-hyperbola-tail-sum-rational
 (lw-complexp (lw-dirichlet-hyperbola-tail-sum left bound cutoff weights nodes)))

(local (in-theory (disable lw-dirichlet-weighted-prefix)))

(defthm lw-dirichlet-hyperbola-row-split
 (implies (and (posp divisor) (natp bound) (natp cutoff))
  (equal
   (lw-complex-scale (lw-dirichlet-coefficient weights divisor)
    (lw-complex-mul (lw-dirichlet-node nodes divisor) (lw-dirichlet-node-prefix bound nodes)))
   (lw-complex-add
    (lw-dirichlet-hyperbola-product-row divisor bound cutoff weights nodes)
    (lw-dirichlet-hyperbola-tail-row divisor bound cutoff weights nodes))))
 :hints (("Goal" :induct (lw-dirichlet-hyperbola-tail-row divisor bound cutoff weights nodes)
                 :in-theory (enable lw-dirichlet-hyperbola-product-row))))

(local (in-theory (disable lw-dirichlet-hyperbola-tail-row lw-dirichlet-node-prefix)))

(defthm lw-dirichlet-rectangle-hyperbola-split
 (implies (and (natp left) (natp bound) (natp cutoff))
  (equal
   (lw-complex-mul (lw-dirichlet-weighted-prefix left weights nodes)
                   (lw-dirichlet-node-prefix bound nodes))
   (lw-complex-add
    (lw-dirichlet-hyperbola-product-sum left bound cutoff weights nodes)
    (lw-dirichlet-hyperbola-tail-sum left bound cutoff weights nodes))))
 :hints (("Goal"
  :induct (lw-dirichlet-hyperbola-tail-sum left bound cutoff weights nodes)
  :in-theory (enable lw-dirichlet-weighted-prefix lw-dirichlet-hyperbola-product-sum))
  (and stable-under-simplificationp
   '(:use ((:instance lw-dirichlet-hyperbola-row-split (divisor left)))
     :in-theory (disable lw-complex-scale-product
                        lw-dirichlet-weighted-prefix lw-dirichlet-hyperbola-product-sum
                        lw-dirichlet-hyperbola-tail-sum lw-dirichlet-hyperbola-row-split)
     :do-not-induct t))))

(local (defthm lw-dht-subtract-left
 (implies (and (lw-complexp a) (lw-complexp b))
  (equal (lw-complex-sub (lw-complex-add a b) a) b))
 :hints (("Goal" :in-theory (enable lw-complexp lw-complex-add lw-complex-sub)))))

(defthm lw-dirichlet-rectangle-hyperbola-difference
 (implies (and (natp left) (natp bound) (natp cutoff))
  (equal
   (lw-complex-sub
    (lw-complex-mul (lw-dirichlet-weighted-prefix left weights nodes)
                    (lw-dirichlet-node-prefix bound nodes))
    (lw-dirichlet-hyperbola-product-sum left bound cutoff weights nodes))
   (lw-dirichlet-hyperbola-tail-sum left bound cutoff weights nodes)))
 :hints (("Goal"
  :use (lw-dirichlet-rectangle-hyperbola-split)
  :in-theory (disable lw-dirichlet-rectangle-hyperbola-split
                      lw-dirichlet-hyperbola-tail-sum)
  :do-not-induct t)))

(defun lw-dirichlet-square-rounding-cost (rate height index)
 (if (equal index 1) 0
   (+ (lw-dirichlet-cubic-node-cost rate height index)
      (* 6 (lw-exp-lipschitz-cap index)))))

(defthm lw-dirichlet-square-rounding-cost-valid
 (implies (and (rationalp rate) (< 3 rate) (rationalp height) (posp index))
  (and (rationalp (lw-dirichlet-square-rounding-cost rate height index))
       (<= 0 (lw-dirichlet-square-rounding-cost rate height index))))
 :hints (("Goal"
  :use (lw-dirichlet-cubic-node-cost-valid (:instance lw-exp-lipschitz-cap-valid (cap index)))
  :in-theory (disable lw-dirichlet-cubic-node-cost-valid lw-exp-lipschitz-cap-valid)
  :do-not-induct t)))

(local (defthm lw-dht-mangoldt-one
 (equal (car (lw-mangoldt-bounds 1 error)) 0)
 :hints (("Goal" :in-theory (enable lw-mangoldt-bounds)))))

(defthm lw-dirichlet-sample-square-bound
 (implies (and (rationalp rate) (< 3 rate) (rationalp height) (posp index)
               (rationalp error) (< 0 error) (<= error 1))
  (lw-complex-diskp
   (lw-dirichlet-sample rate height index error error)
   (+ (* 2 (/ index) (/ index))
      (* (lw-dirichlet-square-rounding-cost rate height index) error))))
 :hints (("Goal"
  :use ((:instance lw-complex-dirichlet-cubic-point-bound (weight 1) (log-error error)))
  :in-theory (e/d (lw-dirichlet-sample)
                  (lw-complex-dirichlet-cubic-point-bound))
  :nonlinearp t :do-not-induct t)))

(defthm lw-mangoldt-dirichlet-sample-square-bound
 (implies (and (rationalp rate) (< 3 rate) (rationalp height) (posp index)
               (rationalp coefficient-error) (< 0 coefficient-error)
               (rationalp error) (< 0 error) (<= error 1))
  (lw-complex-diskp
   (lw-complex-scale (car (lw-mangoldt-bounds index coefficient-error))
                     (lw-dirichlet-sample rate height index error error))
   (+ (* 2 (/ index) (/ index))
      (* (lw-dirichlet-square-rounding-cost rate height index) error))))
 :hints (("Goal"
  :use ((:instance lw-mangoldt-lower-coarse (epsilon coefficient-error))
        (:instance lw-complex-dirichlet-cubic-point-bound
         (weight (car (lw-mangoldt-bounds index coefficient-error))) (log-error error)))
  :in-theory (e/d (lw-dirichlet-sample)
                  (lw-mangoldt-lower-coarse lw-complex-dirichlet-cubic-point-bound))
  :nonlinearp t :do-not-induct t)))

(local (in-theory (disable lw-dirichlet-square-rounding-cost)))

(local (defthm lw-dht-nonnegative-product
 (implies (and (rationalp a) (<= 0 a) (rationalp b) (<= 0 b)) (<= 0 (* a b)))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-dht-reciprocal-square-data
 (implies (posp index)
  (and (rationalp (* 2 (/ index) (/ index)))
       (<= 0 (* 2 (/ index) (/ index))) (<= (* 2 (/ index) (/ index)) 2)))
 :hints (("Goal"
  :use ((:instance lw-reciprocal-antitone (left 1) (right index)))
  :in-theory (disable lw-reciprocal-antitone)
  :nonlinearp t :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-dht-small-square
 (implies (and (rationalp error) (<= 0 error) (<= error 1)) (<= (* error error) error))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-dht-pair-radius
 (implies (and (rationalp a) (<= 0 a) (<= a 2) (rationalp b) (<= 0 b) (<= b 2)
               (rationalp x) (<= 0 x) (rationalp y) (<= 0 y)
               (rationalp error) (<= 0 error) (<= error 1))
  (<= (* (+ a (* x error)) (+ b (* y error)))
      (+ (* a b) (* (+ (* 2 x) (* 2 y) (* x y)) error))))
 :hints (("Goal"
  :use (lw-dht-small-square
        (:instance lw-dht-nonnegative-product (a x) (b y))
        (:instance lw-dht-multiply-order (a a) (b 2) (factor (* y error)))
        (:instance lw-dht-multiply-order (a b) (b 2) (factor (* x error)))
        (:instance lw-dht-multiply-order (a (* error error)) (b error) (factor (* x y))))
  :nonlinearp t :do-not-induct t))
 :rule-classes nil))

(defun lw-dirichlet-pair-rounding-cost (rate height left right)
 (+ (* 2 (lw-dirichlet-square-rounding-cost rate height left))
    (* 2 (lw-dirichlet-square-rounding-cost rate height right))
    (* (lw-dirichlet-square-rounding-cost rate height left)
       (lw-dirichlet-square-rounding-cost rate height right))))

(defthm lw-dirichlet-pair-rounding-cost-valid
 (implies (and (rationalp rate) (< 3 rate) (rationalp height) (posp left) (posp right))
  (and (rationalp (lw-dirichlet-pair-rounding-cost rate height left right))
       (<= 0 (lw-dirichlet-pair-rounding-cost rate height left right))))
 :hints (("Goal"
  :use ((:instance lw-dirichlet-square-rounding-cost-valid (index left))
        (:instance lw-dirichlet-square-rounding-cost-valid (index right)))
  :in-theory (disable lw-dirichlet-square-rounding-cost-valid)
  :nonlinearp t :do-not-induct t)))

(defthm lw-mangoldt-dirichlet-product-square-bound
 (implies (and (rationalp rate) (< 3 rate) (rationalp height) (posp left) (posp right)
               (rationalp coefficient-error) (< 0 coefficient-error)
               (rationalp error) (< 0 error) (<= error 1))
  (lw-complex-diskp
   (lw-complex-scale (car (lw-mangoldt-bounds left coefficient-error))
    (lw-complex-mul (lw-dirichlet-sample rate height left error error)
                    (lw-dirichlet-sample rate height right error error)))
   (+ (* 4 (/ left) (/ left) (/ right) (/ right))
      (* (lw-dirichlet-pair-rounding-cost rate height left right) error))))
 :hints (("Goal"
  :use ((:instance lw-dirichlet-square-rounding-cost-valid (index left))
        (:instance lw-dirichlet-square-rounding-cost-valid (index right))
        (:instance lw-dht-reciprocal-square-data (index left))
        (:instance lw-dht-reciprocal-square-data (index right))
        (:instance lw-mangoldt-dirichlet-sample-square-bound (index left))
        (:instance lw-dirichlet-sample-square-bound (index right))
        (:instance lw-dht-pair-radius
         (a (* 2 (/ left) (/ left))) (b (* 2 (/ right) (/ right)))
         (x (lw-dirichlet-square-rounding-cost rate height left))
         (y (lw-dirichlet-square-rounding-cost rate height right)))
        (:instance lw-complex-mul-disk
         (left (lw-complex-scale (car (lw-mangoldt-bounds left coefficient-error))
                                (lw-dirichlet-sample rate height left error error)))
         (right (lw-dirichlet-sample rate height right error error))
         (radius (+ (* 2 (/ left) (/ left))
                    (* (lw-dirichlet-square-rounding-cost rate height left) error)))
         (other-radius (+ (* 2 (/ right) (/ right))
                          (* (lw-dirichlet-square-rounding-cost rate height right) error))))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-scale (car (lw-mangoldt-bounds left coefficient-error))
          (lw-complex-mul (lw-dirichlet-sample rate height left error error)
                          (lw-dirichlet-sample rate height right error error))))
         (radius (* (+ (* 2 (/ left) (/ left))
                       (* (lw-dirichlet-square-rounding-cost rate height left) error))
                    (+ (* 2 (/ right) (/ right))
                       (* (lw-dirichlet-square-rounding-cost rate height right) error))))
         (cap (+ (* 4 (/ left) (/ left) (/ right) (/ right))
                 (* (lw-dirichlet-pair-rounding-cost rate height left right) error)))))
  :in-theory (disable lw-dirichlet-square-rounding-cost-valid
                      lw-mangoldt-dirichlet-sample-square-bound lw-dirichlet-sample-square-bound
                      lw-complex-mul-disk lw-complex-disk-enlarge)
  :nonlinearp nil :do-not-induct t)))

(local (in-theory (disable lw-dirichlet-pair-rounding-cost)))

(defun lw-dirichlet-tail-row-rounding-cost (rate height divisor bound cutoff)
 (declare (xargs :measure (nfix bound)))
 (if (zp bound) 0
   (+ (if (< cutoff (* divisor bound))
          (lw-dirichlet-pair-rounding-cost rate height divisor bound) 0)
      (lw-dirichlet-tail-row-rounding-cost rate height divisor (- bound 1) cutoff))))

(defthm lw-dirichlet-tail-row-rounding-cost-valid
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (posp divisor) (natp bound) (natp cutoff))
  (and (rationalp (lw-dirichlet-tail-row-rounding-cost rate height divisor bound cutoff))
       (<= 0 (lw-dirichlet-tail-row-rounding-cost rate height divisor bound cutoff))))
 :hints (("Goal" :induct (lw-dirichlet-tail-row-rounding-cost rate height divisor bound cutoff))
  (and stable-under-simplificationp
   '(:use ((:instance lw-dirichlet-pair-rounding-cost-valid (left divisor) (right bound)))
     :in-theory (disable lw-dirichlet-tail-row-rounding-cost lw-dirichlet-pair-rounding-cost-valid)
     :do-not-induct t))))

(local (in-theory (disable lw-dirichlet-tail-row-rounding-cost)))

(defun lw-dirichlet-tail-rounding-cost (rate height left bound cutoff)
 (declare (xargs :measure (nfix left)))
 (if (zp left) 0
   (+ (lw-dirichlet-tail-row-rounding-cost rate height left bound cutoff)
      (lw-dirichlet-tail-rounding-cost rate height (- left 1) bound cutoff))))

(defthm lw-dirichlet-tail-rounding-cost-valid
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (natp left) (natp bound) (natp cutoff))
  (and (rationalp (lw-dirichlet-tail-rounding-cost rate height left bound cutoff))
       (<= 0 (lw-dirichlet-tail-rounding-cost rate height left bound cutoff))))
 :hints (("Goal" :induct (lw-dirichlet-tail-rounding-cost rate height left bound cutoff))
  (and stable-under-simplificationp
   '(:use ((:instance lw-dirichlet-tail-row-rounding-cost-valid (divisor left)))
     :in-theory (disable lw-dirichlet-tail-rounding-cost lw-dirichlet-tail-row-rounding-cost-valid)
     :do-not-induct t))))

(local (in-theory (disable lw-dirichlet-tail-rounding-cost)))

(defthm lw-dirichlet-hyperbola-tail-row-bound
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (posp divisor) (natp bound) (natp cutoff) (natp total)
               (<= divisor total) (<= bound total)
               (rationalp coefficient-error) (< 0 coefficient-error)
               (rationalp error) (< 0 error) (<= error 1))
  (lw-complex-diskp
   (lw-dirichlet-hyperbola-tail-row
    divisor bound cutoff (lw-mangoldt-dirichlet-weights total coefficient-error)
    (lw-dirichlet-sample-table rate height total error error))
   (+ (lw-hyperbola-tail-row-majorant divisor bound cutoff)
      (* (lw-dirichlet-tail-row-rounding-cost rate height divisor bound cutoff) error))))
 :hints (("Goal"
  :induct (lw-dirichlet-hyperbola-tail-row
           divisor bound cutoff (lw-mangoldt-dirichlet-weights total coefficient-error)
           (lw-dirichlet-sample-table rate height total error error))
  :in-theory (enable lw-dirichlet-hyperbola-tail-row lw-hyperbola-tail-row-majorant
                     lw-dirichlet-tail-row-rounding-cost))
  (and stable-under-simplificationp
   '(:use ((:instance lw-mangoldt-dirichlet-product-square-bound (left divisor) (right bound))
           (:instance lw-complex-add-disk
            (left (lw-complex-scale (car (lw-mangoldt-bounds divisor coefficient-error))
             (lw-complex-mul (lw-dirichlet-sample rate height divisor error error)
                             (lw-dirichlet-sample rate height bound error error))))
            (right (lw-dirichlet-hyperbola-tail-row
             divisor (- bound 1) cutoff (lw-mangoldt-dirichlet-weights total coefficient-error)
             (lw-dirichlet-sample-table rate height total error error)))
            (radius (+ (* 4 (/ divisor) (/ divisor) (/ bound) (/ bound))
                       (* (lw-dirichlet-pair-rounding-cost rate height divisor bound) error)))
            (other-radius (+ (lw-hyperbola-tail-row-majorant divisor (- bound 1) cutoff)
                             (* (lw-dirichlet-tail-row-rounding-cost rate height divisor (- bound 1) cutoff)
                                error)))))
     :in-theory (disable lw-dirichlet-hyperbola-tail-row lw-hyperbola-tail-row-majorant
                         lw-dirichlet-tail-row-rounding-cost lw-mangoldt-dirichlet-product-square-bound
                         lw-complex-add-disk)
     :nonlinearp nil :do-not-induct t))))

(defthm lw-dirichlet-hyperbola-tail-bound
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (natp left) (natp bound) (natp cutoff) (natp total)
               (<= left total) (<= bound total)
               (rationalp coefficient-error) (< 0 coefficient-error)
               (rationalp error) (< 0 error) (<= error 1))
  (lw-complex-diskp
   (lw-dirichlet-hyperbola-tail-sum
    left bound cutoff (lw-mangoldt-dirichlet-weights total coefficient-error)
    (lw-dirichlet-sample-table rate height total error error))
   (+ (lw-hyperbola-tail-majorant left bound cutoff)
      (* (lw-dirichlet-tail-rounding-cost rate height left bound cutoff) error))))
 :hints (("Goal"
  :induct (lw-dirichlet-hyperbola-tail-sum
           left bound cutoff (lw-mangoldt-dirichlet-weights total coefficient-error)
           (lw-dirichlet-sample-table rate height total error error))
  :in-theory (enable lw-dirichlet-hyperbola-tail-sum lw-hyperbola-tail-majorant
                     lw-dirichlet-tail-rounding-cost))
  (and stable-under-simplificationp
   '(:use ((:instance lw-dirichlet-hyperbola-tail-row-bound (divisor left))
           (:instance lw-complex-add-disk
            (left (lw-dirichlet-hyperbola-tail-row
             left bound cutoff (lw-mangoldt-dirichlet-weights total coefficient-error)
             (lw-dirichlet-sample-table rate height total error error)))
            (right (lw-dirichlet-hyperbola-tail-sum
             (- left 1) bound cutoff (lw-mangoldt-dirichlet-weights total coefficient-error)
             (lw-dirichlet-sample-table rate height total error error)))
            (radius (+ (lw-hyperbola-tail-row-majorant left bound cutoff)
                       (* (lw-dirichlet-tail-row-rounding-cost rate height left bound cutoff) error)))
            (other-radius (+ (lw-hyperbola-tail-majorant (- left 1) bound cutoff)
                             (* (lw-dirichlet-tail-rounding-cost rate height (- left 1) bound cutoff)
                                error)))))
     :in-theory (disable lw-dirichlet-hyperbola-tail-sum lw-hyperbola-tail-majorant
                         lw-dirichlet-tail-rounding-cost lw-dirichlet-hyperbola-tail-row-bound
                         lw-complex-add-disk)
     :nonlinearp nil :do-not-induct t))))

(defthm lw-dirichlet-hyperbola-absolute-tail
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (natp left) (natp bound) (natp cutoff) (natp total) (posp start)
               (<= (* start start) cutoff) (<= left total) (<= bound total)
               (rationalp coefficient-error) (< 0 coefficient-error)
               (rationalp error) (< 0 error) (<= error 1))
  (lw-complex-diskp
   (lw-dirichlet-hyperbola-tail-sum
    left bound cutoff (lw-mangoldt-dirichlet-weights total coefficient-error)
    (lw-dirichlet-sample-table rate height total error error))
   (+ (* 16 (/ start))
      (* (lw-dirichlet-tail-rounding-cost rate height left bound cutoff) error))))
 :hints (("Goal"
  :use (lw-dirichlet-hyperbola-tail-bound
        lw-hyperbola-tail-majorant-bound
        (:instance lw-complex-disk-enlarge
         (point (lw-dirichlet-hyperbola-tail-sum
          left bound cutoff (lw-mangoldt-dirichlet-weights total coefficient-error)
          (lw-dirichlet-sample-table rate height total error error)))
         (radius (+ (lw-hyperbola-tail-majorant left bound cutoff)
                    (* (lw-dirichlet-tail-rounding-cost rate height left bound cutoff) error)))
         (cap (+ (* 16 (/ start))
                 (* (lw-dirichlet-tail-rounding-cost rate height left bound cutoff) error)))))
  :in-theory (disable lw-dirichlet-hyperbola-tail-sum lw-dirichlet-hyperbola-tail-bound
                      lw-hyperbola-tail-majorant-bound lw-complex-disk-enlarge)
  :do-not-induct t)))

(local (in-theory (disable lw-dirichlet-hyperbola-cost lw-mangoldt-convolution-cost
                          lw-dirichlet-convolution-precision lw-dirichlet-series-count
                          lw-dirichlet-weighted-prefix lw-dirichlet-node-prefix
                          lw-dirichlet-hyperbola-tail-sum)))

(defthm lw-dirichlet-convolution-precision-small
 (implies (and (rationalp rate) (<= 0 rate) (rationalp height) (natp count)
               (rationalp error) (< 0 error))
  (<= (lw-dirichlet-convolution-precision rate height count error) error))
 :hints (("Goal"
  :use ((:instance lw-dirichlet-hyperbola-cost-valid (left count) (bound count) (limit count))
        (:instance lw-reciprocal-antitone
         (left 1) (right (+ 1 (lw-dirichlet-hyperbola-cost rate height count count count)
                            (* 2 (lw-mangoldt-convolution-cost count)))))
        (:instance lw-dht-multiply-order
         (a (/ (+ 1 (lw-dirichlet-hyperbola-cost rate height count count count)
                     (* 2 (lw-mangoldt-convolution-cost count)))))
         (b 1) (factor error)))
  :in-theory (e/d (lw-dirichlet-convolution-precision)
                  (lw-dirichlet-hyperbola-cost-valid lw-reciprocal-antitone))
  :nonlinearp nil :do-not-induct t)))

(defun lw-complex-mangoldt-canonical-prefix (rate height count error)
 (lw-dirichlet-weighted-prefix
  count (lw-mangoldt-dirichlet-weights count error)
  (lw-dirichlet-sample-table rate height count error error)))

(defun lw-complex-ordinary-canonical-prefix (rate height count error)
 (lw-dirichlet-node-prefix count (lw-dirichlet-sample-table rate height count error error)))

(defthm lw-complex-dirichlet-rectangle-convolution-error
 (implies (and (rationalp rate) (< 3 rate) (rationalp height) (natp count)
               (posp start) (<= (* start start) count) (rationalp error) (< 0 error))
  (let ((request (lw-dirichlet-convolution-precision rate height count error)))
   (lw-complex-diskp
    (lw-complex-sub
     (lw-complex-mul (lw-complex-mangoldt-canonical-prefix rate height count request)
                     (lw-complex-ordinary-canonical-prefix rate height count request))
     (lw-complex-log-dirichlet-sum rate height count request request request))
    (+ (* 16 (/ start))
       (* (lw-dirichlet-tail-rounding-cost rate height count count count) request) error))))
 :hints (("Goal"
  :use
  (lw-dirichlet-convolution-precision-valid
   lw-complex-mangoldt-finite-convolution
   (:instance lw-dirichlet-hyperbola-absolute-tail
    (left count) (bound count) (cutoff count) (total count)
    (coefficient-error (lw-dirichlet-convolution-precision rate height count error))
    (error (lw-dirichlet-convolution-precision rate height count error)))
   (:instance lw-dirichlet-rectangle-hyperbola-difference
    (left count) (bound count) (cutoff count)
    (weights (lw-mangoldt-dirichlet-weights count
              (lw-dirichlet-convolution-precision rate height count error)))
    (nodes (lw-dirichlet-sample-table rate height count
            (lw-dirichlet-convolution-precision rate height count error)
            (lw-dirichlet-convolution-precision rate height count error))))
   (:instance lw-complex-difference-triangle
    (left (lw-complex-mul
     (lw-complex-mangoldt-canonical-prefix rate height count
      (lw-dirichlet-convolution-precision rate height count error))
     (lw-complex-ordinary-canonical-prefix rate height count
      (lw-dirichlet-convolution-precision rate height count error))))
    (middle (lw-complex-mangoldt-product-hyperbola rate height count
             (lw-dirichlet-convolution-precision rate height count error)
             (lw-dirichlet-convolution-precision rate height count error)
             (lw-dirichlet-convolution-precision rate height count error)))
    (right (lw-complex-log-dirichlet-sum rate height count
            (lw-dirichlet-convolution-precision rate height count error)
            (lw-dirichlet-convolution-precision rate height count error)
            (lw-dirichlet-convolution-precision rate height count error)))
    (radius (+ (* 16 (/ start))
               (* (lw-dirichlet-tail-rounding-cost rate height count count count)
                  (lw-dirichlet-convolution-precision rate height count error))))
    (other-radius error)))
  :in-theory (e/d (lw-complex-mangoldt-product-hyperbola)
   (lw-dirichlet-convolution-precision-valid lw-complex-mangoldt-finite-convolution
    lw-dirichlet-hyperbola-absolute-tail lw-dirichlet-rectangle-hyperbola-difference
    lw-complex-difference-triangle))
  :do-not-induct t)))

(defun lw-dirichlet-rectangle-count (error)
 (* (lw-dirichlet-series-count (* 1/4 error))
    (lw-dirichlet-series-count (* 1/4 error))))

(defthm lw-dirichlet-rectangle-count-valid
 (implies (and (rationalp error) (< 0 error))
  (and (posp (lw-dirichlet-rectangle-count error))
       (posp (lw-dirichlet-series-count (* 1/4 error)))
       (equal (lw-dirichlet-rectangle-count error)
              (* (lw-dirichlet-series-count (* 1/4 error))
                 (lw-dirichlet-series-count (* 1/4 error))))
       (<= (* 16 (/ (lw-dirichlet-series-count (* 1/4 error)))) (* 1/2 error))))
 :hints (("Goal" :use ((:instance lw-dirichlet-series-count-valid (error (* 1/4 error))))
                 :in-theory (disable lw-dirichlet-series-count-valid)
                 :nonlinearp t :do-not-induct t)))

(local (in-theory (disable lw-dirichlet-rectangle-count)))

(defun lw-dirichlet-rectangle-budget (rate height count error)
 (/ error (* 2 (+ 1 (lw-dirichlet-tail-rounding-cost rate height count count count)))))

(local (defthm lw-dht-budget-algebra
 (implies (and (rationalp cost) (<= 0 cost) (rationalp error) (< 0 error))
  (let ((budget (/ error (* 2 (+ 1 cost)))))
   (and (rationalp budget) (< 0 budget) (<= (* (+ 1 cost) budget) (* 1/2 error)))))
 :hints (("Goal"
  :use ((:instance lw-positive-division-bound
         (numerator (* (+ 1 cost) error)) (divisor (* 2 (+ 1 cost))) (bound (* 1/2 error))))
  :nonlinearp t :do-not-induct t))
 :rule-classes nil))

(defthm lw-dirichlet-rectangle-budget-valid
 (implies (and (rationalp rate) (< 3 rate) (rationalp height) (natp count)
               (rationalp error) (< 0 error))
  (let* ((budget (lw-dirichlet-rectangle-budget rate height count error))
         (request (lw-dirichlet-convolution-precision rate height count budget)))
   (and (rationalp budget) (< 0 budget) (rationalp request) (< 0 request) (<= request 1)
        (<= (+ budget (* (lw-dirichlet-tail-rounding-cost rate height count count count) request))
            (* 1/2 error)))))
 :hints (("Goal"
  :use ((:instance lw-dirichlet-tail-rounding-cost-valid (left count) (bound count) (cutoff count))
        (:instance lw-dht-budget-algebra
         (cost (lw-dirichlet-tail-rounding-cost rate height count count count)))
        (:instance lw-dirichlet-convolution-precision-valid
         (error (lw-dirichlet-rectangle-budget rate height count error)))
        (:instance lw-dirichlet-convolution-precision-small
         (error (lw-dirichlet-rectangle-budget rate height count error)))
        (:instance lw-dht-multiply-order
         (a (lw-dirichlet-convolution-precision rate height count
             (lw-dirichlet-rectangle-budget rate height count error)))
         (b (lw-dirichlet-rectangle-budget rate height count error))
         (factor (lw-dirichlet-tail-rounding-cost rate height count count count))))
  :in-theory (disable lw-dirichlet-tail-rounding-cost-valid
                      lw-dirichlet-convolution-precision-valid lw-dirichlet-convolution-precision-small)
  :nonlinearp nil :do-not-induct t)))

(local (in-theory (disable lw-dirichlet-rectangle-budget)))

(defthm lw-complex-dirichlet-computed-rectangle-convolution
 (implies (and (rationalp rate) (< 3 rate) (rationalp height) (rationalp error) (< 0 error))
  (let* ((count (lw-dirichlet-rectangle-count error))
         (budget (lw-dirichlet-rectangle-budget rate height count error))
         (request (lw-dirichlet-convolution-precision rate height count budget)))
   (lw-complex-diskp
    (lw-complex-sub
     (lw-complex-mul (lw-complex-mangoldt-canonical-prefix rate height count request)
                     (lw-complex-ordinary-canonical-prefix rate height count request))
     (lw-complex-log-dirichlet-sum rate height count request request request))
    error)))
 :hints (("Goal"
  :use
  (lw-dirichlet-rectangle-count-valid
   (:instance lw-dirichlet-rectangle-budget-valid (count (lw-dirichlet-rectangle-count error)))
   (:instance lw-complex-dirichlet-rectangle-convolution-error
    (count (lw-dirichlet-rectangle-count error))
    (start (lw-dirichlet-series-count (* 1/4 error)))
    (error (lw-dirichlet-rectangle-budget rate height (lw-dirichlet-rectangle-count error) error)))
   (:instance lw-complex-disk-enlarge
    (point (lw-complex-sub
     (lw-complex-mul
      (lw-complex-mangoldt-canonical-prefix rate height (lw-dirichlet-rectangle-count error)
       (lw-dirichlet-convolution-precision rate height (lw-dirichlet-rectangle-count error)
        (lw-dirichlet-rectangle-budget rate height (lw-dirichlet-rectangle-count error) error)))
      (lw-complex-ordinary-canonical-prefix rate height (lw-dirichlet-rectangle-count error)
       (lw-dirichlet-convolution-precision rate height (lw-dirichlet-rectangle-count error)
        (lw-dirichlet-rectangle-budget rate height (lw-dirichlet-rectangle-count error) error))))
     (lw-complex-log-dirichlet-sum rate height (lw-dirichlet-rectangle-count error)
      (lw-dirichlet-convolution-precision rate height (lw-dirichlet-rectangle-count error)
       (lw-dirichlet-rectangle-budget rate height (lw-dirichlet-rectangle-count error) error))
      (lw-dirichlet-convolution-precision rate height (lw-dirichlet-rectangle-count error)
       (lw-dirichlet-rectangle-budget rate height (lw-dirichlet-rectangle-count error) error))
      (lw-dirichlet-convolution-precision rate height (lw-dirichlet-rectangle-count error)
       (lw-dirichlet-rectangle-budget rate height (lw-dirichlet-rectangle-count error) error)))))
    (radius (+ (* 16 (/ (lw-dirichlet-series-count (* 1/4 error))))
     (* (lw-dirichlet-tail-rounding-cost rate height
          (lw-dirichlet-rectangle-count error) (lw-dirichlet-rectangle-count error)
          (lw-dirichlet-rectangle-count error))
        (lw-dirichlet-convolution-precision rate height (lw-dirichlet-rectangle-count error)
         (lw-dirichlet-rectangle-budget rate height (lw-dirichlet-rectangle-count error) error)))
     (lw-dirichlet-rectangle-budget rate height (lw-dirichlet-rectangle-count error) error)))
    (cap error)))
  :in-theory (disable lw-dirichlet-rectangle-count-valid lw-dirichlet-rectangle-budget-valid
                      lw-complex-dirichlet-rectangle-convolution-error lw-complex-disk-enlarge)
  :do-not-induct t)))




