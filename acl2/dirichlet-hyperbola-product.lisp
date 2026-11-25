(in-package "ACL2")

(include-book "mangoldt-dirichlet-convolution")

; Actual finite products E(a)*E(b), with a computed common precision.
; Hyperbola reindexing and divisor replacement then identify them with
; the logarithm-weighted finite Dirichlet sum up to any positive error.

(local (in-theory (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-scale
 lw-complex-mul lw-complex-diskp lw-diskp lw-dirichlet-sample
 lw-dirichlet-product-cap lw-mangoldt-bounds lw-mangoldt-dirichlet-weights
 lw-dirichlet-sample-table lw-dirichlet-coefficient lw-dirichlet-node
 lw-complex-log-ramp-independent-exp lw-prime-factors
 lw-dirichlet-hyperbola-row lw-dirichlet-hyperbola-sum
 lw-dirichlet-hyperbola-row-reindex lw-dirichlet-hyperbola-reindex
 lw-complex-mangoldt-hyperbola lw-complex-mangoldt-hyperbola-reindex
 lw-complex-mangoldt-divisor-transform lw-complex-log-dirichlet-sum
 lw-mangoldt-convolution-cost lw-complex-sub-add-first lw-complex-sub-add-cancel
 lw-complex-scale-product)))

(local (defthm lw-dhp-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-dhp-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-dhp-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-dhp-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-dhp-times-negative (a b) (b a)))
                 :in-theory (disable lw-dhp-times-negative)))))

(local (defthm lw-dhp-zero-times (equal (* 0 a) 0)))

(local (defthm lw-dhp-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-dhp-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-dhp-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-dhp-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-dhp-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-dhp-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-dhp-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-dhp-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-dhp-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-dhp-left-commutes)))))

(defun lw-dirichlet-pair-cost (rate height left right)
 (if (or (equal left 1) (equal right 1)) 0
   (+ (lw-dirichlet-product-cap rate height left)
      (lw-dirichlet-product-cap rate height right)
      66 (* 6 (+ rate (abs height))))))

(defthm lw-dirichlet-pair-cost-valid
 (implies (and (rationalp rate) (<= 0 rate) (rationalp height) (posp left) (posp right))
  (and (rationalp (lw-dirichlet-pair-cost rate height left right))
       (<= 0 (lw-dirichlet-pair-cost rate height left right))))
 :hints (("Goal"
  :use ((:instance lw-dirichlet-product-cap-valid (index left))
        (:instance lw-dirichlet-product-cap-valid (index right)))
  :in-theory (disable lw-dirichlet-product-cap-valid)
  :do-not-induct t)))

(defthm lw-dirichlet-sample-product-error
 (implies (and (rationalp rate) (<= 0 rate) (rationalp height) (posp left) (posp right)
               (rationalp error) (< 0 error))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-complex-mul (lw-dirichlet-sample rate height left error error)
                    (lw-dirichlet-sample rate height right error error))
    (lw-dirichlet-sample rate height (* left right) error error))
   (* (lw-dirichlet-pair-cost rate height left right) error)))
 :hints (("Goal"
  :use ((:instance lw-complex-dirichlet-product-multiplication
         (left-log-error error) (right-log-error error) (product-log-error error)
         (left-error error) (right-error error) (product-error error)))
  :in-theory (e/d (lw-dirichlet-sample)
                  (lw-complex-dirichlet-product-multiplication))
  :nonlinearp t :do-not-induct t)))

(local (defthm lw-dhp-scale-sub
 (implies (and (rationalp factor) (lw-complexp a) (lw-complexp b))
  (equal (lw-complex-sub (lw-complex-scale factor a) (lw-complex-scale factor b))
         (lw-complex-scale factor (lw-complex-sub a b))))
 :hints (("Goal" :in-theory (enable lw-complexp lw-complex-scale lw-complex-sub)))))

(defthm lw-mangoldt-dirichlet-pair-error
 (implies (and (rationalp rate) (<= 0 rate) (rationalp height) (posp left) (posp right)
               (rationalp coefficient-error) (< 0 coefficient-error)
               (rationalp error) (< 0 error))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-complex-scale (car (lw-mangoldt-bounds left coefficient-error))
     (lw-complex-mul (lw-dirichlet-sample rate height left error error)
                     (lw-dirichlet-sample rate height right error error)))
    (lw-complex-scale (car (lw-mangoldt-bounds left coefficient-error))
     (lw-dirichlet-sample rate height (* left right) error error)))
   (* left (lw-dirichlet-pair-cost rate height left right) error)))
 :hints (("Goal"
  :use (lw-dirichlet-sample-product-error lw-dirichlet-pair-cost-valid
        (:instance lw-mangoldt-lower-coarse (index left) (epsilon coefficient-error))
        (:instance lw-complex-scale-disk
         (factor (car (lw-mangoldt-bounds left coefficient-error)))
         (point (lw-complex-sub
          (lw-complex-mul (lw-dirichlet-sample rate height left error error)
                          (lw-dirichlet-sample rate height right error error))
          (lw-dirichlet-sample rate height (* left right) error error)))
         (radius (* (lw-dirichlet-pair-cost rate height left right) error)))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-scale (car (lw-mangoldt-bounds left coefficient-error))
          (lw-complex-sub
           (lw-complex-mul (lw-dirichlet-sample rate height left error error)
                           (lw-dirichlet-sample rate height right error error))
           (lw-dirichlet-sample rate height (* left right) error error))))
         (radius (* (abs (car (lw-mangoldt-bounds left coefficient-error)))
                    (lw-dirichlet-pair-cost rate height left right) error))
         (cap (* left (lw-dirichlet-pair-cost rate height left right) error))))
  :in-theory (disable lw-dirichlet-sample-product-error lw-dirichlet-pair-cost-valid
                      lw-mangoldt-lower-coarse lw-complex-scale-disk lw-complex-disk-enlarge
                      lw-dirichlet-pair-cost)
  :nonlinearp t :do-not-induct t)))

(defun lw-dirichlet-hyperbola-product-row (divisor bound limit weights nodes)
 (declare (xargs :measure (nfix bound)))
 (if (zp bound) (cons 0 0)
   (lw-complex-add
    (if (<= (* divisor bound) limit)
        (lw-complex-scale (lw-dirichlet-coefficient weights divisor)
         (lw-complex-mul (lw-dirichlet-node nodes divisor) (lw-dirichlet-node nodes bound)))
      (cons 0 0))
    (lw-dirichlet-hyperbola-product-row divisor (- bound 1) limit weights nodes))))

(defthm lw-dirichlet-hyperbola-product-row-rational
 (lw-complexp (lw-dirichlet-hyperbola-product-row divisor bound limit weights nodes)))

(defun lw-dirichlet-hyperbola-product-sum (left bound limit weights nodes)
 (declare (xargs :measure (nfix left)))
 (if (zp left) (cons 0 0)
   (lw-complex-add
    (lw-dirichlet-hyperbola-product-row left bound limit weights nodes)
    (lw-dirichlet-hyperbola-product-sum (- left 1) bound limit weights nodes))))

(defthm lw-dirichlet-hyperbola-product-sum-rational
 (lw-complexp (lw-dirichlet-hyperbola-product-sum left bound limit weights nodes)))

(defun lw-dirichlet-hyperbola-row-cost (rate height divisor bound limit)
 (declare (xargs :measure (nfix bound)))
 (if (zp bound) 0
   (+ (if (<= (* divisor bound) limit)
          (* divisor (lw-dirichlet-pair-cost rate height divisor bound)) 0)
      (lw-dirichlet-hyperbola-row-cost rate height divisor (- bound 1) limit))))

(local (in-theory (disable lw-dirichlet-pair-cost)))

(defthm lw-dirichlet-hyperbola-row-cost-valid
 (implies (and (rationalp rate) (<= 0 rate) (rationalp height) (posp divisor)
               (natp bound) (natp limit))
  (and (rationalp (lw-dirichlet-hyperbola-row-cost rate height divisor bound limit))
       (<= 0 (lw-dirichlet-hyperbola-row-cost rate height divisor bound limit))))
 :hints (("Goal" :induct (lw-dirichlet-hyperbola-row-cost rate height divisor bound limit))
  (and stable-under-simplificationp
   '(:use ((:instance lw-dirichlet-pair-cost-valid (left divisor) (right bound)))
     :in-theory (disable lw-dirichlet-pair-cost lw-dirichlet-pair-cost-valid
                         lw-dirichlet-hyperbola-row-cost)
     :nonlinearp t :do-not-induct t))))

(local (in-theory (disable lw-dirichlet-hyperbola-row-cost)))

(defun lw-dirichlet-hyperbola-cost (rate height left bound limit)
 (declare (xargs :measure (nfix left)))
 (if (zp left) 0
   (+ (lw-dirichlet-hyperbola-row-cost rate height left bound limit)
      (lw-dirichlet-hyperbola-cost rate height (- left 1) bound limit))))

(defthm lw-dirichlet-hyperbola-cost-valid
 (implies (and (rationalp rate) (<= 0 rate) (rationalp height)
               (natp left) (natp bound) (natp limit))
  (and (rationalp (lw-dirichlet-hyperbola-cost rate height left bound limit))
       (<= 0 (lw-dirichlet-hyperbola-cost rate height left bound limit))))
 :hints (("Goal" :induct (lw-dirichlet-hyperbola-cost rate height left bound limit))
  (and stable-under-simplificationp
   '(:use ((:instance lw-dirichlet-hyperbola-row-cost-valid (divisor left)))
     :in-theory (disable lw-dirichlet-hyperbola-cost lw-dirichlet-hyperbola-row-cost
                         lw-dirichlet-hyperbola-row-cost-valid)
     :do-not-induct t))))

(local (in-theory (disable lw-dhp-scale-sub)))

(local (defthm lw-dhp-add-errors
 (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c) (lw-complexp d)
               (lw-complex-diskp (lw-complex-sub a b) radius)
               (lw-complex-diskp (lw-complex-sub c d) other-radius))
  (lw-complex-diskp (lw-complex-sub (lw-complex-add a c) (lw-complex-add b d))
                    (+ radius other-radius)))
 :hints (("Goal"
  :use ((:instance lw-complex-sub-add (a a) (b c) (c b) (d d))
        (:instance lw-complex-add-disk
         (left (lw-complex-sub a b)) (right (lw-complex-sub c d))))
  :in-theory (disable lw-complex-sub-add lw-complex-add-disk)
  :do-not-induct t))
 :rule-classes nil))

(local (in-theory (disable lw-complex-sub-add)))

(defthm lw-dirichlet-hyperbola-product-row-error
 (implies (and (rationalp rate) (<= 0 rate) (rationalp height)
               (posp divisor) (natp bound) (natp limit) (natp total)
               (<= divisor total) (<= bound total) (<= limit total)
               (rationalp coefficient-error) (< 0 coefficient-error)
               (rationalp error) (< 0 error))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-dirichlet-hyperbola-product-row
     divisor bound limit (lw-mangoldt-dirichlet-weights total coefficient-error)
     (lw-dirichlet-sample-table rate height total error error))
    (lw-dirichlet-hyperbola-row
     divisor bound limit (lw-mangoldt-dirichlet-weights total coefficient-error)
     (lw-dirichlet-sample-table rate height total error error)))
   (* (lw-dirichlet-hyperbola-row-cost rate height divisor bound limit) error)))
 :hints (("Goal"
  :induct (lw-dirichlet-hyperbola-product-row
           divisor bound limit (lw-mangoldt-dirichlet-weights total coefficient-error)
           (lw-dirichlet-sample-table rate height total error error))
  :in-theory (enable lw-dirichlet-hyperbola-row lw-dirichlet-hyperbola-row-cost))
  (and stable-under-simplificationp
   '(:use ((:instance lw-mangoldt-dirichlet-pair-error (left divisor) (right bound))
           (:instance lw-dhp-add-errors
            (a (lw-complex-scale (car (lw-mangoldt-bounds divisor coefficient-error))
              (lw-complex-mul (lw-dirichlet-sample rate height divisor error error)
                              (lw-dirichlet-sample rate height bound error error))))
            (b (lw-complex-scale (car (lw-mangoldt-bounds divisor coefficient-error))
              (lw-dirichlet-sample rate height (* divisor bound) error error)))
            (c (lw-dirichlet-hyperbola-product-row
              divisor (- bound 1) limit (lw-mangoldt-dirichlet-weights total coefficient-error)
              (lw-dirichlet-sample-table rate height total error error)))
            (d (lw-dirichlet-hyperbola-row
              divisor (- bound 1) limit (lw-mangoldt-dirichlet-weights total coefficient-error)
              (lw-dirichlet-sample-table rate height total error error)))
            (radius (* divisor (lw-dirichlet-pair-cost rate height divisor bound) error))
            (other-radius (* (lw-dirichlet-hyperbola-row-cost rate height divisor (- bound 1) limit) error))))
     :in-theory (disable lw-dirichlet-hyperbola-product-row lw-dirichlet-hyperbola-row
                         lw-dirichlet-hyperbola-row-cost lw-mangoldt-dirichlet-pair-error
                         lw-complex-add-disk lw-dirichlet-hyperbola-cost)
     :nonlinearp t :do-not-induct t))))

(local (in-theory (disable lw-dirichlet-hyperbola-product-row lw-dirichlet-hyperbola-cost)))

(defthm lw-dirichlet-hyperbola-product-error
 (implies (and (rationalp rate) (<= 0 rate) (rationalp height)
               (natp left) (natp bound) (natp limit) (natp total)
               (<= left total) (<= bound total) (<= limit total)
               (rationalp coefficient-error) (< 0 coefficient-error)
               (rationalp error) (< 0 error))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-dirichlet-hyperbola-product-sum
     left bound limit (lw-mangoldt-dirichlet-weights total coefficient-error)
     (lw-dirichlet-sample-table rate height total error error))
    (lw-dirichlet-hyperbola-sum
     left bound limit (lw-mangoldt-dirichlet-weights total coefficient-error)
     (lw-dirichlet-sample-table rate height total error error)))
   (* (lw-dirichlet-hyperbola-cost rate height left bound limit) error)))
 :hints (("Goal"
  :induct (lw-dirichlet-hyperbola-product-sum
           left bound limit (lw-mangoldt-dirichlet-weights total coefficient-error)
           (lw-dirichlet-sample-table rate height total error error))
  :in-theory (enable lw-dirichlet-hyperbola-sum lw-dirichlet-hyperbola-cost))
  (and stable-under-simplificationp
   '(:use ((:instance lw-dirichlet-hyperbola-product-row-error (divisor left))
           (:instance lw-dhp-add-errors
            (a (lw-dirichlet-hyperbola-product-row
              left bound limit (lw-mangoldt-dirichlet-weights total coefficient-error)
              (lw-dirichlet-sample-table rate height total error error)))
            (b (lw-dirichlet-hyperbola-row
              left bound limit (lw-mangoldt-dirichlet-weights total coefficient-error)
              (lw-dirichlet-sample-table rate height total error error)))
            (c (lw-dirichlet-hyperbola-product-sum
              (- left 1) bound limit (lw-mangoldt-dirichlet-weights total coefficient-error)
              (lw-dirichlet-sample-table rate height total error error)))
            (d (lw-dirichlet-hyperbola-sum
              (- left 1) bound limit (lw-mangoldt-dirichlet-weights total coefficient-error)
              (lw-dirichlet-sample-table rate height total error error)))
            (radius (* (lw-dirichlet-hyperbola-row-cost rate height left bound limit) error))
            (other-radius (* (lw-dirichlet-hyperbola-cost rate height (- left 1) bound limit) error))))
     :in-theory (disable lw-dirichlet-hyperbola-product-sum lw-dirichlet-hyperbola-sum
                         lw-dirichlet-hyperbola-cost lw-dirichlet-hyperbola-product-row-error
                         lw-complex-add-disk)
     :nonlinearp nil :do-not-induct t))))

(defun lw-complex-mangoldt-product-hyperbola (rate height count log-error coefficient-error node-error)
 (lw-dirichlet-hyperbola-product-sum
  count count count (lw-mangoldt-dirichlet-weights count coefficient-error)
  (lw-dirichlet-sample-table rate height count log-error node-error)))

(defun lw-dirichlet-convolution-precision (rate height count error)
 (min 1 (/ error (+ 1 (lw-dirichlet-hyperbola-cost rate height count count count)
                         (* 2 (lw-mangoldt-convolution-cost count))))))

(local (defthm lw-dhp-precision-algebra
 (implies (and (rationalp cost) (<= 0 cost) (rationalp error) (< 0 error))
  (let ((request (min 1 (/ error (+ 1 cost)))))
   (and (rationalp request) (< 0 request) (<= request 1) (<= (* cost request) error))))
 :hints (("Goal"
  :use ((:instance lw-positive-division-bound
         (numerator (* cost error)) (divisor (+ 1 cost)) (bound error))
        (:instance lw-dhp-multiply-order
         (a (min 1 (/ error (+ 1 cost)))) (b (/ error (+ 1 cost))) (factor cost)))
  :nonlinearp t :do-not-induct t))
 :rule-classes nil))

(defthm lw-dirichlet-convolution-precision-valid
 (implies (and (rationalp rate) (<= 0 rate) (rationalp height) (natp count)
               (rationalp error) (< 0 error))
  (let ((request (lw-dirichlet-convolution-precision rate height count error)))
   (and (rationalp request) (< 0 request) (<= request 1)
        (<= (+ (* (lw-dirichlet-hyperbola-cost rate height count count count) request)
               (* 2 (lw-mangoldt-convolution-cost count) request)) error))))
 :hints (("Goal"
  :use ((:instance lw-dirichlet-hyperbola-cost-valid (left count) (bound count) (limit count))
        (:instance lw-dhp-precision-algebra
         (cost (+ (lw-dirichlet-hyperbola-cost rate height count count count)
                  (* 2 (lw-mangoldt-convolution-cost count))))))
  :in-theory (disable lw-dirichlet-hyperbola-cost-valid)
  :do-not-induct t)))

(local (in-theory (disable lw-dirichlet-convolution-precision)))

(defthm lw-complex-mangoldt-finite-convolution
 (implies (and (rationalp rate) (<= 0 rate) (rationalp height) (natp count)
               (rationalp error) (< 0 error))
  (let ((request (lw-dirichlet-convolution-precision rate height count error)))
   (lw-complex-diskp
    (lw-complex-sub
     (lw-complex-mangoldt-product-hyperbola rate height count request request request)
     (lw-complex-log-dirichlet-sum rate height count request request request))
    error)))
 :hints (("Goal"
  :use
  (lw-dirichlet-convolution-precision-valid
   (:instance lw-dirichlet-hyperbola-product-error
    (left count) (bound count) (limit count) (total count)
    (coefficient-error (lw-dirichlet-convolution-precision rate height count error))
    (error (lw-dirichlet-convolution-precision rate height count error)))
   (:instance lw-complex-mangoldt-hyperbola-reindex
    (log-error (lw-dirichlet-convolution-precision rate height count error))
    (error (lw-dirichlet-convolution-precision rate height count error))
    (node-error (lw-dirichlet-convolution-precision rate height count error)))
   (:instance lw-complex-mangoldt-divisor-transform-error
    (log-error (lw-dirichlet-convolution-precision rate height count error))
    (error (lw-dirichlet-convolution-precision rate height count error))
    (node-error (lw-dirichlet-convolution-precision rate height count error)))
   (:instance lw-complex-difference-triangle
    (left (lw-complex-mangoldt-product-hyperbola rate height count
           (lw-dirichlet-convolution-precision rate height count error)
           (lw-dirichlet-convolution-precision rate height count error)
           (lw-dirichlet-convolution-precision rate height count error)))
    (middle (lw-complex-mangoldt-hyperbola rate height count
             (lw-dirichlet-convolution-precision rate height count error)
             (lw-dirichlet-convolution-precision rate height count error)
             (lw-dirichlet-convolution-precision rate height count error)))
    (right (lw-complex-log-dirichlet-sum rate height count
            (lw-dirichlet-convolution-precision rate height count error)
            (lw-dirichlet-convolution-precision rate height count error)
            (lw-dirichlet-convolution-precision rate height count error)))
    (radius (* (lw-dirichlet-hyperbola-cost rate height count count count)
               (lw-dirichlet-convolution-precision rate height count error)))
    (other-radius (* 2 (lw-mangoldt-convolution-cost count)
                     (lw-dirichlet-convolution-precision rate height count error))))
   (:instance lw-complex-disk-enlarge
    (point (lw-complex-sub
     (lw-complex-mangoldt-product-hyperbola rate height count
      (lw-dirichlet-convolution-precision rate height count error)
      (lw-dirichlet-convolution-precision rate height count error)
      (lw-dirichlet-convolution-precision rate height count error))
     (lw-complex-log-dirichlet-sum rate height count
      (lw-dirichlet-convolution-precision rate height count error)
      (lw-dirichlet-convolution-precision rate height count error)
      (lw-dirichlet-convolution-precision rate height count error))))
    (radius (+ (* (lw-dirichlet-hyperbola-cost rate height count count count)
                  (lw-dirichlet-convolution-precision rate height count error))
               (* 2 (lw-mangoldt-convolution-cost count)
                  (lw-dirichlet-convolution-precision rate height count error))))
    (cap error)))
  :in-theory (e/d (lw-complex-mangoldt-hyperbola)
   (lw-dirichlet-hyperbola-product-error lw-dirichlet-convolution-precision-valid
    lw-complex-mangoldt-hyperbola-reindex lw-complex-mangoldt-divisor-transform-error
    lw-dirichlet-hyperbola-product-sum lw-complex-difference-triangle lw-complex-disk-enlarge))
  :do-not-induct t)))



