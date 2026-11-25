(in-package "ACL2")

(include-book "integer-divisibility")
(include-book "cauchy-polynomials")

; Exact finite hyperbola reindexing for rational coefficients and
; rational complex nodes stored in explicit association lists.

(local (in-theory (disable lw-divides lw-primep lw-no-divisor
                          lw-complexp lw-complex-add lw-complex-scale)))

(local (defthm lw-fdc-left-commutes
 (equal (* a (* b c)) (* b (* a c)))
 :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                      (:instance associativity-of-* (x b) (y a) (z c))
                      (:instance commutativity-of-* (x a) (y b)))
                 :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-fdc-left-distributes
 (equal (* (+ a b) c) (+ (* a c) (* b c)))
 :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                 :in-theory (disable distributivity)))))

(local (defthm lw-fdc-inverse-factor
 (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
 :hints (("Goal"
  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
        (:instance inverse-of-* (x divisor)))
  :in-theory (disable associativity-of-* commutativity-of-* lw-fdc-left-commutes)))))

(defthm lw-divides-positive-quotient
 (implies (and (posp divisor) (posp value) (lw-divides divisor value))
  (and (posp (* value (/ divisor))) (<= (* value (/ divisor)) value)
       (equal (* divisor (* value (/ divisor))) value)))
 :hints (("Goal"
  :use ((:instance lw-fdc-inverse-factor (coefficient value)))
  :in-theory (e/d (lw-divides) (lw-fdc-inverse-factor))
  :nonlinearp t :do-not-induct t)))

(defthm lw-divides-product-quotient
 (implies (and (posp divisor) (integerp value))
  (equal (* (* divisor value) (/ divisor)) value))
 :hints (("Goal" :use ((:instance lw-fdc-inverse-factor (coefficient value)))
                 :in-theory (disable lw-fdc-inverse-factor))))

(defthm lw-divides-positive-product
 (implies (and (posp divisor) (posp value))
  (lw-divides divisor (* divisor value)))
 :hints (("Goal" :use (lw-divides-product-quotient)
                 :in-theory (e/d (lw-divides) (lw-divides-product-quotient)))))

(defun lw-dirichlet-coefficient (table index)
 (rfix (cdr (assoc-equal index table))))

(defun lw-dirichlet-node (table index)
 (let ((value (cdr (assoc-equal index table))))
  (cons (rfix (car value)) (rfix (cdr value)))))

(defthm lw-dirichlet-coefficient-rational
 (rationalp (lw-dirichlet-coefficient table index))
 :rule-classes (:rewrite :type-prescription))

(defthm lw-dirichlet-node-rational
 (lw-complexp (lw-dirichlet-node table index))
 :hints (("Goal" :in-theory (enable lw-complexp))))

(local (in-theory (disable lw-dirichlet-coefficient lw-dirichlet-node)))

(defun lw-bounded-divisorp (divisor value bound)
 (and (lw-divides divisor value) (<= (* value (/ divisor)) bound)))

(local (in-theory (disable lw-bounded-divisorp)))

(local (defthm lw-fdc-divisor-step
 (implies (and (posp divisor) (posp value) (posp bound))
  (equal (if (lw-bounded-divisorp divisor value bound) 1 0)
         (+ (if (lw-bounded-divisorp divisor value (- bound 1)) 1 0)
            (if (equal value (* divisor bound)) 1 0))))
 :hints (("Goal"
  :use (lw-divides-positive-quotient
        (:instance lw-divides-positive-product (value bound))
        (:instance lw-divides-product-quotient (value bound)))
  :in-theory (e/d (lw-bounded-divisorp)
   (lw-divides-positive-quotient lw-divides-positive-product lw-divides-product-quotient))
  :nonlinearp t :do-not-induct t))
 :rule-classes nil))

(defun lw-dirichlet-divisor-coefficients (value limit bound weights)
 (declare (xargs :measure (nfix limit)))
 (if (zp limit) 0
   (+ (if (lw-bounded-divisorp limit value bound) (lw-dirichlet-coefficient weights limit) 0)
      (lw-dirichlet-divisor-coefficients value (- limit 1) bound weights))))

(defthm lw-dirichlet-divisor-coefficients-rational
 (rationalp (lw-dirichlet-divisor-coefficients value limit bound weights))
 :rule-classes (:rewrite :type-prescription))

(defun lw-dirichlet-divisor-column (divisor limit bound weights nodes)
 (declare (xargs :measure (nfix limit)))
 (if (zp limit) (cons 0 0)
   (lw-complex-add
    (if (lw-bounded-divisorp divisor limit bound)
        (lw-complex-scale (lw-dirichlet-coefficient weights divisor) (lw-dirichlet-node nodes limit))
      (cons 0 0))
    (lw-dirichlet-divisor-column divisor (- limit 1) bound weights nodes))))

(defthm lw-dirichlet-divisor-column-rational
 (lw-complexp (lw-dirichlet-divisor-column divisor limit bound weights nodes)))

(local (defun lw-fdc-node-delta (target limit nodes)
 (declare (xargs :measure (nfix limit)))
 (if (zp limit) (cons 0 0)
   (lw-complex-add (if (equal target limit) (lw-dirichlet-node nodes limit) (cons 0 0))
                  (lw-fdc-node-delta target (- limit 1) nodes)))))

(local (defthm lw-fdc-node-delta-rational
 (lw-complexp (lw-fdc-node-delta target limit nodes))))

(local (defthm lw-fdc-node-delta-exact
 (implies (and (posp target) (natp limit))
  (equal (lw-fdc-node-delta target limit nodes)
         (if (<= target limit) (lw-dirichlet-node nodes target) (cons 0 0))))
 :hints (("Goal" :induct (lw-fdc-node-delta target limit nodes)))))

(local (in-theory (disable lw-dirichlet-divisor-column lw-dirichlet-divisor-coefficients
                          lw-fdc-node-delta)))

(local (defthm lw-fdc-divisor-step-cell
 (implies (and (posp divisor) (posp value) (posp bound))
  (equal
   (if (lw-bounded-divisorp divisor value bound)
       (lw-complex-scale (lw-dirichlet-coefficient weights divisor) (lw-dirichlet-node nodes value))
     (cons 0 0))
   (lw-complex-add
    (if (lw-bounded-divisorp divisor value (- bound 1))
        (lw-complex-scale (lw-dirichlet-coefficient weights divisor) (lw-dirichlet-node nodes value))
      (cons 0 0))
    (if (equal value (* divisor bound))
        (lw-complex-scale (lw-dirichlet-coefficient weights divisor) (lw-dirichlet-node nodes value))
      (cons 0 0)))))
 :hints (("Goal" :use (lw-fdc-divisor-step)
                 :in-theory (disable lw-bounded-divisorp)
                 :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-fdc-scale-coefficients
 (implies (and (rationalp a) (rationalp b))
  (equal (lw-complex-scale (+ a b) point)
         (lw-complex-add (lw-complex-scale a point) (lw-complex-scale b point))))
 :hints (("Goal" :in-theory (enable lw-complex-scale lw-complex-add)))))

(local (defthm lw-fdc-zero-scale
 (equal (lw-complex-scale 0 point) (cons 0 0))
 :hints (("Goal" :in-theory (enable lw-complex-scale)))))

(local (defthm lw-fdc-column-step
 (implies (and (posp divisor) (posp bound) (natp limit))
  (equal (lw-dirichlet-divisor-column divisor limit bound weights nodes)
         (lw-complex-add
          (lw-dirichlet-divisor-column divisor limit (- bound 1) weights nodes)
          (lw-complex-scale (lw-dirichlet-coefficient weights divisor)
                            (lw-fdc-node-delta (* divisor bound) limit nodes)))))
 :hints (("Goal" :induct (lw-dirichlet-divisor-column divisor limit bound weights nodes)
                 :in-theory (e/d (lw-dirichlet-divisor-column lw-fdc-node-delta)
                                 (lw-fdc-node-delta-exact)))
  (and stable-under-simplificationp
   '(:use ((:instance lw-fdc-divisor-step-cell (value limit))
           (:instance lw-fdc-divisor-step (value (* divisor bound))))
     :in-theory (disable lw-dirichlet-divisor-column lw-fdc-node-delta lw-fdc-node-delta-exact)
     :nonlinearp t :do-not-induct t)))
 :rule-classes nil))

(local (defthm lw-fdc-column-zero-bound
 (implies (posp divisor)
  (equal (lw-dirichlet-divisor-column divisor limit 0 weights nodes) (cons 0 0)))
 :hints (("Goal" :induct (lw-dirichlet-divisor-column divisor limit 0 weights nodes)
                 :in-theory (enable lw-dirichlet-divisor-column))
  (and stable-under-simplificationp
   '(:use ((:instance lw-divides-positive-quotient (value limit)))
     :in-theory (e/d (lw-bounded-divisorp)
                     (lw-divides-positive-quotient lw-dirichlet-divisor-column))
     :do-not-induct t)))))

(defun lw-dirichlet-hyperbola-row (divisor bound limit weights nodes)
 (declare (xargs :measure (nfix bound)))
 (if (zp bound) (cons 0 0)
   (lw-complex-add
    (if (<= (* divisor bound) limit)
        (lw-complex-scale (lw-dirichlet-coefficient weights divisor)
                          (lw-dirichlet-node nodes (* divisor bound)))
      (cons 0 0))
    (lw-dirichlet-hyperbola-row divisor (- bound 1) limit weights nodes))))

(defthm lw-dirichlet-hyperbola-row-rational
 (lw-complexp (lw-dirichlet-hyperbola-row divisor bound limit weights nodes)))

(defthm lw-dirichlet-hyperbola-row-reindex
 (implies (and (posp divisor) (natp bound) (natp limit))
  (equal (lw-dirichlet-hyperbola-row divisor bound limit weights nodes)
         (lw-dirichlet-divisor-column divisor limit bound weights nodes)))
 :hints (("Goal" :induct (lw-dirichlet-hyperbola-row divisor bound limit weights nodes))
  (and stable-under-simplificationp
   '(:use (lw-fdc-column-step)
     :in-theory (disable lw-dirichlet-hyperbola-row lw-dirichlet-divisor-column)
     :nonlinearp t :do-not-induct t))))

(defun lw-dirichlet-hyperbola-sum (left bound limit weights nodes)
 (declare (xargs :measure (nfix left)))
 (if (zp left) (cons 0 0)
   (lw-complex-add
    (lw-dirichlet-hyperbola-row left bound limit weights nodes)
    (lw-dirichlet-hyperbola-sum (- left 1) bound limit weights nodes))))

(defun lw-dirichlet-convolution-sum (limit left bound weights nodes)
 (declare (xargs :measure (nfix limit)))
 (if (zp limit) (cons 0 0)
   (lw-complex-add
    (lw-complex-scale (lw-dirichlet-divisor-coefficients limit left bound weights)
                      (lw-dirichlet-node nodes limit))
    (lw-dirichlet-convolution-sum (- limit 1) left bound weights nodes))))

(defthm lw-dirichlet-hyperbola-sum-rational
 (lw-complexp (lw-dirichlet-hyperbola-sum left bound limit weights nodes)))

(defthm lw-dirichlet-convolution-sum-rational
 (lw-complexp (lw-dirichlet-convolution-sum limit left bound weights nodes)))

(local (in-theory (disable lw-dirichlet-hyperbola-row)))

(local (defthm lw-fdc-convolution-step-left
 (implies (and (posp left) (natp limit))
  (equal (lw-dirichlet-convolution-sum limit left bound weights nodes)
         (lw-complex-add
          (lw-dirichlet-divisor-column left limit bound weights nodes)
          (lw-dirichlet-convolution-sum limit (- left 1) bound weights nodes))))
 :hints (("Goal"
  :induct (lw-dirichlet-convolution-sum limit left bound weights nodes)
  :in-theory (enable lw-dirichlet-divisor-column lw-dirichlet-divisor-coefficients)))
 :rule-classes nil))

(local (defthm lw-fdc-convolution-zero-left
 (equal (lw-dirichlet-convolution-sum limit 0 bound weights nodes) (cons 0 0))
 :hints (("Goal" :induct (lw-dirichlet-convolution-sum limit 0 bound weights nodes)
                 :in-theory (enable lw-dirichlet-divisor-coefficients)))))

(local (in-theory (disable lw-dirichlet-convolution-sum)))

(defthm lw-dirichlet-hyperbola-reindex
 (implies (and (natp left) (natp bound) (natp limit))
  (equal (lw-dirichlet-hyperbola-sum left bound limit weights nodes)
         (lw-dirichlet-convolution-sum limit left bound weights nodes)))
 :hints (("Goal" :induct (lw-dirichlet-hyperbola-sum left bound limit weights nodes))
  (and stable-under-simplificationp
   '(:use (lw-fdc-convolution-step-left)
     :in-theory (e/d (lw-dirichlet-convolution-sum)
                     (lw-dirichlet-hyperbola-sum lw-dirichlet-divisor-column))
     :do-not-induct t))))

(defun lw-divisor-coefficient-sum (value limit weights)
 (declare (xargs :measure (nfix limit)))
 (if (zp limit) 0
   (+ (if (lw-divides limit value) (lw-dirichlet-coefficient weights limit) 0)
      (lw-divisor-coefficient-sum value (- limit 1) weights))))

(defthm lw-divisor-coefficient-sum-rational
 (rationalp (lw-divisor-coefficient-sum value limit weights))
 :rule-classes (:rewrite :type-prescription))

(local (defthm lw-fdc-large-bound-divisor
 (implies (and (posp divisor) (posp value) (rationalp bound) (<= value bound))
  (equal (lw-bounded-divisorp divisor value bound) (lw-divides divisor value)))
 :hints (("Goal" :use (lw-divides-positive-quotient)
                 :in-theory (e/d (lw-bounded-divisorp) (lw-divides-positive-quotient))))))

(defthm lw-dirichlet-divisor-coefficients-large-bound
 (implies (and (posp value) (rationalp bound) (<= value bound))
  (equal (lw-dirichlet-divisor-coefficients value limit bound weights)
         (lw-divisor-coefficient-sum value limit weights)))
 :hints (("Goal" :induct (lw-dirichlet-divisor-coefficients value limit bound weights)
                 :in-theory (enable lw-dirichlet-divisor-coefficients))))

(local (defthm lw-fdc-divisor-too-large
 (implies (and (posp value) (natp divisor) (< value divisor)) (not (lw-divides divisor value)))
 :hints (("Goal" :use (lw-divides-positive-bound)
                 :in-theory (disable lw-divides-positive-bound)))))

(local (defun lw-fdc-stable-induct (upper lower)
 (declare (xargs :measure (nfix upper)))
 (if (or (zp upper) (<= upper lower)) lower
   (lw-fdc-stable-induct (- upper 1) lower))))

(defthm lw-divisor-coefficient-sum-stable
 (implies (and (posp value) (natp lower) (natp upper) (<= value lower) (<= lower upper))
  (equal (lw-divisor-coefficient-sum value upper weights)
         (lw-divisor-coefficient-sum value lower weights)))
 :hints (("Goal" :induct (lw-fdc-stable-induct upper lower)))
 :rule-classes nil)

(defthm lw-dirichlet-divisor-coefficients-full
 (implies (and (posp value) (natp limit) (<= value limit)
               (natp bound) (<= value bound))
  (equal (lw-dirichlet-divisor-coefficients value limit bound weights)
         (lw-divisor-coefficient-sum value value weights)))
 :hints (("Goal"
  :use ((:instance lw-dirichlet-divisor-coefficients-large-bound)
        (:instance lw-divisor-coefficient-sum-stable (lower value) (upper limit)))
  :in-theory (disable lw-dirichlet-divisor-coefficients-large-bound lw-divisor-coefficient-sum)
  :do-not-induct t)))

(defun lw-dirichlet-divisor-transform (limit weights nodes)
 (declare (xargs :measure (nfix limit)))
 (if (zp limit) (cons 0 0)
   (lw-complex-add
    (lw-complex-scale (lw-divisor-coefficient-sum limit limit weights)
                      (lw-dirichlet-node nodes limit))
    (lw-dirichlet-divisor-transform (- limit 1) weights nodes))))

(defthm lw-dirichlet-divisor-transform-rational
 (lw-complexp (lw-dirichlet-divisor-transform limit weights nodes)))

(defthm lw-dirichlet-convolution-full-divisors
 (implies (and (natp limit) (natp left) (natp bound) (<= limit left) (<= limit bound))
  (equal (lw-dirichlet-convolution-sum limit left bound weights nodes)
         (lw-dirichlet-divisor-transform limit weights nodes)))
 :hints (("Goal" :induct (lw-dirichlet-convolution-sum limit left bound weights nodes)
                 :in-theory (enable lw-dirichlet-convolution-sum))))

(defthm lw-dirichlet-full-hyperbola-divisors
 (implies (natp limit)
  (equal (lw-dirichlet-hyperbola-sum limit limit limit weights nodes)
         (lw-dirichlet-divisor-transform limit weights nodes)))
 :hints (("Goal" :use ((:instance lw-dirichlet-hyperbola-reindex (left limit) (bound limit))
                      (:instance lw-dirichlet-convolution-full-divisors (left limit) (bound limit)))
                 :in-theory (disable lw-dirichlet-hyperbola-reindex
                                     lw-dirichlet-convolution-full-divisors lw-dirichlet-hyperbola-sum)
                 :do-not-induct t)))



