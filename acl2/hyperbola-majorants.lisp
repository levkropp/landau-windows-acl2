(in-package "ACL2")

(include-book "log-bounds")

; Absolute majorants for finite rectangles outside a hyperbola.
; These are rational finite sums, with no convergence assumption.

(local (defthm lw-hpt-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-hpt-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-hpt-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-hpt-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-hpt-times-negative (a b) (b a)))
                 :in-theory (disable lw-hpt-times-negative)))))

(local (defthm lw-hpt-zero-times (equal (* 0 a) 0)))

(local (defthm lw-hpt-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-hpt-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-hpt-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-hpt-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-hpt-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-hpt-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-hpt-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-hpt-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-hpt-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-hpt-left-commutes)))))

(local (defthm lw-hpt-reciprocal-difference
 (implies (and (rationalp count) (< 1 count))
  (equal (- (/ (- count 1)) (/ count))
         (* (/ count) (/ (- count 1)))))
 :hints (("Goal"
  :use ((:instance lw-hpt-inverse-factor (divisor count) (coefficient (/ (- count 1))))
        (:instance lw-hpt-inverse-factor (divisor (- count 1)) (coefficient (/ count))))
  :in-theory (disable lw-hpt-inverse-factor)
  :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-hpt-reciprocal-step
 (implies (and (rationalp count) (< 1 count))
  (<= (* (/ count) (/ count)) (- (/ (- count 1)) (/ count))))
 :hints (("Goal"
  :use (lw-hpt-reciprocal-difference
        (:instance lw-reciprocal-antitone (left (- count 1)) (right count))
        (:instance lw-hpt-multiply-order
         (a (/ count)) (b (/ (- count 1))) (factor (/ count))))
  :in-theory (disable inverse-of-* lw-reciprocal-antitone)
  :nonlinearp t :do-not-induct t))
 :rule-classes nil))

(defun lw-reciprocal-square-prefix (count)
 (declare (xargs :measure (nfix count)))
 (if (zp count) 0
   (+ (* (/ count) (/ count)) (lw-reciprocal-square-prefix (- count 1)))))

(defun lw-reciprocal-square-tail (count start)
 (declare (xargs :measure (nfix count)))
 (if (or (zp count) (<= count start)) 0
   (+ (* (/ count) (/ count)) (lw-reciprocal-square-tail (- count 1) start))))

(defthm lw-reciprocal-square-prefix-data
 (and (rationalp (lw-reciprocal-square-prefix count))
      (<= 0 (lw-reciprocal-square-prefix count)))
 :hints (("Goal" :induct (lw-reciprocal-square-prefix count) :nonlinearp t)))

(defthm lw-reciprocal-square-tail-data
 (and (rationalp (lw-reciprocal-square-tail count start))
      (<= 0 (lw-reciprocal-square-tail count start)))
 :hints (("Goal" :induct (lw-reciprocal-square-tail count start) :nonlinearp t)))

(defthm lw-reciprocal-square-prefix-telescope
 (implies (posp count)
  (<= (lw-reciprocal-square-prefix count) (- 2 (/ count))))
 :hints (("Goal" :induct (lw-reciprocal-square-prefix count))
  (and stable-under-simplificationp
   '(:use (lw-hpt-reciprocal-step)
     :in-theory (disable lw-reciprocal-square-prefix)
     :do-not-induct t))))

(defthm lw-reciprocal-square-prefix-bound
 (<= (lw-reciprocal-square-prefix count) 2)
 :hints (("Goal" :cases ((posp count))
                 :use (lw-reciprocal-square-prefix-telescope)
                 :in-theory (disable lw-reciprocal-square-prefix-telescope))))

(defthm lw-reciprocal-square-tail-telescope
 (implies (and (posp start) (natp count) (<= start count))
  (<= (lw-reciprocal-square-tail count start) (- (/ start) (/ count))))
 :hints (("Goal" :induct (lw-reciprocal-square-tail count start))
  (and stable-under-simplificationp
   '(:use (lw-hpt-reciprocal-step)
     :in-theory (disable lw-reciprocal-square-tail)
     :do-not-induct t))))

(local (defthm lw-hpt-tail-empty
 (implies (<= count start) (equal (lw-reciprocal-square-tail count start) 0))
 :hints (("Goal" :expand ((lw-reciprocal-square-tail count start))))))

(defthm lw-reciprocal-square-tail-bound
 (implies (and (posp start) (natp count))
  (<= (lw-reciprocal-square-tail count start) (/ start)))
 :hints (("Goal" :cases ((<= start count))
                 :use (lw-reciprocal-square-tail-telescope)
                 :in-theory (disable lw-reciprocal-square-tail-telescope))))

(local (in-theory (disable lw-reciprocal-square-prefix lw-reciprocal-square-tail)))

(defthm lw-hyperbola-square-containment
 (implies (and (posp start) (posp left) (posp right)
               (rationalp cutoff) (<= (* start start) cutoff) (< cutoff (* left right)))
  (or (< start left) (< start right)))
 :hints (("Goal"
  :use ((:instance lw-hpt-multiply-order (a left) (b start) (factor right))
        (:instance lw-hpt-multiply-order (a right) (b start) (factor start)))
  :nonlinearp nil :do-not-induct t))
 :rule-classes nil)

(defun lw-hyperbola-tail-row-majorant (left bound cutoff)
 (declare (xargs :measure (nfix bound)))
 (if (zp bound) 0
   (+ (if (< cutoff (* left bound)) (* 4 (/ left) (/ left) (/ bound) (/ bound)) 0)
      (lw-hyperbola-tail-row-majorant left (- bound 1) cutoff))))

(defun lw-hyperbola-tail-majorant (left bound cutoff)
 (declare (xargs :measure (nfix left)))
 (if (zp left) 0
   (+ (lw-hyperbola-tail-row-majorant left bound cutoff)
      (lw-hyperbola-tail-majorant (- left 1) bound cutoff))))

(defthm lw-hyperbola-tail-row-majorant-data
 (implies (and (posp left) (natp bound))
  (and (rationalp (lw-hyperbola-tail-row-majorant left bound cutoff))
       (<= 0 (lw-hyperbola-tail-row-majorant left bound cutoff))))
 :hints (("Goal" :induct (lw-hyperbola-tail-row-majorant left bound cutoff) :nonlinearp t)))

(defthm lw-hyperbola-tail-majorant-data
 (implies (and (natp left) (natp bound))
  (and (rationalp (lw-hyperbola-tail-majorant left bound cutoff))
       (<= 0 (lw-hyperbola-tail-majorant left bound cutoff))))
 :hints (("Goal" :induct (lw-hyperbola-tail-majorant left bound cutoff))))

(defthm lw-hyperbola-tail-row-union-bound
 (implies (and (posp left) (natp bound) (posp start)
               (rationalp cutoff) (<= (* start start) cutoff))
  (<= (lw-hyperbola-tail-row-majorant left bound cutoff)
      (* 4 (/ left) (/ left)
         (+ (if (< start left) (lw-reciprocal-square-prefix bound) 0)
            (lw-reciprocal-square-tail bound start)))))
 :hints (("Goal"
  :induct (lw-hyperbola-tail-row-majorant left bound cutoff)
  :in-theory (enable lw-reciprocal-square-prefix lw-reciprocal-square-tail))
  (and stable-under-simplificationp
   '(:use ((:instance lw-hyperbola-square-containment (right bound)))
     :in-theory (disable lw-hyperbola-tail-row-majorant
                         lw-reciprocal-square-prefix lw-reciprocal-square-tail)
     :nonlinearp t :do-not-induct t))))

(local (in-theory (disable lw-hyperbola-tail-row-majorant)))

(defthm lw-hyperbola-tail-union-bound
 (implies (and (natp left) (natp bound) (posp start)
               (rationalp cutoff) (<= (* start start) cutoff))
  (<= (lw-hyperbola-tail-majorant left bound cutoff)
      (* 4 (+ (* (lw-reciprocal-square-tail left start) (lw-reciprocal-square-prefix bound))
              (* (lw-reciprocal-square-prefix left) (lw-reciprocal-square-tail bound start))))))
 :hints (("Goal"
  :induct (lw-hyperbola-tail-majorant left bound cutoff)
  :in-theory (enable lw-reciprocal-square-prefix lw-reciprocal-square-tail))
  (and stable-under-simplificationp
   '(:use (lw-hyperbola-tail-row-union-bound)
     :in-theory (disable lw-hyperbola-tail-majorant lw-hyperbola-tail-row-union-bound
                         lw-reciprocal-square-prefix lw-reciprocal-square-tail)
     :nonlinearp t :do-not-induct t))))

(defthm lw-hyperbola-tail-majorant-bound
 (implies (and (natp left) (natp bound) (posp start)
               (rationalp cutoff) (<= (* start start) cutoff))
  (<= (lw-hyperbola-tail-majorant left bound cutoff) (* 16 (/ start))))
 :hints (("Goal"
  :use (lw-hyperbola-tail-union-bound
        (:instance lw-reciprocal-square-prefix-bound (count left))
        (:instance lw-reciprocal-square-prefix-bound (count bound))
        (:instance lw-reciprocal-square-prefix-data (count left))
        (:instance lw-reciprocal-square-prefix-data (count bound))
        (:instance lw-reciprocal-square-tail-data (count left))
        (:instance lw-reciprocal-square-tail-data (count bound))
        (:instance lw-reciprocal-square-tail-bound (count left))
        (:instance lw-reciprocal-square-tail-bound (count bound)))
  :in-theory (disable lw-hyperbola-tail-majorant lw-hyperbola-tail-union-bound
                      lw-reciprocal-square-prefix-bound lw-reciprocal-square-prefix-data
                      lw-reciprocal-square-tail-data lw-reciprocal-square-tail-bound)
  :nonlinearp t :do-not-induct t)))

