(in-package "ACL2")

(include-book "polynomial-addition")
(include-book "polynomial-difference")

; Coefficient maps for physical disks and independent polynomial lengths.
; Rescaling and zero padding retain exact finite evaluation identities.

(local (in-theory
 (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
          lw-complex-diskp lw-diskp lw-complex-power lw-rational-power
          lw-complex-polynomial lw-complex-polynomial-horner lw-complex-coefficient-at
          lw-polynomial-add lw-polynomial-multiply-coefficients lw-polynomial-difference
          lw-complex-mul-subtract lw-complex-mul-commutative lw-complex-mul-left-commutes
          lw-complex-disk-enlarge lw-disk-enlarge)))

(local (defthm lw-pcm-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pcm-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pcm-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pcm-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pcm-times-negative (a b) (b a)))
                 :in-theory (disable lw-pcm-times-negative)))))

(local (defthm lw-pcm-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pcm-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pcm-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pcm-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pcm-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pcm-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pcm-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-pcm-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pcm-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pcm-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-pcm-left-commutes)))))

(local (defthm lw-pcm-scale-product
 (implies (and (rationalp a) (rationalp b) (lw-complexp left) (lw-complexp right))
  (equal (lw-complex-mul (lw-complex-scale a left) (lw-complex-scale b right))
         (lw-complex-scale (* a b) (lw-complex-mul left right))))
 :hints (("Goal" :in-theory (union-theories
   '(lw-complexp lw-complex-mul lw-complex-scale lw-pcm-left-commutes lw-pcm-left-distributes lw-pcm-fold-constants lw-pcm-times-negative lw-pcm-negative-times lw-pcm-zero-times lw-pcm-minus-one lw-pcm-double-negative lw-pcm-add-cancel lw-pcm-double lw-pcm-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))))))

(local (defthm lw-pcm-len-nonnegative
 (<= 0 (len coefficients))
 :hints (("Goal" :induct (len coefficients) :in-theory (enable len)))
 :rule-classes (:rewrite :linear)))

(defthm lw-complex-power-scale
 (implies (and (rationalp factor) (lw-complexp point) (natp index))
  (equal (lw-complex-power (lw-complex-scale factor point) index)
         (lw-complex-scale (lw-rational-power factor index) (lw-complex-power point index))))
 :hints (("Goal" :induct (lw-complex-power point index)
  :in-theory (union-theories
   '(lw-complexp lw-complex-power lw-rational-power lw-pcm-scale-product lw-complex-scale-one lw-complex-power-rational lw-rational-power-rational lw-complex-scale-rational lw-pcm-left-commutes lw-pcm-left-distributes lw-pcm-fold-constants lw-pcm-times-negative lw-pcm-negative-times lw-pcm-zero-times lw-pcm-minus-one lw-pcm-double-negative lw-pcm-add-cancel lw-pcm-double lw-pcm-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory)))))

(defun lw-polynomial-rescale (coefficients factor offset)
 (if (endp coefficients) nil
  (cons (lw-complex-scale (lw-rational-power factor offset) (car coefficients))
        (lw-polynomial-rescale (cdr coefficients) factor (+ 1 offset)))))

(defthm lw-polynomial-rescale-valid
 (implies (and (lw-complex-coefficientsp coefficients) (rationalp factor) (natp offset))
  (and (lw-complex-coefficientsp (lw-polynomial-rescale coefficients factor offset))
       (equal (len (lw-polynomial-rescale coefficients factor offset)) (len coefficients))))
 :hints (("Goal" :induct (lw-polynomial-rescale coefficients factor offset)
  :in-theory (union-theories
   '(lw-polynomial-rescale lw-complex-coefficientsp lw-complex-scale-rational lw-rational-power-rational len lw-pcm-len-nonnegative endp lw-pcm-left-commutes lw-pcm-left-distributes lw-pcm-fold-constants lw-pcm-times-negative lw-pcm-negative-times lw-pcm-zero-times lw-pcm-minus-one lw-pcm-double-negative lw-pcm-add-cancel lw-pcm-double lw-pcm-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory)))))

(defthm lw-polynomial-rescale-coefficient
 (implies (and (lw-complex-coefficientsp coefficients) (rationalp factor) (natp offset) (natp target))
  (equal (lw-complex-coefficient-at (lw-polynomial-rescale coefficients factor offset) target offset)
         (lw-complex-scale (lw-rational-power factor target) (lw-complex-coefficient-at coefficients target offset))))
 :hints (("Goal" :induct (lw-polynomial-rescale coefficients factor offset)
  :in-theory (union-theories
   '(lw-polynomial-rescale lw-complex-coefficientsp lw-complex-coefficient-at lw-complex-scale-add lw-complex-scale-zero lw-complex-scale-rational lw-complex-coefficient-at-rational lw-rational-power-rational lw-complex-add-zero endp lw-pcm-left-commutes lw-pcm-left-distributes lw-pcm-fold-constants lw-pcm-times-negative lw-pcm-negative-times lw-pcm-zero-times lw-pcm-minus-one lw-pcm-double-negative lw-pcm-add-cancel lw-pcm-double lw-pcm-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory)))))

(local (defthm lw-pcm-move-scale
 (implies (and (rationalp factor) (lw-complexp left) (lw-complexp right))
  (equal (lw-complex-mul (lw-complex-scale factor left) right)
         (lw-complex-mul left (lw-complex-scale factor right))))
 :hints (("Goal" :in-theory (union-theories
   '(lw-complexp lw-complex-mul lw-complex-scale lw-pcm-left-commutes lw-pcm-left-distributes lw-pcm-fold-constants lw-pcm-times-negative lw-pcm-negative-times lw-pcm-zero-times lw-pcm-minus-one lw-pcm-double-negative lw-pcm-add-cancel lw-pcm-double lw-pcm-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))))))

(defthm lw-polynomial-rescale-evaluation
 (implies (and (lw-complex-coefficientsp coefficients) (rationalp factor) (natp offset) (lw-complexp point))
  (equal (lw-complex-polynomial (lw-polynomial-rescale coefficients factor offset) point offset)
         (lw-complex-polynomial coefficients (lw-complex-scale factor point) offset)))
 :hints (("Goal" :induct (lw-polynomial-rescale coefficients factor offset)
  :in-theory (union-theories
   '(lw-polynomial-rescale lw-complex-polynomial lw-complex-coefficientsp lw-complex-power-scale lw-pcm-move-scale lw-complex-power-rational lw-complex-scale-rational lw-rational-power-rational endp lw-pcm-left-commutes lw-pcm-left-distributes lw-pcm-fold-constants lw-pcm-times-negative lw-pcm-negative-times lw-pcm-zero-times lw-pcm-minus-one lw-pcm-double-negative lw-pcm-add-cancel lw-pcm-double lw-pcm-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory)))))

(defun lw-polynomial-pad (coefficients count)
 (declare (xargs :measure (nfix count)))
 (if (zp count) nil
  (cons (if (consp coefficients) (car coefficients) (cons 0 0))
        (lw-polynomial-pad (cdr coefficients) (- count 1)))))

(defthm lw-polynomial-pad-valid
 (implies (and (lw-complex-coefficientsp coefficients) (natp count))
  (and (lw-complex-coefficientsp (lw-polynomial-pad coefficients count))
       (equal (len (lw-polynomial-pad coefficients count)) count)))
 :hints (("Goal" :induct (lw-polynomial-pad coefficients count)
  :in-theory (union-theories
   '(lw-polynomial-pad lw-complex-coefficientsp lw-complexp len lw-pcm-len-nonnegative endp lw-pcm-left-commutes lw-pcm-left-distributes lw-pcm-fold-constants lw-pcm-times-negative lw-pcm-negative-times lw-pcm-zero-times lw-pcm-minus-one lw-pcm-double-negative lw-pcm-add-cancel lw-pcm-double lw-pcm-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory)))))

(local (defun lw-pcm-pad-eval-induct (coefficients count offset)
 (declare (xargs :measure (nfix count)))
 (if (zp count) (list coefficients offset)
  (lw-pcm-pad-eval-induct (cdr coefficients) (- count 1) (+ 1 offset)))))

(local (defthm lw-pcm-pad-empty
 (implies (and (natp count) (lw-complexp point) (natp offset))
  (equal (lw-complex-polynomial (lw-polynomial-pad nil count) point offset) (cons 0 0)))
 :hints (("Goal" :induct (lw-pcm-pad-eval-induct nil count offset)
  :in-theory (union-theories
   '((:induction lw-pcm-pad-eval-induct) lw-polynomial-pad lw-complex-polynomial lw-complexp lw-complex-add-zero lw-complex-scale-zero lw-complex-mul-zero lw-complex-power-rational lw-pcm-left-commutes lw-pcm-left-distributes lw-pcm-fold-constants lw-pcm-times-negative lw-pcm-negative-times lw-pcm-zero-times lw-pcm-minus-one lw-pcm-double-negative lw-pcm-add-cancel lw-pcm-double lw-pcm-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))))))

(local (defthm lw-pcm-empty-length
 (implies (<= (len coefficients) 0) (not (consp coefficients)))
 :hints (("Goal" :in-theory (enable len)))))

(defthm lw-polynomial-pad-evaluation
 (implies (and (lw-complex-coefficientsp coefficients) (natp count) (<= (len coefficients) count)
               (lw-complexp point) (natp offset))
  (equal (lw-complex-polynomial (lw-polynomial-pad coefficients count) point offset)
         (lw-complex-polynomial coefficients point offset)))
 :hints (("Goal" :induct (lw-pcm-pad-eval-induct coefficients count offset)
  :in-theory (union-theories
   '((:induction lw-pcm-pad-eval-induct) lw-polynomial-pad lw-complex-polynomial lw-complexp lw-complex-coefficientsp lw-pcm-empty-length lw-pcm-pad-empty lw-complex-add-zero lw-complex-mul-zero lw-complex-power-rational len lw-pcm-len-nonnegative endp lw-pcm-left-commutes lw-pcm-left-distributes lw-pcm-fold-constants lw-pcm-times-negative lw-pcm-negative-times lw-pcm-zero-times lw-pcm-minus-one lw-pcm-double-negative lw-pcm-add-cancel lw-pcm-double lw-pcm-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory)))))

(defthm lw-complex-coefficient-at-outside
 (implies (and (lw-complex-coefficientsp coefficients) (natp target) (natp offset)
               (<= (+ offset (len coefficients)) target))
  (equal (lw-complex-coefficient-at coefficients target offset) (cons 0 0)))
 :hints (("Goal" :induct (lw-complex-coefficient-at coefficients target offset)
  :in-theory (union-theories
   '(lw-complex-coefficient-at lw-complex-coefficientsp lw-complex-add-zero lw-complexp len lw-pcm-len-nonnegative endp lw-pcm-left-commutes lw-pcm-left-distributes lw-pcm-fold-constants lw-pcm-times-negative lw-pcm-negative-times lw-pcm-zero-times lw-pcm-minus-one lw-pcm-double-negative lw-pcm-add-cancel lw-pcm-double lw-pcm-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory)))))

(defthm lw-polynomial-pad-coefficient
 (implies (and (lw-complex-coefficientsp coefficients) (natp count) (<= (len coefficients) count)
               (natp target) (natp offset))
  (equal (lw-complex-coefficient-at (lw-polynomial-pad coefficients count) target offset)
         (lw-complex-coefficient-at coefficients target offset)))
 :hints (("Goal" :induct (lw-pcm-pad-eval-induct coefficients count offset)
  :in-theory (union-theories
   '((:induction lw-pcm-pad-eval-induct) lw-polynomial-pad lw-complex-coefficient-at lw-complex-coefficientsp lw-complex-add-zero lw-complex-coefficient-at-rational lw-pcm-empty-length lw-complexp len lw-pcm-len-nonnegative endp lw-pcm-left-commutes lw-pcm-left-distributes lw-pcm-fold-constants lw-pcm-times-negative lw-pcm-negative-times lw-pcm-zero-times lw-pcm-minus-one lw-pcm-double-negative lw-pcm-add-cancel lw-pcm-double lw-pcm-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory)))))

(local (in-theory (disable lw-polynomial-rescale lw-polynomial-pad)))

(defun lw-polynomial-disk-difference (left right radius count)
 (lw-polynomial-difference
  (lw-polynomial-pad (lw-polynomial-rescale left radius 0) count)
  (lw-polynomial-pad (lw-polynomial-rescale right radius 0) count)))

(local (in-theory (disable lw-polynomial-disk-difference)))

(defthm lw-polynomial-disk-difference-valid
 (implies (and (lw-complex-coefficientsp left) (lw-complex-coefficientsp right) (rationalp radius)
               (natp count) (<= (len left) count) (<= (len right) count))
  (and (lw-complex-coefficientsp (lw-polynomial-disk-difference left right radius count)) (equal (len (lw-polynomial-disk-difference left right radius count)) count)))
 :hints (("Goal"
  :use ((:instance lw-polynomial-rescale-valid (coefficients left) (factor radius) (offset 0))
        (:instance lw-polynomial-rescale-valid (coefficients right) (factor radius) (offset 0))
        (:instance lw-polynomial-pad-valid (coefficients (lw-polynomial-rescale left radius 0)))
        (:instance lw-polynomial-pad-valid (coefficients (lw-polynomial-rescale right radius 0)))
        (:instance lw-polynomial-difference-valid (left (lw-polynomial-pad (lw-polynomial-rescale left radius 0) count)) (right (lw-polynomial-pad (lw-polynomial-rescale right radius 0) count))))
  :in-theory (union-theories
   '(lw-polynomial-disk-difference lw-pcm-left-commutes lw-pcm-left-distributes lw-pcm-fold-constants lw-pcm-times-negative lw-pcm-negative-times lw-pcm-zero-times lw-pcm-minus-one lw-pcm-double-negative lw-pcm-add-cancel lw-pcm-double lw-pcm-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-polynomial-disk-difference-evaluation
 (implies (and (lw-complex-coefficientsp left) (lw-complex-coefficientsp right) (rationalp radius)
               (natp count) (<= (len left) count) (<= (len right) count) (lw-complexp point))
  (equal (lw-complex-polynomial (lw-polynomial-disk-difference left right radius count) point 0)
         (lw-complex-sub (lw-complex-polynomial left (lw-complex-scale radius point) 0)
                         (lw-complex-polynomial right (lw-complex-scale radius point) 0))))
 :hints (("Goal"
  :use ((:instance lw-polynomial-rescale-valid (coefficients left) (factor radius) (offset 0))
        (:instance lw-polynomial-rescale-valid (coefficients right) (factor radius) (offset 0))
        (:instance lw-polynomial-pad-valid (coefficients (lw-polynomial-rescale left radius 0)))
        (:instance lw-polynomial-pad-valid (coefficients (lw-polynomial-rescale right radius 0)))
        (:instance lw-polynomial-difference-evaluation (left (lw-polynomial-pad (lw-polynomial-rescale left radius 0) count)) (right (lw-polynomial-pad (lw-polynomial-rescale right radius 0) count)) (offset 0))
        (:instance lw-polynomial-pad-evaluation (coefficients (lw-polynomial-rescale left radius 0)) (offset 0))
        (:instance lw-polynomial-pad-evaluation (coefficients (lw-polynomial-rescale right radius 0)) (offset 0))
        (:instance lw-polynomial-rescale-evaluation (coefficients left) (factor radius) (offset 0))
        (:instance lw-polynomial-rescale-evaluation (coefficients right) (factor radius) (offset 0)))
  :in-theory (union-theories
   '(lw-polynomial-disk-difference lw-pcm-left-commutes lw-pcm-left-distributes lw-pcm-fold-constants lw-pcm-times-negative lw-pcm-negative-times lw-pcm-zero-times lw-pcm-minus-one lw-pcm-double-negative lw-pcm-add-cancel lw-pcm-double lw-pcm-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-polynomial-disk-difference-coefficient
 (implies (and (lw-complex-coefficientsp left) (lw-complex-coefficientsp right) (rationalp radius)
               (natp count) (<= (len left) count) (<= (len right) count) (natp index) (< index count))
  (equal (nth index (lw-polynomial-disk-difference left right radius count))
         (lw-complex-sub
          (lw-complex-coefficient-at (lw-polynomial-rescale left radius 0) index 0)
          (lw-complex-coefficient-at (lw-polynomial-rescale right radius 0) index 0))))
 :hints (("Goal"
  :use ((:instance lw-polynomial-rescale-valid (coefficients left) (factor radius) (offset 0))
        (:instance lw-polynomial-rescale-valid (coefficients right) (factor radius) (offset 0))
        (:instance lw-polynomial-pad-valid (coefficients (lw-polynomial-rescale left radius 0)))
        (:instance lw-polynomial-pad-valid (coefficients (lw-polynomial-rescale right radius 0)))
        (:instance lw-polynomial-difference-nth (left (lw-polynomial-pad (lw-polynomial-rescale left radius 0) count)) (right (lw-polynomial-pad (lw-polynomial-rescale right radius 0) count)))
        (:instance lw-polynomial-pad-coefficient (coefficients (lw-polynomial-rescale left radius 0)) (target index) (offset 0))
        (:instance lw-polynomial-pad-coefficient (coefficients (lw-polynomial-rescale right radius 0)) (target index) (offset 0))
        (:instance lw-complex-coefficient-at-nth (coefficients (lw-polynomial-pad (lw-polynomial-rescale left radius 0) count)) (target index) (offset 0))
        (:instance lw-complex-coefficient-at-nth (coefficients (lw-polynomial-pad (lw-polynomial-rescale right radius 0) count)) (target index) (offset 0)))
  :in-theory (union-theories
   '(lw-polynomial-disk-difference lw-pcm-left-commutes lw-pcm-left-distributes lw-pcm-fold-constants lw-pcm-times-negative lw-pcm-negative-times lw-pcm-zero-times lw-pcm-minus-one lw-pcm-double-negative lw-pcm-add-cancel lw-pcm-double lw-pcm-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t)))


