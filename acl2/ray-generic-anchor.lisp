(in-package "ACL2")

(include-book "ray-triangle-products")
(include-book "polygon-index")

; A computed rational direction not collinear with any finite nonzero
; point: slope 1 + sum abs(y/x), taking the summand as zero at x=0.

(local (defthm lw-rga-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-rga-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-rga-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-rga-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-rga-times-negative (a b) (b a)))
                 :in-theory (disable lw-rga-times-negative)))))

(local (defthm lw-rga-zero-times (equal (* 0 a) 0)))

(local (defthm lw-rga-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-rga-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-rga-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-rga-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-rga-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-rga-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-rga-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-rga-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-rga-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-rga-left-commutes)))))

(defun lw-ray-nonzero-pointsp (points)
 (if (endp points) (equal points nil)
  (and (lw-complexp (car points)) (not (equal (car points) (cons 0 0)))
       (lw-ray-nonzero-pointsp (cdr points)))))

(defun lw-ray-slope-mass (points)
 (if (endp points) 0
  (+ (if (equal (caar points) 0) 0 (abs (* (cdar points) (/ (caar points)))))
     (lw-ray-slope-mass (cdr points)))))

(defun lw-ray-anchor-noncollinearp (anchor points)
 (if (endp points) t
  (and (not (equal (lw-complex-det anchor (car points)) 0))
       (lw-ray-anchor-noncollinearp anchor (cdr points)))))

(defun lw-ray-generic-anchor (points)
 (cons 1 (+ 1 (lw-ray-slope-mass points))))

(local (defthm lw-rga-rational-product
 (implies (and (rationalp x) (rationalp y)) (rationalp (* x y)))
 :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-rga-rational-sum
 (implies (and (rationalp x) (rationalp y)) (rationalp (+ x y)))
 :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-rga-rational-inverse
 (implies (rationalp x) (rationalp (/ x)))
 :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-rga-abs-valid
 (implies (rationalp x) (and (rationalp (abs x)) (<= 0 (abs x))))
 :rule-classes (:rewrite :type-prescription)))

(defthm lw-ray-slope-mass-valid
 (implies (lw-ray-nonzero-pointsp points)
  (and (rationalp (lw-ray-slope-mass points)) (<= 0 (lw-ray-slope-mass points))))
 :hints (("Goal" :induct (lw-ray-slope-mass points)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-nonzero-pointsp lw-ray-slope-mass lw-complexp lw-rga-rational-product lw-rga-rational-sum lw-rga-rational-inverse lw-rga-abs-valid lw-rga-left-commutes lw-rga-left-distributes lw-rga-fold-constants lw-rga-times-negative lw-rga-negative-times lw-rga-zero-times lw-rga-minus-one lw-rga-double-negative lw-rga-add-cancel lw-rga-double lw-rga-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))
 :rule-classes (:rewrite :type-prescription))

(local (defthm lw-rga-divide-equation
 (implies (and (rationalp x) (not (equal x 0)) (rationalp y) (rationalp slope)
               (equal y (* slope x)))
          (equal (* y (/ x)) slope))
 :hints (("Goal"
  :use ((:instance lw-rga-inverse-factor (divisor x) (coefficient slope)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-rga-left-commutes lw-rga-left-distributes lw-rga-fold-constants lw-rga-times-negative lw-rga-negative-times lw-rga-zero-times lw-rga-minus-one lw-rga-double-negative lw-rga-add-cancel lw-rga-double lw-rga-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-rga-det-slope
 (implies (and (lw-complexp point) (not (equal (car point) 0)) (rationalp slope)
               (equal (lw-complex-det (cons 1 slope) point) 0))
          (equal (* (cdr point) (/ (car point))) slope))
 :hints (("Goal"
  :use ((:instance lw-rga-divide-equation
          (x (car point)) (y (cdr point))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-complexp lw-complex-det lw-rga-left-commutes lw-rga-left-distributes lw-rga-fold-constants lw-rga-times-negative lw-rga-negative-times lw-rga-zero-times lw-rga-minus-one lw-rga-double-negative lw-rga-add-cancel lw-rga-double lw-rga-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-rga-pair
 (implies (consp point) (equal (cons (car point) (cdr point)) point))))

(defthm lw-ray-large-slope-noncollinear
 (implies (and (lw-complexp point) (not (equal point (cons 0 0)))
               (rationalp slope) (< (abs (* (cdr point) (/ (car point)))) slope))
  (not (equal (lw-complex-det (cons 1 slope) point) 0)))
 :hints (("Goal" :cases ((equal (car point) 0))
  :use (lw-rga-det-slope)
  :in-theory (union-theories
 '(fold-consts-in-+ lw-complexp lw-complex-det lw-rga-pair abs lw-rga-left-commutes lw-rga-left-distributes lw-rga-fold-constants lw-rga-times-negative lw-rga-negative-times lw-rga-zero-times lw-rga-minus-one lw-rga-double-negative lw-rga-add-cancel lw-rga-double lw-rga-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-rga-axis-noncollinear
 (implies (and (lw-complexp point) (not (equal point (cons 0 0)))
               (equal (car point) 0) (rationalp slope))
  (not (equal (lw-complex-det (cons 1 slope) point) 0)))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complexp lw-complex-det lw-rga-pair lw-rga-left-commutes lw-rga-left-distributes lw-rga-fold-constants lw-rga-times-negative lw-rga-negative-times lw-rga-zero-times lw-rga-minus-one lw-rga-double-negative lw-rga-add-cancel lw-rga-double lw-rga-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-rga-large-slope-check
 (implies (and (lw-ray-nonzero-pointsp points) (rationalp slope)
               (< (lw-ray-slope-mass points) slope))
  (lw-ray-anchor-noncollinearp (cons 1 slope) points))
 :hints (("Goal" :induct (lw-ray-slope-mass points)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-slope-mass lw-ray-nonzero-pointsp lw-ray-anchor-noncollinearp lw-ray-slope-mass-valid lw-ray-large-slope-noncollinear lw-rga-axis-noncollinear lw-complexp lw-rga-rational-product lw-rga-rational-inverse lw-rga-abs-valid lw-rga-left-commutes lw-rga-left-distributes lw-rga-fold-constants lw-rga-times-negative lw-rga-negative-times lw-rga-zero-times lw-rga-minus-one lw-rga-double-negative lw-rga-add-cancel lw-rga-double lw-rga-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-ray-generic-anchor-certificate
 (implies (lw-ray-nonzero-pointsp points)
  (and (lw-complexp (lw-ray-generic-anchor points))
       (not (equal (lw-ray-generic-anchor points) (cons 0 0)))
       (lw-ray-anchor-noncollinearp (lw-ray-generic-anchor points) points)))
 :hints (("Goal"
  :use ((:instance lw-rga-large-slope-check (slope (+ 1 (lw-ray-slope-mass points)))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-generic-anchor lw-ray-slope-mass-valid lw-complexp lw-rga-left-commutes lw-rga-left-distributes lw-rga-fold-constants lw-rga-times-negative lw-rga-negative-times lw-rga-zero-times lw-rga-minus-one lw-rga-double-negative lw-rga-add-cancel lw-rga-double lw-rga-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-ray-anchor-noncollinear-first
 (implies (and (consp points) (lw-ray-anchor-noncollinearp anchor points))
  (and (not (equal (lw-complex-det anchor (car points)) 0))
       (lw-ray-anchor-noncollinearp anchor (cdr points))))
 :hints (("Goal" :expand ((lw-ray-anchor-noncollinearp anchor points)))))

(defthm lw-ray-anchor-noncollinear-last
 (implies (and (lw-ray-anchor-noncollinearp anchor points)
               (not (equal (lw-complex-det anchor current) 0)))
  (not (equal (lw-complex-det anchor (lw-ray-path-last current points)) 0)))
 :hints (("Goal" :induct (lw-ray-path-last current points)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-path-last lw-ray-anchor-noncollinearp lw-rga-left-commutes lw-rga-left-distributes lw-rga-fold-constants lw-rga-times-negative lw-rga-negative-times lw-rga-zero-times lw-rga-minus-one lw-rga-double-negative lw-rga-add-cancel lw-rga-double lw-rga-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

