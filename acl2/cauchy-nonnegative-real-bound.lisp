(in-package "ACL2")

(include-book "cauchy-nonnegative-real-coefficients")
(include-book "polynomial-geometric-bounds")

; A single finite nonnegative-real-part check controls every nonconstant
; coefficient and hence the polynomial on a strict inner disk.

(local (defthm lw-cnrb-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-cnrb-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-cnrb-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-cnrb-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-cnrb-times-negative (a b) (b a)))
                 :in-theory (disable lw-cnrb-times-negative)))))

(local (defthm lw-cnrb-zero-times (equal (* 0 a) 0)))

(local (defthm lw-cnrb-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-cnrb-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-cnrb-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-cnrb-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-cnrb-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-cnrb-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-cnrb-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cnrb-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defun lw-cauchy-nonnegative-real-polynomial-check (coefficients error)
  (let ((degree (* 2 (len coefficients))))
    (lw-cauchy-nonnegative-real-check coefficients (lw-cauchy-orbit-rotation degree)
      (lw-cauchy-coefficient-count coefficients degree error))))

(local
 (defthm lw-cnrb-length-natural
   (natp (len coefficients))
   :hints (("Goal" :induct (len coefficients) :in-theory (enable len)))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm lw-cnrb-nth-successor
   (implies (and (consp coefficients) (natp index))
            (equal (nth (+ 1 index) coefficients) (nth index (cdr coefficients))))
   :hints (("Goal" :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              nth endp
              lw-cnrb-left-commutes lw-cnrb-left-distributes lw-cnrb-fold-constants
              lw-cnrb-times-negative lw-cnrb-negative-times lw-cnrb-zero-times
              lw-cnrb-minus-one lw-cnrb-double-negative lw-cnrb-add-cancel lw-cnrb-double lw-cnrb-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                   :do-not-induct t))))

(local
 (defthm lw-cnrb-tail-caps
   (implies (and (lw-complex-coefficientsp coefficients) (consp coefficients)
                 (rationalp error) (< 0 error)
                 (lw-cauchy-nonnegative-real-polynomial-check coefficients error))
            (lw-polynomial-coefficient-caps (cdr coefficients) (+ (* 2 (car (car coefficients))) (* 4 error))))
   :hints (("Goal"
            :use ((:instance lw-polynomial-cap-index-data (coefficients (cdr coefficients)) (cap (+ (* 2 (car (car coefficients))) (* 4 error))))
                  (:instance lw-cauchy-nonnegative-real-coefficient-cap
                    (degree (* 2 (len coefficients))) (target (+ 1 (lw-polynomial-cap-index (cdr coefficients) (+ (* 2 (car (car coefficients))) (* 4 error)))))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-cnrb-length-natural lw-cnrb-nth-successor len nth endp
              lw-complex-coefficientsp lw-cauchy-nonnegative-real-polynomial-check
              lw-cnrb-left-commutes lw-cnrb-left-distributes lw-cnrb-fold-constants
              lw-cnrb-times-negative lw-cnrb-negative-times lw-cnrb-zero-times
              lw-cnrb-minus-one lw-cnrb-double-negative lw-cnrb-add-cancel lw-cnrb-double lw-cnrb-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-cnrb-real-difference
   (implies (and (lw-complexp left) (lw-complexp right))
            (and (rationalp (car left)) (rationalp (car right))
                 (equal (car (lw-complex-sub left right)) (- (car left) (car right)))))
   :hints (("Goal" :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complexp lw-complex-sub
              lw-cnrb-left-commutes lw-cnrb-left-distributes lw-cnrb-fold-constants
              lw-cnrb-times-negative lw-cnrb-negative-times lw-cnrb-zero-times
              lw-cnrb-minus-one lw-cnrb-double-negative lw-cnrb-add-cancel lw-cnrb-double lw-cnrb-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                   :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-cnrb-constant-cancel
   (implies (and (lw-complexp constant) (lw-complexp tail))
            (equal (lw-complex-sub (lw-complex-add constant tail) constant) tail))
   :hints (("Goal" :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complexp lw-complex-add lw-complex-sub
              lw-cnrb-left-commutes lw-cnrb-left-distributes lw-cnrb-fold-constants
              lw-cnrb-times-negative lw-cnrb-negative-times lw-cnrb-zero-times
              lw-cnrb-minus-one lw-cnrb-double-negative lw-cnrb-add-cancel lw-cnrb-double lw-cnrb-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                   :do-not-induct t))
   :rule-classes nil))

(defthm lw-cauchy-nonnegative-real-polynomial-bound
  (implies (and (lw-complex-coefficientsp coefficients) (consp coefficients)
                (rationalp error) (< 0 error) (<= 0 (car (car coefficients)))
                (lw-cauchy-nonnegative-real-polynomial-check coefficients error)
                (lw-complex-diskp point radius) (< radius 1))
           (and (lw-complex-diskp (lw-complex-sub (lw-complex-polynomial coefficients point 0) (car coefficients)) (* radius (/ (+ (* 2 (car (car coefficients))) (* 4 error)) (- 1 radius))))
                (<= (car (lw-complex-polynomial coefficients point 0)) (+ (car (car coefficients)) (* radius (/ (+ (* 2 (car (car coefficients))) (* 4 error)) (- 1 radius)))))))
  :hints (("Goal"
           :use (lw-cnrb-tail-caps lw-complex-disk-data lw-complex-polynomial-horner
                 (:instance lw-complex-polynomial-rational (offset 0))
                 (:instance lw-complex-polynomial-rational (coefficients (cdr coefficients)) (offset 0))
                 (:instance lw-cnrb-real-difference (left (lw-complex-polynomial coefficients point 0)) (right (car coefficients)))
                 (:instance lw-complex-polynomial-geometric-tail-bound (coefficients (cdr coefficients)) (cap (+ (* 2 (car (car coefficients))) (* 4 error))) (offset 0))
                 (:instance lw-complex-mul-disk (left point) (right (lw-complex-polynomial (cdr coefficients) point 0)) (other-radius (/ (+ (* 2 (car (car coefficients))) (* 4 error)) (- 1 radius))))
                 (:instance lw-complex-ring-rational (left point) (right (lw-complex-polynomial (cdr coefficients) point 0)))
                 (:instance lw-cnrb-constant-cancel (constant (car coefficients))
                   (tail (lw-complex-mul point (lw-complex-polynomial (cdr coefficients) point 0))))
                 (:instance lw-complex-disk-coordinates (point (lw-complex-sub (lw-complex-polynomial coefficients point 0) (car coefficients))) (radius (* radius (/ (+ (* 2 (car (car coefficients))) (* 4 error)) (- 1 radius))))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complex-coefficientsp lw-geometric-disk-gain lw-rational-power abs
              lw-cnrb-left-commutes lw-cnrb-left-distributes lw-cnrb-fold-constants
              lw-cnrb-times-negative lw-cnrb-negative-times lw-cnrb-zero-times
              lw-cnrb-minus-one lw-cnrb-double-negative lw-cnrb-add-cancel lw-cnrb-double lw-cnrb-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
