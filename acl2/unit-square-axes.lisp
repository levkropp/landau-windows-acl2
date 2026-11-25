(in-package "ACL2")

(include-book "ray-translations")
(include-book "unit-square-steps")

; The canonical square's sampled sides have exact fixed coordinates.

(local (defthm lw-usa-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-usa-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-usa-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-usa-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-usa-times-negative (a b) (b a)))
                 :in-theory (disable lw-usa-times-negative)))))

(local (defthm lw-usa-zero-times (equal (* 0 a) 0)))

(local (defthm lw-usa-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-usa-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-usa-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-usa-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-usa-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-usa-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-usa-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-usa-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-usa-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-usa-left-commutes)))))
(local (defthm lw-usa-rational-inverse
 (implies (rationalp x) (rationalp (/ x))) :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-usa-rational-product
 (implies (and (rationalp x) (rationalp y)) (rationalp (* x y)))
 :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-usa-side-coordinates
 (implies (and (posp count) (natp index) (natp edge) (< edge 4))
  (equal
   (lw-polynomial-line-value '((0 . 0) (1 . 0))
    (lw-polynomial-square-edge-left '(-1 . -1) 2 edge)
    (lw-polynomial-square-edge-right '(-1 . -1) 2 edge) count index)
   (cond ((equal edge 0) (cons (+ -1 (* 2 index (/ count))) -1))
         ((equal edge 1) (cons (+ -1 (* 2 index (/ count))) 1))
         ((equal edge 2) (cons 1 (+ -1 (* 2 index (/ count)))))
         (t (cons -1 (+ -1 (* 2 index (/ count))))))))
 :hints (("Goal"
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-line-value lw-polynomial-line-point lw-complex-identity-polynomial lw-complexp lw-polynomial-square-edge-left lw-polynomial-square-edge-right lw-complex-segment lw-complex-add lw-complex-scale lw-usa-rational-inverse lw-usa-rational-product lw-usa-left-commutes lw-usa-left-distributes lw-usa-fold-constants lw-usa-times-negative lw-usa-negative-times lw-usa-zero-times lw-usa-minus-one lw-usa-double-negative lw-usa-add-cancel lw-usa-double lw-usa-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :cases ((equal edge 0) (equal edge 1) (equal edge 2))))))


(local (defthm lw-usa-side-0
 (implies (and (posp count) (natp index) (natp remaining))
  (lw-ray-fixed-imag-pointsp (lw-polynomial-line-values '((0 . 0) (1 . 0))
     (lw-polynomial-square-edge-left '(-1 . -1) 2 0)
     (lw-polynomial-square-edge-right '(-1 . -1) 2 0) count index remaining) -1))
 :hints (("Goal" :induct (lw-polynomial-line-values '((0 . 0) (1 . 0))
     (lw-polynomial-square-edge-left '(-1 . -1) 2 0)
     (lw-polynomial-square-edge-right '(-1 . -1) 2 0) count index remaining)
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-polynomial-line-values) lw-polynomial-line-values lw-ray-fixed-imag-pointsp lw-usa-side-coordinates lw-complexp lw-usa-rational-inverse lw-usa-rational-product endp lw-usa-left-commutes lw-usa-left-distributes lw-usa-fold-constants lw-usa-times-negative lw-usa-negative-times lw-usa-zero-times lw-usa-minus-one lw-usa-double-negative lw-usa-add-cancel lw-usa-double lw-usa-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-usa-side-1
 (implies (and (posp count) (natp index) (natp remaining))
  (lw-ray-fixed-imag-pointsp (lw-polynomial-line-values '((0 . 0) (1 . 0))
     (lw-polynomial-square-edge-left '(-1 . -1) 2 1)
     (lw-polynomial-square-edge-right '(-1 . -1) 2 1) count index remaining) 1))
 :hints (("Goal" :induct (lw-polynomial-line-values '((0 . 0) (1 . 0))
     (lw-polynomial-square-edge-left '(-1 . -1) 2 1)
     (lw-polynomial-square-edge-right '(-1 . -1) 2 1) count index remaining)
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-polynomial-line-values) lw-polynomial-line-values lw-ray-fixed-imag-pointsp lw-usa-side-coordinates lw-complexp lw-usa-rational-inverse lw-usa-rational-product endp lw-usa-left-commutes lw-usa-left-distributes lw-usa-fold-constants lw-usa-times-negative lw-usa-negative-times lw-usa-zero-times lw-usa-minus-one lw-usa-double-negative lw-usa-add-cancel lw-usa-double lw-usa-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-usa-side-2
 (implies (and (posp count) (natp index) (natp remaining))
  (lw-ray-fixed-real-pointsp (lw-polynomial-line-values '((0 . 0) (1 . 0))
     (lw-polynomial-square-edge-left '(-1 . -1) 2 2)
     (lw-polynomial-square-edge-right '(-1 . -1) 2 2) count index remaining) 1))
 :hints (("Goal" :induct (lw-polynomial-line-values '((0 . 0) (1 . 0))
     (lw-polynomial-square-edge-left '(-1 . -1) 2 2)
     (lw-polynomial-square-edge-right '(-1 . -1) 2 2) count index remaining)
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-polynomial-line-values) lw-polynomial-line-values lw-ray-fixed-real-pointsp lw-usa-side-coordinates lw-complexp lw-usa-rational-inverse lw-usa-rational-product endp lw-usa-left-commutes lw-usa-left-distributes lw-usa-fold-constants lw-usa-times-negative lw-usa-negative-times lw-usa-zero-times lw-usa-minus-one lw-usa-double-negative lw-usa-add-cancel lw-usa-double lw-usa-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-usa-side-3
 (implies (and (posp count) (natp index) (natp remaining))
  (lw-ray-fixed-real-pointsp (lw-polynomial-line-values '((0 . 0) (1 . 0))
     (lw-polynomial-square-edge-left '(-1 . -1) 2 3)
     (lw-polynomial-square-edge-right '(-1 . -1) 2 3) count index remaining) -1))
 :hints (("Goal" :induct (lw-polynomial-line-values '((0 . 0) (1 . 0))
     (lw-polynomial-square-edge-left '(-1 . -1) 2 3)
     (lw-polynomial-square-edge-right '(-1 . -1) 2 3) count index remaining)
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-polynomial-line-values) lw-polynomial-line-values lw-ray-fixed-real-pointsp lw-usa-side-coordinates lw-complexp lw-usa-rational-inverse lw-usa-rational-product endp lw-usa-left-commutes lw-usa-left-distributes lw-usa-fold-constants lw-usa-times-negative lw-usa-negative-times lw-usa-zero-times lw-usa-minus-one lw-usa-double-negative lw-usa-add-cancel lw-usa-double lw-usa-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-unit-square-side-axes
 (implies (posp count)
  (and (lw-ray-fixed-imag-pointsp (lw-unit-square-side count 0) -1)
       (lw-ray-fixed-imag-pointsp (lw-unit-square-side count 1) 1)
       (lw-ray-fixed-real-pointsp (lw-unit-square-side count 2) 1)
       (lw-ray-fixed-real-pointsp (lw-unit-square-side count 3) -1)))
 :hints (("Goal"
  :use ((:instance lw-usa-side-0 (index 0) (remaining (+ 1 count)))
        (:instance lw-usa-side-1 (index 0) (remaining (+ 1 count)))
        (:instance lw-usa-side-2 (index 0) (remaining (+ 1 count)))
        (:instance lw-usa-side-3 (index 0) (remaining (+ 1 count))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-unit-square-side lw-usa-left-commutes lw-usa-left-distributes lw-usa-fold-constants lw-usa-times-negative lw-usa-negative-times lw-usa-zero-times lw-usa-minus-one lw-usa-double-negative lw-usa-add-cancel lw-usa-double lw-usa-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
