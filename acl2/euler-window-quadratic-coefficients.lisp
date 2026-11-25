(in-package "ACL2")

(include-book "euler-window-coefficients")
(include-book "kernel-window-index-block")
(include-book "euler-mellin-quadratic-model")

(defun lw-euler-window-local-coefficient-radius (ceiling numerator denominator index error)
  (+ (lw-euler-window-coefficient-radius-at index ceiling numerator denominator error error)
     error))

(defun lw-euler-window-quadratic-radius (height ceiling numerator denominator index error)
  (+ (* (lw-complex-l1 (lw-zeta-residue-denominator (cons 252 height)))
        (lw-euler-window-local-coefficient-radius ceiling numerator denominator (+ 2 index) error))
     (* (lw-complex-l1 (lw-complex-sub (cons 1 0) (lw-complex-scale 2 (cons 252 height))))
        (lw-euler-window-local-coefficient-radius ceiling numerator denominator (+ 1 index) error))
     (lw-euler-window-local-coefficient-radius ceiling numerator denominator index error)))

(local (defthm lw-ewqc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ewqc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ewqc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ewqc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ewqc-times-negative (a b) (b a)))
                 :in-theory (disable lw-ewqc-times-negative)))))

(local (defthm lw-ewqc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ewqc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ewqc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ewqc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ewqc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ewqc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ewqc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

; Transport the failed-search bound to the outer radius and anchor used
; by the factor model. The window and the coefficient order stay fixed.
(defthm lw-failed-search-euler-local-coefficient-bound
  (implies (and (rationalp start) (natp minimum-index) (natp width)
                (<= (lw-kernel-window-block-threshold minimum-index width) start)
                (natp index) (<= (lw-window-index start) index)
                (<= index (+ (lw-window-index start) width))
                (rationalp height) (rationalp outer-radius)
                (< 0 outer-radius) (< outer-radius 252)
                (lw-euler-value-clearance-check 252 height anchor-error)
                (rationalp ceiling) (<= 0 ceiling)
                (natp numerator) (posp denominator) (<= numerator denominator)
                (not (lw-landau-window-search start ceiling numerator denominator))
                (rationalp error) (< 0 error))
           (lw-complex-diskp (lw-complex-euler-mellin-coefficient-value 252 height outer-radius anchor-error index error)
                             (lw-euler-window-local-coefficient-radius ceiling numerator denominator index error)))
  :hints (("Goal"
           :use (lw-kernel-window-index-block-data
                 (:instance lw-failed-search-euler-coefficient-bound-at
                   (coefficient-error error) (real-error error))
                 (:instance lw-complex-mellin-euler-coefficient-rational (rate 252))
                 (:instance lw-complex-euler-mellin-coefficient-rational
                   (rate 252))
                 (:instance lw-mellin-euler-native-coefficient-agreement
                   (rate 252) (left-error error) (right-error error))
                 (:instance lw-complex-difference-triangle
                   (left (lw-complex-euler-mellin-coefficient-value 252 height outer-radius anchor-error index error)) (middle (lw-complex-mellin-euler-coefficient-value 252 height index error)) (right (cons 0 0))
                   (radius error)
                   (other-radius (lw-euler-window-coefficient-radius-at index ceiling numerator denominator error error))))
           :in-theory
           (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-window-local-coefficient-radius
              lw-complex-sub-zero lw-euler-neighborhood-data
              lw-euler-local-normalized-data
              lw-ewqc-left-commutes lw-ewqc-left-distributes lw-ewqc-fold-constants
              lw-ewqc-times-negative lw-ewqc-negative-times lw-ewqc-zero-times
              lw-ewqc-minus-one lw-ewqc-double-negative lw-ewqc-add-cancel lw-ewqc-double lw-ewqc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

; A power-sum witness at index+2 consumes the three consecutive
; orders index, index+1 and index+2 from this single window.
(defthm lw-failed-search-euler-quadratic-coefficient-bound
  (implies (and (rationalp start) (natp minimum-index) (natp width)
                (<= (lw-kernel-window-block-threshold minimum-index width) start)
                (natp index) (<= (lw-window-index start) index)
                (<= (+ 2 index) (+ (lw-window-index start) width))
                (rationalp height) (rationalp outer-radius)
                (< 0 outer-radius) (< outer-radius 252)
                (lw-euler-value-clearance-check 252 height anchor-error)
                (rationalp ceiling) (<= 0 ceiling)
                (natp numerator) (posp denominator) (<= numerator denominator)
                (not (lw-landau-window-search start ceiling numerator denominator))
                (rationalp error) (< 0 error))
           (lw-complex-diskp (lw-euler-mellin-quadratic-coefficient-value 252 height outer-radius anchor-error index error)
                             (lw-euler-window-quadratic-radius height ceiling numerator denominator index error)))
  :hints (("Goal"
           :use (lw-failed-search-euler-local-coefficient-bound
                 (:instance lw-failed-search-euler-local-coefficient-bound (index (+ 1 index)))
                 (:instance lw-failed-search-euler-local-coefficient-bound (index (+ 2 index)))
                 (:instance lw-pole-quadratic-coefficient-disk-bound
                   (center (cons 252 height))
                   (a (lw-complex-euler-mellin-coefficient-value 252 height outer-radius anchor-error (+ 2 index) error))
                   (b (lw-complex-euler-mellin-coefficient-value 252 height outer-radius anchor-error (+ 1 index) error))
                   (c (lw-complex-euler-mellin-coefficient-value 252 height outer-radius anchor-error index error))
                   (left-error (lw-euler-window-local-coefficient-radius ceiling numerator denominator (+ 2 index) error))
                   (middle-error (lw-euler-window-local-coefficient-radius ceiling numerator denominator (+ 1 index) error))
                   (right-error (lw-euler-window-local-coefficient-radius ceiling numerator denominator index error))))
           :in-theory
           (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complexp lw-euler-mellin-quadratic-coefficient-value
              lw-euler-window-quadratic-radius
              lw-ewqc-left-commutes lw-ewqc-left-distributes lw-ewqc-fold-constants
              lw-ewqc-times-negative lw-ewqc-negative-times lw-ewqc-zero-times
              lw-ewqc-minus-one lw-ewqc-double-negative lw-ewqc-add-cancel lw-ewqc-double lw-ewqc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
