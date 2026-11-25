(in-package "ACL2")

(include-book "complex-quotient-increments")
(include-book "euler-anchor-value")

; A finite check on an actual Euler value certifies all finer values.
; The real anchor supplies a computed accepted check.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-reciprocal lw-complex-norm-square
                 lw-complex-l1 lw-rational-power lw-complex-exp-value lw-complex-exp-cap
                 lw-complex-exp-uniform-cap lw-exp-lipschitz-cap lw-log-bounds
                 lw-complex-laplace-point lw-complex-laplace-shifted-value
                 lw-complex-laplace-shifted-grid lw-complex-mul-subtract
                 lw-complex-mul-commutative lw-complex-mul-left-commutes
                 lw-exp-bounds lw-exp-neg-bounds lw-exp-index lw-exp-band lw-exp-sum lw-exp-term
                 lw-damped-phase-sample lw-phase-value
                 lw-complex-exp-integral-value lw-complex-exp-integral-grid
                 lw-complex-exp-primitive-value lw-complex-exp-grid
                 lw-complex-disk-enlarge lw-disk-enlarge lw-precision-fuel)))
(local (in-theory (disable lw-complex-log-ramp-exp lw-complex-log-ramp-endpoint lw-complex-log-ramp-model)))

(local (in-theory (disable lw-complex-euler-continuation-value)))

(local (defthm lw-evc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-evc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-evc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-evc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-evc-times-negative (a b) (b a)))
                 :in-theory (disable lw-evc-times-negative)))))

(local (defthm lw-evc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-evc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-evc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-evc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-evc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-evc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-evc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-evc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-evc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-evc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-evc-left-commutes)))))

(defun lw-euler-value-clearance-size (rate height anchor-error)
 (lw-complex-l1 (lw-complex-euler-continuation-value rate height anchor-error)))

(defun lw-euler-value-clearance-lower (rate height anchor-error)
 (* 1/4 (lw-euler-value-clearance-size rate height anchor-error)))

(defun lw-euler-value-clearance-check (rate height anchor-error)
 (and (rationalp rate) (< 0 rate) (rationalp height)
      (rationalp anchor-error) (< 0 anchor-error)
      (< 0 (lw-euler-value-clearance-size rate height anchor-error))
      (<= anchor-error (* 1/16 (lw-euler-value-clearance-size rate height anchor-error)))))

(local (in-theory (disable lw-euler-value-clearance-size lw-euler-value-clearance-lower lw-euler-value-clearance-check)))

(local (defthm lw-evc-zero-size
 (equal (lw-complex-l1 (cons 0 0)) 0)
 :hints (("Goal" :in-theory (union-theories
 '(lw-complex-l1 abs lw-evc-left-commutes lw-evc-left-distributes lw-evc-fold-constants lw-evc-times-negative lw-evc-negative-times lw-evc-zero-times lw-evc-minus-one lw-evc-double-negative lw-evc-add-cancel lw-evc-double lw-evc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-euler-value-clearance-data
 (implies (lw-euler-value-clearance-check rate height anchor-error)
  (and (rationalp rate) (< 0 rate) (rationalp height)
       (rationalp anchor-error) (< 0 anchor-error)
       (rationalp (lw-euler-value-clearance-size rate height anchor-error))
       (< 0 (lw-euler-value-clearance-size rate height anchor-error))
       (rationalp (lw-euler-value-clearance-lower rate height anchor-error))
       (< 0 (lw-euler-value-clearance-lower rate height anchor-error))
       (<= anchor-error (* 1/4 (lw-euler-value-clearance-lower rate height anchor-error)))
       (lw-complexp (lw-complex-euler-continuation-value rate height anchor-error))
       (not (equal (lw-complex-euler-continuation-value rate height anchor-error) (cons 0 0)))))
 :hints (("Goal"
  :use ((:instance lw-complex-euler-continuation-value-rational (error anchor-error))
        (:instance lw-complex-l1-bound (point (lw-complex-euler-continuation-value rate height anchor-error))))
  :in-theory (union-theories
 '(lw-euler-value-clearance-check lw-euler-value-clearance-size lw-euler-value-clearance-lower lw-evc-zero-size lw-evc-left-commutes lw-evc-left-distributes lw-evc-fold-constants lw-evc-times-negative lw-evc-negative-times lw-evc-zero-times lw-evc-minus-one lw-evc-double-negative lw-evc-add-cancel lw-evc-double lw-evc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(local (defthm lw-evc-disk-l1
 (implies (lw-complex-diskp point radius)
  (<= (lw-complex-l1 point) (* 2 radius)))
 :hints (("Goal" :use (lw-complex-disk-coordinates)
  :in-theory (union-theories
 '(lw-complex-l1 lw-evc-left-commutes lw-evc-left-distributes lw-evc-fold-constants lw-evc-times-negative lw-evc-negative-times lw-evc-zero-times lw-evc-minus-one lw-evc-double-negative lw-evc-add-cancel lw-evc-double lw-evc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-evc-pair-reconstruction
 (implies (lw-complexp point) (equal (cons (car point) (cdr point)) point))
 :hints (("Goal" :in-theory (enable lw-complexp)))))

(local (defthm lw-evc-shift-identity
 (implies (and (lw-complexp point) (lw-complexp anchor))
  (equal (lw-complex-add anchor (lw-complex-sub point anchor)) point))
 :hints (("Goal"
  :in-theory (union-theories
 '(lw-complexp lw-complex-add lw-complex-sub lw-evc-pair-reconstruction lw-evc-left-commutes lw-evc-left-distributes lw-evc-fold-constants lw-evc-times-negative lw-evc-negative-times lw-evc-zero-times lw-evc-minus-one lw-evc-double-negative lw-evc-add-cancel lw-evc-double lw-evc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(defthm lw-complex-euler-value-clearance
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
               (rationalp request) (< 0 request)
               (<= request (* 1/4 (lw-euler-value-clearance-lower rate height anchor-error))))
  (and
   (lw-complexp (lw-complex-euler-continuation-value rate height request))
   (not (equal (lw-complex-euler-continuation-value rate height request) (cons 0 0)))
   (<= (* (lw-euler-value-clearance-lower rate height anchor-error)
          (lw-euler-value-clearance-lower rate height anchor-error))
       (lw-complex-norm-square (lw-complex-euler-continuation-value rate height request)))
   (lw-complex-diskp
    (lw-complex-reciprocal (lw-complex-euler-continuation-value rate height request))
    (/ (lw-euler-value-clearance-lower rate height anchor-error)))))
 :hints (("Goal"
  :use (lw-euler-value-clearance-data
        (:instance lw-complex-euler-continuation-value-rational (error request))
        (:instance lw-complex-euler-continuation-value-cauchy (left-error request) (right-error anchor-error))
        (:instance lw-complex-operations-rational
         (left (lw-complex-euler-continuation-value rate height request))
         (right (lw-complex-euler-continuation-value rate height anchor-error)) (factor 1))
        (:instance lw-evc-disk-l1
         (point (lw-complex-sub (lw-complex-euler-continuation-value rate height request)
                  (lw-complex-euler-continuation-value rate height anchor-error)))
         (radius (+ request anchor-error)))
        (:instance lw-complex-small-shift-clearance
         (anchor (lw-complex-euler-continuation-value rate height anchor-error))
         (offset (lw-complex-sub (lw-complex-euler-continuation-value rate height request)
                   (lw-complex-euler-continuation-value rate height anchor-error)))))
  :in-theory (union-theories
 '(lw-euler-value-clearance-lower lw-euler-value-clearance-size lw-evc-shift-identity lw-evc-left-commutes lw-evc-left-distributes lw-evc-fold-constants lw-evc-times-negative lw-evc-negative-times lw-evc-zero-times lw-evc-minus-one lw-evc-double-negative lw-evc-add-cancel lw-evc-double lw-evc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))


(defthm lw-euler-value-anchor-clearance
 (implies (and (rationalp anchor-error) (< 0 anchor-error) (<= anchor-error 1/64))
  (and (lw-euler-value-clearance-check 1 0 anchor-error)
       (<= 255/1024 (lw-euler-value-clearance-lower 1 0 anchor-error))
       (<= (lw-euler-value-clearance-lower 1 0 anchor-error) 1/2)))
 :hints (("Goal"
  :use ((:instance lw-complex-euler-anchor-value (error anchor-error))
        (:instance lw-complex-euler-continuation-value-rational (rate 1) (height 0) (error anchor-error))
        (:instance lw-complex-disk-coordinates
         (point (lw-complex-sub (lw-complex-euler-continuation-value 1 0 anchor-error) (cons 1 0)))
         (radius (* 1/4 anchor-error))))
  :cases ((<= 0 (car (lw-complex-euler-continuation-value 1 0 anchor-error)))
          (<= 0 (cdr (lw-complex-euler-continuation-value 1 0 anchor-error))))
  :in-theory (union-theories
 '(lw-euler-value-clearance-check lw-euler-value-clearance-size lw-euler-value-clearance-lower lw-complexp lw-complex-sub lw-complex-l1 abs lw-evc-left-commutes lw-evc-left-distributes lw-evc-fold-constants lw-evc-times-negative lw-evc-negative-times lw-evc-zero-times lw-evc-minus-one lw-evc-double-negative lw-evc-add-cancel lw-evc-double lw-evc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))


