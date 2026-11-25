(in-package "ACL2")

(include-book "normalized-local-polynomial")
(include-book "polynomial-affine")

; Clearing s(s-1) leaves a linear term and the negative log derivative.
(local (defthm lw-mqn-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-mqn-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-mqn-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-mqn-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-mqn-times-negative (a b) (b a)))
                 :in-theory (disable lw-mqn-times-negative)))))

(local (defthm lw-mqn-zero-times (equal (* 0 a) 0)))

(local (defthm lw-mqn-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-mqn-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-mqn-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-mqn-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-mqn-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-mqn-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))


(local
 (defthm lw-mqn-one-inverse
   (implies (and (lw-complexp a) (lw-complexp b)
                 (not (equal a (cons 0 0))))
            (and (equal (lw-complex-mul (lw-complex-mul a b) (lw-complex-reciprocal a)) b)
                 (equal (lw-complex-mul a (lw-complex-mul b (lw-complex-reciprocal a))) b)))
   :hints (("Goal"
            :use (lw-complex-reciprocal-cancel-product
                  (:instance lw-complex-mul-commutative (left (lw-complex-mul a b)) (right (lw-complex-reciprocal a)))
                  (:instance lw-complex-mul-commutative (left b) (right (lw-complex-reciprocal a))))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-complex-ring-rational lw-complex-reciprocal-rational lw-mqn-left-commutes lw-mqn-left-distributes lw-mqn-fold-constants lw-mqn-times-negative lw-mqn-negative-times lw-mqn-zero-times lw-mqn-minus-one lw-mqn-double-negative lw-mqn-add-cancel lw-mqn-double lw-mqn-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))))

(local
 (defthm lw-mqn-two-inverses
   (implies (and (lw-complexp s) (lw-complexp t-minus-one) (lw-complexp value)
                 (not (equal s (cons 0 0))) (not (equal t-minus-one (cons 0 0))))
            (equal (lw-complex-mul (lw-complex-mul s t-minus-one)
                    (lw-complex-mul value (lw-complex-mul (lw-complex-reciprocal s) (lw-complex-reciprocal t-minus-one))))
                   value))
   :hints (("Goal"
            :use ((:instance lw-complex-reciprocal-product (a s) (b t-minus-one))
                  (:instance lw-mqn-one-inverse (a (lw-complex-mul s t-minus-one)) (b value)))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-complex-ring-rational lw-complex-reciprocal-rational lw-complex-product-nonzero lw-mqn-left-commutes lw-mqn-left-distributes lw-mqn-fold-constants lw-mqn-times-negative lw-mqn-negative-times lw-mqn-zero-times lw-mqn-minus-one lw-mqn-double-negative lw-mqn-add-cancel lw-mqn-double lw-mqn-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))))

(local
 (defthm lw-mqn-subtraction
   (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c))
            (equal (lw-complex-sub a (lw-complex-sub b c))
                   (lw-complex-sub (lw-complex-add a c) b)))
   :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-complexp lw-complex-add lw-complex-sub consp lw-mqn-left-commutes lw-mqn-left-distributes lw-mqn-fold-constants lw-mqn-times-negative lw-mqn-negative-times lw-mqn-zero-times lw-mqn-minus-one lw-mqn-double-negative lw-mqn-add-cancel lw-mqn-double lw-mqn-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-complex-local-normalization-times-quadratic
  (implies (and (lw-complexp anchor) (lw-complexp point) (lw-complexp value)
                (rationalp gamma)
                (not (equal (lw-complex-add anchor point) (cons 0 0)))
                (not (equal (lw-complex-add (lw-complex-sub anchor (cons 1 0)) point) (cons 0 0))))
           (equal (lw-complex-mul (lw-complex-mul (lw-complex-add anchor point) (lw-complex-add (lw-complex-sub anchor (cons 1 0)) point)) (lw-complex-local-normalization anchor point value gamma))
                  (lw-complex-sub (lw-complex-add (lw-complex-add (lw-complex-sub anchor (cons 1 0)) point) (lw-complex-scale gamma (lw-complex-add anchor point))) value)))
  :hints (("Goal"
           :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-complex-local-normalization lw-complex-mul-subtract lw-complex-ring-rational lw-complex-scale-rational lw-complex-reciprocal-rational lw-mqn-one-inverse lw-mqn-two-inverses lw-mqn-subtraction lw-mqn-left-commutes lw-mqn-left-distributes lw-mqn-fold-constants lw-mqn-times-negative lw-mqn-negative-times lw-mqn-zero-times lw-mqn-minus-one lw-mqn-double-negative lw-mqn-add-cancel lw-mqn-double lw-mqn-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(defun lw-polynomial-mellin-quadratic (anchor coefficients)
  (lw-polynomial-multiply-linear anchor (cons 1 0)
    (lw-polynomial-multiply-linear (lw-complex-sub anchor (cons 1 0))
      (cons 1 0) coefficients)))

(defthm lw-polynomial-mellin-quadratic-valid
  (implies (and (lw-complexp anchor) (lw-complex-coefficientsp coefficients))
           (lw-complex-coefficientsp (lw-polynomial-mellin-quadratic anchor coefficients)))
  :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-polynomial-mellin-quadratic lw-polynomial-multiply-linear-valid lw-complex-ring-rational lw-mqn-left-commutes lw-mqn-left-distributes lw-mqn-fold-constants lw-mqn-times-negative lw-mqn-negative-times lw-mqn-zero-times lw-mqn-minus-one lw-mqn-double-negative lw-mqn-add-cancel lw-mqn-double lw-mqn-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-polynomial-mellin-quadratic-evaluation
  (implies (and (lw-complexp anchor) (lw-complexp point)
                (lw-complex-coefficientsp coefficients))
           (equal (lw-complex-polynomial (lw-polynomial-mellin-quadratic anchor coefficients) point 0)
                  (lw-complex-mul (lw-complex-mul (lw-complex-add anchor point) (lw-complex-add (lw-complex-sub anchor (cons 1 0)) point)) (lw-complex-polynomial coefficients point 0))))
  :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-polynomial-mellin-quadratic lw-polynomial-multiply-linear-valid lw-polynomial-multiply-linear-evaluation lw-complex-mul-associative lw-complex-mul-one lw-complex-ring-rational lw-complex-polynomial-rational lw-mqn-left-commutes lw-mqn-left-distributes lw-mqn-fold-constants lw-mqn-times-negative lw-mqn-negative-times lw-mqn-zero-times lw-mqn-minus-one lw-mqn-double-negative lw-mqn-add-cancel lw-mqn-double lw-mqn-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
                  :do-not-induct t)))

(defun lw-mellin-quadratic-cap (anchor radius)
  (* (lw-normalized-local-point-cap anchor radius) (lw-normalized-local-point-cap (lw-complex-sub anchor (cons 1 0)) radius)))

(local
 (defthm lw-mqn-linear-cap
   (implies (and (lw-complexp anchor) (lw-complex-diskp point radius))
            (lw-complex-diskp (lw-complex-add anchor point) (lw-normalized-local-point-cap anchor radius)))
   :hints (("Goal"
            :use ((:instance lw-complex-l1-bound (point anchor))
                  (:instance lw-complex-add-disk
                    (left anchor) (right point) (radius (lw-complex-l1 anchor)) (other-radius radius))
                  (:instance lw-complex-disk-data)
                  (:instance lw-complex-disk-enlarge
                    (point (lw-complex-add anchor point))
                    (radius (+ (lw-complex-l1 anchor) radius)) (cap (lw-normalized-local-point-cap anchor radius))))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-normalized-local-point-cap lw-mqn-left-commutes lw-mqn-left-distributes lw-mqn-fold-constants lw-mqn-times-negative lw-mqn-negative-times lw-mqn-zero-times lw-mqn-minus-one lw-mqn-double-negative lw-mqn-add-cancel lw-mqn-double lw-mqn-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))))

(defthm lw-mellin-quadratic-point-cap
  (implies (and (lw-complexp anchor) (lw-complex-diskp point radius))
           (lw-complex-diskp (lw-complex-mul (lw-complex-add anchor point) (lw-complex-add (lw-complex-sub anchor (cons 1 0)) point)) (lw-mellin-quadratic-cap anchor radius)))
  :hints (("Goal"
           :use ((:instance lw-complex-mul-disk (left (lw-complex-add anchor point)) (right (lw-complex-add (lw-complex-sub anchor (cons 1 0)) point))
                   (radius (lw-normalized-local-point-cap anchor radius)) (other-radius (lw-normalized-local-point-cap (lw-complex-sub anchor (cons 1 0)) radius))))
           :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-mellin-quadratic-cap lw-mqn-linear-cap lw-complex-ring-rational lw-mqn-left-commutes lw-mqn-left-distributes lw-mqn-fold-constants lw-mqn-times-negative lw-mqn-negative-times lw-mqn-zero-times lw-mqn-minus-one lw-mqn-double-negative lw-mqn-add-cancel lw-mqn-double lw-mqn-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
           :do-not-induct t)))

(defthm lw-polynomial-mellin-quadratic-normalization-error
  (implies (and (lw-complexp anchor) (not (equal anchor (cons 0 0)))
                (not (equal (lw-complex-sub anchor (cons 1 0)) (cons 0 0)))
                (rationalp radius) (<= 0 radius)
                (<= radius (* 1/4 (lw-complex-l1 anchor)))
                (<= radius (* 1/4 (lw-complex-l1 (lw-complex-sub anchor (cons 1 0)))))
                (lw-complex-diskp point radius)
                (lw-complex-coefficientsp coefficients)
                (rationalp log-cap) (<= 0 log-cap)
                (rationalp gamma) (<= (abs gamma) 2)
                (lw-complex-diskp (lw-complex-polynomial coefficients point 0) log-cap)
                (rationalp error) (< 0 error))
           (lw-complex-diskp
            (lw-complex-sub (lw-complex-sub (lw-complex-add (lw-complex-add (lw-complex-sub anchor (cons 1 0)) point) (lw-complex-scale gamma (lw-complex-add anchor point))) (lw-complex-polynomial coefficients point 0)) (lw-complex-polynomial (lw-polynomial-mellin-quadratic anchor (lw-normalized-local-polynomial anchor coefficients gamma error)) point 0))
            (* (lw-mellin-quadratic-cap anchor radius) (* (lw-normalized-local-inverse-cost anchor radius log-cap) error))))
  :hints (("Goal"
           :use (lw-normalized-local-point-data lw-normalized-local-polynomial-error
                 lw-mellin-quadratic-point-cap lw-normalized-local-polynomial-valid
                 (:instance lw-complex-local-normalization-times-quadratic (value (lw-complex-polynomial coefficients point 0)))
                 (:instance lw-complex-left-product-error
                   (factor (lw-complex-mul (lw-complex-add anchor point) (lw-complex-add (lw-complex-sub anchor (cons 1 0)) point))) (cap (lw-mellin-quadratic-cap anchor radius))
                   (a (lw-complex-local-normalization anchor point (lw-complex-polynomial coefficients point 0) gamma)) (b (lw-complex-polynomial (lw-normalized-local-polynomial anchor coefficients gamma error) point 0))
                   (error (* (lw-normalized-local-inverse-cost anchor radius log-cap) error))))
           :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-polynomial-mellin-quadratic-evaluation lw-complex-polynomial-rational lw-complex-local-normalization-rational lw-mqn-left-commutes lw-mqn-left-distributes lw-mqn-fold-constants lw-mqn-times-negative lw-mqn-negative-times lw-mqn-zero-times lw-mqn-minus-one lw-mqn-double-negative lw-mqn-add-cancel lw-mqn-double lw-mqn-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
