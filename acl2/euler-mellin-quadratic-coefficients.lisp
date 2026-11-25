(in-package "ACL2")

(include-book "mellin-quadratic-normalization")
(include-book "euler-normalized-polynomial")
(include-book "polynomial-cauchy-caps")
(include-book "polynomial-capped-coefficients")

; The affine numerator is (s-1)+gamma*s. Its terms above order one vanish.
(defun lw-mellin-linear-numerator (anchor gamma)
  (list (lw-complex-add (lw-complex-sub anchor (cons 1 0))
                        (lw-complex-scale gamma anchor))
        (cons (+ 1 gamma) 0)))

(defun lw-euler-mellin-quadratic-difference (rate height outer-radius anchor-error target error)
  (let ((numerator (lw-polynomial-subtract (lw-mellin-linear-numerator (cons rate height) (lw-euler-normalized-gamma rate height outer-radius anchor-error error)) (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error target (lw-euler-normalized-request rate height outer-radius anchor-error error))))
        (quadratic (lw-polynomial-mellin-quadratic (cons rate height) (lw-euler-normalized-polynomial rate height outer-radius anchor-error target error))))
    (lw-polynomial-disk-difference numerator quadratic (lw-euler-normalized-disk-radius rate height outer-radius anchor-error)
      (+ (len numerator) (len quadratic)))))

(local (defthm lw-emqc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-emqc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-emqc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-emqc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-emqc-times-negative (a b) (b a)))
                 :in-theory (disable lw-emqc-times-negative)))))

(local (defthm lw-emqc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-emqc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-emqc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-emqc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-emqc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-emqc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-emqc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))


(local (defthm lw-emqc-length-natural
         (natp (len coefficients))
         :rule-classes (:rewrite :type-prescription)))

(local
 (defthm lw-emqc-linear-valid
   (implies (and (lw-complexp anchor) (rationalp gamma))
            (and (lw-complex-coefficientsp (lw-mellin-linear-numerator anchor gamma))
                 (equal (len (lw-mellin-linear-numerator anchor gamma)) 2)))
   :hints (("Goal"
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-mellin-linear-numerator lw-complexp consp lw-complex-coefficientsp lw-complex-ring-rational lw-complex-scale-rational len lw-emqc-left-commutes lw-emqc-left-distributes lw-emqc-fold-constants lw-emqc-times-negative lw-emqc-negative-times lw-emqc-zero-times lw-emqc-minus-one lw-emqc-double-negative lw-emqc-add-cancel lw-emqc-double lw-emqc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))))

(local
 (defthm lw-emqc-linear-evaluation
   (implies (and (lw-complexp anchor) (lw-complexp point) (rationalp gamma))
            (equal (lw-complex-polynomial (lw-mellin-linear-numerator anchor gamma) point 0)
                   (lw-complex-add (lw-complex-add (lw-complex-sub anchor (cons 1 0)) point)
                                    (lw-complex-scale gamma (lw-complex-add anchor point)))))
   :hints (("Goal"
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-mellin-linear-numerator lw-complex-polynomial lw-complex-power lw-complexp consp endp lw-complex-mul lw-complex-scale lw-complex-add lw-complex-sub lw-emqc-left-commutes lw-emqc-left-distributes lw-emqc-fold-constants lw-emqc-times-negative lw-emqc-negative-times lw-emqc-zero-times lw-emqc-minus-one lw-emqc-double-negative lw-emqc-add-cancel lw-emqc-double lw-emqc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))))

(local
 (defthm lw-emqc-rational-pair
   (implies (and (rationalp real) (rationalp imag))
            (lw-complexp (cons real imag)))
   :hints (("Goal" :in-theory (union-theories '(lw-complexp car-cons cdr-cons consp) (theory 'minimal-theory))))))

(local
 (defthm lw-emqc-input-data
   (implies (and (lw-euler-value-clearance-check rate height anchor-error)
                (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
                (not (and (equal rate 1) (equal height 0)))
                (natp target) (rationalp error) (< 0 error))
            (and (lw-complexp (cons rate height)) (lw-complex-coefficientsp (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error target (lw-euler-normalized-request rate height outer-radius anchor-error error)))
                 (lw-complex-coefficientsp (lw-euler-normalized-polynomial rate height outer-radius anchor-error target error))
                 (lw-complex-coefficientsp (lw-polynomial-subtract (lw-mellin-linear-numerator (cons rate height) (lw-euler-normalized-gamma rate height outer-radius anchor-error error)) (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error target (lw-euler-normalized-request rate height outer-radius anchor-error error))))
                 (lw-complex-coefficientsp (lw-polynomial-mellin-quadratic (cons rate height) (lw-euler-normalized-polynomial rate height outer-radius anchor-error target error)))
                 (lw-complex-coefficientsp (lw-euler-mellin-quadratic-difference rate height outer-radius anchor-error target error))
                 (rationalp (lw-euler-normalized-disk-radius rate height outer-radius anchor-error)) (< 0 (lw-euler-normalized-disk-radius rate height outer-radius anchor-error))
                 (rationalp (lw-euler-normalized-gamma rate height outer-radius anchor-error error)) (<= (abs (lw-euler-normalized-gamma rate height outer-radius anchor-error error)) 2)))
   :hints (("Goal"
            :use (lw-euler-value-clearance-data lw-euler-normalized-disk-data lw-euler-normalized-request-data lw-euler-normalized-polynomial-valid
                  (:instance lw-euler-uniform-log-polynomial-valid (error (lw-euler-normalized-request rate height outer-radius anchor-error error))))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-emqc-rational-pair max lw-emqc-linear-valid lw-polynomial-mellin-quadratic-valid lw-polynomial-subtract-valid lw-polynomial-disk-difference-valid lw-euler-mellin-quadratic-difference lw-emqc-length-natural lw-emqc-left-commutes lw-emqc-left-distributes lw-emqc-fold-constants lw-emqc-times-negative lw-emqc-negative-times lw-emqc-zero-times lw-emqc-minus-one lw-emqc-double-negative lw-emqc-add-cancel lw-emqc-double lw-emqc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-emqc-point-comparison
   (implies (and (lw-euler-value-clearance-check rate height anchor-error)
                (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
                (not (and (equal rate 1) (equal height 0)))
                (natp target) (rationalp error) (< 0 error)
                 (lw-complex-diskp point (lw-euler-normalized-disk-radius rate height outer-radius anchor-error)))
            (lw-complex-diskp (lw-complex-sub (lw-complex-polynomial (lw-polynomial-subtract (lw-mellin-linear-numerator (cons rate height) (lw-euler-normalized-gamma rate height outer-radius anchor-error error)) (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error target (lw-euler-normalized-request rate height outer-radius anchor-error error))) point 0) (lw-complex-polynomial (lw-polynomial-mellin-quadratic (cons rate height) (lw-euler-normalized-polynomial rate height outer-radius anchor-error target error)) point 0)) (* (lw-mellin-quadratic-cap (cons rate height) (lw-euler-normalized-disk-radius rate height outer-radius anchor-error)) (* (lw-normalized-local-inverse-cost (cons rate height) (lw-euler-normalized-disk-radius rate height outer-radius anchor-error) (lw-euler-uniform-log-cap rate height outer-radius anchor-error)) (lw-euler-normalized-request rate height outer-radius anchor-error error)))))
   :hints (("Goal"
            :use (lw-emqc-input-data lw-euler-neighborhood-data lw-euler-normalized-disk-data lw-euler-normalized-request-data
                  (:instance lw-complex-disk-data (radius (lw-euler-normalized-disk-radius rate height outer-radius anchor-error)))
                  (:instance lw-complex-disk-enlarge
                    (radius (lw-euler-normalized-disk-radius rate height outer-radius anchor-error)) (cap (lw-euler-neighborhood-radius rate height outer-radius anchor-error)))
                  (:instance lw-complex-euler-uniform-log-polynomial-cap (error (lw-euler-normalized-request rate height outer-radius anchor-error error)))
                  (:instance lw-polynomial-mellin-quadratic-normalization-error
                    (anchor (cons rate height)) (radius (lw-euler-normalized-disk-radius rate height outer-radius anchor-error)) (coefficients (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error target (lw-euler-normalized-request rate height outer-radius anchor-error error)))
                    (gamma (lw-euler-normalized-gamma rate height outer-radius anchor-error error)) (log-cap (lw-euler-uniform-log-cap rate height outer-radius anchor-error)) (error (lw-euler-normalized-request rate height outer-radius anchor-error error))))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-euler-normalized-polynomial lw-emqc-linear-valid lw-emqc-linear-evaluation lw-polynomial-subtract-evaluation lw-emqc-left-commutes lw-emqc-left-distributes lw-emqc-fold-constants lw-emqc-times-negative lw-emqc-negative-times lw-emqc-zero-times lw-emqc-minus-one lw-emqc-double-negative lw-emqc-add-cancel lw-emqc-double lw-emqc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-emqc-difference-bound
   (implies (and (lw-euler-value-clearance-check rate height anchor-error)
                (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
                (not (and (equal rate 1) (equal height 0)))
                (natp target) (rationalp error) (< 0 error) (lw-complex-diskp point 1))
            (lw-complex-diskp (lw-complex-polynomial (lw-euler-mellin-quadratic-difference rate height outer-radius anchor-error target error) point 0) (* (lw-mellin-quadratic-cap (cons rate height) (lw-euler-normalized-disk-radius rate height outer-radius anchor-error)) (* (lw-normalized-local-inverse-cost (cons rate height) (lw-euler-normalized-disk-radius rate height outer-radius anchor-error) (lw-euler-uniform-log-cap rate height outer-radius anchor-error)) (lw-euler-normalized-request rate height outer-radius anchor-error error)))))
   :hints (("Goal"
            :use (lw-emqc-input-data
                  (:instance lw-complex-disk-data (radius 1))
                  (:instance lw-complex-scale-disk (factor (lw-euler-normalized-disk-radius rate height outer-radius anchor-error)) (radius 1))
                  (:instance lw-emqc-point-comparison (point (lw-complex-scale (lw-euler-normalized-disk-radius rate height outer-radius anchor-error) point)))
                  (:instance lw-polynomial-disk-difference-evaluation
                    (left (lw-polynomial-subtract (lw-mellin-linear-numerator (cons rate height) (lw-euler-normalized-gamma rate height outer-radius anchor-error error)) (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error target (lw-euler-normalized-request rate height outer-radius anchor-error error)))) (right (lw-polynomial-mellin-quadratic (cons rate height) (lw-euler-normalized-polynomial rate height outer-radius anchor-error target error))) (radius (lw-euler-normalized-disk-radius rate height outer-radius anchor-error))
                    (count (+ (len (lw-polynomial-subtract (lw-mellin-linear-numerator (cons rate height) (lw-euler-normalized-gamma rate height outer-radius anchor-error error)) (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error target (lw-euler-normalized-request rate height outer-radius anchor-error error)))) (len (lw-polynomial-mellin-quadratic (cons rate height) (lw-euler-normalized-polynomial rate height outer-radius anchor-error target error)))))))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-euler-mellin-quadratic-difference lw-emqc-length-natural abs lw-emqc-left-commutes lw-emqc-left-distributes lw-emqc-fold-constants lw-emqc-times-negative lw-emqc-negative-times lw-emqc-zero-times lw-emqc-minus-one lw-emqc-double-negative lw-emqc-add-cancel lw-emqc-double lw-emqc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-emqc-samples-pass
   (implies (and (lw-euler-value-clearance-check rate height anchor-error)
                (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
                (not (and (equal rate 1) (equal height 0)))
                (natp target) (rationalp error) (< 0 error) (natp degree) (natp count))
            (lw-cauchy-boundary-check (lw-euler-mellin-quadratic-difference rate height outer-radius anchor-error target error) (lw-cauchy-orbit-rotation degree) 0 count (* (lw-mellin-quadratic-cap (cons rate height) (lw-euler-normalized-disk-radius rate height outer-radius anchor-error)) (* (lw-normalized-local-inverse-cost (cons rate height) (lw-euler-normalized-disk-radius rate height outer-radius anchor-error) (lw-euler-uniform-log-cap rate height outer-radius anchor-error)) (lw-euler-normalized-request rate height outer-radius anchor-error error)))))
   :hints (("Goal" :induct (lw-cauchy-boundary-check (lw-euler-mellin-quadratic-difference rate height outer-radius anchor-error target error) (lw-cauchy-orbit-rotation degree) 0 count (* (lw-mellin-quadratic-cap (cons rate height) (lw-euler-normalized-disk-radius rate height outer-radius anchor-error)) (* (lw-normalized-local-inverse-cost (cons rate height) (lw-euler-normalized-disk-radius rate height outer-radius anchor-error) (lw-euler-uniform-log-cap rate height outer-radius anchor-error)) (lw-euler-normalized-request rate height outer-radius anchor-error error))))
                   :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-cauchy-boundary-check lw-cauchy-orbit-data lw-complex-unit-power lw-emqc-left-commutes lw-emqc-left-distributes lw-emqc-fold-constants lw-emqc-times-negative lw-emqc-negative-times lw-emqc-zero-times lw-emqc-minus-one lw-emqc-double-negative lw-emqc-add-cancel lw-emqc-double lw-emqc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
                   :do-not '(generalize fertilize))
           (and stable-under-simplificationp
                '(:use ((:instance lw-emqc-difference-bound
                          (point (lw-complex-power (lw-cauchy-orbit-rotation degree) (- count 1)))))
                  :do-not-induct t)))
   :rule-classes nil))

(local
 (defthm lw-emqc-scaled-error
   (implies (and (lw-euler-value-clearance-check rate height anchor-error)
                (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
                (not (and (equal rate 1) (equal height 0)))
                (natp target) (rationalp error) (< 0 error) (natp index))
            (lw-complex-diskp
             (lw-complex-sub (lw-complex-scale (lw-rational-power (lw-euler-normalized-disk-radius rate height outer-radius anchor-error) index) (lw-complex-coefficient-at (lw-polynomial-subtract (lw-mellin-linear-numerator (cons rate height) (lw-euler-normalized-gamma rate height outer-radius anchor-error error)) (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error target (lw-euler-normalized-request rate height outer-radius anchor-error error))) index 0))
                             (lw-complex-scale (lw-rational-power (lw-euler-normalized-disk-radius rate height outer-radius anchor-error) index) (lw-complex-coefficient-at (lw-polynomial-mellin-quadratic (cons rate height) (lw-euler-normalized-polynomial rate height outer-radius anchor-error target error)) index 0))) (* (lw-mellin-quadratic-cap (cons rate height) (lw-euler-normalized-disk-radius rate height outer-radius anchor-error)) (* (lw-normalized-local-inverse-cost (cons rate height) (lw-euler-normalized-disk-radius rate height outer-radius anchor-error) (lw-euler-uniform-log-cap rate height outer-radius anchor-error)) (lw-euler-normalized-request rate height outer-radius anchor-error error)))))
   :hints (("Goal"
            :use (lw-emqc-input-data
                  (:instance lw-emqc-difference-bound (point (cons 1 0)))
                  (:instance lw-complex-disk-data (point (lw-complex-polynomial (lw-euler-mellin-quadratic-difference rate height outer-radius anchor-error target error) (cons 1 0) 0))
                    (radius (* (lw-mellin-quadratic-cap (cons rate height) (lw-euler-normalized-disk-radius rate height outer-radius anchor-error)) (* (lw-normalized-local-inverse-cost (cons rate height) (lw-euler-normalized-disk-radius rate height outer-radius anchor-error) (lw-euler-uniform-log-cap rate height outer-radius anchor-error)) (lw-euler-normalized-request rate height outer-radius anchor-error error)))))
                  (:instance lw-polynomial-cauchy-cap-data (coefficients (lw-euler-mellin-quadratic-difference rate height outer-radius anchor-error target error)) (cap (* (lw-mellin-quadratic-cap (cons rate height) (lw-euler-normalized-disk-radius rate height outer-radius anchor-error)) (* (lw-normalized-local-inverse-cost (cons rate height) (lw-euler-normalized-disk-radius rate height outer-radius anchor-error) (lw-euler-uniform-log-cap rate height outer-radius anchor-error)) (lw-euler-normalized-request rate height outer-radius anchor-error error)))))
                  (:instance lw-emqc-samples-pass (degree (len (lw-euler-mellin-quadratic-difference rate height outer-radius anchor-error target error))) (count (lw-cauchy-coefficient-count (lw-euler-mellin-quadratic-difference rate height outer-radius anchor-error target error) (len (lw-euler-mellin-quadratic-difference rate height outer-radius anchor-error target error)) (lw-polynomial-cap-test-error (lw-euler-mellin-quadratic-difference rate height outer-radius anchor-error target error) (* (lw-mellin-quadratic-cap (cons rate height) (lw-euler-normalized-disk-radius rate height outer-radius anchor-error)) (* (lw-normalized-local-inverse-cost (cons rate height) (lw-euler-normalized-disk-radius rate height outer-radius anchor-error) (lw-euler-uniform-log-cap rate height outer-radius anchor-error)) (lw-euler-normalized-request rate height outer-radius anchor-error error)))))))
                  (:instance lw-polynomial-cauchy-cap-check-sound (coefficients (lw-euler-mellin-quadratic-difference rate height outer-radius anchor-error target error)) (cap (* (lw-mellin-quadratic-cap (cons rate height) (lw-euler-normalized-disk-radius rate height outer-radius anchor-error)) (* (lw-normalized-local-inverse-cost (cons rate height) (lw-euler-normalized-disk-radius rate height outer-radius anchor-error) (lw-euler-uniform-log-cap rate height outer-radius anchor-error)) (lw-euler-normalized-request rate height outer-radius anchor-error error)))))
                  (:instance lw-polynomial-disk-difference-capped-coefficient
                    (left (lw-polynomial-subtract (lw-mellin-linear-numerator (cons rate height) (lw-euler-normalized-gamma rate height outer-radius anchor-error error)) (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error target (lw-euler-normalized-request rate height outer-radius anchor-error error)))) (right (lw-polynomial-mellin-quadratic (cons rate height) (lw-euler-normalized-polynomial rate height outer-radius anchor-error target error))) (radius (lw-euler-normalized-disk-radius rate height outer-radius anchor-error))
                    (count (+ (len (lw-polynomial-subtract (lw-mellin-linear-numerator (cons rate height) (lw-euler-normalized-gamma rate height outer-radius anchor-error error)) (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error target (lw-euler-normalized-request rate height outer-radius anchor-error error)))) (len (lw-polynomial-mellin-quadratic (cons rate height) (lw-euler-normalized-polynomial rate height outer-radius anchor-error target error))))) (cap (* (lw-mellin-quadratic-cap (cons rate height) (lw-euler-normalized-disk-radius rate height outer-radius anchor-error)) (* (lw-normalized-local-inverse-cost (cons rate height) (lw-euler-normalized-disk-radius rate height outer-radius anchor-error) (lw-euler-uniform-log-cap rate height outer-radius anchor-error)) (lw-euler-normalized-request rate height outer-radius anchor-error error))))))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) (:executable-counterpart lw-complex-diskp) lw-euler-mellin-quadratic-difference lw-polynomial-cauchy-cap-check lw-emqc-length-natural lw-polynomial-rescale-coefficient lw-emqc-left-commutes lw-emqc-left-distributes lw-emqc-fold-constants lw-emqc-times-negative lw-emqc-negative-times lw-emqc-zero-times lw-emqc-minus-one lw-emqc-double-negative lw-emqc-add-cancel lw-emqc-double lw-emqc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-emqc-scale-coefficient
   (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp factor) (natp target) (natp offset))
            (equal (lw-complex-coefficient-at (lw-polynomial-multiply-coefficients factor coefficients) target offset)
                   (lw-complex-mul factor (lw-complex-coefficient-at coefficients target offset))))
   :hints (("Goal" :induct (lw-complex-coefficient-at coefficients target offset)
                   :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) (:executable-counterpart lw-complex-diskp) lw-complex-coefficientsp lw-complex-coefficient-at lw-polynomial-multiply-coefficients lw-polynomial-multiply-coefficients-valid lw-complex-coefficient-at-rational lw-complex-mul-zero lw-complex-add-zero lw-complex-mul-distribute endp lw-emqc-left-commutes lw-emqc-left-distributes lw-emqc-fold-constants lw-emqc-times-negative lw-emqc-negative-times lw-emqc-zero-times lw-emqc-minus-one lw-emqc-double-negative lw-emqc-add-cancel lw-emqc-double lw-emqc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
                   :do-not '(generalize fertilize)))))

(local
 (defthm lw-emqc-minus-one-multiplier
   (implies (lw-complexp point)
            (equal (lw-complex-mul (cons -1 0) point) (lw-complex-scale -1 point)))
   :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) (:executable-counterpart lw-complex-diskp) lw-complexp lw-complex-mul lw-complex-scale consp lw-emqc-left-commutes lw-emqc-left-distributes lw-emqc-fold-constants lw-emqc-times-negative lw-emqc-negative-times lw-emqc-zero-times lw-emqc-minus-one lw-emqc-double-negative lw-emqc-add-cancel lw-emqc-double lw-emqc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local
 (defthm lw-emqc-higher-numerator
   (implies (and (lw-euler-value-clearance-check rate height anchor-error)
                (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
                (not (and (equal rate 1) (equal height 0)))
                (natp target) (rationalp error) (< 0 error) (natp index) (<= 2 index))
            (equal (lw-complex-coefficient-at (lw-polynomial-subtract (lw-mellin-linear-numerator (cons rate height) (lw-euler-normalized-gamma rate height outer-radius anchor-error error)) (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error target (lw-euler-normalized-request rate height outer-radius anchor-error error))) index 0) (lw-complex-scale -1 (lw-complex-coefficient-at (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error target (lw-euler-normalized-request rate height outer-radius anchor-error error)) index 0))))
   :hints (("Goal"
            :use (lw-emqc-input-data
                  (:instance lw-complex-coefficient-at-outside
                    (coefficients (lw-mellin-linear-numerator (cons rate height) (lw-euler-normalized-gamma rate height outer-radius anchor-error error)))
                    (target index) (offset 0)))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) (:executable-counterpart lw-complex-diskp) lw-polynomial-subtract lw-emqc-linear-valid lw-polynomial-add-coefficient lw-polynomial-multiply-coefficients-valid lw-emqc-scale-coefficient lw-complex-coefficient-at-rational lw-emqc-minus-one-multiplier lw-complex-scale-rational lw-complex-add-zero lw-emqc-left-commutes lw-emqc-left-distributes lw-emqc-fold-constants lw-emqc-times-negative lw-emqc-negative-times lw-emqc-zero-times lw-emqc-minus-one lw-emqc-double-negative lw-emqc-add-cancel lw-emqc-double lw-emqc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-emqc-unscale-disk
   (implies (and (lw-complexp point) (rationalp factor) (< 0 factor)
                 (lw-complex-diskp (lw-complex-scale factor point) cap))
            (lw-complex-diskp point (* cap (/ factor))))
   :hints (("Goal"
            :use ((:instance lw-complex-scale-disk (point (lw-complex-scale factor point))
                    (radius cap) (factor (/ factor)))
                  (:instance lw-complex-scale-compose (left (/ factor)) (right factor))
                  (:instance inverse-of-* (x factor)))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) (:executable-counterpart lw-complex-diskp) abs lw-complex-scale-one lw-reciprocal-positive lw-emqc-left-commutes lw-emqc-left-distributes lw-emqc-fold-constants lw-emqc-times-negative lw-emqc-negative-times lw-emqc-zero-times lw-emqc-minus-one lw-emqc-double-negative lw-emqc-add-cancel lw-emqc-double lw-emqc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-euler-mellin-quadratic-coefficient-error
  (implies (and (lw-euler-value-clearance-check rate height anchor-error)
                (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
                (not (and (equal rate 1) (equal height 0)))
                (natp target) (rationalp error) (< 0 error) (natp index) (<= 2 index))
           (lw-complex-diskp
            (lw-complex-sub (lw-complex-scale -1 (lw-complex-coefficient-at (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error target (lw-euler-normalized-request rate height outer-radius anchor-error error)) index 0)) (lw-complex-coefficient-at (lw-polynomial-mellin-quadratic (cons rate height) (lw-euler-normalized-polynomial rate height outer-radius anchor-error target error)) index 0))
            (* (* (lw-mellin-quadratic-cap (cons rate height) (lw-euler-normalized-disk-radius rate height outer-radius anchor-error)) (* (lw-normalized-local-inverse-cost (cons rate height) (lw-euler-normalized-disk-radius rate height outer-radius anchor-error) (lw-euler-uniform-log-cap rate height outer-radius anchor-error)) (lw-euler-normalized-request rate height outer-radius anchor-error error))) (/ (lw-rational-power (lw-euler-normalized-disk-radius rate height outer-radius anchor-error) index)))))
  :hints (("Goal"
           :use (lw-emqc-input-data lw-emqc-scaled-error lw-emqc-higher-numerator
                 (:instance lw-rational-power-positive (base (lw-euler-normalized-disk-radius rate height outer-radius anchor-error)) (exponent index))
                 (:instance lw-emqc-unscale-disk (factor (lw-rational-power (lw-euler-normalized-disk-radius rate height outer-radius anchor-error) index)) (cap (* (lw-mellin-quadratic-cap (cons rate height) (lw-euler-normalized-disk-radius rate height outer-radius anchor-error)) (* (lw-normalized-local-inverse-cost (cons rate height) (lw-euler-normalized-disk-radius rate height outer-radius anchor-error) (lw-euler-uniform-log-cap rate height outer-radius anchor-error)) (lw-euler-normalized-request rate height outer-radius anchor-error error))))
                   (point (lw-complex-sub (lw-complex-scale -1 (lw-complex-coefficient-at (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error target (lw-euler-normalized-request rate height outer-radius anchor-error error)) index 0)) (lw-complex-coefficient-at (lw-polynomial-mellin-quadratic (cons rate height) (lw-euler-normalized-polynomial rate height outer-radius anchor-error target error)) index 0)))))
           :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) (:executable-counterpart lw-complex-diskp) lw-complex-sub-scales lw-rational-power-rational lw-complex-coefficient-at-rational lw-complex-scale-rational lw-complex-ring-rational lw-emqc-left-commutes lw-emqc-left-distributes lw-emqc-fold-constants lw-emqc-times-negative lw-emqc-negative-times lw-emqc-zero-times lw-emqc-minus-one lw-emqc-double-negative lw-emqc-add-cancel lw-emqc-double lw-emqc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
