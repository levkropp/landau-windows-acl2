(in-package "ACL2")

(include-book "euler-mellin-quadratic-coefficients")
(include-book "mellin-quadratic-coefficient-formula")
(include-book "euler-mellin-moments")

(defun lw-euler-mellin-quadratic-coefficient-value (rate height outer-radius anchor-error index coefficient-error)
  (lw-pole-quadratic-coefficient (cons rate height) (lw-complex-euler-mellin-coefficient-value rate height outer-radius anchor-error (+ 2 index) coefficient-error) (lw-complex-euler-mellin-coefficient-value rate height outer-radius anchor-error (+ 1 index) coefficient-error) (lw-complex-euler-mellin-coefficient-value rate height outer-radius anchor-error index coefficient-error)))

(defun lw-euler-mellin-quadratic-log-model (rate height outer-radius anchor-error target index model-error)
  (lw-complex-scale (lw-rational-power -1 index) (lw-complex-coefficient-at (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error target (lw-euler-normalized-request rate height outer-radius anchor-error model-error)) index 0)))

(defun lw-euler-mellin-quadratic-transport-error (rate height outer-radius anchor-error index coefficient-error model-error)
  (+ (* 1/2 coefficient-error) (* 1/2 model-error (/ (lw-rational-power (lw-euler-local-normalized-radius rate height outer-radius anchor-error) index)))))

(defun lw-euler-mellin-quadratic-log-error (rate height outer-radius anchor-error index coefficient-error model-error)
  (+ (+ (* (lw-complex-l1 (lw-zeta-residue-denominator (cons rate height))) (lw-euler-mellin-quadratic-transport-error rate height outer-radius anchor-error (+ 2 index) coefficient-error model-error))
                   (* (lw-complex-l1 (lw-complex-sub (cons 1 0) (lw-complex-scale 2 (cons rate height)))) (lw-euler-mellin-quadratic-transport-error rate height outer-radius anchor-error (+ 1 index) coefficient-error model-error))
                   (lw-euler-mellin-quadratic-transport-error rate height outer-radius anchor-error index coefficient-error model-error)) (* (lw-mellin-quadratic-cap (cons rate height) (lw-euler-normalized-disk-radius rate height outer-radius anchor-error))
                 (* (lw-normalized-local-inverse-cost (cons rate height) (lw-euler-normalized-disk-radius rate height outer-radius anchor-error)
                      (lw-euler-uniform-log-cap rate height outer-radius anchor-error)) (lw-euler-normalized-request rate height outer-radius anchor-error model-error))
                 (/ (lw-rational-power (lw-euler-normalized-disk-radius rate height outer-radius anchor-error) (+ 2 index))))))

(local (defthm lw-emqm-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-emqm-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-emqm-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-emqm-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-emqm-times-negative (a b) (b a)))
                 :in-theory (disable lw-emqm-times-negative)))))

(local (defthm lw-emqm-zero-times (equal (* 0 a) 0)))

(local (defthm lw-emqm-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-emqm-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-emqm-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-emqm-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-emqm-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-emqm-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))


(local
 (defthm lw-emqm-quadratic-subtraction
   (implies (and (lw-complexp center) (lw-complexp a) (lw-complexp b) (lw-complexp c)
                 (lw-complexp x) (lw-complexp y) (lw-complexp z))
            (equal (lw-complex-sub (lw-pole-quadratic-coefficient center a b c)
                                   (lw-pole-quadratic-coefficient center x y z))
                   (lw-pole-quadratic-coefficient center (lw-complex-sub a x)
                                                  (lw-complex-sub b y) (lw-complex-sub c z))))
   :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-pole-quadratic-coefficient lw-complex-sub-add lw-complex-ring-rational lw-zeta-residue-denominator-rational lw-complex-scale-rational lw-complex-mul-subtract lw-emqm-left-commutes lw-emqm-left-distributes lw-emqm-fold-constants lw-emqm-times-negative lw-emqm-negative-times lw-emqm-zero-times lw-emqm-minus-one lw-emqm-double-negative lw-emqm-add-cancel lw-emqm-double lw-emqm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
                   :do-not-induct t))))

(defthm lw-pole-quadratic-coefficient-disk-bound
  (implies (and (lw-complexp center)
                (lw-complex-diskp a left-error) (lw-complex-diskp b middle-error)
                (lw-complex-diskp c right-error))
           (lw-complex-diskp
            (lw-pole-quadratic-coefficient center a b c)
            (+ (* (lw-complex-l1 (lw-zeta-residue-denominator center)) left-error)
               (* (lw-complex-l1 (lw-complex-sub (cons 1 0) (lw-complex-scale 2 center))) middle-error)
               right-error)))
  :hints (("Goal"
           :use ((:instance lw-complex-l1-bound (point (lw-zeta-residue-denominator center)))
                 (:instance lw-complex-l1-bound (point (lw-complex-sub (cons 1 0) (lw-complex-scale 2 center))))
                 (:instance lw-complex-mul-disk (left (lw-zeta-residue-denominator center)) (right a) (radius (lw-complex-l1 (lw-zeta-residue-denominator center))) (other-radius left-error))
                 (:instance lw-complex-mul-disk (left (lw-complex-sub (cons 1 0) (lw-complex-scale 2 center))) (right b) (radius (lw-complex-l1 (lw-complex-sub (cons 1 0) (lw-complex-scale 2 center)))) (other-radius middle-error))
                 (:instance lw-complex-add-disk (left (lw-complex-mul (lw-complex-sub (cons 1 0) (lw-complex-scale 2 center)) b)) (right c)
                   (radius (* (lw-complex-l1 (lw-complex-sub (cons 1 0) (lw-complex-scale 2 center))) middle-error)) (other-radius right-error))
                 (:instance lw-complex-add-disk (left (lw-complex-mul (lw-zeta-residue-denominator center) a))
                   (right (lw-complex-add (lw-complex-mul (lw-complex-sub (cons 1 0) (lw-complex-scale 2 center)) b) c))
                   (radius (* (lw-complex-l1 (lw-zeta-residue-denominator center)) left-error))
                   (other-radius (+ (* (lw-complex-l1 (lw-complex-sub (cons 1 0) (lw-complex-scale 2 center))) middle-error) right-error))))
           :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-pole-quadratic-coefficient lw-complex-ring-rational lw-zeta-residue-denominator-rational lw-complex-scale-rational lw-emqm-left-commutes lw-emqm-left-distributes lw-emqm-fold-constants lw-emqm-times-negative lw-emqm-negative-times lw-emqm-zero-times lw-emqm-minus-one lw-emqm-double-negative lw-emqm-add-cancel lw-emqm-double lw-emqm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm lw-emqm-coefficient-reflection-error
   (implies (and (lw-euler-value-clearance-check rate height anchor-error)
                (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
                (< 3 rate) (natp target) (natp index)
                (rationalp coefficient-error) (< 0 coefficient-error)
                (rationalp model-error) (< 0 model-error))
            (and (lw-complexp (lw-complex-euler-mellin-coefficient-value rate height outer-radius anchor-error index coefficient-error)) (lw-complexp (lw-complex-scale (lw-rational-power -1 index) (lw-complex-coefficient-at (lw-euler-normalized-polynomial rate height outer-radius anchor-error target model-error) index 0)))
                 (lw-complex-diskp (lw-complex-sub (lw-complex-euler-mellin-coefficient-value rate height outer-radius anchor-error index coefficient-error) (lw-complex-scale (lw-rational-power -1 index) (lw-complex-coefficient-at (lw-euler-normalized-polynomial rate height outer-radius anchor-error target model-error) index 0))) (lw-euler-mellin-quadratic-transport-error rate height outer-radius anchor-error index coefficient-error model-error))))
   :hints (("Goal"
            :use (lw-euler-mellin-sign-data
                  (:instance lw-euler-local-normalized-polynomial-valid (error model-error))
                  (:instance lw-complex-euler-mellin-coefficient-rational (error coefficient-error))
                  (:instance lw-complex-euler-normalized-physical-coefficient-rational (error coefficient-error))
                  (:instance lw-complex-euler-normalized-physical-polynomial-comparison (polynomial-error model-error))
                  (:instance lw-complex-scale-disk
                    (point (lw-complex-sub (lw-complex-euler-normalized-physical-coefficient-value rate height outer-radius anchor-error index coefficient-error) (lw-complex-coefficient-at (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error target model-error) index 0)))
                    (factor (lw-rational-power -1 index)) (radius (lw-euler-mellin-quadratic-transport-error rate height outer-radius anchor-error index coefficient-error model-error))))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-euler-mellin-quadratic-transport-error lw-complex-euler-mellin-coefficient-value lw-euler-local-normalized-polynomial lw-complex-coefficient-at-rational lw-complex-sub-scales lw-complex-scale-rational lw-rational-power-rational lw-emqm-left-commutes lw-emqm-left-distributes lw-emqm-fold-constants lw-emqm-times-negative lw-emqm-negative-times lw-emqm-zero-times lw-emqm-minus-one lw-emqm-double-negative lw-emqm-add-cancel lw-emqm-double lw-emqm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-emqm-quadratic-typed
   (implies (and (lw-complexp center) (lw-complexp a) (lw-complexp b) (lw-complexp c))
            (lw-complexp (lw-pole-quadratic-coefficient center a b c)))
   :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-pole-quadratic-coefficient lw-complex-ring-rational lw-zeta-residue-denominator-rational lw-complex-scale-rational lw-emqm-left-commutes lw-emqm-left-distributes lw-emqm-fold-constants lw-emqm-times-negative lw-emqm-negative-times lw-emqm-zero-times lw-emqm-minus-one lw-emqm-double-negative lw-emqm-add-cancel lw-emqm-double lw-emqm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local
 (defthm lw-emqm-center-typed
   (implies (and (rationalp rate) (rationalp height))
            (lw-complexp (cons rate height)))
   :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-complexp consp lw-emqm-left-commutes lw-emqm-left-distributes lw-emqm-fold-constants lw-emqm-times-negative lw-emqm-negative-times lw-emqm-zero-times lw-emqm-minus-one lw-emqm-double-negative lw-emqm-add-cancel lw-emqm-double lw-emqm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local
 (defthm lw-emqm-quadratic-model-error
   (implies (and (lw-euler-value-clearance-check rate height anchor-error)
                (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
                (< 3 rate) (natp target) (natp index)
                (rationalp coefficient-error) (< 0 coefficient-error)
                (rationalp model-error) (< 0 model-error))
            (and (lw-complexp (lw-euler-mellin-quadratic-coefficient-value rate height outer-radius anchor-error index coefficient-error))
                 (lw-complexp (lw-pole-quadratic-coefficient (cons rate height) (lw-complex-scale (lw-rational-power -1 (+ 2 index)) (lw-complex-coefficient-at (lw-euler-normalized-polynomial rate height outer-radius anchor-error target model-error) (+ 2 index) 0)) (lw-complex-scale (lw-rational-power -1 (+ 1 index)) (lw-complex-coefficient-at (lw-euler-normalized-polynomial rate height outer-radius anchor-error target model-error) (+ 1 index) 0)) (lw-complex-scale (lw-rational-power -1 index) (lw-complex-coefficient-at (lw-euler-normalized-polynomial rate height outer-radius anchor-error target model-error) index 0))))
                 (lw-complex-diskp (lw-complex-sub (lw-euler-mellin-quadratic-coefficient-value rate height outer-radius anchor-error index coefficient-error) (lw-pole-quadratic-coefficient (cons rate height) (lw-complex-scale (lw-rational-power -1 (+ 2 index)) (lw-complex-coefficient-at (lw-euler-normalized-polynomial rate height outer-radius anchor-error target model-error) (+ 2 index) 0)) (lw-complex-scale (lw-rational-power -1 (+ 1 index)) (lw-complex-coefficient-at (lw-euler-normalized-polynomial rate height outer-radius anchor-error target model-error) (+ 1 index) 0)) (lw-complex-scale (lw-rational-power -1 index) (lw-complex-coefficient-at (lw-euler-normalized-polynomial rate height outer-radius anchor-error target model-error) index 0))))
                  (+ (* (lw-complex-l1 (lw-zeta-residue-denominator (cons rate height))) (lw-euler-mellin-quadratic-transport-error rate height outer-radius anchor-error (+ 2 index) coefficient-error model-error))
                     (* (lw-complex-l1 (lw-complex-sub (cons 1 0) (lw-complex-scale 2 (cons rate height)))) (lw-euler-mellin-quadratic-transport-error rate height outer-radius anchor-error (+ 1 index) coefficient-error model-error))
                     (lw-euler-mellin-quadratic-transport-error rate height outer-radius anchor-error index coefficient-error model-error)))))
   :hints (("Goal"
            :use (lw-euler-value-clearance-data
                  lw-emqm-coefficient-reflection-error
                  (:instance lw-emqm-coefficient-reflection-error (index (+ 1 index)))
                  (:instance lw-emqm-coefficient-reflection-error (index (+ 2 index)))
                  (:instance lw-pole-quadratic-coefficient-disk-bound
                    (center (cons rate height))
                    (a (lw-complex-sub (lw-complex-euler-mellin-coefficient-value rate height outer-radius anchor-error (+ 2 index) coefficient-error) (lw-complex-scale (lw-rational-power -1 (+ 2 index)) (lw-complex-coefficient-at (lw-euler-normalized-polynomial rate height outer-radius anchor-error target model-error) (+ 2 index) 0))))
                    (b (lw-complex-sub (lw-complex-euler-mellin-coefficient-value rate height outer-radius anchor-error (+ 1 index) coefficient-error) (lw-complex-scale (lw-rational-power -1 (+ 1 index)) (lw-complex-coefficient-at (lw-euler-normalized-polynomial rate height outer-radius anchor-error target model-error) (+ 1 index) 0))))
                    (c (lw-complex-sub (lw-complex-euler-mellin-coefficient-value rate height outer-radius anchor-error index coefficient-error) (lw-complex-scale (lw-rational-power -1 index) (lw-complex-coefficient-at (lw-euler-normalized-polynomial rate height outer-radius anchor-error target model-error) index 0))))
                    (left-error (lw-euler-mellin-quadratic-transport-error rate height outer-radius anchor-error (+ 2 index) coefficient-error model-error))
                    (middle-error (lw-euler-mellin-quadratic-transport-error rate height outer-radius anchor-error (+ 1 index) coefficient-error model-error)) (right-error (lw-euler-mellin-quadratic-transport-error rate height outer-radius anchor-error index coefficient-error model-error))))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-euler-mellin-quadratic-coefficient-value lw-emqm-quadratic-subtraction lw-emqm-quadratic-typed lw-emqm-center-typed lw-complex-ring-rational lw-emqm-left-commutes lw-emqm-left-distributes lw-emqm-fold-constants lw-emqm-times-negative lw-emqm-negative-times lw-emqm-zero-times lw-emqm-minus-one lw-emqm-double-negative lw-emqm-add-cancel lw-emqm-double lw-emqm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-emqm-reflect-negative
   (implies (and (rationalp sign) (lw-complexp point))
            (equal (lw-complex-scale -1 (lw-complex-scale sign point))
                   (lw-complex-scale sign (lw-complex-scale -1 point))))
   :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-complex-scale-compose lw-emqm-left-commutes lw-emqm-left-distributes lw-emqm-fold-constants lw-emqm-times-negative lw-emqm-negative-times lw-emqm-zero-times lw-emqm-minus-one lw-emqm-double-negative lw-emqm-add-cancel lw-emqm-double lw-emqm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local
 (defthm lw-emqm-raw-reflected-error
   (implies (and (lw-euler-value-clearance-check rate height anchor-error)
                (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
                (< 3 rate) (natp target) (natp index)
                (rationalp coefficient-error) (< 0 coefficient-error)
                (rationalp model-error) (< 0 model-error))
            (and (lw-complexp (lw-complex-scale -1 (lw-euler-mellin-quadratic-log-model rate height outer-radius anchor-error target (+ 2 index) model-error)))
                 (lw-complex-diskp (lw-complex-sub (lw-complex-scale -1 (lw-euler-mellin-quadratic-log-model rate height outer-radius anchor-error target (+ 2 index) model-error)) (lw-pole-quadratic-coefficient (cons rate height) (lw-complex-scale (lw-rational-power -1 (+ 2 index)) (lw-complex-coefficient-at (lw-euler-normalized-polynomial rate height outer-radius anchor-error target model-error) (+ 2 index) 0)) (lw-complex-scale (lw-rational-power -1 (+ 1 index)) (lw-complex-coefficient-at (lw-euler-normalized-polynomial rate height outer-radius anchor-error target model-error) (+ 1 index) 0)) (lw-complex-scale (lw-rational-power -1 index) (lw-complex-coefficient-at (lw-euler-normalized-polynomial rate height outer-radius anchor-error target model-error) index 0)))) (* (lw-mellin-quadratic-cap (cons rate height) (lw-euler-normalized-disk-radius rate height outer-radius anchor-error))
                 (* (lw-normalized-local-inverse-cost (cons rate height) (lw-euler-normalized-disk-radius rate height outer-radius anchor-error)
                      (lw-euler-uniform-log-cap rate height outer-radius anchor-error)) (lw-euler-normalized-request rate height outer-radius anchor-error model-error))
                 (/ (lw-rational-power (lw-euler-normalized-disk-radius rate height outer-radius anchor-error) (+ 2 index)))))))
   :hints (("Goal"
            :use (lw-euler-value-clearance-data
                  (:instance lw-euler-normalized-request-data (error model-error))
                  (:instance lw-euler-normalized-polynomial-valid (error model-error))
                  (:instance lw-euler-uniform-log-polynomial-valid (error (lw-euler-normalized-request rate height outer-radius anchor-error model-error)))
                  (:instance lw-euler-mellin-sign-data (index (+ 2 index)))
                  (:instance lw-euler-mellin-quadratic-coefficient-error (index (+ 2 index)) (error model-error))
                  (:instance lw-polynomial-mellin-quadratic-reflected-coefficient (anchor (cons rate height)) (coefficients (lw-euler-normalized-polynomial rate height outer-radius anchor-error target model-error)))
                  (:instance lw-complex-scale-disk (point (lw-complex-sub (lw-complex-scale -1 (lw-complex-coefficient-at (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error target (lw-euler-normalized-request rate height outer-radius anchor-error model-error)) (+ 2 index) 0)) (lw-complex-coefficient-at (lw-polynomial-mellin-quadratic (cons rate height) (lw-euler-normalized-polynomial rate height outer-radius anchor-error target model-error)) (+ 2 index) 0)))
                    (factor (lw-rational-power -1 (+ 2 index))) (radius (* (lw-mellin-quadratic-cap (cons rate height) (lw-euler-normalized-disk-radius rate height outer-radius anchor-error))
                 (* (lw-normalized-local-inverse-cost (cons rate height) (lw-euler-normalized-disk-radius rate height outer-radius anchor-error)
                      (lw-euler-uniform-log-cap rate height outer-radius anchor-error)) (lw-euler-normalized-request rate height outer-radius anchor-error model-error))
                 (/ (lw-rational-power (lw-euler-normalized-disk-radius rate height outer-radius anchor-error) (+ 2 index)))))))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-euler-mellin-quadratic-log-model lw-complex-sub-scales lw-emqm-reflect-negative lw-polynomial-mellin-quadratic-valid lw-emqm-center-typed lw-complex-coefficient-at-rational lw-complex-scale-rational lw-rational-power-rational lw-emqm-left-commutes lw-emqm-left-distributes lw-emqm-fold-constants lw-emqm-times-negative lw-emqm-negative-times lw-emqm-zero-times lw-emqm-minus-one lw-emqm-double-negative lw-emqm-add-cancel lw-emqm-double lw-emqm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-euler-mellin-quadratic-log-comparison
  (implies (and (lw-euler-value-clearance-check rate height anchor-error)
                (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
                (< 3 rate) (natp target) (natp index)
                (rationalp coefficient-error) (< 0 coefficient-error)
                (rationalp model-error) (< 0 model-error))
           (lw-complex-diskp (lw-complex-sub (lw-euler-mellin-quadratic-coefficient-value rate height outer-radius anchor-error index coefficient-error) (lw-complex-scale -1 (lw-euler-mellin-quadratic-log-model rate height outer-radius anchor-error target (+ 2 index) model-error))) (lw-euler-mellin-quadratic-log-error rate height outer-radius anchor-error index coefficient-error model-error)))
  :hints (("Goal"
           :use (lw-emqm-quadratic-model-error lw-emqm-raw-reflected-error
                 (:instance lw-complex-difference-symmetric
                   (left (lw-complex-scale -1 (lw-euler-mellin-quadratic-log-model rate height outer-radius anchor-error target (+ 2 index) model-error))) (right (lw-pole-quadratic-coefficient (cons rate height) (lw-complex-scale (lw-rational-power -1 (+ 2 index)) (lw-complex-coefficient-at (lw-euler-normalized-polynomial rate height outer-radius anchor-error target model-error) (+ 2 index) 0)) (lw-complex-scale (lw-rational-power -1 (+ 1 index)) (lw-complex-coefficient-at (lw-euler-normalized-polynomial rate height outer-radius anchor-error target model-error) (+ 1 index) 0)) (lw-complex-scale (lw-rational-power -1 index) (lw-complex-coefficient-at (lw-euler-normalized-polynomial rate height outer-radius anchor-error target model-error) index 0)))) (radius (* (lw-mellin-quadratic-cap (cons rate height) (lw-euler-normalized-disk-radius rate height outer-radius anchor-error))
                 (* (lw-normalized-local-inverse-cost (cons rate height) (lw-euler-normalized-disk-radius rate height outer-radius anchor-error)
                      (lw-euler-uniform-log-cap rate height outer-radius anchor-error)) (lw-euler-normalized-request rate height outer-radius anchor-error model-error))
                 (/ (lw-rational-power (lw-euler-normalized-disk-radius rate height outer-radius anchor-error) (+ 2 index))))))
                 (:instance lw-complex-difference-triangle
                   (left (lw-euler-mellin-quadratic-coefficient-value rate height outer-radius anchor-error index coefficient-error)) (middle (lw-pole-quadratic-coefficient (cons rate height) (lw-complex-scale (lw-rational-power -1 (+ 2 index)) (lw-complex-coefficient-at (lw-euler-normalized-polynomial rate height outer-radius anchor-error target model-error) (+ 2 index) 0)) (lw-complex-scale (lw-rational-power -1 (+ 1 index)) (lw-complex-coefficient-at (lw-euler-normalized-polynomial rate height outer-radius anchor-error target model-error) (+ 1 index) 0)) (lw-complex-scale (lw-rational-power -1 index) (lw-complex-coefficient-at (lw-euler-normalized-polynomial rate height outer-radius anchor-error target model-error) index 0)))) (right (lw-complex-scale -1 (lw-euler-mellin-quadratic-log-model rate height outer-radius anchor-error target (+ 2 index) model-error))) (radius (+ (* (lw-complex-l1 (lw-zeta-residue-denominator (cons rate height))) (lw-euler-mellin-quadratic-transport-error rate height outer-radius anchor-error (+ 2 index) coefficient-error model-error)) (* (lw-complex-l1 (lw-complex-sub (cons 1 0) (lw-complex-scale 2 (cons rate height)))) (lw-euler-mellin-quadratic-transport-error rate height outer-radius anchor-error (+ 1 index) coefficient-error model-error)) (lw-euler-mellin-quadratic-transport-error rate height outer-radius anchor-error index coefficient-error model-error))) (other-radius (* (lw-mellin-quadratic-cap (cons rate height) (lw-euler-normalized-disk-radius rate height outer-radius anchor-error))
                 (* (lw-normalized-local-inverse-cost (cons rate height) (lw-euler-normalized-disk-radius rate height outer-radius anchor-error)
                      (lw-euler-uniform-log-cap rate height outer-radius anchor-error)) (lw-euler-normalized-request rate height outer-radius anchor-error model-error))
                 (/ (lw-rational-power (lw-euler-normalized-disk-radius rate height outer-radius anchor-error) (+ 2 index)))))))
           :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-euler-mellin-quadratic-log-error lw-emqm-left-commutes lw-emqm-left-distributes lw-emqm-fold-constants lw-emqm-times-negative lw-emqm-negative-times lw-emqm-zero-times lw-emqm-minus-one lw-emqm-double-negative lw-emqm-add-cancel lw-emqm-double lw-emqm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
