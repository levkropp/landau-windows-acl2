(in-package "ACL2")

(include-book "kernel-window-refinement")

; Total mass for actual upper kernel enclosures, with only the requested
; primitive precision left in the bound.
(local (in-theory
        (disable lw-kernel-grid-upper-sum lw-kernel-grid-upper-sum-valid lw-kernel-grid-upper-sum-comparison
                 lw-mellin-grid-weight-sum lw-mellin-grid-weight-mass-bound
                 lw-rational-power lw-rational-power-nonnegative
                 lw-kernel-grid-count lw-kernel-grid-step lw-kernel-grid-count-adequate lw-kernel-grid-step-valid)))

(local (defthm lw-um-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-um-times-negative
         (implies (and (rationalp a) (rationalp b)) (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-um-negative-times
         (implies (and (rationalp a) (rationalp b)) (equal (* (- a) b) (- (* a b))))))
(local (defthm lw-um-zero-times (equal (* 0 a) 0)))
(local (defthm lw-um-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))
(local (defthm lw-um-double-negative (implies (rationalp a) (equal (- (- a)) a))))
(local (defthm lw-um-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))
(local (defthm lw-um-left-distribute
         (implies (and (rationalp a) (rationalp b) (rationalp c))
                  (equal (* (+ a b) c) (+ (* a c) (* b c))))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-um-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b) (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-um-nonnegative-product
         (implies (and (rationalp a) (<= 0 a) (rationalp b) (<= 0 b)) (<= 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-um-positive-refinement
         (implies (and (rationalp excess) (< 0 excess) (rationalp measure) (<= 0 measure))
                  (and (rationalp (/ excess (* 2 (+ 1 measure))))
                       (< 0 (/ excess (* 2 (+ 1 measure))))
                       (<= (* measure (/ excess (* 2 (+ 1 measure)))) (/ excess 2))))
         :hints (("Goal" :use ((:instance lw-positive-division-bound
                                (numerator (* measure excess)) (divisor (* 2 (+ 1 measure))) (bound (/ excess 2))))
                         :nonlinearp t))
         :rule-classes nil))

(defthm lw-kernel-grid-upper-mass-bound
  (implies (and (natp count) (natp index) (rationalp rate) (< 0 rate)
                (rationalp step) (< 0 step) (<= (* 2 rate step (+ 1 index)) 1) (rationalp error) (< 0 error))
           (<= (lw-kernel-grid-upper-sum 0 count rate index step error)
               (+ (* 2 (lw-rational-power (/ rate) (+ 1 index))) (* count step error))))
  :hints (("Goal"
           :cases ((<= (lw-kernel-grid-upper-sum 0 count rate index step error)
                       (+ (* 2 (lw-rational-power (/ rate) (+ 1 index))) (* count step error))))
           :use ((:instance lw-kernel-grid-upper-sum-valid (address 0))
                 (:instance lw-um-positive-refinement (measure (* count step))
                   (excess (- (lw-kernel-grid-upper-sum 0 count rate index step error)
                              (+ (* 2 (lw-rational-power (/ rate) (+ 1 index))) (* count step error)))))
                 (:instance lw-mellin-grid-weight-mass-bound
                   (error (/ (- (lw-kernel-grid-upper-sum 0 count rate index step error)
                                 (+ (* 2 (lw-rational-power (/ rate) (+ 1 index))) (* count step error)))
                             (* 2 (+ 1 (* count step))))))
                 (:instance lw-kernel-grid-upper-sum-comparison (address 0)
                   (sample-error (/ (- (lw-kernel-grid-upper-sum 0 count rate index step error)
                                        (+ (* 2 (lw-rational-power (/ rate) (+ 1 index))) (* count step error)))
                                    (* 2 (+ 1 (* count step)))))))
           :nonlinearp t)))

(local (in-theory (disable lw-kernel-grid-upper-mass-bound)))

(defthm lw-kernel-computed-grid-upper-mass-bound
  (implies (and (rationalp cap) (< 0 cap) (rationalp rate) (< 0 rate) (natp index)
                (rationalp mesh) (< 0 mesh) (rationalp error) (< 0 error))
           (<= (lw-kernel-grid-upper-sum 0 (lw-kernel-grid-count cap rate index mesh) rate index
                                         (lw-kernel-grid-step cap rate index mesh) error)
               (+ (* 2 (lw-rational-power (/ rate) (+ 1 index))) (* cap error))))
  :hints (("Goal" :use (lw-kernel-grid-count-adequate lw-kernel-grid-step-valid
                        (:instance lw-kernel-grid-upper-mass-bound
                          (count (lw-kernel-grid-count cap rate index mesh)) (step (lw-kernel-grid-step cap rate index mesh))))
                  :nonlinearp t)))
