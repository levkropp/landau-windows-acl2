(in-package "ACL2")

(include-book "euler-circle-joint-model")
(include-book "euler-circle-factor-sum-cap")
(include-book "circle-exterior-coefficient-model")
(include-book "polynomial-cauchy-caps")

(defun lw-euler-circle-empty-log-polynomial (center radius plus-arcs minus-arcs anchor-error request approximation-error)
  (let ((error (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)))
    (lw-circle-exterior-polynomial
     (lw-euler-circle-factor-roots center radius 0 error error)
     radius 0 approximation-error)))

(local (defthm lw-eclm-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-eclm-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-eclm-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-eclm-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-eclm-times-negative (a b) (b a)))
                 :in-theory (disable lw-eclm-times-negative)))))

(local (defthm lw-eclm-zero-times (equal (* 0 a) 0)))

(local (defthm lw-eclm-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-eclm-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-eclm-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-eclm-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-eclm-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-eclm-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-eclm-length-natural
         (natp (len roots))
         :rule-classes (:rewrite :type-prescription)))

(local
 (defthm lw-eclm-exterior-identity
   (implies (and (lw-ray-pointsp roots)
                 (equal (len (lw-circle-pole-roots roots radius)) 0))
            (equal (lw-circle-exterior-roots roots radius) roots))
   :hints (("Goal" :induct (lw-circle-pole-roots roots radius)
                   :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-pole-roots lw-circle-exterior-roots lw-ray-pointsp len lw-eclm-length-natural endp
              lw-eclm-left-commutes lw-eclm-left-distributes lw-eclm-fold-constants
              lw-eclm-times-negative lw-eclm-negative-times lw-eclm-zero-times
              lw-eclm-minus-one lw-eclm-double-negative lw-eclm-add-cancel lw-eclm-double lw-eclm-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                   :do-not '(generalize fertilize)))))

(local
 (defthm lw-eclm-empty-roots
   (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
                 (lw-euler-value-clearance-check (car center) (cdr center) anchor-error)
                 (equal (lw-euler-circle-interior-count center radius plus-arcs minus-arcs) 0)
                 (rationalp request) (< 0 request))
            (lw-circle-exterior-rootsp (lw-euler-circle-factor-roots center radius 0 (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)) radius))
   :hints (("Goal"
            :use (lw-euler-circle-outer-data
                  (:instance lw-euler-circle-joint-request-adequate (target 0))
                  (:instance lw-euler-circle-center-model-data (target 0) (error (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)) (epsilon (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)))
                  (:instance lw-euler-circle-anchor-min-data (point (cons 1 0)))
                  (:instance lw-euler-circle-exterior-roots-data (target 0) (error (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)) (epsilon (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)))
                  (:instance lw-eclm-exterior-identity (roots (lw-euler-circle-factor-roots center radius 0 (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-circle-center-modelp (:executable-counterpart lw-complex-norm-square)
              lw-eclm-left-commutes lw-eclm-left-distributes lw-eclm-fold-constants
              lw-eclm-times-negative lw-eclm-negative-times lw-eclm-zero-times
              lw-eclm-minus-one lw-eclm-double-negative lw-eclm-add-cancel lw-eclm-double lw-eclm-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-euler-circle-empty-log-polynomial-comparison
  (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
                (lw-euler-value-clearance-check (car center) (cdr center) anchor-error)
                (equal (lw-euler-circle-interior-count center radius plus-arcs minus-arcs) 0)
                (rationalp request) (< 0 request)
                (rationalp approximation-error) (< 0 approximation-error) (lw-complex-diskp point 1))
           (and (lw-complex-coefficientsp (lw-euler-circle-empty-log-polynomial center radius plus-arcs minus-arcs anchor-error request approximation-error))
                (lw-complex-diskp (lw-complex-sub (lw-polynomial-factor-log-sum (lw-euler-circle-factor-roots center radius 0 (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)) (lw-complex-scale radius point)) (lw-complex-polynomial (lw-euler-circle-empty-log-polynomial center radius plus-arcs minus-arcs anchor-error request approximation-error) point 0)) approximation-error)))
  :hints (("Goal"
           :use (lw-eclm-empty-roots lw-euler-circle-outer-data
                 (:instance lw-circle-exterior-polynomial-valid (roots (lw-euler-circle-factor-roots center radius 0 (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request))) (target 0) (error approximation-error))
                 (:instance lw-circle-exterior-polynomial-error (roots (lw-euler-circle-factor-roots center radius 0 (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request))) (target 0) (error approximation-error)))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-circle-empty-log-polynomial
              lw-eclm-left-commutes lw-eclm-left-distributes lw-eclm-fold-constants
              lw-eclm-times-negative lw-eclm-negative-times lw-eclm-zero-times
              lw-eclm-minus-one lw-eclm-double-negative lw-eclm-add-cancel lw-eclm-double lw-eclm-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm lw-eclm-boundary-polynomial-cap
   (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
                (lw-euler-value-clearance-check (car center) (cdr center) anchor-error)
                (equal (lw-euler-circle-interior-count center radius plus-arcs minus-arcs) 0)
                (rationalp request) (< 0 request)
                (rationalp approximation-error) (< 0 approximation-error) (<= approximation-error 1)
                 (lw-complexp point) (equal (lw-complex-norm-square point) 1))
            (lw-complex-diskp (lw-complex-polynomial (lw-euler-circle-empty-log-polynomial center radius plus-arcs minus-arcs anchor-error request approximation-error) point 0) (+ 1 (lw-euler-circle-factor-sum-cap center radius plus-arcs minus-arcs))))
   :hints (("Goal"
            :use (lw-euler-circle-empty-log-polynomial-comparison lw-euler-circle-factor-sum-cap-data
                  (:instance lw-euler-circle-anchor-min-data)
                  (:instance lw-euler-circle-joint-request-adequate (target 0))
                  (:instance lw-complex-disk-norm-square (radius 1))
                  (:instance lw-euler-circle-factor-sum-bound (target 0) (error (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)) (epsilon (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)))
                  (:instance lw-complex-disk-data (point (lw-polynomial-factor-log-sum (lw-euler-circle-factor-roots center radius 0 (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)) (lw-complex-scale radius point))) (radius (lw-euler-circle-factor-sum-cap center radius plus-arcs minus-arcs)))
                  (:instance lw-complex-polynomial-rational (coefficients (lw-euler-circle-empty-log-polynomial center radius plus-arcs minus-arcs anchor-error request approximation-error)) (offset 0))
                  (:instance lw-complex-difference-symmetric (left (lw-polynomial-factor-log-sum (lw-euler-circle-factor-roots center radius 0 (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)) (lw-complex-scale radius point))) (right (lw-complex-polynomial (lw-euler-circle-empty-log-polynomial center radius plus-arcs minus-arcs anchor-error request approximation-error) point 0)) (radius approximation-error))
                  (:instance lw-complex-difference-triangle (left (lw-complex-polynomial (lw-euler-circle-empty-log-polynomial center radius plus-arcs minus-arcs anchor-error request approximation-error) point 0)) (middle (lw-polynomial-factor-log-sum (lw-euler-circle-factor-roots center radius 0 (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)) (lw-complex-scale radius point))) (right (cons 0 0))
                    (radius approximation-error) (other-radius (lw-euler-circle-factor-sum-cap center radius plus-arcs minus-arcs)))
                  (:instance lw-complex-disk-enlarge (point (lw-complex-polynomial (lw-euler-circle-empty-log-polynomial center radius plus-arcs minus-arcs anchor-error request approximation-error) point 0)) (radius (+ approximation-error (lw-euler-circle-factor-sum-cap center radius plus-arcs minus-arcs))) (cap (+ 1 (lw-euler-circle-factor-sum-cap center radius plus-arcs minus-arcs)))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complex-sub-zero lw-euler-circle-center-modelp
              lw-eclm-left-commutes lw-eclm-left-distributes lw-eclm-fold-constants
              lw-eclm-times-negative lw-eclm-negative-times lw-eclm-zero-times
              lw-eclm-minus-one lw-eclm-double-negative lw-eclm-add-cancel lw-eclm-double lw-eclm-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-eclm-boundary-check
   (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
                (lw-euler-value-clearance-check (car center) (cdr center) anchor-error)
                (equal (lw-euler-circle-interior-count center radius plus-arcs minus-arcs) 0)
                (rationalp request) (< 0 request)
                (rationalp approximation-error) (< 0 approximation-error) (<= approximation-error 1) (natp degree) (natp count))
            (lw-cauchy-boundary-check (lw-euler-circle-empty-log-polynomial center radius plus-arcs minus-arcs anchor-error request approximation-error) (lw-cauchy-orbit-rotation degree) 0 count (+ 1 (lw-euler-circle-factor-sum-cap center radius plus-arcs minus-arcs))))
   :hints (("Goal" :induct (lw-cauchy-boundary-check (lw-euler-circle-empty-log-polynomial center radius plus-arcs minus-arcs anchor-error request approximation-error) (lw-cauchy-orbit-rotation degree) 0 count (+ 1 (lw-euler-circle-factor-sum-cap center radius plus-arcs minus-arcs)))
                   :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-cauchy-boundary-check
              lw-eclm-left-commutes lw-eclm-left-distributes lw-eclm-fold-constants
              lw-eclm-times-negative lw-eclm-negative-times lw-eclm-zero-times
              lw-eclm-minus-one lw-eclm-double-negative lw-eclm-add-cancel lw-eclm-double lw-eclm-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory)))
           (and stable-under-simplificationp
                '(:use (lw-cauchy-orbit-data
                        (:instance lw-cauchy-orbit-power-norm-one (index (- count 1)))
                        (:instance lw-complex-power-rational (point (lw-cauchy-orbit-rotation degree)) (index (- count 1)))
                        (:instance lw-eclm-boundary-polynomial-cap (point (lw-complex-power (lw-cauchy-orbit-rotation degree) (- count 1)))))
                  :do-not-induct t)))
   :rule-classes nil))

(defthm lw-euler-circle-empty-log-polynomial-caps
  (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
                (lw-euler-value-clearance-check (car center) (cdr center) anchor-error)
                (equal (lw-euler-circle-interior-count center radius plus-arcs minus-arcs) 0)
                (rationalp request) (< 0 request)
                (rationalp approximation-error) (< 0 approximation-error) (<= approximation-error 1))
           (and (lw-complex-coefficientsp (lw-euler-circle-empty-log-polynomial center radius plus-arcs minus-arcs anchor-error request approximation-error))
                (lw-polynomial-coefficient-caps (lw-euler-circle-empty-log-polynomial center radius plus-arcs minus-arcs anchor-error request approximation-error) (+ 1 (lw-euler-circle-factor-sum-cap center radius plus-arcs minus-arcs)))))
  :hints (("Goal"
           :use (lw-euler-circle-factor-sum-cap-data
                 (:instance lw-euler-circle-empty-log-polynomial-comparison (point (cons 0 0)))
                 (:instance lw-polynomial-cauchy-cap-data (coefficients (lw-euler-circle-empty-log-polynomial center radius plus-arcs minus-arcs anchor-error request approximation-error)) (cap (+ 1 (lw-euler-circle-factor-sum-cap center radius plus-arcs minus-arcs))))
                 (:instance lw-eclm-boundary-check (degree (len (lw-euler-circle-empty-log-polynomial center radius plus-arcs minus-arcs anchor-error request approximation-error)))
                   (count (lw-cauchy-coefficient-count (lw-euler-circle-empty-log-polynomial center radius plus-arcs minus-arcs anchor-error request approximation-error) (len (lw-euler-circle-empty-log-polynomial center radius plus-arcs minus-arcs anchor-error request approximation-error)) (lw-polynomial-cap-test-error (lw-euler-circle-empty-log-polynomial center radius plus-arcs minus-arcs anchor-error request approximation-error) (+ 1 (lw-euler-circle-factor-sum-cap center radius plus-arcs minus-arcs))))))
                 (:instance lw-polynomial-cauchy-cap-check-sound (coefficients (lw-euler-circle-empty-log-polynomial center radius plus-arcs minus-arcs anchor-error request approximation-error)) (cap (+ 1 (lw-euler-circle-factor-sum-cap center radius plus-arcs minus-arcs)))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-polynomial-cauchy-cap-check (:executable-counterpart lw-complex-diskp)
              lw-eclm-left-commutes lw-eclm-left-distributes lw-eclm-fold-constants
              lw-eclm-times-negative lw-eclm-negative-times lw-eclm-zero-times
              lw-eclm-minus-one lw-eclm-double-negative lw-eclm-add-cancel lw-eclm-double lw-eclm-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
