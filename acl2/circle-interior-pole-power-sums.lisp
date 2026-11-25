(in-package "ACL2")

(include-book "euler-circle-interior-collar")
(include-book "circle-factor-coefficient-split")
(include-book "power-sum-search")
(include-book "polynomial-coefficient-maps")

; With every selected offset inside radius, the normalized reciprocal
; nodes have norm at least one. Unit weights count repeated factors.
(defun lw-circle-interior-pole-power-system (roots radius)
  (if (endp roots) nil
    (let ((root (car roots)))
      (cons (cons (lw-complex-scale radius (lw-complex-reciprocal (lw-complex-scale -1 root))) (cons 1 0))
            (lw-circle-interior-pole-power-system (cdr roots) radius)))))

(defun lw-circle-interior-pole-large-index (roots radius start)
  (- (lw-power-sum-large-index (lw-circle-interior-pole-power-system roots radius) start) 1))

(local (defthm lw-cipps-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-cipps-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-cipps-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-cipps-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-cipps-times-negative (a b) (b a)))
                 :in-theory (disable lw-cipps-times-negative)))))

(local (defthm lw-cipps-zero-times (equal (* 0 a) 0)))

(local (defthm lw-cipps-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-cipps-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-cipps-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-cipps-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-cipps-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-cipps-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-cipps-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cipps-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cipps-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-cipps-left-commutes)))))
(local (defthm lw-cipps-length-natural
         (natp (len roots))
         :rule-classes (:rewrite :type-prescription)))

(local
 (defthm lw-cipps-negative-norm
   (implies (lw-complexp root)
            (equal (lw-complex-norm-square (lw-complex-scale -1 root)) (lw-complex-norm-square root)))
   :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-complexp lw-complex-norm-square lw-complex-scale consp lw-cipps-left-commutes lw-cipps-left-distributes lw-cipps-fold-constants lw-cipps-times-negative lw-cipps-negative-times lw-cipps-zero-times lw-cipps-minus-one lw-cipps-double-negative lw-cipps-add-cancel lw-cipps-double lw-cipps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local
 (defthm lw-cipps-scale-norm
   (implies (and (lw-complexp point) (rationalp factor))
            (equal (lw-complex-norm-square (lw-complex-scale factor point))
                   (* factor factor (lw-complex-norm-square point))))
   :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-complexp lw-complex-norm-square lw-complex-scale consp lw-cipps-left-commutes lw-cipps-left-distributes lw-cipps-fold-constants lw-cipps-times-negative lw-cipps-negative-times lw-cipps-zero-times lw-cipps-minus-one lw-cipps-double-negative lw-cipps-add-cancel lw-cipps-double lw-cipps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local
 (defthm lw-cipps-ratio-order
   (implies (and (rationalp power) (< 0 power) (rationalp bound) (<= power bound))
            (<= 1 (* bound (/ power))))
   :hints (("Goal"
            :use ((:instance lw-cipps-multiply-order (a power) (b bound) (factor (/ power)))
                  (:instance inverse-of-* (x power)))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-reciprocal-positive lw-cipps-left-commutes lw-cipps-left-distributes lw-cipps-fold-constants lw-cipps-times-negative lw-cipps-negative-times lw-cipps-zero-times lw-cipps-minus-one lw-cipps-double-negative lw-cipps-add-cancel lw-cipps-double lw-cipps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-cipps-offset-nonzero
   (implies (and (lw-complexp root) (< 0 (lw-complex-norm-square root)))
            (not (equal (lw-complex-scale -1 root) (cons 0 0))))
   :hints (("Goal" :use (lw-cipps-negative-norm)
                   :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complex-norm-square) lw-cipps-left-commutes lw-cipps-left-distributes lw-cipps-fold-constants lw-cipps-times-negative lw-cipps-negative-times lw-cipps-zero-times lw-cipps-minus-one lw-cipps-double-negative lw-cipps-add-cancel lw-cipps-double lw-cipps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
                   :do-not-induct t))))

(local
 (defthm lw-cipps-node-data
   (implies (and (lw-complexp root) (rationalp radius) (< 0 radius)
                 (< 0 (lw-complex-norm-square root))
                 (<= (lw-complex-norm-square root) (* radius radius)))
            (and (lw-complexp (lw-complex-scale radius (lw-complex-reciprocal (lw-complex-scale -1 root)))) (<= 1 (lw-complex-norm-square (lw-complex-scale radius (lw-complex-reciprocal (lw-complex-scale -1 root)))))))
   :hints (("Goal"
            :use (lw-cipps-negative-norm (:instance lw-complex-norm-square-reciprocal (point (lw-complex-scale -1 root)))
                 
                  (:instance lw-cipps-ratio-order (power (lw-complex-norm-square root)) (bound (* radius radius))))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-cipps-offset-nonzero lw-cipps-scale-norm (:executable-counterpart lw-complex-norm-square) lw-complex-scale-rational lw-complex-reciprocal-rational lw-complex-norm-square-valid lw-cipps-left-commutes lw-cipps-left-distributes lw-cipps-fold-constants lw-cipps-times-negative lw-cipps-negative-times lw-cipps-zero-times lw-cipps-minus-one lw-cipps-double-negative lw-cipps-add-cancel lw-cipps-double lw-cipps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))))

(defthm lw-circle-interior-pole-power-system-data
  (implies (and (lw-circle-interior-rootsp roots radius) (lw-circle-exterior-rootsp roots 0)
                (rationalp radius) (< 0 radius))
           (and (lw-power-outer-systemp (lw-circle-interior-pole-power-system roots radius))
                (equal (len (lw-circle-interior-pole-power-system roots radius)) (len roots))
                (equal (consp (lw-circle-interior-pole-power-system roots radius)) (consp roots))))
  :hints (("Goal" :induct (lw-circle-interior-pole-power-system roots radius)
                  :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-circle-interior-pole-power-system lw-circle-interior-rootsp lw-circle-exterior-rootsp lw-power-outer-systemp lw-cipps-node-data len endp lw-cipps-left-commutes lw-cipps-left-distributes lw-cipps-fold-constants lw-cipps-times-negative lw-cipps-negative-times lw-cipps-zero-times lw-cipps-minus-one lw-cipps-double-negative lw-cipps-add-cancel lw-cipps-double lw-cipps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
                  :do-not '(generalize fertilize))))

(local
 (defthm lw-cipps-power-zero
   (equal (lw-complex-power point 0) (cons 1 0))
   :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-complex-power lw-cipps-left-commutes lw-cipps-left-distributes lw-cipps-fold-constants lw-cipps-times-negative lw-cipps-negative-times lw-cipps-zero-times lw-cipps-minus-one lw-cipps-double-negative lw-cipps-add-cancel lw-cipps-double lw-cipps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local
 (defthm lw-cipps-positive-integer-complex
   (implies (rationalp x) (lw-complexp (cons x 0)))
   :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-complexp consp lw-cipps-left-commutes lw-cipps-left-distributes lw-cipps-fold-constants lw-cipps-times-negative lw-cipps-negative-times lw-cipps-zero-times lw-cipps-minus-one lw-cipps-double-negative lw-cipps-add-cancel lw-cipps-double lw-cipps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-circle-interior-pole-power-sum-zero
  (equal (lw-weighted-power-sum (lw-circle-interior-pole-power-system roots radius) 0) (cons (len roots) 0))
  :hints (("Goal" :induct (lw-circle-interior-pole-power-system roots radius)
                  :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-circle-interior-pole-power-system lw-weighted-power-sum lw-cipps-power-zero lw-complex-add lw-cipps-positive-integer-complex lw-complex-mul-one lw-cipps-length-natural len endp lw-cipps-left-commutes lw-cipps-left-distributes lw-cipps-fold-constants lw-cipps-times-negative lw-cipps-negative-times lw-cipps-zero-times lw-cipps-minus-one lw-cipps-double-negative lw-cipps-add-cancel lw-cipps-double lw-cipps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
                  :do-not '(generalize fertilize))))

(defun lw-circle-interior-pole-count-cap (count start)
  (* 1/8 count (/ (lw-power-domination-factor count (+ start count)))))

(defthm lw-circle-interior-pole-cap-by-count
  (implies (and (rationalp radius) (< 0 radius)
                (lw-circle-interior-rootsp roots radius)
                (lw-circle-exterior-rootsp roots 0))
           (equal (lw-power-large-term-cap
                   (lw-circle-interior-pole-power-system roots radius) start)
                  (lw-circle-interior-pole-count-cap (len roots) start)))
  :hints (("Goal"
           :use (lw-circle-interior-pole-power-system-data
                 lw-circle-interior-pole-power-sum-zero)
           :in-theory
           (union-theories
            '(lw-circle-interior-pole-count-cap lw-power-large-term-cap
              lw-complex-l1 lw-cipps-length-natural abs
              car-cons cdr-cons unicity-of-0 commutativity-of-+ fix natp)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(defthm lw-circle-interior-pole-power-sum-coefficient
  (implies (and (lw-ray-pointsp roots) (rationalp radius) (natp index))
           (equal (lw-weighted-power-sum (lw-circle-interior-pole-power-system roots radius) (+ 1 index))
                  (lw-complex-scale (lw-rational-power radius (+ 1 index)) (lw-circle-exterior-coefficient roots -1 index))))
  :hints (("Goal" :induct (lw-circle-interior-pole-power-system roots radius)
                  :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-circle-interior-pole-power-system lw-weighted-power-sum lw-circle-exterior-coefficient lw-pole-unit-coefficient-formula lw-circle-factor-coefficient-rational lw-complex-power-scale lw-complex-scale-one lw-complex-scale-add lw-complex-scale-zero lw-complex-mul-one lw-ray-pointsp lw-complex-scale-rational lw-complex-power-rational lw-complex-reciprocal-rational lw-complex-ring-rational lw-rational-power-one lw-rational-power-rational endp lw-cipps-left-commutes lw-cipps-left-distributes lw-cipps-fold-constants lw-cipps-times-negative lw-cipps-negative-times lw-cipps-zero-times lw-cipps-minus-one lw-cipps-double-negative lw-cipps-add-cancel lw-cipps-double lw-cipps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
                  :do-not '(generalize fertilize))))

(local (defthm lw-cipps-length-positive
         (implies (consp roots) (< 0 (len roots)))
         :rule-classes (:rewrite :linear)))

(local
 (defthm lw-cipps-rescale-error
   (implies (and (rationalp factor) (< 0 factor) (rationalp cap)
                 (lw-complex-diskp point (* cap (/ factor))))
            (lw-complex-diskp (lw-complex-scale factor point) cap))
   :hints (("Goal"
            :use ((:instance lw-complex-scale-disk (radius (* cap (/ factor))))
                  (:instance lw-cipps-inverse-factor (divisor factor) (coefficient cap)))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) abs lw-cipps-left-commutes lw-cipps-left-distributes lw-cipps-fold-constants lw-cipps-times-negative lw-cipps-negative-times lw-cipps-zero-times lw-cipps-minus-one lw-cipps-double-negative lw-cipps-add-cancel lw-cipps-double lw-cipps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))))

(defthm lw-circle-interior-pole-large-index-data
  (implies (and (lw-circle-interior-rootsp roots radius) (lw-circle-exterior-rootsp roots 0)
                (rationalp radius) (< 0 radius) (consp roots) (natp start))
           (and (natp (lw-circle-interior-pole-large-index roots radius start)) (<= start (lw-circle-interior-pole-large-index roots radius start)) (< (lw-circle-interior-pole-large-index roots radius start) (+ start (len roots)))
                (not (lw-complex-diskp (lw-circle-exterior-coefficient roots -1 (lw-circle-interior-pole-large-index roots radius start)) (* (lw-power-large-term-cap (lw-circle-interior-pole-power-system roots radius) start) (/ (lw-rational-power radius (+ 1 (lw-circle-interior-pole-large-index roots radius start)))))))))
  :hints (("Goal"
           :use (lw-circle-interior-pole-power-system-data
                 (:instance lw-power-sum-large-index-certificate (entries (lw-circle-interior-pole-power-system roots radius)))
                 (:instance lw-power-large-term-cap-valid (entries (lw-circle-interior-pole-power-system roots radius)))
                 (:instance lw-rational-power-positive (base radius) (exponent (+ 1 (lw-circle-interior-pole-large-index roots radius start))))
                 (:instance lw-circle-interior-pole-power-sum-coefficient (index (lw-circle-interior-pole-large-index roots radius start)))
                 (:instance lw-cipps-rescale-error (point (lw-circle-exterior-coefficient roots -1 (lw-circle-interior-pole-large-index roots radius start))) (factor (lw-rational-power radius (+ 1 (lw-circle-interior-pole-large-index roots radius start)))) (cap (lw-power-large-term-cap (lw-circle-interior-pole-power-system roots radius) start))))
           :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-circle-interior-pole-large-index lw-circle-interior-pole-power-sum-zero lw-circle-exterior-roots-typed lw-power-outer-system-typed lw-rational-power-rational lw-cipps-length-natural lw-cipps-length-positive cons-equal lw-cipps-left-commutes lw-cipps-left-distributes lw-cipps-fold-constants lw-cipps-times-negative lw-cipps-negative-times lw-cipps-zero-times lw-cipps-minus-one lw-cipps-double-negative lw-cipps-add-cancel lw-cipps-double lw-cipps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
