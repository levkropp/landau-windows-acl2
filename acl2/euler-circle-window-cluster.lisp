(in-package "ACL2")

(include-book "euler-circle-joint-model")
(include-book "euler-circle-mellin-coefficients")
(include-book "euler-window-quadratic-coefficients")

(defun lw-euler-circle-window-coefficient-index (center radius plus-arcs minus-arcs anchor-error start request)
  (let* ((error (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request))
         (roots (lw-circle-pole-roots
                 (lw-euler-circle-factor-roots center radius 0 error error) radius))
         (cutoff (- radius (lw-euler-circle-collar-width center radius plus-arcs minus-arcs)))
         (order (lw-circle-interior-pole-large-index roots cutoff (+ 2 (lw-window-index start)))))
    (- order 2)))

(defun lw-euler-circle-window-pole-limit (center radius plus-arcs minus-arcs start index)
  (* (lw-circle-interior-pole-count-cap (lw-euler-circle-interior-count center radius plus-arcs minus-arcs) (+ 2 (lw-window-index start)))
     (/ (lw-rational-power (- radius (lw-euler-circle-collar-width center radius plus-arcs minus-arcs)) (+ 3 index)))))

(defun lw-euler-circle-window-coefficient-upper
    (center radius plus-arcs minus-arcs anchor-error ceiling numerator denominator index error)
  (+ (lw-euler-window-quadratic-radius (cdr center) ceiling numerator denominator index error)
     (lw-euler-circle-mellin-coefficient-error center radius anchor-error
       error error index error error error error)
     (* (lw-euler-circle-factor-sum-cap center radius plus-arcs minus-arcs)
        (/ (lw-rational-power radius (+ 2 index))))))

(local (defthm lw-eccw-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-eccw-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-eccw-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-eccw-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-eccw-times-negative (a b) (b a)))
                 :in-theory (disable lw-eccw-times-negative)))))

(local (defthm lw-eccw-zero-times (equal (* 0 a) 0)))

(local (defthm lw-eccw-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-eccw-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-eccw-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-eccw-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-eccw-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-eccw-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local
 (defthm lw-eccw-index-arithmetic
   (implies (and (natp base) (natp count) (natp order)
                 (<= (+ base 2) order)
                 (< order (+ base 2 count)))
            (and (natp (- order 2))
                 (equal (+ 2 (- order 2)) order)
                 (equal (+ 3 (- order 2)) (+ order 1))
                 (<= base (- order 2))
                 (<= order (+ base 1 count))))
   :hints (("Goal"
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              
              lw-eccw-left-commutes lw-eccw-left-distributes lw-eccw-fold-constants
              lw-eccw-times-negative lw-eccw-negative-times lw-eccw-zero-times
              lw-eccw-minus-one lw-eccw-double-negative lw-eccw-add-cancel lw-eccw-double lw-eccw-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))
   :rule-classes nil))

(local (defthm lw-eccw-len-natural
         (natp (len roots))
         :rule-classes (:rewrite :type-prescription)))

(defthm lw-euler-circle-window-coefficient-index-data
   (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
                (lw-euler-value-clearance-check (car center) (cdr center) anchor-error)
                (rationalp request) (< 0 request)
                (< 0 (lw-euler-circle-interior-count center radius plus-arcs minus-arcs)))
            (let ((index (lw-euler-circle-window-coefficient-index center radius plus-arcs minus-arcs anchor-error start request)))
              (and (posp (lw-euler-circle-interior-count center radius plus-arcs minus-arcs))
                   (natp index)
                   (<= (lw-window-index start) index)
                   (< index (+ (lw-window-index start) (lw-euler-circle-interior-count center radius plus-arcs minus-arcs)))
                   (<= (+ 2 index) (+ (lw-window-index start) 1 (lw-euler-circle-interior-count center radius plus-arcs minus-arcs)))
                   (not (lw-complex-diskp (lw-circle-exterior-coefficient (lw-circle-pole-roots (lw-euler-circle-factor-roots center radius 0 (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)) radius) -1 (+ 2 index)) (lw-euler-circle-window-pole-limit center radius plus-arcs minus-arcs start index))))))
   :hints (("Goal"
            :use ((:instance lw-euler-circle-joint-root-data (target 0))
                  (:instance lw-euler-circle-joint-large-index-data (target 0) (start (+ 2 (lw-window-index start))))
                  (:instance lw-window-index-natural (lower (car (lw-log-bounds start 1/1000))))
                  (:instance lw-circle-interior-pole-cap-by-count (roots (lw-circle-pole-roots (lw-euler-circle-factor-roots center radius 0 (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)) radius)) (radius (- radius (lw-euler-circle-collar-width center radius plus-arcs minus-arcs))) (start (+ 2 (lw-window-index start))))
                  (:instance lw-eccw-index-arithmetic (base (lw-window-index start)) (count (lw-euler-circle-interior-count center radius plus-arcs minus-arcs)) (order (lw-circle-interior-pole-large-index (lw-circle-pole-roots (lw-euler-circle-factor-roots center radius 0 (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)) radius) (- radius (lw-euler-circle-collar-width center radius plus-arcs minus-arcs)) (+ 2 (lw-window-index start))))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-window-index lw-euler-circle-window-pole-limit
              lw-euler-circle-window-coefficient-index lw-eccw-len-natural
              lw-eccw-left-commutes lw-eccw-left-distributes lw-eccw-fold-constants
              lw-eccw-times-negative lw-eccw-negative-times lw-eccw-zero-times
              lw-eccw-minus-one lw-eccw-double-negative lw-eccw-add-cancel lw-eccw-double lw-eccw-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
  :rule-classes nil)

(local
 (defthm lw-eccw-subtract-sum
   (implies (and (lw-complexp other) (lw-complexp pole))
            (equal (lw-complex-sub (lw-complex-add other pole) other) pole))
   :hints (("Goal" :in-theory
            (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complexp lw-complex-add lw-complex-sub
              lw-eccw-left-commutes lw-eccw-left-distributes lw-eccw-fold-constants
              lw-eccw-times-negative lw-eccw-negative-times lw-eccw-zero-times
              lw-eccw-minus-one lw-eccw-double-negative lw-eccw-add-cancel lw-eccw-double lw-eccw-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defthm lw-eccw-disks-contradict
   (implies (and (lw-complexp pole)
                 (lw-complex-diskp other window-bound)
                 (lw-complex-diskp (lw-complex-add other pole) model-bound)
                 (not (lw-complex-diskp pole limit))
                 (rationalp limit)
                 (<= (+ window-bound model-bound) limit))
            nil)
   :hints (("Goal"
            :use ((:instance lw-complex-disk-data (point other) (radius window-bound))
                  lw-eccw-subtract-sum
                  (:instance lw-complex-sub-disk (left (lw-complex-add other pole))
                    (right other) (radius model-bound) (other-radius window-bound))
                  (:instance lw-complex-disk-enlarge (point pole)
                    (radius (+ model-bound window-bound)) (cap limit)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              
              lw-eccw-left-commutes lw-eccw-left-distributes lw-eccw-fold-constants
              lw-eccw-times-negative lw-eccw-negative-times lw-eccw-zero-times
              lw-eccw-minus-one lw-eccw-double-negative lw-eccw-add-cancel lw-eccw-double lw-eccw-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

; One scalar budget check suffices for the computed cluster order.
(defthm lw-euler-circle-window-cluster-witness
  (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
                (lw-euler-value-clearance-check (car center) (cdr center) anchor-error)
                (rationalp request) (< 0 request)
                (< 0 (lw-euler-circle-interior-count center radius plus-arcs minus-arcs))
                (equal (car center) 252)
                (rationalp start) (natp minimum-index)
                (<= (lw-kernel-window-block-threshold minimum-index (+ 1 (lw-euler-circle-interior-count center radius plus-arcs minus-arcs))) start)
                (rationalp ceiling) (<= 0 ceiling)
                (natp numerator) (posp denominator) (<= numerator denominator)
                (<= (lw-euler-circle-window-coefficient-upper center radius plus-arcs minus-arcs anchor-error ceiling numerator denominator (lw-euler-circle-window-coefficient-index center radius plus-arcs minus-arcs anchor-error start request) (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)) (lw-euler-circle-window-pole-limit center radius plus-arcs minus-arcs start (lw-euler-circle-window-coefficient-index center radius plus-arcs minus-arcs anchor-error start request))))
           (lw-landau-window-search start ceiling numerator denominator))
  :hints (("Goal"
           :use (lw-euler-circle-window-coefficient-index-data lw-euler-circle-outer-data
                 (:instance lw-euler-circle-joint-root-data (target 0))
                 (:instance lw-euler-circle-joint-request-adequate (target 0))
                 (:instance lw-euler-circle-center-model-data (target 0) (error (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)) (epsilon (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)))
                 (:instance lw-circle-pole-split-valid (roots (lw-euler-circle-factor-roots center radius 0 (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request))))
                 (:instance lw-circle-factor-coefficient-rational (roots (lw-circle-pole-roots (lw-euler-circle-factor-roots center radius 0 (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)) radius)) (radius -1) (index (+ 2 (lw-euler-circle-window-coefficient-index center radius plus-arcs minus-arcs anchor-error start request))))
                 (:instance lw-failed-search-euler-quadratic-coefficient-bound
                   (height (cdr center)) (outer-radius (lw-euler-circle-outer-radius center radius)) (index (lw-euler-circle-window-coefficient-index center radius plus-arcs minus-arcs anchor-error start request))
                   (width (+ 1 (lw-euler-circle-interior-count center radius plus-arcs minus-arcs))) (error (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)))
                 (:instance lw-euler-circle-mellin-pole-comparison
                   (target 0) (error (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)) (epsilon (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request))
                   (index (lw-euler-circle-window-coefficient-index center radius plus-arcs minus-arcs anchor-error start request)) (extraction-error (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)) (coefficient-error (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request))
                   (model-error (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)) (value-error (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)))
                 (:instance lw-euler-circle-anchor-min-data (point (cons 1 0)))
                 (:instance lw-eccw-disks-contradict (pole (lw-circle-exterior-coefficient (lw-circle-pole-roots (lw-euler-circle-factor-roots center radius 0 (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)) radius) -1 (+ 2 (lw-euler-circle-window-coefficient-index center radius plus-arcs minus-arcs anchor-error start request)))) (other (lw-euler-mellin-quadratic-coefficient-value (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error (lw-euler-circle-window-coefficient-index center radius plus-arcs minus-arcs anchor-error start request) (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)))
                   (window-bound (lw-euler-window-quadratic-radius (cdr center) ceiling numerator denominator (lw-euler-circle-window-coefficient-index center radius plus-arcs minus-arcs anchor-error start request) (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request))) (model-bound (+ (lw-euler-circle-mellin-coefficient-error center radius anchor-error (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-window-coefficient-index center radius plus-arcs minus-arcs anchor-error start request) (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request) (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request))
                    (* (lw-euler-circle-factor-sum-cap center radius plus-arcs minus-arcs) (/ (lw-rational-power radius (+ 2 (lw-euler-circle-window-coefficient-index center radius plus-arcs minus-arcs anchor-error start request))))))) (limit (lw-euler-circle-window-pole-limit center radius plus-arcs minus-arcs start (lw-euler-circle-window-coefficient-index center radius plus-arcs minus-arcs anchor-error start request))))
                 lw-euler-circle-collar-width-data
                 (:instance lw-rational-power-rational (base (- radius (lw-euler-circle-collar-width center radius plus-arcs minus-arcs))) (exponent (+ 3 (lw-euler-circle-window-coefficient-index center radius plus-arcs minus-arcs anchor-error start request))))
                 (:instance lw-power-domination-factor-valid (count (lw-euler-circle-interior-count center radius plus-arcs minus-arcs)) (index (+ (+ 2 (lw-window-index start)) (lw-euler-circle-interior-count center radius plus-arcs minus-arcs)))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-circle-window-coefficient-upper lw-euler-circle-window-pole-limit
              lw-circle-interior-pole-count-cap lw-window-index lw-window-index-natural
              lw-reciprocal-positive len 
              lw-eccw-left-commutes lw-eccw-left-distributes lw-eccw-fold-constants
              lw-eccw-times-negative lw-eccw-negative-times lw-eccw-zero-times
              lw-eccw-minus-one lw-eccw-double-negative lw-eccw-add-cancel lw-eccw-double lw-eccw-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
