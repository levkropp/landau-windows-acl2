(in-package "ACL2")

(include-book "dirichlet-node-mass")

; The first three nodes have bounded mass. Every later node is
; covered by the dyadic summable bound to the right of 1.

(local (defthm lw-drmc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-drmc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-drmc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-drmc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-drmc-times-negative (a b) (b a)))
                 :in-theory (disable lw-drmc-times-negative)))))

(local (defthm lw-drmc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-drmc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-drmc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-drmc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-drmc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-drmc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-drmc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-drmc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-drmc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-drmc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-drmc-left-commutes)))))

(local (deftheory lw-drmc-arithmetic (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-drmc-left-commutes lw-drmc-left-distributes lw-drmc-fold-constants
              lw-drmc-times-negative lw-drmc-negative-times lw-drmc-zero-times
              lw-drmc-minus-one lw-drmc-double-negative lw-drmc-add-cancel lw-drmc-double lw-drmc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))

(defun lw-dirichlet-right-tail-majorant (rate)
  (* 64 (/ (- rate 1)) (/ (- rate 1))))

(defun lw-dirichlet-right-mass-cap (rate)
  (+ 13 (lw-dirichlet-right-tail-majorant rate)))

(defthm lw-dirichlet-right-mass-cap-data
  (implies (and (rationalp rate) (< 1 rate))
           (and (rationalp (lw-dirichlet-right-tail-majorant rate))
                (< 0 (lw-dirichlet-right-tail-majorant rate))
                (rationalp (lw-dirichlet-right-mass-cap rate))
                (< 13 (lw-dirichlet-right-mass-cap rate))))
  :hints (("Goal"
           :use ((:instance lw-reciprocal-positive (value (- rate 1)))
                 (:instance lw-drmc-positive-product (a (/ (- rate 1))) (b (/ (- rate 1)))))
           :in-theory (union-theories '(lw-dirichlet-right-tail-majorant lw-dirichlet-right-mass-cap) (theory 'lw-drmc-arithmetic))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm lw-drmc-first-three
   (implies (and (rationalp rate) (<= 0 rate) (rationalp height)
                 (rationalp request) (< 0 request) (<= request 1))
            (<= (lw-dirichlet-sample-mass rate height 1 3 request) 12))
   :hints (("Goal"
            :use ((:instance lw-dirichlet-sample-unit-cap (index 1) (log-error request) (node-error request))
                   (:instance lw-complex-disk-l1-upper (point (lw-dirichlet-sample rate height 1 request request)) (radius 2))
                   (:instance lw-complex-l1-bound (point (lw-dirichlet-sample rate height 1 request request)))
                   (:instance lw-dirichlet-sample-rational (index 1) (log-error request) (node-error request))
                   (:instance lw-dirichlet-sample-unit-cap (index 2) (log-error request) (node-error request))
                   (:instance lw-complex-disk-l1-upper (point (lw-dirichlet-sample rate height 2 request request)) (radius 2))
                   (:instance lw-complex-l1-bound (point (lw-dirichlet-sample rate height 2 request request)))
                   (:instance lw-dirichlet-sample-rational (index 2) (log-error request) (node-error request))
                   (:instance lw-dirichlet-sample-unit-cap (index 3) (log-error request) (node-error request))
                   (:instance lw-complex-disk-l1-upper (point (lw-dirichlet-sample rate height 3 request request)) (radius 2))
                   (:instance lw-complex-l1-bound (point (lw-dirichlet-sample rate height 3 request request)))
                   (:instance lw-dirichlet-sample-rational (index 3) (log-error request) (node-error request)))
            :in-theory (union-theories '(lw-dirichlet-sample-mass) (theory 'lw-drmc-arithmetic))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-dirichlet-right-dyadic-table-tail
  (implies
   (and (rationalp rate) (< 1 rate) (rationalp height)
        (natp lower) (<= 2 lower) (natp upper) (<= lower upper)
        (rationalp request) (< 0 request) (<= request 1))
   (let* ((count (- (lw-rational-power 2 upper) 1))
          (start (- (lw-rational-power 2 lower) 1))
          (nodes (lw-dirichlet-sample-table rate height count request request)))
     (<= (lw-dirichlet-node-mass count start nodes)
         (+ (* (lw-dirichlet-right-tail-majorant rate) (/ (- lower 1)))
            (* (lw-dirichlet-right-dyadic-cost rate height lower upper) request)))))
  :hints (("Goal"
           :use ((:instance lw-rational-power-natural (base 2) (exponent lower))
                 (:instance lw-rational-power-natural (base 2) (exponent upper))
                 (:instance lw-rational-power-positive (base 2) (exponent lower))
                 (:instance lw-rational-power-positive (base 2) (exponent upper))
                 (:instance lw-dirichlet-right-dyadic-mass-bound (error request))
                 (:instance lw-rational-power-monotone-exponent (base 2) (small lower) (large upper))
                 (:instance lw-dirichlet-right-dyadic-tail-bound (error request))
                 (:instance lw-dirichlet-node-mass-sample-table
                   (total (- (lw-rational-power 2 upper) 1))
                   (lower (- (lw-rational-power 2 lower) 1))
                   (upper (- (lw-rational-power 2 upper) 1)) (error request)))
           :in-theory (union-theories '(lw-dirichlet-right-tail-majorant) (theory 'lw-drmc-arithmetic))
           :do-not-induct t))
  :rule-classes nil)

(defthm lw-dirichlet-right-dyadic-table-cap
  (implies
   (and (rationalp rate) (< 1 rate) (rationalp height) (natp block) (<= 2 block)
        (rationalp request) (< 0 request) (<= request 1)
        (<= (* (lw-dirichlet-right-dyadic-cost rate height 2 block) request) 1))
   (let* ((count (- (lw-rational-power 2 block) 1))
          (nodes (lw-dirichlet-sample-table rate height count request request)))
     (<= (lw-dirichlet-node-mass count 0 nodes) (lw-dirichlet-right-mass-cap rate))))
  :hints (("Goal"
           :use (lw-drmc-first-three
                 (:instance lw-rational-power-monotone-exponent (base 2) (small 2) (large block))
                 (:instance lw-rational-power-natural (base 2) (exponent block))
                 (:instance lw-dirichlet-node-mass-sample-table
                   (total (- (lw-rational-power 2 block) 1)) (lower 0)
                   (upper (- (lw-rational-power 2 block) 1)) (error request))
                 (:instance lw-dirichlet-right-dyadic-mass-bound (lower 2) (upper block) (error request))
                 (:instance lw-dirichlet-right-dyadic-tail-bound (lower 2) (upper block) (error request))
                 (:instance lw-dirichlet-sample-mass-split (start 1) (first 3)
                   (last (- (lw-rational-power 2 block) 4)) (error request))
                 (:instance lw-dirichlet-sample-mass-rational (start 1) (count 3) (error request))
                 (:instance lw-dirichlet-sample-mass-rational (start 4) (count (- (lw-rational-power 2 block) 4)) (error request)))
           :in-theory (union-theories '(lw-dirichlet-right-mass-cap lw-dirichlet-right-tail-majorant
                                       (:executable-counterpart lw-rational-power)) (theory 'lw-drmc-arithmetic))
           :do-not-induct t))
  :rule-classes nil)
