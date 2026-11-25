(in-package "ACL2")

(include-book "euler-circle-pole-band")
(include-book "euler-circle-uniform-grid")

; Return the physical radius followed by the two checked charts.

(local (defthm lw-ecgc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ecgc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ecgc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ecgc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ecgc-times-negative (a b) (b a)))
                 :in-theory (disable lw-ecgc-times-negative)))))

(local (defthm lw-ecgc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ecgc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ecgc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ecgc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ecgc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ecgc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ecgc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ecgc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecgc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecgc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ecgc-left-commutes)))))

(defun lw-euler-circle-generated-cover
    (rate height outer-radius target error factor-error lower upper scale cutoff-square)
  (let* ((band (lw-euler-circle-pole-band rate height outer-radius lower upper))
         (low (car band))
         (high (cdr band))
         (limit (lw-euler-circle-uniform-approximation-limit
                 rate height outer-radius low high scale cutoff-square))
         (clearance (lw-euler-circle-uniform-distance
                     rate height outer-radius low high scale cutoff-square))
         (normalized-radius
           (car (lw-euler-circle-bounded-radius rate height outer-radius target
                  (min error limit) (min factor-error limit) low high cutoff-square)))
         (radius (* outer-radius normalized-radius))
         (arcs (lw-euler-circle-anchored-grid rate height outer-radius radius
                 (lw-euler-circle-pole-gap outer-radius band) clearance)))
    (list radius (car arcs) (cadr arcs))))

(local
 (defthm lw-ecgc-request-data
   (implies
    (and (rationalp rate) (< 3 rate) (rationalp height)
       (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
       (rationalp lower) (<= 0 lower) (rationalp upper) (< lower upper)
       (rationalp scale) (< upper scale)
       (rationalp cutoff-square) (< (* scale scale) cutoff-square) (< cutoff-square 1) (natp target) (rationalp error) (< 0 error) (rationalp factor-error) (< 0 factor-error))
    (and (rationalp (car (lw-euler-circle-pole-band rate height outer-radius lower upper))) (rationalp (cdr (lw-euler-circle-pole-band rate height outer-radius lower upper))) (<= lower (car (lw-euler-circle-pole-band rate height outer-radius lower upper)))
         (< (car (lw-euler-circle-pole-band rate height outer-radius lower upper)) (cdr (lw-euler-circle-pole-band rate height outer-radius lower upper))) (<= (cdr (lw-euler-circle-pole-band rate height outer-radius lower upper)) upper)
         (rationalp (min error (lw-euler-circle-uniform-approximation-limit rate height outer-radius (car (lw-euler-circle-pole-band rate height outer-radius lower upper)) (cdr (lw-euler-circle-pole-band rate height outer-radius lower upper)) scale cutoff-square))) (< 0 (min error (lw-euler-circle-uniform-approximation-limit rate height outer-radius (car (lw-euler-circle-pole-band rate height outer-radius lower upper)) (cdr (lw-euler-circle-pole-band rate height outer-radius lower upper)) scale cutoff-square))) (<= (min error (lw-euler-circle-uniform-approximation-limit rate height outer-radius (car (lw-euler-circle-pole-band rate height outer-radius lower upper)) (cdr (lw-euler-circle-pole-band rate height outer-radius lower upper)) scale cutoff-square)) (lw-euler-circle-uniform-approximation-limit rate height outer-radius (car (lw-euler-circle-pole-band rate height outer-radius lower upper)) (cdr (lw-euler-circle-pole-band rate height outer-radius lower upper)) scale cutoff-square))
         (rationalp (min factor-error (lw-euler-circle-uniform-approximation-limit rate height outer-radius (car (lw-euler-circle-pole-band rate height outer-radius lower upper)) (cdr (lw-euler-circle-pole-band rate height outer-radius lower upper)) scale cutoff-square))) (< 0 (min factor-error (lw-euler-circle-uniform-approximation-limit rate height outer-radius (car (lw-euler-circle-pole-band rate height outer-radius lower upper)) (cdr (lw-euler-circle-pole-band rate height outer-radius lower upper)) scale cutoff-square))) (<= (min factor-error (lw-euler-circle-uniform-approximation-limit rate height outer-radius (car (lw-euler-circle-pole-band rate height outer-radius lower upper)) (cdr (lw-euler-circle-pole-band rate height outer-radius lower upper)) scale cutoff-square)) (lw-euler-circle-uniform-approximation-limit rate height outer-radius (car (lw-euler-circle-pole-band rate height outer-radius lower upper)) (cdr (lw-euler-circle-pole-band rate height outer-radius lower upper)) scale cutoff-square))
         (rationalp (lw-euler-circle-pole-gap outer-radius (lw-euler-circle-pole-band rate height outer-radius lower upper))) (< 0 (lw-euler-circle-pole-gap outer-radius (lw-euler-circle-pole-band rate height outer-radius lower upper)))))
   :hints (("Goal"
            :use (lw-euler-circle-pole-band-data
                  (:instance lw-euler-circle-uniform-clearance-budget-data (lower (car (lw-euler-circle-pole-band rate height outer-radius lower upper))) (upper (cdr (lw-euler-circle-pole-band rate height outer-radius lower upper)))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              min
              lw-ecgc-left-commutes lw-ecgc-left-distributes lw-ecgc-fold-constants
              lw-ecgc-times-negative lw-ecgc-negative-times lw-ecgc-zero-times
              lw-ecgc-minus-one lw-ecgc-double-negative lw-ecgc-add-cancel lw-ecgc-double lw-ecgc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-euler-circle-generated-cover-valid
  (implies
   (and (rationalp rate) (< 3 rate) (rationalp height)
       (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
       (rationalp lower) (<= 0 lower) (rationalp upper) (< lower upper)
       (rationalp scale) (< upper scale)
       (rationalp cutoff-square) (< (* scale scale) cutoff-square) (< cutoff-square 1) (natp target) (rationalp error) (< 0 error) (rationalp factor-error) (< 0 factor-error))
   (let ((data (lw-euler-circle-generated-cover rate height outer-radius target error factor-error lower upper scale cutoff-square)))
     (and (rationalp (car data))
          (< (* outer-radius lower) (car data))
          (< (car data) (* outer-radius upper))
          (lw-euler-circle-coverp (cons rate height) (car data) (cadr data) (caddr data))
          (lw-euler-value-clearance-check rate height (lw-euler-zeta-clearance-request rate height)))))
  :hints (("Goal"
           :use (lw-ecgc-request-data lw-euler-zeta-clearance-check
                 (:instance lw-euler-circle-uniform-radius-data
                   (lower (car (lw-euler-circle-pole-band rate height outer-radius lower upper))) (upper (cdr (lw-euler-circle-pole-band rate height outer-radius lower upper))) (error (min error (lw-euler-circle-uniform-approximation-limit rate height outer-radius (car (lw-euler-circle-pole-band rate height outer-radius lower upper)) (cdr (lw-euler-circle-pole-band rate height outer-radius lower upper)) scale cutoff-square))) (factor-error (min factor-error (lw-euler-circle-uniform-approximation-limit rate height outer-radius (car (lw-euler-circle-pole-band rate height outer-radius lower upper)) (cdr (lw-euler-circle-pole-band rate height outer-radius lower upper)) scale cutoff-square))))
                 (:instance lw-euler-circle-pole-band-separation (radius (car (lw-euler-circle-bounded-radius rate height outer-radius target (min error (lw-euler-circle-uniform-approximation-limit rate height outer-radius (car (lw-euler-circle-pole-band rate height outer-radius lower upper)) (cdr (lw-euler-circle-pole-band rate height outer-radius lower upper)) scale cutoff-square)) (min factor-error (lw-euler-circle-uniform-approximation-limit rate height outer-radius (car (lw-euler-circle-pole-band rate height outer-radius lower upper)) (cdr (lw-euler-circle-pole-band rate height outer-radius lower upper)) scale cutoff-square)) (car (lw-euler-circle-pole-band rate height outer-radius lower upper)) (cdr (lw-euler-circle-pole-band rate height outer-radius lower upper)) cutoff-square))))
                 (:instance lw-euler-circle-anchored-grid-valid
                   (lower (car (lw-euler-circle-pole-band rate height outer-radius lower upper))) (upper (cdr (lw-euler-circle-pole-band rate height outer-radius lower upper))) (error (min error (lw-euler-circle-uniform-approximation-limit rate height outer-radius (car (lw-euler-circle-pole-band rate height outer-radius lower upper)) (cdr (lw-euler-circle-pole-band rate height outer-radius lower upper)) scale cutoff-square))) (factor-error (min factor-error (lw-euler-circle-uniform-approximation-limit rate height outer-radius (car (lw-euler-circle-pole-band rate height outer-radius lower upper)) (cdr (lw-euler-circle-pole-band rate height outer-radius lower upper)) scale cutoff-square))) (gap (lw-euler-circle-pole-gap outer-radius (lw-euler-circle-pole-band rate height outer-radius lower upper))))
                 (:instance lw-ecgc-positive-product (a (- (car (lw-euler-circle-bounded-radius rate height outer-radius target (min error (lw-euler-circle-uniform-approximation-limit rate height outer-radius (car (lw-euler-circle-pole-band rate height outer-radius lower upper)) (cdr (lw-euler-circle-pole-band rate height outer-radius lower upper)) scale cutoff-square)) (min factor-error (lw-euler-circle-uniform-approximation-limit rate height outer-radius (car (lw-euler-circle-pole-band rate height outer-radius lower upper)) (cdr (lw-euler-circle-pole-band rate height outer-radius lower upper)) scale cutoff-square)) (car (lw-euler-circle-pole-band rate height outer-radius lower upper)) (cdr (lw-euler-circle-pole-band rate height outer-radius lower upper)) cutoff-square)) lower)) (b outer-radius))
                 (:instance lw-ecgc-positive-product (a (- upper (car (lw-euler-circle-bounded-radius rate height outer-radius target (min error (lw-euler-circle-uniform-approximation-limit rate height outer-radius (car (lw-euler-circle-pole-band rate height outer-radius lower upper)) (cdr (lw-euler-circle-pole-band rate height outer-radius lower upper)) scale cutoff-square)) (min factor-error (lw-euler-circle-uniform-approximation-limit rate height outer-radius (car (lw-euler-circle-pole-band rate height outer-radius lower upper)) (cdr (lw-euler-circle-pole-band rate height outer-radius lower upper)) scale cutoff-square)) (car (lw-euler-circle-pole-band rate height outer-radius lower upper)) (cdr (lw-euler-circle-pole-band rate height outer-radius lower upper)) cutoff-square)))) (b outer-radius)))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-circle-generated-cover
              lw-ecgc-left-commutes lw-ecgc-left-distributes lw-ecgc-fold-constants
              lw-ecgc-times-negative lw-ecgc-negative-times lw-ecgc-zero-times
              lw-ecgc-minus-one lw-ecgc-double-negative lw-ecgc-add-cancel lw-ecgc-double lw-ecgc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
