(in-package "ACL2")

(include-book "circle-finite-radius-selection")
(include-book "complex-exp")

; Reserve a subinterval before choosing any polynomial or factor precision.

(local (defthm lw-ecpb-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ecpb-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ecpb-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ecpb-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ecpb-times-negative (a b) (b a)))
                 :in-theory (disable lw-ecpb-times-negative)))))

(local (defthm lw-ecpb-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ecpb-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ecpb-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ecpb-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ecpb-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ecpb-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ecpb-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ecpb-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecpb-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecpb-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ecpb-left-commutes)))))

(local
 (defthm lw-ecpb-square-order
   (implies (and (rationalp a) (rationalp b) (<= 0 a) (<= a b))
            (<= (* a a) (* b b)))
   :hints (("Goal"
            :use ((:instance lw-ecpb-multiply-order (factor a))
                  (:instance lw-ecpb-multiply-order (factor b)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)

              lw-ecpb-left-commutes lw-ecpb-left-distributes lw-ecpb-fold-constants
              lw-ecpb-times-negative lw-ecpb-negative-times lw-ecpb-zero-times
              lw-ecpb-minus-one lw-ecpb-double-negative lw-ecpb-add-cancel lw-ecpb-double lw-ecpb-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))
   :rule-classes nil))

(defun lw-euler-circle-pole-band (rate height outer-radius lower upper)
  (lw-circle-finite-radius-bracket (list (lw-complex-scale (/ outer-radius) (lw-complex-sub (cons 1 0) (cons rate height)))) lower upper))

(defun lw-euler-circle-pole-gap (outer-radius band)
  (* outer-radius outer-radius (lw-circle-finite-radius-gap band)))

(local
 (defthm lw-ecpb-norm-scale
   (implies (and (rationalp factor) (lw-complexp point))
            (equal (lw-complex-norm-square (lw-complex-scale factor point))
                   (* factor factor (lw-complex-norm-square point))))
   :hints (("Goal" :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complex-norm-square lw-complex-scale lw-complexp
              lw-ecpb-left-commutes lw-ecpb-left-distributes lw-ecpb-fold-constants
              lw-ecpb-times-negative lw-ecpb-negative-times lw-ecpb-zero-times
              lw-ecpb-minus-one lw-ecpb-double-negative lw-ecpb-add-cancel lw-ecpb-double lw-ecpb-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                   :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-ecpb-physical-norm
   (implies (and (rationalp scale) (< 0 scale) (lw-complexp point))
            (equal (* scale scale (lw-complex-norm-square (lw-complex-scale (/ scale) point)))
                   (lw-complex-norm-square point)))
   :hints (("Goal"
            :use ((:instance lw-complex-scale-rational (factor (/ scale)))
                  (:instance lw-complex-scale-compose (left scale) (right (/ scale)))
                  (:instance inverse-of-* (x scale))
                  (:instance lw-ecpb-norm-scale (factor scale) (point (lw-complex-scale (/ scale) point))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complex-scale-one
              lw-ecpb-left-commutes lw-ecpb-left-distributes lw-ecpb-fold-constants
              lw-ecpb-times-negative lw-ecpb-negative-times lw-ecpb-zero-times
              lw-ecpb-minus-one lw-ecpb-double-negative lw-ecpb-add-cancel lw-ecpb-double lw-ecpb-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-euler-circle-pole-band-data
  (implies
   (and (rationalp rate) (rationalp height) (rationalp outer-radius) (< 0 outer-radius)
       (rationalp lower) (<= 0 lower) (rationalp upper) (< lower upper))
   (and (rationalp (car (lw-euler-circle-pole-band rate height outer-radius lower upper))) (rationalp (cdr (lw-euler-circle-pole-band rate height outer-radius lower upper)))
        (<= lower (car (lw-euler-circle-pole-band rate height outer-radius lower upper))) (< (car (lw-euler-circle-pole-band rate height outer-radius lower upper)) (cdr (lw-euler-circle-pole-band rate height outer-radius lower upper))) (<= (cdr (lw-euler-circle-pole-band rate height outer-radius lower upper)) upper)
        (rationalp (lw-circle-finite-radius-gap (lw-euler-circle-pole-band rate height outer-radius lower upper))) (< 0 (lw-circle-finite-radius-gap (lw-euler-circle-pole-band rate height outer-radius lower upper)))
        (rationalp (lw-euler-circle-pole-gap outer-radius (lw-euler-circle-pole-band rate height outer-radius lower upper))) (< 0 (lw-euler-circle-pole-gap outer-radius (lw-euler-circle-pole-band rate height outer-radius lower upper)))
        (lw-circle-radial-bracket-clear (list (lw-complex-scale (/ outer-radius) (lw-complex-sub (cons 1 0) (cons rate height)))) (car (lw-euler-circle-pole-band rate height outer-radius lower upper)) (cdr (lw-euler-circle-pole-band rate height outer-radius lower upper)) (lw-circle-finite-radius-gap (lw-euler-circle-pole-band rate height outer-radius lower upper)))))
  :hints (("Goal"
           :use ((:instance lw-complex-ring-rational (left (cons 1 0)) (right (cons rate height)))
                 (:instance lw-complex-scale-rational (factor (/ outer-radius)) (point (lw-complex-sub (cons 1 0) (cons rate height))))
                 (:instance lw-circle-finite-radius-bracket-data (roots (list (lw-complex-scale (/ outer-radius) (lw-complex-sub (cons 1 0) (cons rate height))))))
                 (:instance lw-ecpb-positive-product (a outer-radius) (b outer-radius))
                 (:instance lw-ecpb-positive-product
                   (a (- (cdr (lw-euler-circle-pole-band rate height outer-radius lower upper)) (car (lw-euler-circle-pole-band rate height outer-radius lower upper)))) (b (- (cdr (lw-euler-circle-pole-band rate height outer-radius lower upper)) (car (lw-euler-circle-pole-band rate height outer-radius lower upper)))))
                 (:instance lw-ecpb-positive-product (a (* outer-radius outer-radius)) (b (lw-circle-finite-radius-gap (lw-euler-circle-pole-band rate height outer-radius lower upper)))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-circle-pole-band lw-euler-circle-pole-gap lw-circle-finite-radius-gap
              lw-ray-pointsp lw-complexp endp
              lw-ecpb-left-commutes lw-ecpb-left-distributes lw-ecpb-fold-constants
              lw-ecpb-times-negative lw-ecpb-negative-times lw-ecpb-zero-times
              lw-ecpb-minus-one lw-ecpb-double-negative lw-ecpb-add-cancel lw-ecpb-double lw-ecpb-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm lw-ecpb-band-gap-at-radius
   (implies
    (and (lw-complexp point) (rationalp low) (<= 0 low)
         (rationalp high) (rationalp radius) (<= low radius) (<= radius high)
         (rationalp gap) (lw-circle-radial-bracket-clear (list point) low high gap))
    (or (<= (+ (lw-complex-norm-square point) gap) (* radius radius))
        (<= (+ (* radius radius) gap) (lw-complex-norm-square point))))
   :hints (("Goal"
            :use ((:instance lw-ecpb-square-order (a low) (b radius))
                  (:instance lw-ecpb-square-order (a radius) (b high))
                  lw-complex-norm-square-valid)
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-radial-bracket-clear endp
              lw-ecpb-left-commutes lw-ecpb-left-distributes lw-ecpb-fold-constants
              lw-ecpb-times-negative lw-ecpb-negative-times lw-ecpb-zero-times
              lw-ecpb-minus-one lw-ecpb-double-negative lw-ecpb-add-cancel lw-ecpb-double lw-ecpb-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-euler-circle-pole-band-separation
  (implies
   (and (rationalp rate) (rationalp height) (rationalp outer-radius) (< 0 outer-radius)
       (rationalp lower) (<= 0 lower) (rationalp upper) (< lower upper)
        (rationalp radius) (<= (car (lw-euler-circle-pole-band rate height outer-radius lower upper)) radius) (<= radius (cdr (lw-euler-circle-pole-band rate height outer-radius lower upper))))
   (or (<= (+ (lw-complex-norm-square (lw-complex-sub (cons 1 0) (cons rate height))) (lw-euler-circle-pole-gap outer-radius (lw-euler-circle-pole-band rate height outer-radius lower upper))) (* outer-radius radius outer-radius radius))
       (<= (+ (* outer-radius radius outer-radius radius) (lw-euler-circle-pole-gap outer-radius (lw-euler-circle-pole-band rate height outer-radius lower upper))) (lw-complex-norm-square (lw-complex-sub (cons 1 0) (cons rate height))))))
  :hints (("Goal"
           :use (lw-euler-circle-pole-band-data
                 (:instance lw-complex-ring-rational (left (cons 1 0)) (right (cons rate height)))
                 (:instance lw-complex-scale-rational (factor (/ outer-radius)) (point (lw-complex-sub (cons 1 0) (cons rate height))))
                 (:instance lw-complex-norm-square-valid (point (lw-complex-scale (/ outer-radius) (lw-complex-sub (cons 1 0) (cons rate height)))))
                 (:instance lw-ecpb-physical-norm (scale outer-radius) (point (lw-complex-sub (cons 1 0) (cons rate height))))
                 (:instance lw-ecpb-positive-product (a outer-radius) (b outer-radius))
                 (:instance lw-ecpb-band-gap-at-radius (point (lw-complex-scale (/ outer-radius) (lw-complex-sub (cons 1 0) (cons rate height))))
                   (low (car (lw-euler-circle-pole-band rate height outer-radius lower upper))) (high (cdr (lw-euler-circle-pole-band rate height outer-radius lower upper))) (gap (lw-circle-finite-radius-gap (lw-euler-circle-pole-band rate height outer-radius lower upper))))
                 (:instance lw-ecpb-multiply-order (a (+ (lw-complex-norm-square (lw-complex-scale (/ outer-radius) (lw-complex-sub (cons 1 0) (cons rate height)))) (lw-circle-finite-radius-gap (lw-euler-circle-pole-band rate height outer-radius lower upper)))) (b (* radius radius)) (factor (* outer-radius outer-radius)))
                 (:instance lw-ecpb-multiply-order (a (+ (* radius radius) (lw-circle-finite-radius-gap (lw-euler-circle-pole-band rate height outer-radius lower upper)))) (b (lw-complex-norm-square (lw-complex-scale (/ outer-radius) (lw-complex-sub (cons 1 0) (cons rate height))))) (factor (* outer-radius outer-radius))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-circle-pole-gap lw-complexp
              lw-ecpb-left-commutes lw-ecpb-left-distributes lw-ecpb-fold-constants
              lw-ecpb-times-negative lw-ecpb-negative-times lw-ecpb-zero-times
              lw-ecpb-minus-one lw-ecpb-double-negative lw-ecpb-add-cancel lw-ecpb-double lw-ecpb-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
