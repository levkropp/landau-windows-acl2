(in-package "ACL2")

(include-book "circle-radial-clearance")

; A circle strictly inside an Euler disk leaves room for equal local outer disks.

(local (defthm lw-ecrg-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ecrg-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ecrg-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ecrg-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ecrg-times-negative (a b) (b a)))
                 :in-theory (disable lw-ecrg-times-negative)))))

(local (defthm lw-ecrg-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ecrg-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ecrg-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ecrg-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ecrg-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ecrg-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ecrg-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ecrg-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecrg-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecrg-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ecrg-left-commutes)))))

(defun lw-euler-circle-local-outer (radius outer-radius)
  (* 1/2 (- outer-radius radius)))

(local
 (defthm lw-ecrg-point-translation
   (implies (and (rationalp rate) (rationalp height) (lw-complexp point))
            (and (lw-complexp (lw-complex-sub point (cons rate height)))
                 (equal (car (lw-complex-sub point (cons rate height))) (- (car point) rate))
                 (equal (lw-complex-sub point (cons 1 0)) (lw-complex-sub (lw-complex-sub point (cons rate height)) (lw-complex-sub (cons 1 0) (cons rate height))))))
   :hints (("Goal" :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complexp lw-complex-sub
              lw-ecrg-left-commutes lw-ecrg-left-distributes lw-ecrg-fold-constants
              lw-ecrg-times-negative lw-ecrg-negative-times lw-ecrg-zero-times
              lw-ecrg-minus-one lw-ecrg-double-negative lw-ecrg-add-cancel lw-ecrg-double lw-ecrg-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                   :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-ecrg-l1-lower
   (implies (and (lw-complexp point) (rationalp lower) (< 0 lower)
                 (< (* lower lower) (lw-complex-norm-square point)))
            (< lower (lw-complex-l1 point)))
   :hints (("Goal"
            :cases ((<= (lw-complex-l1 point) lower))
            :use (lw-complex-l1-bound
                  (:instance lw-complex-disk-enlarge (radius (lw-complex-l1 point)) (cap lower))
                  (:instance lw-complex-disk-norm-square (radius lower)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              
              lw-ecrg-left-commutes lw-ecrg-left-distributes lw-ecrg-fold-constants
              lw-ecrg-times-negative lw-ecrg-negative-times lw-ecrg-zero-times
              lw-ecrg-minus-one lw-ecrg-double-negative lw-ecrg-add-cancel lw-ecrg-double lw-ecrg-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-ecrg-origin-clearance
   (implies (and (rationalp rate) (rationalp height)
       (rationalp radius) (< 0 radius)
       (rationalp outer-radius) (< radius outer-radius) (< outer-radius rate) (lw-complexp point) (equal (lw-complex-norm-square (lw-complex-sub point (cons rate height))) (* radius radius)))
            (and (rationalp (lw-euler-circle-local-outer radius outer-radius)) (< 0 (lw-euler-circle-local-outer radius outer-radius)) (< (lw-euler-circle-local-outer radius outer-radius) (car point))
                 (<= (+ radius (lw-euler-circle-local-outer radius outer-radius)) outer-radius)
                 (lw-complex-diskp (lw-complex-sub point (cons rate height)) radius)
                 (<= (- rate outer-radius) (lw-complex-l1 point))))
   :hints (("Goal"
            :use (lw-ecrg-point-translation
                  (:instance lw-complex-disk-norm-square (point (lw-complex-sub point (cons rate height))))
                  (:instance lw-complex-disk-coordinates (point (lw-complex-sub point (cons rate height)))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-circle-local-outer lw-complexp lw-complex-l1 abs
              lw-ecrg-left-commutes lw-ecrg-left-distributes lw-ecrg-fold-constants
              lw-ecrg-times-negative lw-ecrg-negative-times lw-ecrg-zero-times
              lw-ecrg-minus-one lw-ecrg-double-negative lw-ecrg-add-cancel lw-ecrg-double lw-ecrg-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-ecrg-pole-clearance
   (implies (and (rationalp rate) (rationalp height)
       (rationalp radius) (< 0 radius)
       (rationalp outer-radius) (< radius outer-radius) (< outer-radius rate) (lw-complexp point) (equal (lw-complex-norm-square (lw-complex-sub point (cons rate height))) (* radius radius)) (rationalp gap) (< 0 gap)
       (or (<= (+ (lw-complex-norm-square (lw-complex-sub (cons 1 0) (cons rate height))) gap) (* radius radius))
           (<= (+ (* radius radius) gap) (lw-complex-norm-square (lw-complex-sub (cons 1 0) (cons rate height))))))
            (and (rationalp (lw-circle-radial-clearance radius gap)) (< 0 (lw-circle-radial-clearance radius gap))
                 (<= (lw-circle-radial-clearance radius gap) (lw-complex-l1 (lw-complex-sub point (cons 1 0))))))
   :hints (("Goal"
            :use (lw-ecrg-point-translation
                  (:instance lw-complex-ring-rational (left (cons 1 0)) (right (cons rate height)))
                  (:instance lw-complex-ring-rational (left point) (right (cons 1 0)))
                  (:instance lw-circle-radial-clearance-valid (point (lw-complex-sub point (cons rate height))) (root (lw-complex-sub (cons 1 0) (cons rate height))))
                  (:instance lw-ecrg-l1-lower (point (lw-complex-sub point (cons 1 0))) (lower (lw-circle-radial-clearance radius gap))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complexp
              lw-ecrg-left-commutes lw-ecrg-left-distributes lw-ecrg-fold-constants
              lw-ecrg-times-negative lw-ecrg-negative-times lw-ecrg-zero-times
              lw-ecrg-minus-one lw-ecrg-double-negative lw-ecrg-add-cancel lw-ecrg-double lw-ecrg-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-euler-circle-regular-point-data
  (implies
   (and (rationalp rate) (rationalp height)
       (rationalp radius) (< 0 radius)
       (rationalp outer-radius) (< radius outer-radius) (< outer-radius rate) (lw-complexp point) (equal (lw-complex-norm-square (lw-complex-sub point (cons rate height))) (* radius radius)) (rationalp gap) (< 0 gap)
       (or (<= (+ (lw-complex-norm-square (lw-complex-sub (cons 1 0) (cons rate height))) gap) (* radius radius))
           (<= (+ (* radius radius) gap) (lw-complex-norm-square (lw-complex-sub (cons 1 0) (cons rate height))))))
   (and (rationalp (lw-euler-circle-local-outer radius outer-radius)) (< 0 (lw-euler-circle-local-outer radius outer-radius)) (< (lw-euler-circle-local-outer radius outer-radius) (car point))
        (<= (+ radius (lw-euler-circle-local-outer radius outer-radius)) outer-radius)
        (lw-complex-diskp (lw-complex-sub point (cons rate height)) radius)
        (<= (- rate outer-radius) (lw-complex-l1 point))
        (rationalp (lw-circle-radial-clearance radius gap)) (< 0 (lw-circle-radial-clearance radius gap))
        (<= (lw-circle-radial-clearance radius gap) (lw-complex-l1 (lw-complex-sub point (cons 1 0))))))
  :hints (("Goal"
           :use (lw-ecrg-origin-clearance lw-ecrg-pole-clearance)
           :in-theory (theory 'minimal-theory)
           :do-not-induct t))
  :rule-classes nil)
