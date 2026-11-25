(in-package "ACL2")

(include-book "circle-finite-radius-selection")
(include-book "circle-factor-reflection")
(include-book "rpow-continuity")

; Only roots inside the count cutoff consume a quarter-step of separation.

(local (defthm lw-cbr-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-cbr-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-cbr-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-cbr-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-cbr-times-negative (a b) (b a)))
                 :in-theory (disable lw-cbr-times-negative)))))

(local (defthm lw-cbr-zero-times (equal (* 0 a) 0)))

(local (defthm lw-cbr-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-cbr-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-cbr-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-cbr-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-cbr-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-cbr-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-cbr-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cbr-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local
 (defthm lw-cbr-square-order
   (implies (and (rationalp a) (rationalp b) (<= 0 a) (<= a b))
            (<= (* a a) (* b b)))
   :hints (("Goal"
            :use ((:instance lw-cbr-multiply-order (factor a))
                  (:instance lw-cbr-multiply-order (factor b)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)

              lw-cbr-left-commutes lw-cbr-left-distributes lw-cbr-fold-constants
              lw-cbr-times-negative lw-cbr-negative-times lw-cbr-zero-times
              lw-cbr-minus-one lw-cbr-double-negative lw-cbr-add-cancel lw-cbr-double lw-cbr-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))
   :rule-classes nil))

(defun lw-circle-inner-factor-roots (roots cutoff-square)
  (declare (xargs :measure (acl2-count roots)
                  :hints (("Goal" :in-theory (theory 'ground-zero)))))
  (if (endp roots)
      nil
    (let ((tail (lw-circle-inner-factor-roots (cdr roots) cutoff-square)))
      (if (<= (lw-complex-norm-square (car roots)) cutoff-square)
          (cons (car roots) tail)
        tail))))

(defthm lw-circle-inner-factor-roots-data
  (implies (lw-ray-pointsp roots)
           (and (lw-ray-pointsp (lw-circle-inner-factor-roots roots cutoff-square))
                (equal (len (lw-circle-inner-factor-roots roots cutoff-square))
                       (lw-circle-inner-factor-count roots cutoff-square))))
  :hints (("Goal"
           :induct (lw-circle-inner-factor-roots roots cutoff-square)
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              (:induction lw-circle-inner-factor-roots)
              lw-circle-inner-factor-roots lw-circle-inner-factor-count
              (:type-prescription lw-circle-inner-factor-count) lw-ray-pointsp len endp
              lw-cbr-left-commutes lw-cbr-left-distributes lw-cbr-fold-constants
              lw-cbr-times-negative lw-cbr-negative-times lw-cbr-zero-times
              lw-cbr-minus-one lw-cbr-double-negative lw-cbr-add-cancel lw-cbr-double lw-cbr-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not '(generalize fertilize))))

(local
 (defthm lw-cbr-length-natural
   (natp (len roots))
   :hints (("Goal" :induct (len roots) :in-theory (enable len)))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm lw-cbr-quarter-branch-width
   (implies (and (rationalp lower) (rationalp upper))
            (equal (- (cdr (lw-circle-radius-branch square lower upper))
                      (car (lw-circle-radius-branch square lower upper)))
                   (* 1/4 (- upper lower))))
   :hints (("Goal" :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-radius-branch
              lw-cbr-left-commutes lw-cbr-left-distributes lw-cbr-fold-constants
              lw-cbr-times-negative lw-cbr-negative-times lw-cbr-zero-times
              lw-cbr-minus-one lw-cbr-double-negative lw-cbr-add-cancel lw-cbr-double lw-cbr-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                   :do-not-induct t))))

(local
 (defthm lw-cbr-quarter-branch-rational
   (implies (and (rationalp lower) (rationalp upper))
            (and (rationalp (car (lw-circle-radius-branch square lower upper)))
                 (rationalp (cdr (lw-circle-radius-branch square lower upper)))))
   :hints (("Goal" :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-radius-branch
              lw-cbr-left-commutes lw-cbr-left-distributes lw-cbr-fold-constants
              lw-cbr-times-negative lw-cbr-negative-times lw-cbr-zero-times
              lw-cbr-minus-one lw-cbr-double-negative lw-cbr-add-cancel lw-cbr-double lw-cbr-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                   :do-not-induct t))))

(local
 (defthm lw-cbr-power-successor
   (implies (natp n)
            (equal (lw-rational-power 1/4 (+ 1 n))
                   (* 1/4 (lw-rational-power 1/4 n))))
   :hints (("Goal" :expand ((lw-rational-power 1/4 (+ 1 n)))
                   :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-rational-power
              lw-cbr-left-commutes lw-cbr-left-distributes lw-cbr-fold-constants
              lw-cbr-times-negative lw-cbr-negative-times lw-cbr-zero-times
              lw-cbr-minus-one lw-cbr-double-negative lw-cbr-add-cancel lw-cbr-double lw-cbr-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                   :do-not-induct t))))

(defthm lw-circle-finite-radius-bracket-width
  (implies (and (rationalp lower) (rationalp upper))
           (let ((bracket (lw-circle-finite-radius-bracket roots lower upper)))
             (equal (- (cdr bracket) (car bracket))
                    (* (- upper lower) (lw-rational-power 1/4 (len roots))))))
  :hints (("Goal"
           :induct (lw-circle-finite-radius-bracket roots lower upper)
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              (:induction lw-circle-finite-radius-bracket)
              lw-circle-finite-radius-bracket lw-cbr-quarter-branch-width lw-cbr-quarter-branch-rational
              lw-cbr-power-successor lw-cbr-length-natural (:executable-counterpart lw-rational-power)
              lw-rational-power-rational len endp
              lw-cbr-left-commutes lw-cbr-left-distributes lw-cbr-fold-constants
              lw-cbr-times-negative lw-cbr-negative-times lw-cbr-zero-times
              lw-cbr-minus-one lw-cbr-double-negative lw-cbr-add-cancel lw-cbr-double lw-cbr-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not '(generalize fertilize)))
  :rule-classes nil)

(defun lw-circle-bounded-radius-gap (lower upper cutoff-square budget)
  (let ((width (* (- upper lower) (lw-rational-power 1/4 budget))))
    (min (* width width) (- cutoff-square (* upper upper)))))

(defun lw-circle-bounded-radius (roots lower upper cutoff-square budget)
  (let ((bracket (lw-circle-finite-radius-bracket (lw-circle-inner-factor-roots roots cutoff-square) lower upper)))
    (cons (lw-circle-finite-radius bracket) (lw-circle-bounded-radius-gap lower upper cutoff-square budget))))

(local
 (defthm lw-cbr-quarter-power-order
   (implies (and (natp length) (natp budget) (<= length budget))
            (<= (lw-rational-power 1/4 budget) (lw-rational-power 1/4 length)))
   :hints (("Goal"
            :use ((:instance lw-rational-power-add-exponents
                    (base 1/4) (left length) (right (- budget length)))
                  (:instance lw-rational-power-rational (base 1/4) (exponent length))
                  (:instance lw-rational-power-rational (base 1/4) (exponent (- budget length)))
                  (:instance lw-rational-power-nonnegative (base 1/4) (exponent length))
                  (:instance lw-rational-power-monotone-base (left 1/4) (right 1) (exponent (- budget length)))
                  (:instance lw-cbr-multiply-order
                    (a (lw-rational-power 1/4 (- budget length))) (b 1)
                    (factor (lw-rational-power 1/4 length))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-rational-power-one
              lw-cbr-left-commutes lw-cbr-left-distributes lw-cbr-fold-constants
              lw-cbr-times-negative lw-cbr-negative-times lw-cbr-zero-times
              lw-cbr-minus-one lw-cbr-double-negative lw-cbr-add-cancel lw-cbr-double lw-cbr-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-cbr-gap-data
   (implies (and (rationalp lower) (<= 0 lower) (rationalp upper) (< lower upper)
                 (rationalp cutoff-square) (< (* upper upper) cutoff-square)
                 (natp length) (natp budget) (<= length budget)
                 (rationalp width) (equal width (* (- upper lower) (lw-rational-power 1/4 length))))
            (and (rationalp (lw-circle-bounded-radius-gap lower upper cutoff-square budget)) (< 0 (lw-circle-bounded-radius-gap lower upper cutoff-square budget))
                 (<= (lw-circle-bounded-radius-gap lower upper cutoff-square budget) (* width width))
                 (<= (+ (* upper upper) (lw-circle-bounded-radius-gap lower upper cutoff-square budget)) cutoff-square)))
   :hints (("Goal"
            :use (lw-cbr-quarter-power-order
                  (:instance lw-rational-power-rational (base 1/4) (exponent budget))
                  (:instance lw-rational-power-rational (base 1/4) (exponent length))
                  (:instance lw-rational-power-positive (base 1/4) (exponent budget))
                  (:instance lw-cbr-positive-product (a (- upper lower)) (b (lw-rational-power 1/4 budget)))
                  (:instance lw-cbr-positive-product
                    (a (* (- upper lower) (lw-rational-power 1/4 budget)))
                    (b (* (- upper lower) (lw-rational-power 1/4 budget))))
                  (:instance lw-cbr-multiply-order
                    (a (lw-rational-power 1/4 budget)) (b (lw-rational-power 1/4 length)) (factor (- upper lower)))
                  (:instance lw-cbr-square-order
                    (a (* (- upper lower) (lw-rational-power 1/4 budget))) (b width)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-bounded-radius-gap min
              lw-cbr-left-commutes lw-cbr-left-distributes lw-cbr-fold-constants
              lw-cbr-times-negative lw-cbr-negative-times lw-cbr-zero-times
              lw-cbr-minus-one lw-cbr-double-negative lw-cbr-add-cancel lw-cbr-double lw-cbr-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t :nonlinearp nil))
   :rule-classes nil))

(local
 (defthm lw-cbr-filter-clear
   (implies (and (lw-ray-pointsp roots)
                 (rationalp radius) (rationalp cutoff-square)
                 (rationalp gap) (rationalp old-gap) (<= gap old-gap)
                 (<= (+ (* radius radius) gap) cutoff-square)
                 (lw-circle-radial-bracket-clear (lw-circle-inner-factor-roots roots cutoff-square) radius radius old-gap))
            (lw-circle-radial-bracket-clear roots radius radius gap))
   :hints (("Goal"
            :induct (lw-circle-inner-factor-roots roots cutoff-square)
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              (:induction lw-circle-inner-factor-roots)
              lw-circle-inner-factor-roots lw-circle-radial-bracket-clear lw-ray-pointsp endp
              lw-complex-norm-square-valid
              lw-cbr-left-commutes lw-cbr-left-distributes lw-cbr-fold-constants
              lw-cbr-times-negative lw-cbr-negative-times lw-cbr-zero-times
              lw-cbr-minus-one lw-cbr-double-negative lw-cbr-add-cancel lw-cbr-double lw-cbr-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not '(generalize fertilize)))
   :rule-classes nil))

(defthm lw-circle-bounded-radius-valid
  (implies (and (lw-ray-pointsp roots)
                (rationalp lower) (<= 0 lower) (rationalp upper) (< lower upper)
                (rationalp cutoff-square) (< (* upper upper) cutoff-square)
                (natp budget) (<= (lw-circle-inner-factor-count roots cutoff-square) budget))
           (let* ((data (lw-circle-bounded-radius roots lower upper cutoff-square budget))
                  (radius (car data))
                  (gap (cdr data)))
             (and (rationalp radius) (< lower radius) (< radius upper)
                  (rationalp gap) (< 0 gap)
                  (lw-circle-radial-bracket-clear roots radius radius gap))))
  :hints (("Goal"
           :use (lw-circle-inner-factor-roots-data
                 (:instance lw-circle-finite-radius-bracket-width (roots (lw-circle-inner-factor-roots roots cutoff-square)))
                 (:instance lw-circle-finite-separated-radius (roots (lw-circle-inner-factor-roots roots cutoff-square)))
                 (:instance lw-cbr-gap-data
                   (length (len (lw-circle-inner-factor-roots roots cutoff-square))) (width (- (cdr (lw-circle-finite-radius-bracket (lw-circle-inner-factor-roots roots cutoff-square) lower upper)) (car (lw-circle-finite-radius-bracket (lw-circle-inner-factor-roots roots cutoff-square) lower upper)))))
                 (:instance lw-cbr-square-order (a (lw-circle-finite-radius (lw-circle-finite-radius-bracket (lw-circle-inner-factor-roots roots cutoff-square) lower upper))) (b upper))
                 (:instance lw-cbr-filter-clear (radius (lw-circle-finite-radius (lw-circle-finite-radius-bracket (lw-circle-inner-factor-roots roots cutoff-square) lower upper))) (gap (lw-circle-bounded-radius-gap lower upper cutoff-square budget)) (old-gap (lw-circle-finite-radius-gap (lw-circle-finite-radius-bracket (lw-circle-inner-factor-roots roots cutoff-square) lower upper)))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-bounded-radius lw-circle-finite-radius-gap lw-cbr-length-natural lw-rational-power-rational
              lw-cbr-left-commutes lw-cbr-left-distributes lw-cbr-fold-constants
              lw-cbr-times-negative lw-cbr-negative-times lw-cbr-zero-times
              lw-cbr-minus-one lw-cbr-double-negative lw-cbr-add-cancel lw-cbr-double lw-cbr-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
