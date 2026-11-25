(in-package "ACL2")

(include-book "circle-factor-reflection")

; Write each reflected model factor as c*(1-a*z). The common disk
; bound on a*z yields one geometric convergence rate for its logarithm.

(local (defthm lw-crfn-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-crfn-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-crfn-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-crfn-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-crfn-times-negative (a b) (b a)))
                 :in-theory (disable lw-crfn-times-negative)))))

(local (defthm lw-crfn-zero-times (equal (* 0 a) 0)))

(local (defthm lw-crfn-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-crfn-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-crfn-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-crfn-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-crfn-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-crfn-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-crfn-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-crfn-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defun lw-circle-reflected-factor-normalization (root cutoff-square)
  (if (<= (lw-complex-norm-square root) cutoff-square)
      (cons 1 0)
    (lw-complex-scale -1 root)))

(defun lw-circle-reflected-factor-parameter (root cutoff-square)
  (if (<= (lw-complex-norm-square root) cutoff-square)
      (lw-complex-conjugate root)
    (lw-complex-reciprocal root)))

(defun lw-circle-reflected-factor-ratio (inner-radius cutoff-square)
  (* 1/2 (+ 1 (/ (* inner-radius inner-radius) cutoff-square))))

(local
 (defthm lw-crfn-zero-norm
   (equal (lw-complex-norm-square (cons 0 0)) 0)
   :hints (("Goal" :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complex-norm-square
              lw-crfn-left-commutes lw-crfn-left-distributes lw-crfn-fold-constants
              lw-crfn-times-negative lw-crfn-negative-times lw-crfn-zero-times
              lw-crfn-minus-one lw-crfn-double-negative lw-crfn-add-cancel lw-crfn-double lw-crfn-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))))

(local
 (defthm lw-crfn-conjugate-norm
   (implies (lw-complexp root)
            (equal (lw-complex-norm-square (lw-complex-conjugate root))
                   (lw-complex-norm-square root)))
   :hints (("Goal" :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complexp lw-complex-conjugate lw-complex-norm-square
              lw-crfn-left-commutes lw-crfn-left-distributes lw-crfn-fold-constants
              lw-crfn-times-negative lw-crfn-negative-times lw-crfn-zero-times
              lw-crfn-minus-one lw-crfn-double-negative lw-crfn-add-cancel lw-crfn-double lw-crfn-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))))

(local
 (defthm lw-crfn-cutoff-reciprocal
   (implies (and (rationalp cutoff-square) (< 0 cutoff-square) (< cutoff-square 1))
            (<= cutoff-square (/ cutoff-square)))
   :hints (("Goal"
            :use ((:instance lw-reciprocal-antitone (left cutoff-square) (right 1)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)

              lw-crfn-left-commutes lw-crfn-left-distributes lw-crfn-fold-constants
              lw-crfn-times-negative lw-crfn-negative-times lw-crfn-zero-times
              lw-crfn-minus-one lw-crfn-double-negative lw-crfn-add-cancel lw-crfn-double lw-crfn-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-circle-reflected-factor-parameter-data
  (implies (and (lw-complexp root) (rationalp cutoff-square)
                (< 0 cutoff-square) (< cutoff-square 1))
           (and (lw-complexp (lw-circle-reflected-factor-parameter root cutoff-square))
                (<= (lw-complex-norm-square (lw-circle-reflected-factor-parameter root cutoff-square)) (/ cutoff-square))))
  :hints (("Goal"
           :use (lw-crfn-cutoff-reciprocal
                 (:instance lw-complex-norm-square-valid (point root))
                 (:instance lw-complex-conjugate-rational (point root))
                 (:instance lw-complex-reciprocal-rational (point root))
                 (:instance lw-complex-norm-square-reciprocal (point root))
                 (:instance lw-reciprocal-antitone (left cutoff-square) (right (lw-complex-norm-square root))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-reflected-factor-parameter lw-crfn-conjugate-norm lw-crfn-zero-norm
              lw-crfn-left-commutes lw-crfn-left-distributes lw-crfn-fold-constants
              lw-crfn-times-negative lw-crfn-negative-times lw-crfn-zero-times
              lw-crfn-minus-one lw-crfn-double-negative lw-crfn-add-cancel lw-crfn-double lw-crfn-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm lw-crfn-argument-budget
   (implies (and (rationalp inner-radius) (< 0 inner-radius)
                 (rationalp cutoff-square) (< (* inner-radius inner-radius) cutoff-square)
                 (rationalp a-square) (<= 0 a-square) (<= a-square (/ cutoff-square))
                 (rationalp point-square) (<= 0 point-square)
                 (<= point-square (* inner-radius inner-radius)))
            (let ((ratio (lw-circle-reflected-factor-ratio inner-radius cutoff-square)))
              (and (rationalp ratio) (< 0 ratio) (< ratio 1)
                   (<= (* a-square point-square) (* ratio ratio)))))
   :hints (("Goal"
            :use ((:instance lw-reciprocal-positive (value cutoff-square))
                  (:instance lw-crfn-multiply-order (a a-square) (b (/ cutoff-square)) (factor point-square))
                  (:instance lw-crfn-multiply-order
                    (a point-square) (b (* inner-radius inner-radius)) (factor (/ cutoff-square)))
                  (:instance lw-crfn-positive-product (a inner-radius) (b inner-radius))
                  (:instance lw-crfn-positive-product (a (* inner-radius inner-radius)) (b (/ cutoff-square)))
                  (:instance lw-crfn-positive-product
                    (a (- cutoff-square (* inner-radius inner-radius))) (b (/ cutoff-square)))
                  (:instance lw-crfn-positive-product
                    (a (- 1 (/ (* inner-radius inner-radius) cutoff-square)))
                    (b (- 1 (/ (* inner-radius inner-radius) cutoff-square))))
                  (:instance inverse-of-* (x cutoff-square)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-reflected-factor-ratio
              lw-crfn-left-commutes lw-crfn-left-distributes lw-crfn-fold-constants
              lw-crfn-times-negative lw-crfn-negative-times lw-crfn-zero-times
              lw-crfn-minus-one lw-crfn-double-negative lw-crfn-add-cancel lw-crfn-double lw-crfn-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :nonlinearp nil :do-not-induct t))
   :rule-classes nil))

(defthm lw-circle-reflected-factor-argument-disk
  (implies (and (lw-complexp root) (rationalp inner-radius) (< 0 inner-radius)
                (rationalp cutoff-square) (< (* inner-radius inner-radius) cutoff-square) (< cutoff-square 1)
                (lw-complex-diskp point inner-radius))
           (let ((ratio (lw-circle-reflected-factor-ratio inner-radius cutoff-square)))
             (and (rationalp ratio) (< 0 ratio) (< ratio 1)
                  (lw-complex-diskp (lw-complex-mul (lw-circle-reflected-factor-parameter root cutoff-square) point) ratio))))
  :hints (("Goal"
           :use (lw-circle-reflected-factor-parameter-data
                 (:instance lw-complex-disk-data (radius inner-radius))
                 (:instance lw-complex-disk-norm-square (radius inner-radius))
                 (:instance lw-crfn-positive-product (a inner-radius) (b inner-radius))
                 (:instance lw-complex-norm-square-valid (point (lw-circle-reflected-factor-parameter root cutoff-square)))
                 (:instance lw-complex-norm-square-valid)
                 (:instance lw-complex-ring-rational (left (lw-circle-reflected-factor-parameter root cutoff-square)) (right point))
                 (:instance lw-complex-norm-square-product (left (lw-circle-reflected-factor-parameter root cutoff-square)) (right point))
                 (:instance lw-crfn-argument-budget (a-square (lw-complex-norm-square (lw-circle-reflected-factor-parameter root cutoff-square))) (point-square (lw-complex-norm-square point)))
                 (:instance lw-complex-disk-norm-square (point (lw-complex-mul (lw-circle-reflected-factor-parameter root cutoff-square) point)) (radius (lw-circle-reflected-factor-ratio inner-radius cutoff-square))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)

              lw-crfn-left-commutes lw-crfn-left-distributes lw-crfn-fold-constants
              lw-crfn-times-negative lw-crfn-negative-times lw-crfn-zero-times
              lw-crfn-minus-one lw-crfn-double-negative lw-crfn-add-cancel lw-crfn-double lw-crfn-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm lw-crfn-signed-identities
   (implies (and (lw-complexp root) (lw-complexp point))
            (and (equal (lw-complex-mul (lw-complex-scale -1 root) point)
                        (lw-complex-scale -1 (lw-complex-mul root point)))
                 (equal (lw-complex-sub (lw-complex-scale -1 root) (lw-complex-scale -1 point))
                        (lw-complex-sub point root))
                 (equal (lw-complex-sub (cons 1 0) point)
                        (lw-complex-add (cons 1 0) (lw-complex-scale -1 point)))))
   :hints (("Goal" :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complexp lw-complex-add lw-complex-sub lw-complex-scale lw-complex-mul
              lw-crfn-left-commutes lw-crfn-left-distributes lw-crfn-fold-constants
              lw-crfn-times-negative lw-crfn-negative-times lw-crfn-zero-times
              lw-crfn-minus-one lw-crfn-double-negative lw-crfn-add-cancel lw-crfn-double lw-crfn-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                   :do-not-induct t))))

(local
 (defthm lw-crfn-outside-factor
   (implies (and (lw-complexp root) (not (equal root (cons 0 0))) (lw-complexp point))
            (equal
             (lw-complex-mul
              (lw-complex-scale -1 root)
              (lw-complex-sub (cons 1 0) (lw-complex-mul (lw-complex-reciprocal root) point)))
             (lw-complex-sub point root)))
   :hints (("Goal"
            :use ((:instance lw-complex-reciprocal-inverse (point root))
                  (:instance lw-complex-mul-associative (left root) (middle (lw-complex-reciprocal root)) (right point))
                  (:instance lw-complex-mul-subtract
                    (a (lw-complex-scale -1 root)) (b (cons 1 0))
                    (c (lw-complex-mul (lw-complex-reciprocal root) point))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complex-reciprocal-rational lw-complex-mul-one lw-complex-ring-rational
              lw-complex-scale-rational lw-complex-mul-subtract lw-crfn-signed-identities
              lw-crfn-left-commutes lw-crfn-left-distributes lw-crfn-fold-constants
              lw-crfn-times-negative lw-crfn-negative-times lw-crfn-zero-times
              lw-crfn-minus-one lw-crfn-double-negative lw-crfn-add-cancel lw-crfn-double lw-crfn-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-crfn-negative-norm
   (implies (lw-complexp root)
            (equal (lw-complex-norm-square (lw-complex-scale -1 root))
                   (lw-complex-norm-square root)))
   :hints (("Goal" :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complexp lw-complex-scale lw-complex-norm-square
              lw-crfn-left-commutes lw-crfn-left-distributes lw-crfn-fold-constants
              lw-crfn-times-negative lw-crfn-negative-times lw-crfn-zero-times
              lw-crfn-minus-one lw-crfn-double-negative lw-crfn-add-cancel lw-crfn-double lw-crfn-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                   :do-not-induct t))))

(defthm lw-circle-reflected-factor-normalization-valid
  (implies (and (lw-complexp root) (lw-complexp point)
                (rationalp cutoff-square) (<= 0 cutoff-square))
           (let* ((constant (lw-circle-reflected-factor-normalization root cutoff-square))
                  (parameter (lw-circle-reflected-factor-parameter root cutoff-square))
                  (factor
                    (if (<= (lw-complex-norm-square root) cutoff-square)
                        (lw-circle-reflected-factor-value root point)
                      (lw-complex-sub point root))))
             (and (lw-complexp constant) (not (equal constant (cons 0 0)))
                  (equal factor
                    (lw-complex-mul constant (lw-complex-sub (cons 1 0) (lw-complex-mul parameter point)))))))
  :hints (("Goal"
           :use (lw-crfn-outside-factor lw-crfn-negative-norm
                 (:instance lw-complex-norm-square-valid (point root)))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-reflected-factor-normalization lw-circle-reflected-factor-parameter
              lw-circle-reflected-factor-value lw-circle-reflected-factor-slope lw-crfn-zero-norm
              lw-complex-mul-one lw-complex-conjugate-rational lw-complex-reciprocal-rational
              lw-complex-ring-rational lw-complex-scale-rational lw-crfn-signed-identities
              lw-crfn-left-commutes lw-crfn-left-distributes lw-crfn-fold-constants
              lw-crfn-times-negative lw-crfn-negative-times lw-crfn-zero-times
              lw-crfn-minus-one lw-crfn-double-negative lw-crfn-add-cancel lw-crfn-double lw-crfn-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
