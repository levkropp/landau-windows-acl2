(in-package "ACL2")

(include-book "euler-circle-generated-cover")

; The window reduction works with physical radius bands at real part
; 252. Convert each band to a strict band for the cover constructor.

(local (defthm lw-ewcc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ewcc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ewcc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ewcc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ewcc-times-negative (a b) (b a)))
                 :in-theory (disable lw-ewcc-times-negative)))))

(local (defthm lw-ewcc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ewcc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ewcc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ewcc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ewcc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ewcc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ewcc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ewcc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ewcc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ewcc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ewcc-left-commutes)))))

(local (deftheory lw-ewcc-arithmetic (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-ewcc-left-commutes lw-ewcc-left-distributes lw-ewcc-fold-constants
              lw-ewcc-times-negative lw-ewcc-negative-times lw-ewcc-zero-times
              lw-ewcc-minus-one lw-ewcc-double-negative lw-ewcc-add-cancel lw-ewcc-double lw-ewcc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))

(defun lw-euler-window-circle-cover (height lower upper)
  (let* ((outer (* 1/2 (+ 252 upper)))
         (left (/ lower outer))
         (right (/ upper outer))
         (scale (* 1/2 (+ 1 right)))
         (cutoff-square (* 1/2 (+ 1 (* scale scale)))))
    (lw-euler-circle-generated-cover 252 height outer 0 1 1 left right scale cutoff-square)))

(local
 (defthm lw-ewcc-strict-product
   (implies (and (rationalp a) (rationalp b) (< a b) (rationalp factor) (< 0 factor))
            (< (* a factor) (* b factor)))
   :hints (("Goal" :nonlinearp t))
   :rule-classes nil))

(local
 (defthm lw-ewcc-normalized-bounds
   (implies (and (rationalp lower) (<= 0 lower) (rationalp upper) (< lower upper)
                 (rationalp outer) (< upper outer))
            (and (rationalp (/ lower outer)) (<= 0 (/ lower outer))
                 (rationalp (/ upper outer)) (< (/ lower outer) (/ upper outer))
                 (< (/ upper outer) 1)
                 (equal (* outer (/ lower outer)) lower)
                 (equal (* outer (/ upper outer)) upper)))
   :hints (("Goal"
            :use ((:instance lw-reciprocal-positive (value outer))
                  (:instance lw-ewcc-multiply-order (a 0) (b lower) (factor (/ outer)))
                  (:instance lw-ewcc-strict-product (a lower) (b upper) (factor (/ outer)))
                  (:instance lw-ewcc-strict-product (a upper) (b outer) (factor (/ outer)))
                  (:instance lw-ewcc-inverse-factor (divisor outer) (coefficient lower))
                  (:instance lw-ewcc-inverse-factor (divisor outer) (coefficient upper))
                  (:instance inverse-of-* (x outer)))
            :in-theory (theory 'lw-ewcc-arithmetic)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-ewcc-scale-bounds
   (implies (and (rationalp right) (<= 0 right) (< right 1))
            (let* ((scale (* 1/2 (+ 1 right)))
                   (cutoff-square (* 1/2 (+ 1 (* scale scale)))))
              (and (rationalp scale) (< right scale) (rationalp cutoff-square)
                   (< (* scale scale) cutoff-square) (< cutoff-square 1))))
   :hints (("Goal"
            :use ((:instance lw-ewcc-strict-product (a (* 1/2 (+ 1 right))) (b 1)
                              (factor (* 1/2 (+ 1 right)))))
            :in-theory (theory 'lw-ewcc-arithmetic)
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-euler-window-circle-cover-valid
  (implies (and (rationalp height) (rationalp lower) (<= 0 lower)
                (rationalp upper) (< lower upper) (< upper 252))
           (let ((data (lw-euler-window-circle-cover height lower upper)))
             (and (rationalp (car data)) (< lower (car data)) (< (car data) upper)
                  (lw-euler-circle-coverp (cons 252 height) (car data) (cadr data) (caddr data))
                  (lw-euler-value-clearance-check 252 height (lw-euler-zeta-clearance-request 252 height)))))
  :hints (("Goal"
           :use ((:instance lw-ewcc-normalized-bounds (outer (* 1/2 (+ 252 upper))))
                 (:instance lw-ewcc-scale-bounds (right (/ upper (* 1/2 (+ 252 upper)))))
                 (:instance lw-euler-circle-generated-cover-valid
                   (rate 252) (outer-radius (* 1/2 (+ 252 upper))) (target 0) (error 1) (factor-error 1)
                   (lower (/ lower (* 1/2 (+ 252 upper)))) (upper (/ upper (* 1/2 (+ 252 upper))))
                   (scale (* 1/2 (+ 1 (/ upper (* 1/2 (+ 252 upper))))))
                   (cutoff-square (* 1/2 (+ 1
                    (* (* 1/2 (+ 1 (/ upper (* 1/2 (+ 252 upper)))))
                       (* 1/2 (+ 1 (/ upper (* 1/2 (+ 252 upper)))))))))))
           :in-theory (union-theories '(lw-euler-window-circle-cover) (theory 'lw-ewcc-arithmetic))
           :do-not-induct t))
  :rule-classes nil)
