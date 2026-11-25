(in-package "ACL2")

(include-book "euler-window-circle-pair")
(include-book "euler-circle-pair-window-certificate")

; Arithmetic windowed Landau. The threshold and sample request are
; computed from the rational region, independently of the offset.

(local (defthm lw-ewcr-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ewcr-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ewcr-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ewcr-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ewcr-times-negative (a b) (b a)))
                 :in-theory (disable lw-ewcr-times-negative)))))

(local (defthm lw-ewcr-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ewcr-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ewcr-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ewcr-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ewcr-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ewcr-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ewcr-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ewcr-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ewcr-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ewcr-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ewcr-left-commutes)))))

(local (deftheory lw-ewcr-arithmetic (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-ewcr-left-commutes lw-ewcr-left-distributes lw-ewcr-fold-constants
              lw-ewcr-times-negative lw-ewcr-negative-times lw-ewcr-zero-times
              lw-ewcr-minus-one lw-ewcr-double-negative lw-ewcr-add-cancel lw-ewcr-double lw-ewcr-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))

(defun lw-euler-window-ceiling-threshold (cap slack seed-height ceiling numerator denominator)
  (let* ((data (lw-euler-window-prepare-circles cap slack seed-height))
         (center (cons 252 (car data)))
         (modulated (cadr data))
         (empty (caddr data))
         (real-radius (cadddr data)))
    (lw-euler-circle-pair-window-threshold
     center (car modulated) (cadr modulated) (caddr modulated) ceiling numerator denominator
     (car empty) real-radius (cadr empty) (caddr empty))))

(local
 (defthm lw-ewcr-kernel-threshold-natural
   (and (natp (lw-kernel-window-block-threshold minimum-index width))
        (<= 1 (lw-kernel-window-block-threshold minimum-index width)))
   :hints (("Goal"
            :use ((:instance lw-eventual-window-threshold-natural
                     (target (max 64 (max (lw-geometric-index 5000/4977 128)
                                         (max (nfix minimum-index) (nfix width)))))))
            :in-theory (union-theories '(lw-kernel-window-block-threshold) (theory 'lw-ewcr-arithmetic))
            :do-not-induct t))
   :rule-classes (:rewrite :type-prescription)))

(defthm lw-euler-window-ceiling-threshold-natural
  (and (natp (lw-euler-window-ceiling-threshold cap slack seed-height ceiling numerator denominator)) (<= 1 (lw-euler-window-ceiling-threshold cap slack seed-height ceiling numerator denominator)))
  :hints (("Goal"
           :in-theory (union-theories '(lw-euler-window-ceiling-threshold lw-euler-circle-pair-window-threshold
                                       lw-euler-circle-computed-window-threshold lw-ewcr-kernel-threshold-natural)
                                      (theory 'lw-ewcr-arithmetic))
           :do-not-induct t))
  :rule-classes nil)

(defthm lw-euler-window-ceiling-reduction
  (implies
   (and (rationalp cap) (< 251 cap) (< cap (- 252 (/ numerator denominator)))
       (rationalp slack) (< 0 slack) (rationalp seed-height)
       (rationalp ceiling) (<= 0 ceiling) (natp numerator) (posp denominator) (<= numerator denominator)
       (rationalp start) (<= (lw-euler-window-ceiling-threshold cap slack seed-height ceiling numerator denominator) start)
        (lw-euler-window-small-samplep cap slack seed-height offset))
   (let* ((found (lw-landau-window-search start ceiling numerator denominator))
          (address (lw-landau-window-address start ceiling found)))
     (and found (rationalp address) (<= start address)
          (<= (* address address) (* start start start))
          (< 0 (cadr found))
          (equal (cdr found) (lw-signal-bounds address ceiling numerator denominator 1/4)))))
  :hints (("Goal"
           :use (lw-euler-window-prepared-circles-valid lw-euler-window-prepared-circles-positive-count
                 (:instance lw-euler-circle-interior-count-natural (center (cons 252 (car (lw-euler-window-prepare-circles cap slack seed-height))))
                   (radius (car (cadr (lw-euler-window-prepare-circles cap slack seed-height)))) (plus-arcs (cadr (cadr (lw-euler-window-prepare-circles cap slack seed-height)))) (minus-arcs (caddr (cadr (lw-euler-window-prepare-circles cap slack seed-height)))))
                 (:instance lw-euler-circle-collar-width-data (center (cons 252 (car (lw-euler-window-prepare-circles cap slack seed-height))))
                   (radius (car (cadr (lw-euler-window-prepare-circles cap slack seed-height)))) (plus-arcs (cadr (cadr (lw-euler-window-prepare-circles cap slack seed-height)))) (minus-arcs (caddr (cadr (lw-euler-window-prepare-circles cap slack seed-height)))))
                 (:instance lw-euler-circle-pair-window-certificate
                   (center (cons 252 (car (lw-euler-window-prepare-circles cap slack seed-height))))
                   (radius (car (cadr (lw-euler-window-prepare-circles cap slack seed-height)))) (plus-arcs (cadr (cadr (lw-euler-window-prepare-circles cap slack seed-height)))) (minus-arcs (caddr (cadr (lw-euler-window-prepare-circles cap slack seed-height))))
                   (anchor-error (lw-euler-zeta-clearance-request 252 (car (lw-euler-window-prepare-circles cap slack seed-height))))
                   (real-circle-radius (car (caddr (lw-euler-window-prepare-circles cap slack seed-height)))) (real-radius (cadddr (lw-euler-window-prepare-circles cap slack seed-height)))
                   (real-plus-arcs (cadr (caddr (lw-euler-window-prepare-circles cap slack seed-height)))) (real-minus-arcs (caddr (caddr (lw-euler-window-prepare-circles cap slack seed-height))))
                   (real-anchor-error (lw-euler-zeta-clearance-request 252 0)))
                 (:instance lw-reciprocal-positive (value denominator))
                 (:instance lw-ewcr-multiply-order (a 0) (b numerator) (factor (/ denominator))))
           :in-theory (union-theories '(lw-euler-window-ceiling-threshold) (theory 'lw-ewcr-arithmetic))
           :do-not-induct t))
  :rule-classes nil)

(defthm lw-euler-window-sample-separation-from-failed-search
  (implies (and (rationalp cap) (< 251 cap) (< cap (- 252 (/ numerator denominator)))
       (rationalp slack) (< 0 slack) (rationalp seed-height)
       (rationalp ceiling) (<= 0 ceiling) (natp numerator) (posp denominator) (<= numerator denominator)
       (rationalp start) (<= (lw-euler-window-ceiling-threshold cap slack seed-height ceiling numerator denominator) start)
                (not (lw-landau-window-search start ceiling numerator denominator)))
           (not (lw-euler-window-small-samplep cap slack seed-height offset)))
  :hints (("Goal"
           :use (lw-euler-window-ceiling-reduction)
           :in-theory (theory 'lw-ewcr-arithmetic)
           :do-not-induct t))
  :rule-classes nil)
