(in-package "ACL2")

(include-book "window-index")

; A rational height in [-cap, cap] has a computed grid point at most
; one step above it. A finite request minimum can cover every index.

(local (defthm lw-ewhg-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ewhg-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ewhg-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ewhg-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ewhg-times-negative (a b) (b a)))
                 :in-theory (disable lw-ewhg-times-negative)))))

(local (defthm lw-ewhg-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ewhg-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ewhg-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ewhg-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ewhg-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ewhg-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ewhg-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ewhg-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ewhg-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ewhg-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ewhg-left-commutes)))))

(local (deftheory lw-ewhg-arithmetic (union-theories
            '(fold-consts-in-+
              lw-ewhg-left-commutes lw-ewhg-left-distributes lw-ewhg-fold-constants
              lw-ewhg-times-negative lw-ewhg-negative-times lw-ewhg-zero-times
              lw-ewhg-minus-one lw-ewhg-double-negative lw-ewhg-add-cancel lw-ewhg-double lw-ewhg-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))

(defun lw-euler-window-height-count (cap step)
  (lw-ceiling-rational (* 2 cap (/ step))))

(defun lw-euler-window-height-index (cap step height)
  (lw-ceiling-rational (* (+ height cap) (/ step))))

(defun lw-euler-window-grid-height (cap step index)
  (- (* step index) cap))

(local
 (defthm lw-ewhg-strict-product
   (implies (and (rationalp a) (rationalp b) (< a b)
                 (rationalp factor) (< 0 factor))
            (< (* a factor) (* b factor)))
   :hints (("Goal" :nonlinearp t))
   :rule-classes nil))

(defthm lw-euler-window-height-count-natural
  (natp (lw-euler-window-height-count cap step))
  :hints (("Goal" :in-theory (union-theories '(lw-euler-window-height-count (:type-prescription lw-ceiling-rational))
                                             (theory 'lw-ewhg-arithmetic))))
  :rule-classes (:rewrite :type-prescription))

(defthm lw-euler-window-grid-height-rational
  (implies (and (rationalp cap) (rationalp step) (rationalp index))
           (rationalp (lw-euler-window-grid-height cap step index)))
  :hints (("Goal" :in-theory (union-theories '(lw-euler-window-grid-height) (theory 'lw-ewhg-arithmetic))))
  :rule-classes nil)

(defthm lw-euler-window-height-index-data
  (implies (and (rationalp cap) (<= 0 cap) (rationalp step) (< 0 step)
                (rationalp height) (<= (- cap) height) (<= height cap))
           (and (natp (lw-euler-window-height-index cap step height)) (<= (lw-euler-window-height-index cap step height) (lw-euler-window-height-count cap step))
                (<= height (lw-euler-window-grid-height cap step (lw-euler-window-height-index cap step height))) (< (lw-euler-window-grid-height cap step (lw-euler-window-height-index cap step height)) (+ height step))))
  :hints (("Goal"
           :use ((:instance lw-reciprocal-positive (value step))
                 (:instance lw-ceiling-rational-bracket (value (* (+ height cap) (/ step))))
                 (:instance lw-ceiling-rational-bracket (value (* 2 cap (/ step))))
                 (:instance lw-ewhg-multiply-order (a 0) (b (+ height cap)) (factor (/ step)))
                 (:instance lw-ewhg-multiply-order (a (+ height cap)) (b (* 2 cap)) (factor (/ step)))
                 (:instance lw-ewhg-multiply-order
                   (a (* (+ height cap) (/ step))) (b (lw-euler-window-height-index cap step height)) (factor step))
                 (:instance lw-ewhg-strict-product
                   (a (lw-euler-window-height-index cap step height)) (b (+ 1 (* (+ height cap) (/ step)))) (factor step))
                 (:instance lw-ewhg-inverse-factor (divisor step) (coefficient (+ height cap))))
           :in-theory (union-theories '(lw-euler-window-height-count lw-euler-window-height-index
                 lw-euler-window-grid-height (:type-prescription lw-ceiling-rational))
              (theory 'lw-ewhg-arithmetic))
           :do-not-induct t))
  :rule-classes nil)
