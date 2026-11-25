(in-package "ACL2")

(include-book "rational-window")

(local
 (defthm lw-bounds-product-commutes
   (equal (* left (* middle right)) (* middle (* left right)))
   :hints (("Goal" :use ((:instance associativity-of-* (x left) (y middle) (z right))
                        (:instance associativity-of-* (x middle) (y left) (z right))
                        (:instance commutativity-of-* (x left) (y middle)))
                   :in-theory (disable associativity-of-* commutativity-of-*)))))

(defun lw-rational-power (base exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      1
    (* base (lw-rational-power base (- exponent 1)))))

(defthm lw-rational-power-rational
  (implies (rationalp base) (rationalp (lw-rational-power base exponent)))
  :rule-classes (:rewrite :type-prescription))

(defthm lw-rational-power-at-least-one
  (implies (and (rationalp base) (<= 1 base))
           (<= 1 (lw-rational-power base exponent)))
  :hints (("Goal" :induct (lw-rational-power base exponent) :nonlinearp t)))

(defthm lw-rational-power-bernoulli
  (implies (and (rationalp base) (<= 1 base) (natp exponent))
           (<= (+ 1 (* exponent (- base 1))) (lw-rational-power base exponent)))
  :hints (("Goal" :induct (lw-rational-power base exponent) :nonlinearp t)))

(defun lw-geometric-index (base target)
  (+ 1 (lw-precision-fuel target (- base 1))))

(defthm lw-geometric-index-natural
  (natp (lw-geometric-index base target))
  :rule-classes (:rewrite :type-prescription))

(defthm lw-geometric-threshold
  (implies (and (rationalp base)
                (< 1 base)
                (rationalp target)
                (<= 0 target)
                (natp exponent)
                (<= (lw-geometric-index base target) exponent))
           (<= target (lw-rational-power base exponent)))
  :hints (("Goal" :use ((:instance lw-precision-fuel-adequate
                                   (width target) (epsilon (- base 1)))
                        lw-rational-power-bernoulli)
                  :in-theory (disable lw-precision-fuel lw-rational-power
                                      lw-precision-fuel-adequate lw-rational-power-bernoulli)
                  :nonlinearp t)))

(defun lw-landau-index (growth pole-ratio tail-ratio pole-target tail-target ceiling-target)
  (max (lw-geometric-index growth ceiling-target)
       (max (lw-geometric-index pole-ratio pole-target)
            (lw-geometric-index tail-ratio tail-target))))

(defthm lw-landau-index-natural
  (natp (lw-landau-index growth pole-ratio tail-ratio pole-target tail-target ceiling-target))
  :hints (("Goal" :in-theory (disable lw-geometric-index)))
  :rule-classes (:rewrite :type-prescription))

(defthm lw-landau-index-sufficient
  (implies (and (rationalp growth) (< 1 growth)
                (rationalp pole-ratio) (< 1 pole-ratio)
                (rationalp tail-ratio) (< 1 tail-ratio)
                (rationalp pole-target) (<= 0 pole-target)
                (rationalp tail-target) (<= 0 tail-target)
                (rationalp ceiling-target) (<= 0 ceiling-target)
                (natp exponent)
                (<= (lw-landau-index growth pole-ratio tail-ratio
                                     pole-target tail-target ceiling-target) exponent))
           (and (<= ceiling-target (lw-rational-power growth exponent))
                (<= pole-target (lw-rational-power pole-ratio exponent))
                (<= tail-target (lw-rational-power tail-ratio exponent))))
  :hints (("Goal" :use ((:instance lw-geometric-threshold (base growth) (target ceiling-target))
                        (:instance lw-geometric-threshold (base pole-ratio) (target pole-target))
                        (:instance lw-geometric-threshold (base tail-ratio) (target tail-target)))
                  :in-theory (disable lw-geometric-threshold lw-geometric-index lw-rational-power))))

(defthm lw-pole-dominates-remainder
  (implies (and (rationalp pole) (rationalp coefficient) (rationalp remainder)
                (<= (- pole remainder) coefficient)
                (<= remainder (/ pole 2)))
           (<= (/ pole 2) coefficient)))

(defthm lw-landau-coefficient-lower-bound
  (implies (and (rationalp pole)
                (rationalp coefficient)
                (rationalp tail)
                (rationalp ceiling)
                (<= (/ pole 2) coefficient)
                (<= coefficient (+ (* 2 ceiling) 105 tail))
                (<= tail (/ pole 8)))
           (<= (- (* 3/16 pole) 105/2) ceiling)))

(defthm lw-landau-coefficient-obstruction
  (implies (and (rationalp pole)
                (rationalp coefficient)
                (rationalp tail)
                (rationalp ceiling)
                (<= (* 16/3 (+ ceiling 54)) pole)
                (<= (/ pole 2) coefficient)
                (<= coefficient (+ (* 2 ceiling) 105 tail))
                (<= tail (/ pole 8)))
           nil)
  :hints (("Goal" :use (lw-landau-coefficient-lower-bound)
                  :in-theory (disable lw-landau-coefficient-lower-bound)))
  :rule-classes nil)

(assert-event
 (let ((exponent (lw-landau-index 101/100 11/10 6/5 10 20 100)))
   (and (natp exponent)
        (<= 100 (lw-rational-power 101/100 exponent))
        (<= 10 (lw-rational-power 11/10 exponent))
        (<= 20 (lw-rational-power 6/5 exponent)))))
