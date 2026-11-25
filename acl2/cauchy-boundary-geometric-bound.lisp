(in-package "ACL2")

(include-book "polynomial-geometric-bounds")
(include-book "cauchy-extraction")

; One finite boundary check bounds the whole coefficient list.

(defthm lw-cauchy-boundary-coefficient-caps
  (implies (and (lw-complex-coefficientsp coefficients) (natp degree)
                (<= (len coefficients) (+ 1 degree))
                (rationalp cap) (<= 0 cap) (rationalp error) (< 0 error)
                (lw-cauchy-boundary-check coefficients (lw-cauchy-orbit-rotation degree) 0
                  (lw-cauchy-coefficient-count coefficients degree error) cap))
           (lw-polynomial-coefficient-caps coefficients (+ cap error)))
  :hints (("Goal"
           :use ((:instance lw-polynomial-cap-index-data (cap (+ cap error)))
                 (:instance lw-cauchy-finite-coefficient-bound
                   (target (lw-polynomial-cap-index coefficients (+ cap error)))))
           :in-theory (union-theories '(natp) (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(defthm lw-cauchy-polynomial-boundary-geometric-bound
  (implies (and (lw-complex-coefficientsp coefficients) (natp degree)
                (<= (len coefficients) (+ 1 degree))
                (rationalp cap) (<= 0 cap) (rationalp error) (< 0 error)
                (lw-cauchy-boundary-check coefficients (lw-cauchy-orbit-rotation degree) 0
                  (lw-cauchy-coefficient-count coefficients degree error) cap)
                (lw-complex-diskp point radius) (< radius 1))
           (lw-complex-diskp (lw-complex-polynomial coefficients point 0)
                            (/ (+ cap error) (- 1 radius))))
  :hints (("Goal"
           :use (lw-cauchy-boundary-coefficient-caps lw-complex-disk-data lw-geometric-disk-gain-data
                 (:instance lw-complex-polynomial-geometric-tail-bound (cap (+ cap error)) (offset 0)))
           :in-theory (union-theories '(lw-geometric-disk-gain lw-rational-power natp zp fix unicity-of-1 commutativity-of-*) (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
