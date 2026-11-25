(in-package "ACL2")

(include-book "polynomial-normalized-factorization")
(include-book "polynomial-factor-coefficients")

; Express the generated factorization as a polynomial on the requested disk.

(defun lw-polynomial-disk-factor-polynomial (coefficients outer-radius epsilon)
 (lw-polynomial-factor-coefficients
  (lw-polynomial-normalized-factor-roots coefficients outer-radius epsilon)
  (lw-polynomial-leading (lw-polynomial-trim coefficients))))

(defthm lw-polynomial-disk-factor-data
 (implies (and (lw-complex-coefficientsp coefficients) (rationalp outer-radius) (<= 0 outer-radius) (rationalp epsilon) (< 0 epsilon))
  (and (lw-complexp (lw-polynomial-leading (lw-polynomial-trim coefficients)))
       (lw-ray-pointsp (lw-polynomial-normalized-factor-roots coefficients outer-radius epsilon))
       (lw-complex-coefficientsp (lw-polynomial-disk-factor-polynomial coefficients outer-radius epsilon))))
 :hints (("Goal"
  :use (lw-polynomial-trim-valid
        (:instance lw-polynomial-leading-valid (coefficients (lw-polynomial-trim coefficients)))
        (:instance lw-polynomial-normalized-factor-roots-data (bound outer-radius))
        (:instance lw-polynomial-factor-coefficients-valid (roots (lw-polynomial-normalized-factor-roots coefficients outer-radius epsilon)) (leading (lw-polynomial-leading (lw-polynomial-trim coefficients)))))
  :in-theory (union-theories '(lw-polynomial-disk-factor-polynomial) (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-polynomial-disk-factor-evaluation
 (implies (and (and (lw-complex-coefficientsp coefficients) (rationalp outer-radius) (<= 0 outer-radius) (rationalp epsilon) (< 0 epsilon)) (lw-complexp point))
  (equal (lw-complex-polynomial (lw-polynomial-disk-factor-polynomial coefficients outer-radius epsilon) point 0)
         (lw-polynomial-linear-factor-value (lw-polynomial-normalized-factor-roots coefficients outer-radius epsilon) (lw-polynomial-leading (lw-polynomial-trim coefficients)) point)))
 :hints (("Goal"
  :use (lw-polynomial-disk-factor-data
        (:instance lw-polynomial-factor-coefficients-evaluation (roots (lw-polynomial-normalized-factor-roots coefficients outer-radius epsilon)) (leading (lw-polynomial-leading (lw-polynomial-trim coefficients)))))
  :in-theory (union-theories '(lw-polynomial-disk-factor-polynomial) (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-polynomial-disk-factor-value-error
 (implies (and (and (lw-complex-coefficientsp coefficients) (rationalp outer-radius) (<= 0 outer-radius) (rationalp epsilon) (< 0 epsilon)) (lw-complex-diskp point outer-radius))
  (lw-complex-diskp (lw-complex-sub (lw-complex-polynomial coefficients point 0)
                                   (lw-complex-polynomial (lw-polynomial-disk-factor-polynomial coefficients outer-radius epsilon) point 0))
                   epsilon))
 :hints (("Goal"
  :use ((:instance lw-complex-disk-data (radius outer-radius)) lw-polynomial-disk-factor-evaluation
        (:instance lw-polynomial-normalized-approximate-factorization (bound outer-radius)))
  :in-theory (theory 'minimal-theory)
  :do-not-induct t)))
