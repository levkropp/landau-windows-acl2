(in-package "ACL2")

(include-book "mellin-clipped-refinement")

; One mesh for all clipped components and every logarithmic cutpoint.
; The extra minimum lets a later caller also include its native Mellin
; mesh. The same signal and kernel precisions are used throughout.

(local (in-theory
 (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-scale lw-complex-diskp
          lw-mellin-basis-clearance lw-mellin-basis-exponential-point
          lw-mellin-component-endpoint-target lw-mellin-moment-endpoint-target
          lw-mellin-component-endpoint-value lw-mellin-moment-endpoint-value
          lw-mellin-component-refined-grid lw-mellin-exponential-moment-cap
          lw-mellin-clipped-basis-dyadic lw-mellin-frozen-basis-dyadic
          lw-mellin-clipped-basis-before-cutpoint lw-mellin-clipped-ramp-linearization
          lw-mellin-frozen-ramp-before-cutpoint lw-mellin-frozen-ramp-after-cutpoint
          lw-complex-exp-dyadic-depth lw-complex-exp-dyadic-moment-depth
          lw-complex-exp-dyadic-integral-value lw-complex-exp-dyadic-moment-integral-value
          lw-complex-exp-uniform-cap lw-exp-bounds lw-exp-lipschitz-cap
          lw-mellin-weight lw-mellin-phase lw-complex-disk-enlarge
          lw-complex-sub-add-first lw-complex-add-commutative lw-complex-add-left-commutes)))

(defun lw-mellin-component-minimum-depth (kind cap start length sigma height error)
  (if (equal kind 1)
      (lw-complex-exp-dyadic-moment-depth
       (lw-mellin-basis-exponential-point kind sigma height) start length
       (lw-mellin-basis-clearance kind sigma) (lw-mellin-moment-endpoint-target cap sigma length error))
    (lw-complex-exp-dyadic-depth
     (lw-mellin-basis-exponential-point kind sigma height) start length
     (lw-mellin-basis-clearance kind sigma) (lw-mellin-component-endpoint-target kind sigma length error))))

(defun lw-mellin-common-depth (cap start length sigma height error minimum-depth)
  (max (nfix minimum-depth)
       (max (nfix (lw-mellin-component-minimum-depth 0 cap start length sigma height error))
            (max (nfix (lw-mellin-component-minimum-depth 1 cap start length sigma height error))
                 (nfix (lw-mellin-component-minimum-depth 3 cap start length sigma height error))))))

(defun lw-mellin-common-endpoint (kind cap start length cutpoint sigma height error)
  (if (equal kind 1)
      (lw-mellin-moment-endpoint-value cap start length cutpoint sigma height error)
    (lw-mellin-component-endpoint-value kind start length cutpoint sigma height error)))

(local (in-theory (disable lw-mellin-component-minimum-depth lw-mellin-common-depth lw-mellin-common-endpoint)))

(local (defthm lw-mcm-component-depth-natural
 (implies
  (and (rationalp cap) (<= 0 cap) (rationalp start) (<= 0 start)
       (rationalp length) (<= 0 length) (rationalp sigma) (< 1 sigma)
       (rationalp height) (rationalp error) (< 0 error))
  (natp (lw-mellin-component-minimum-depth kind cap start length sigma height error)))
 :hints (("Goal"
   :use (lw-mellin-basis-clearance-valid
         lw-mellin-component-endpoint-target-valid lw-mellin-moment-endpoint-target-valid
         (:instance lw-complex-exp-dyadic-depth-adequate
           (point (lw-mellin-basis-exponential-point kind sigma height))
           (clearance (lw-mellin-basis-clearance kind sigma))
           (error (lw-mellin-component-endpoint-target kind sigma length error)))
         (:instance lw-complex-exp-dyadic-moment-depth-adequate
           (point (lw-mellin-basis-exponential-point 1 sigma height))
           (clearance (lw-mellin-basis-clearance 1 sigma))
           (error (lw-mellin-moment-endpoint-target cap sigma length error))))
   :in-theory (e/d (lw-mellin-component-minimum-depth)
     (lw-mellin-basis-clearance-valid lw-mellin-component-endpoint-target-valid
      lw-mellin-moment-endpoint-target-valid lw-complex-exp-dyadic-depth-adequate
      lw-complex-exp-dyadic-moment-depth-adequate))
   :do-not-induct t))
 :rule-classes nil))

(defthm lw-mellin-common-depth-adequate
 (implies
  (and (rationalp cap) (<= 0 cap) (rationalp start) (<= 0 start)
       (rationalp length) (<= 0 length) (rationalp sigma) (< 1 sigma)
       (rationalp height) (rationalp error) (< 0 error))
  (let ((depth (lw-mellin-common-depth cap start length sigma height error minimum-depth)))
   (and (natp depth) (<= (nfix minimum-depth) depth)
        (<= (lw-mellin-component-minimum-depth 0 cap start length sigma height error) depth)
        (<= (lw-mellin-component-minimum-depth 1 cap start length sigma height error) depth)
        (<= (lw-mellin-component-minimum-depth 3 cap start length sigma height error) depth))))
 :hints (("Goal"
   :use ((:instance lw-mcm-component-depth-natural (kind 0))
         (:instance lw-mcm-component-depth-natural (kind 1))
         (:instance lw-mcm-component-depth-natural (kind 3)))
   :in-theory (enable lw-mellin-common-depth max nfix)
   :do-not-induct t)))

(local (defthm lw-mcm-frozen-parameters
 (implies
  (and (syntaxp (not (and (equal prime '(quote 2)) (equal log-error '(quote 1)))))
       (or (equal kind 0) (equal kind 1) (equal kind 3)))
  (equal
   (lw-mellin-frozen-basis-dyadic kind start end depth sigma height index exp-error prime log-error sample-error)
   (lw-mellin-frozen-basis-dyadic kind start end depth sigma height index exp-error 2 1 sample-error)))
 :hints (("Goal"
   :induct (lw-mellin-frozen-basis-dyadic kind start end depth sigma height index exp-error prime log-error sample-error)
   :in-theory (enable lw-mellin-frozen-basis-dyadic)))))

(local (defthm lw-mcm-clipped-parameters
 (implies
  (and (syntaxp (not (and (equal prime '(quote 2)) (equal log-error '(quote 1)))))
       (or (equal kind 0) (equal kind 1) (equal kind 3)))
  (equal
   (lw-mellin-clipped-basis-dyadic kind start end depth cutpoint sigma height index exp-error prime log-error sample-error)
   (lw-mellin-clipped-basis-dyadic kind start end depth cutpoint sigma height index exp-error 2 1 sample-error)))
 :hints (("Goal"
   :induct (lw-mellin-clipped-basis-dyadic kind start end depth cutpoint sigma height index exp-error prime log-error sample-error)
   :in-theory (enable lw-mellin-clipped-basis-dyadic)))))

(defthm lw-mellin-common-component-comparison
 (implies
  (and (member-equal kind '(0 1 3))
       (rationalp cap) (<= 0 cap) (rationalp start) (<= 0 start)
       (rationalp length) (<= 0 length) (<= (+ start length) cap)
       (rationalp cutpoint) (<= 0 cutpoint) (rationalp sigma) (< 1 sigma) (rationalp height)
       (rationalp exp-error) (< 0 exp-error) (rationalp sample-error) (< 0 sample-error)
       (rationalp error) (< 0 error))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-mellin-clipped-basis-dyadic
     kind start (+ start length) (lw-mellin-common-depth cap start length sigma height error minimum-depth)
     cutpoint sigma height 0 exp-error prime log-error sample-error)
    (lw-mellin-common-endpoint kind cap start length cutpoint sigma height error))
   (+ (* length (lw-mellin-exponential-moment-cap kind cap)
         (+ exp-error (* 2 (lw-complex-exp-uniform-cap cap) sample-error)))
      error)))
 :hints (("Goal"
   :use (lw-mellin-common-depth-adequate
         (:instance lw-mellin-component-refined-comparison
           (depth (lw-mellin-common-depth cap start length sigma height error minimum-depth)))
         (:instance lw-mellin-moment-refined-comparison
           (depth (lw-mellin-common-depth cap start length sigma height error minimum-depth))))
   :cases ((equal kind 1) (equal kind 3))
   :in-theory (e/d (lw-mellin-common-endpoint lw-mellin-component-refined-grid
                   lw-mellin-exponential-moment-cap lw-mellin-component-minimum-depth)
     (lw-mellin-common-depth-adequate lw-mellin-component-refined-comparison lw-mellin-moment-refined-comparison))
   :do-not-induct t)))

(defthm lw-mellin-common-endpoint-rational
 (implies
  (and (rationalp cap) (<= 0 cap) (rationalp start) (<= 0 start)
       (rationalp length) (<= 0 length) (rationalp cutpoint)
       (rationalp sigma) (< 1 sigma) (rationalp height) (rationalp error) (< 0 error))
  (lw-complexp (lw-mellin-common-endpoint kind cap start length cutpoint sigma height error)))
 :hints (("Goal"
   :use (lw-mellin-basis-clearance-valid lw-mellin-component-endpoint-target-valid
         lw-mellin-moment-endpoint-target-valid
         (:instance lw-complex-exp-dyadic-integral-value-rational
           (point (lw-mellin-basis-exponential-point kind sigma height))
           (clearance (lw-mellin-basis-clearance kind sigma))
           (error (lw-mellin-component-endpoint-target kind sigma length error)))
         (:instance lw-complex-exp-dyadic-moment-values-rational
           (point (lw-mellin-basis-exponential-point 1 sigma height))
           (clearance (lw-mellin-basis-clearance 1 sigma))
           (error (lw-mellin-moment-endpoint-target cap sigma length error))))
   :in-theory (e/d (lw-mellin-common-endpoint lw-mellin-component-endpoint-value lw-mellin-moment-endpoint-value)
     (lw-mellin-basis-clearance-valid lw-mellin-component-endpoint-target-valid lw-mellin-moment-endpoint-target-valid
      lw-complex-exp-dyadic-integral-value-rational lw-complex-exp-dyadic-moment-values-rational))
   :do-not-induct t)))

