(in-package "ACL2")

(include-book "mellin-partitions")

; The first cell may have been trimmed while retaining its original
; sample anchor. Later cells use their left endpoints. This lets two
; partitions be merged without changing either computed sample sum.
(defun lw-mellin-meshp (anchor start endpoints cap mesh)
  (and (rationalp anchor) (<= 0 anchor) (rationalp start) (<= anchor start)
       (rationalp cap) (<= start cap) (rationalp mesh) (<= 0 mesh)
       (if (consp endpoints)
           (and (rationalp (car endpoints)) (< start (car endpoints)) (<= (car endpoints) cap)
                (<= (- (car endpoints) anchor) mesh)
                (lw-mellin-meshp (car endpoints) (car endpoints) (cdr endpoints) cap mesh))
         (equal endpoints nil))))

(defun lw-mellin-mesh-sum (anchor start endpoints sigma height index error)
  (if (consp endpoints)
      (lw-complex-add (lw-complex-scale (- (car endpoints) start) (lw-mellin-sample anchor sigma height index 1 error))
                      (lw-mellin-mesh-sum (car endpoints) (car endpoints) (cdr endpoints) sigma height index error))
    (cons 0 0)))

(local (in-theory
        (disable lw-mellin-sample lw-mellin-sample-rational lw-mellin-sample-spatial-transport
                 lw-mellin-spatial-slope lw-mellin-spatial-error-factor lw-mellin-spatial-parameters
                 lw-log-signal-bounds (:executable-counterpart lw-log-signal-bounds)
                 lw-mellin-signal-spatial-cap lw-mellin-signal-spatial-slope
                 lw-complexp lw-complex-diskp lw-complex-add lw-complex-sub lw-complex-scale
                 lw-complex-disk-enlarge lw-disk-enlarge lw-complex-difference-triangle)))

(local (defthm lw-mm-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-mm-times-negative
         (implies (and (rationalp a) (rationalp b)) (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-mm-negative-times
         (implies (and (rationalp a) (rationalp b)) (equal (* (- a) b) (- (* a b))))))
(local (defthm lw-mm-zero-times (equal (* 0 a) 0)))
(local (defthm lw-mm-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))
(local (defthm lw-mm-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))
(local (defthm lw-mm-left-distribute
         (implies (and (rationalp a) (rationalp b) (rationalp c))
                  (equal (* (+ a b) c) (+ (* a c) (* b c))))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(defthm lw-mellin-mesh-end-bounds
  (implies (lw-mellin-meshp anchor start endpoints cap mesh)
           (and (rationalp (lw-partition-end start endpoints))
                (<= start (lw-partition-end start endpoints)) (<= (lw-partition-end start endpoints) cap)
                (implies (consp endpoints) (< start (lw-partition-end start endpoints)))))
  :hints (("Goal" :induct (lw-mellin-meshp anchor start endpoints cap mesh))))

(local (defthm lw-mm-mesh-data
         (implies (lw-mellin-meshp anchor start endpoints cap mesh)
                  (and (rationalp anchor) (<= 0 anchor) (rationalp start) (<= anchor start)
                       (rationalp cap) (<= start cap) (rationalp mesh) (<= 0 mesh)))
         :rule-classes :forward-chaining))
(local (defthm lw-mm-mesh-head
         (implies (and (lw-mellin-meshp anchor start endpoints cap mesh) (consp endpoints))
                  (and (rationalp (car endpoints)) (< start (car endpoints)) (<= (car endpoints) cap)
                       (<= (- (car endpoints) anchor) mesh)
                       (lw-mellin-meshp (car endpoints) (car endpoints) (cdr endpoints) cap mesh)))
         :rule-classes :forward-chaining))
(local (defthm lw-mm-mesh-empty
         (implies (and (lw-mellin-meshp anchor start endpoints cap mesh) (not (consp endpoints)))
                  (equal endpoints nil))
         :rule-classes :forward-chaining))
(local (defthm lw-mm-end-empty
         (equal (lw-partition-end start nil) start)))
(local (defthm lw-mm-end-cons
         (implies (consp endpoints)
                  (equal (lw-partition-end start endpoints) (lw-partition-end (car endpoints) (cdr endpoints))))))
(local (defthm lw-mm-sum-empty
         (equal (lw-mellin-mesh-sum anchor start nil sigma height index error) (cons 0 0))))

(defthm lw-mellin-mesh-trim-valid
  (implies (and (lw-mellin-meshp anchor start endpoints cap mesh) (consp endpoints)
                (rationalp cut) (<= start cut) (< cut (car endpoints)))
           (lw-mellin-meshp anchor cut endpoints cap mesh))
  :hints (("Goal" :expand ((lw-mellin-meshp anchor start endpoints cap mesh)
                           (lw-mellin-meshp anchor cut endpoints cap mesh))))
  :rule-classes nil)

(defthm lw-mellin-mesh-sum-rational
  (implies (and (lw-mellin-meshp anchor start endpoints cap mesh)
                (rationalp sigma) (<= 0 sigma) (rationalp height) (rationalp error) (< 0 error))
           (lw-complexp (lw-mellin-mesh-sum anchor start endpoints sigma height index error)))
  :hints (("Goal" :induct (lw-mellin-meshp anchor start endpoints cap mesh)
                  :in-theory (enable lw-complexp lw-complex-add lw-complex-scale))
          (and stable-under-simplificationp
               '(:use ((:instance lw-mellin-sample-rational (value anchor) (step 1)))
                 :in-theory (enable lw-complexp lw-complex-add lw-complex-scale))))
  :rule-classes (:rewrite :type-prescription))

(local (in-theory (disable (:definition lw-mellin-meshp) (:definition lw-mellin-mesh-sum))))

(defthm lw-mellin-mesh-split-first
  (implies (and (lw-mellin-meshp anchor start endpoints cap mesh) (consp endpoints)
                (rationalp cut) (<= start cut) (<= cut (car endpoints))
                (rationalp sigma) (<= 0 sigma) (rationalp height) (rationalp error) (< 0 error))
           (equal (lw-mellin-mesh-sum anchor start endpoints sigma height index error)
                  (lw-complex-add (lw-complex-scale (- cut start) (lw-mellin-sample anchor sigma height index 1 error))
                                  (lw-mellin-mesh-sum anchor cut endpoints sigma height index error))))
  :hints (("Goal" :use ((:instance lw-mellin-sample-rational (value anchor) (step 1))
                        (:instance lw-mellin-mesh-sum-rational
                          (anchor (car endpoints)) (start (car endpoints)) (endpoints (cdr endpoints))))
                  :expand ((lw-mellin-meshp anchor start endpoints cap mesh)
                           (lw-mellin-mesh-sum anchor start endpoints sigma height index error)
                           (lw-mellin-mesh-sum anchor cut endpoints sigma height index error))
                  :in-theory (e/d (lw-complex-add lw-complex-scale lw-complexp) (lw-mellin-mesh-sum-rational))))
  :rule-classes nil)

(local
 (defthm lw-mm-join-comparison
   (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp left) (lw-complexp right)
                 (rationalp weight) (<= 0 weight) (rationalp rest-weight) (<= 0 rest-weight) (rationalp radius)
                 (lw-complex-diskp (lw-complex-sub a b) radius)
                 (lw-complex-diskp (lw-complex-sub left right) (* rest-weight radius)))
            (lw-complex-diskp
             (lw-complex-sub (lw-complex-add (lw-complex-scale weight a) left)
                             (lw-complex-add (lw-complex-scale weight b) right))
             (* (+ weight rest-weight) radius)))
   :hints (("Goal" :use ((:instance lw-complex-scale-disk (point (lw-complex-sub a b)) (factor weight))
                         (:instance lw-complex-add-disk (left (lw-complex-scale weight (lw-complex-sub a b)))
                           (radius (* weight radius)) (right (lw-complex-sub left right)) (other-radius (* rest-weight radius))))
                   :in-theory (e/d (lw-complexp lw-complex-sub lw-complex-scale lw-complex-add)
                                   (lw-complex-scale-disk lw-complex-add-disk))))
   :rule-classes nil))

(local
 (defthm lw-mm-anchor-comparison
   (implies (and (lw-mellin-meshp left-anchor start left cap left-mesh) (consp left)
                 (lw-mellin-meshp right-anchor start right cap right-mesh) (consp right)
                 (rationalp sigma) (<= 0 sigma) (rationalp height) (natp index)
                 (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
            (lw-complex-diskp
             (lw-complex-sub (lw-mellin-sample left-anchor sigma height index 1 left-error)
                             (lw-mellin-sample right-anchor sigma height index 1 right-error))
             (+ (* (lw-mellin-spatial-slope cap sigma height 1) (+ left-mesh right-mesh))
                (* (lw-mellin-spatial-error-factor cap 1) (+ left-error right-error)))))
   :hints (("Goal" :use ((:instance lw-mellin-spatial-parameters (step 1))
                         (:instance lw-mellin-sample-spatial-transport (left left-anchor) (right right-anchor) (step 1))
                         (:instance lw-complex-disk-enlarge
                           (point (lw-complex-sub (lw-mellin-sample left-anchor sigma height index 1 left-error)
                                                 (lw-mellin-sample right-anchor sigma height index 1 right-error)))
                           (radius (+ (* (lw-mellin-spatial-slope cap sigma height 1) (abs (- left-anchor right-anchor)))
                                      (* (lw-mellin-spatial-error-factor cap 1) (+ left-error right-error))))
                           (cap (+ (* (lw-mellin-spatial-slope cap sigma height 1) (+ left-mesh right-mesh))
                                   (* (lw-mellin-spatial-error-factor cap 1) (+ left-error right-error))))))
                   :expand ((lw-mellin-meshp left-anchor start left cap left-mesh)
                            (lw-mellin-meshp right-anchor start right cap right-mesh))
                   :nonlinearp t))
   :rule-classes nil))

(defun lw-mellin-mesh-pair-radius (cap sigma height left-mesh right-mesh left-error right-error)
  (+ (* (lw-mellin-spatial-slope cap sigma height 1) (+ left-mesh right-mesh))
     (* (lw-mellin-spatial-error-factor cap 1) (+ left-error right-error))))

(defthm lw-mellin-mesh-pair-radius-valid
  (implies (and (rationalp cap) (<= 0 cap) (rationalp sigma) (<= 0 sigma) (rationalp height)
                (rationalp left-mesh) (<= 0 left-mesh) (rationalp right-mesh) (<= 0 right-mesh)
                (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
           (and (rationalp (lw-mellin-mesh-pair-radius cap sigma height left-mesh right-mesh left-error right-error))
                (<= 0 (lw-mellin-mesh-pair-radius cap sigma height left-mesh right-mesh left-error right-error))))
  :hints (("Goal" :use ((:instance lw-mellin-spatial-parameters (step 1))) :nonlinearp t)))

(local (defthm lw-mm-zero-disk
         (lw-complex-diskp (cons 0 0) 0)
         :hints (("Goal" :in-theory (enable lw-complex-diskp lw-complexp lw-diskp)))))
(local (defthm lw-mm-sub-zero
         (equal (lw-complex-sub (cons 0 0) (cons 0 0)) (cons 0 0))
         :hints (("Goal" :in-theory (enable lw-complex-sub)))))

(local
 (defun lw-mm-compare-induction (left-anchor right-anchor start left right)
   (declare (xargs :measure (+ (acl2-count left) (acl2-count right))))
   (if (or (endp left) (endp right)) (list left-anchor right-anchor start)
     (if (< (car left) (car right))
         (lw-mm-compare-induction (car left) right-anchor (car left) (cdr left) right)
       (if (< (car right) (car left))
           (lw-mm-compare-induction left-anchor (car right) (car right) left (cdr right))
         (lw-mm-compare-induction (car left) (car right) (car left) (cdr left) (cdr right)))))))

; The meshes may have unrelated rational endpoints. Neither sample sum
; is replaced with an analytic integral or an assumed approximation.
(local
 (defthm lw-mm-anchor-pair-bound
   (implies (and (lw-mellin-meshp left-anchor start left cap left-mesh) (consp left)
                 (lw-mellin-meshp right-anchor start right cap right-mesh) (consp right)
                 (rationalp sigma) (<= 0 sigma) (rationalp height) (natp index)
                 (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
            (lw-complex-diskp
             (lw-complex-sub (lw-mellin-sample left-anchor sigma height index 1 left-error)
                             (lw-mellin-sample right-anchor sigma height index 1 right-error))
             (lw-mellin-mesh-pair-radius cap sigma height left-mesh right-mesh left-error right-error)))
   :hints (("Goal" :use (lw-mm-anchor-comparison) :in-theory (enable lw-mellin-mesh-pair-radius)))
   :rule-classes nil))

(defthm lw-mellin-meshes-compare
  (implies (and (lw-mellin-meshp left-anchor start left cap left-mesh)
                (lw-mellin-meshp right-anchor start right cap right-mesh)
                (equal (lw-partition-end start left) (lw-partition-end start right))
                (rationalp sigma) (<= 0 sigma) (rationalp height) (natp index)
                (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
           (lw-complex-diskp
            (lw-complex-sub (lw-mellin-mesh-sum left-anchor start left sigma height index left-error)
                            (lw-mellin-mesh-sum right-anchor start right sigma height index right-error))
            (* (- (lw-partition-end start left) start)
               (lw-mellin-mesh-pair-radius cap sigma height left-mesh right-mesh left-error right-error))))
  :hints (("Goal" :induct (lw-mm-compare-induction left-anchor right-anchor start left right)
                  :do-not '(generalize eliminate-destructors) :in-theory (union-theories (theory 'minimal-theory)
                    '(natp endp not (:induction lw-mm-compare-induction)
                      lw-mm-mesh-data lw-mm-mesh-head lw-mm-mesh-empty lw-mm-end-empty lw-mm-end-cons
                      lw-mm-zero-disk lw-mm-sub-zero lw-mm-sum-empty lw-mm-left-commutes lw-mm-times-negative lw-mm-negative-times
                      lw-mm-zero-times lw-mm-minus-one lw-mm-add-cancel lw-mm-left-distribute
                      associativity-of-+ commutativity-of-+ commutativity-2-of-+ commutativity-of-* associativity-of-*
                      distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)))
          ("Subgoal *1/4" :use ((:instance lw-mm-mesh-data (anchor left-anchor) (endpoints left) (mesh left-mesh))
                       (:instance lw-mm-mesh-data (anchor right-anchor) (endpoints right) (mesh right-mesh))
                       (:instance lw-mm-mesh-head (anchor left-anchor) (endpoints left) (mesh left-mesh))
                       (:instance lw-mm-mesh-head (anchor right-anchor) (endpoints right) (mesh right-mesh))
                       (:instance lw-mm-mesh-empty (anchor left-anchor) (endpoints left) (mesh left-mesh))
                       (:instance lw-mm-mesh-empty (anchor right-anchor) (endpoints right) (mesh right-mesh))
                       (:instance lw-mellin-mesh-end-bounds (anchor (car left)) (start (car left)) (endpoints (cdr left)) (mesh left-mesh))
                       (:instance lw-mellin-mesh-end-bounds (anchor (car right)) (start (car right)) (endpoints (cdr right)) (mesh right-mesh))
                       (:instance lw-mellin-mesh-end-bounds (anchor left-anchor) (endpoints left) (mesh left-mesh))
                       (:instance lw-mellin-mesh-end-bounds (anchor right-anchor) (endpoints right) (mesh right-mesh))
                       lw-mellin-mesh-pair-radius-valid lw-mm-anchor-pair-bound
                       (:instance lw-mellin-sample-rational (value left-anchor) (step 1) (error left-error))
                       (:instance lw-mellin-sample-rational (value right-anchor) (step 1) (error right-error))
                       (:instance lw-mellin-mesh-sum-rational (anchor (car left)) (start (car left)) (endpoints (cdr left)) (mesh left-mesh) (error left-error))
                       (:instance lw-mellin-mesh-sum-rational (anchor (car right)) (start (car right)) (endpoints (cdr right)) (mesh right-mesh) (error right-error))
                       (:instance lw-mm-join-comparison
                         (a (lw-mellin-sample left-anchor sigma height index 1 left-error))
                         (b (lw-mellin-sample right-anchor sigma height index 1 right-error))
                         (left (lw-mellin-mesh-sum (car left) (car left) (cdr left) sigma height index left-error)) (right (lw-mellin-mesh-sum (car right) (car right) (cdr right) sigma height index right-error))
                         (weight (- (car left) start)) (rest-weight (- (lw-partition-end start left) (car left)))
                         (radius (lw-mellin-mesh-pair-radius cap sigma height left-mesh right-mesh left-error right-error))))
                  :expand ((lw-mellin-mesh-sum left-anchor start left sigma height index left-error) (lw-mellin-mesh-sum right-anchor start right sigma height index right-error))
                  :in-theory (union-theories (theory 'minimal-theory)
                    '(natp endp not (:induction lw-mm-compare-induction)
                      lw-mm-mesh-data lw-mm-mesh-head lw-mm-mesh-empty lw-mm-end-empty lw-mm-end-cons
                      lw-mm-zero-disk lw-mm-sub-zero lw-mm-sum-empty lw-mm-left-commutes lw-mm-times-negative lw-mm-negative-times
                      lw-mm-zero-times lw-mm-minus-one lw-mm-add-cancel lw-mm-left-distribute
                      associativity-of-+ commutativity-of-+ commutativity-2-of-+ commutativity-of-* associativity-of-*
                      distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)) :do-not '(generalize eliminate-destructors) :do-not-induct t)
          ("Subgoal *1/3" :use ((:instance lw-mm-mesh-data (anchor left-anchor) (endpoints left) (mesh left-mesh))
                       (:instance lw-mm-mesh-data (anchor right-anchor) (endpoints right) (mesh right-mesh))
                       (:instance lw-mm-mesh-head (anchor left-anchor) (endpoints left) (mesh left-mesh))
                       (:instance lw-mm-mesh-head (anchor right-anchor) (endpoints right) (mesh right-mesh))
                       (:instance lw-mm-mesh-empty (anchor left-anchor) (endpoints left) (mesh left-mesh))
                       (:instance lw-mm-mesh-empty (anchor right-anchor) (endpoints right) (mesh right-mesh))
                       (:instance lw-mellin-mesh-end-bounds (anchor (car left)) (start (car left)) (endpoints (cdr left)) (mesh left-mesh))
                       (:instance lw-mellin-mesh-end-bounds (anchor (car right)) (start (car right)) (endpoints (cdr right)) (mesh right-mesh))
                       (:instance lw-mellin-mesh-end-bounds (anchor left-anchor) (endpoints left) (mesh left-mesh))
                       (:instance lw-mellin-mesh-end-bounds (anchor right-anchor) (endpoints right) (mesh right-mesh))
                       lw-mellin-mesh-pair-radius-valid lw-mm-anchor-pair-bound
                       (:instance lw-mellin-sample-rational (value left-anchor) (step 1) (error left-error))
                       (:instance lw-mellin-sample-rational (value right-anchor) (step 1) (error right-error))
                       (:instance lw-mellin-mesh-trim-valid (anchor left-anchor) (endpoints left) (mesh left-mesh) (cut (car right)))
                       (:instance lw-mellin-mesh-split-first (anchor left-anchor) (endpoints left) (mesh left-mesh) (error left-error) (cut (car right)))
                       (:instance lw-mellin-mesh-sum-rational (anchor left-anchor) (start (car right)) (endpoints left) (mesh left-mesh) (error left-error))
                       (:instance lw-mellin-mesh-sum-rational (anchor (car right)) (start (car right)) (endpoints (cdr right)) (mesh right-mesh) (error right-error))
                       (:instance lw-mm-join-comparison
                         (a (lw-mellin-sample left-anchor sigma height index 1 left-error))
                         (b (lw-mellin-sample right-anchor sigma height index 1 right-error))
                         (left (lw-mellin-mesh-sum left-anchor (car right) left sigma height index left-error)) (right (lw-mellin-mesh-sum (car right) (car right) (cdr right) sigma height index right-error))
                         (weight (- (car right) start)) (rest-weight (- (lw-partition-end start left) (car right)))
                         (radius (lw-mellin-mesh-pair-radius cap sigma height left-mesh right-mesh left-error right-error))))
                  :expand ((lw-mellin-mesh-sum right-anchor start right sigma height index right-error))
                  :in-theory (union-theories (theory 'minimal-theory)
                    '(natp endp not (:induction lw-mm-compare-induction)
                      lw-mm-mesh-data lw-mm-mesh-head lw-mm-mesh-empty lw-mm-end-empty lw-mm-end-cons
                      lw-mm-zero-disk lw-mm-sub-zero lw-mm-sum-empty lw-mm-left-commutes lw-mm-times-negative lw-mm-negative-times
                      lw-mm-zero-times lw-mm-minus-one lw-mm-add-cancel lw-mm-left-distribute
                      associativity-of-+ commutativity-of-+ commutativity-2-of-+ commutativity-of-* associativity-of-*
                      distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)) :do-not '(generalize eliminate-destructors) :do-not-induct t)
          ("Subgoal *1/2" :use ((:instance lw-mm-mesh-data (anchor left-anchor) (endpoints left) (mesh left-mesh))
                       (:instance lw-mm-mesh-data (anchor right-anchor) (endpoints right) (mesh right-mesh))
                       (:instance lw-mm-mesh-head (anchor left-anchor) (endpoints left) (mesh left-mesh))
                       (:instance lw-mm-mesh-head (anchor right-anchor) (endpoints right) (mesh right-mesh))
                       (:instance lw-mm-mesh-empty (anchor left-anchor) (endpoints left) (mesh left-mesh))
                       (:instance lw-mm-mesh-empty (anchor right-anchor) (endpoints right) (mesh right-mesh))
                       (:instance lw-mellin-mesh-end-bounds (anchor (car left)) (start (car left)) (endpoints (cdr left)) (mesh left-mesh))
                       (:instance lw-mellin-mesh-end-bounds (anchor (car right)) (start (car right)) (endpoints (cdr right)) (mesh right-mesh))
                       (:instance lw-mellin-mesh-end-bounds (anchor left-anchor) (endpoints left) (mesh left-mesh))
                       (:instance lw-mellin-mesh-end-bounds (anchor right-anchor) (endpoints right) (mesh right-mesh))
                       lw-mellin-mesh-pair-radius-valid lw-mm-anchor-pair-bound
                       (:instance lw-mellin-sample-rational (value left-anchor) (step 1) (error left-error))
                       (:instance lw-mellin-sample-rational (value right-anchor) (step 1) (error right-error))
                       (:instance lw-mellin-mesh-trim-valid (anchor right-anchor) (endpoints right) (mesh right-mesh) (cut (car left)))
                       (:instance lw-mellin-mesh-split-first (anchor right-anchor) (endpoints right) (mesh right-mesh) (error right-error) (cut (car left)))
                       (:instance lw-mellin-mesh-sum-rational (anchor (car left)) (start (car left)) (endpoints (cdr left)) (mesh left-mesh) (error left-error))
                       (:instance lw-mellin-mesh-sum-rational (anchor right-anchor) (start (car left)) (endpoints right) (mesh right-mesh) (error right-error))
                       (:instance lw-mm-join-comparison
                         (a (lw-mellin-sample left-anchor sigma height index 1 left-error))
                         (b (lw-mellin-sample right-anchor sigma height index 1 right-error))
                         (left (lw-mellin-mesh-sum (car left) (car left) (cdr left) sigma height index left-error)) (right (lw-mellin-mesh-sum right-anchor (car left) right sigma height index right-error))
                         (weight (- (car left) start)) (rest-weight (- (lw-partition-end start left) (car left)))
                         (radius (lw-mellin-mesh-pair-radius cap sigma height left-mesh right-mesh left-error right-error))))
                  :expand ((lw-mellin-mesh-sum left-anchor start left sigma height index left-error))
                  :in-theory (union-theories (theory 'minimal-theory)
                    '(natp endp not (:induction lw-mm-compare-induction)
                      lw-mm-mesh-data lw-mm-mesh-head lw-mm-mesh-empty lw-mm-end-empty lw-mm-end-cons
                      lw-mm-zero-disk lw-mm-sub-zero lw-mm-sum-empty lw-mm-left-commutes lw-mm-times-negative lw-mm-negative-times
                      lw-mm-zero-times lw-mm-minus-one lw-mm-add-cancel lw-mm-left-distribute
                      associativity-of-+ commutativity-of-+ commutativity-2-of-+ commutativity-of-* associativity-of-*
                      distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)) :do-not '(generalize eliminate-destructors) :do-not-induct t)
          ("Subgoal *1/1" :use ((:instance lw-mm-mesh-data (anchor left-anchor) (endpoints left) (mesh left-mesh))
                       (:instance lw-mm-mesh-data (anchor right-anchor) (endpoints right) (mesh right-mesh))
                       (:instance lw-mm-mesh-head (anchor left-anchor) (endpoints left) (mesh left-mesh))
                       (:instance lw-mm-mesh-head (anchor right-anchor) (endpoints right) (mesh right-mesh))
                       (:instance lw-mm-mesh-empty (anchor left-anchor) (endpoints left) (mesh left-mesh))
                       (:instance lw-mm-mesh-empty (anchor right-anchor) (endpoints right) (mesh right-mesh))
                       (:instance lw-mellin-mesh-end-bounds (anchor (car left)) (start (car left)) (endpoints (cdr left)) (mesh left-mesh))
                       (:instance lw-mellin-mesh-end-bounds (anchor (car right)) (start (car right)) (endpoints (cdr right)) (mesh right-mesh))
                       (:instance lw-mellin-mesh-end-bounds (anchor left-anchor) (endpoints left) (mesh left-mesh))
                       (:instance lw-mellin-mesh-end-bounds (anchor right-anchor) (endpoints right) (mesh right-mesh)))
                  :expand ((lw-mellin-mesh-sum left-anchor start left sigma height index left-error) (lw-mellin-mesh-sum right-anchor start right sigma height index right-error))
                  :in-theory (union-theories (theory 'minimal-theory)
                    '(natp endp not (:induction lw-mm-compare-induction)
                      lw-mm-mesh-data lw-mm-mesh-head lw-mm-mesh-empty lw-mm-end-empty lw-mm-end-cons
                      lw-mm-zero-disk lw-mm-sub-zero lw-mm-sum-empty lw-mm-left-commutes lw-mm-times-negative lw-mm-negative-times
                      lw-mm-zero-times lw-mm-minus-one lw-mm-add-cancel lw-mm-left-distribute
                      associativity-of-+ commutativity-of-+ commutativity-2-of-+ commutativity-of-* associativity-of-*
                      distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)) :do-not '(generalize eliminate-destructors) :do-not-induct t)))

(local (in-theory (disable lw-mellin-meshes-compare lw-mellin-mesh-pair-radius)))

(defthm lw-mellin-mesh-true-list
  (implies (lw-mellin-meshp anchor start endpoints cap mesh) (true-listp endpoints))
  :hints (("Goal" :induct (lw-mellin-meshp anchor start endpoints cap mesh)
                  :in-theory (enable lw-mellin-meshp))))

(defthm lw-mellin-mesh-append-valid
  (implies (and (lw-mellin-meshp start start prefix cap mesh)
                (lw-mellin-meshp (lw-partition-end start prefix) (lw-partition-end start prefix) suffix cap mesh))
           (lw-mellin-meshp start start (append prefix suffix) cap mesh))
  :hints (("Goal" :induct (lw-mellin-meshp start start prefix cap mesh)
                  :in-theory (enable lw-mellin-meshp lw-partition-end))))

(local (defthm lw-mm-add-associative
         (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c))
                  (equal (lw-complex-add (lw-complex-add a b) c) (lw-complex-add a (lw-complex-add b c))))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-add)))))
(local (defthm lw-mm-add-zero
         (implies (lw-complexp a)
                  (and (equal (lw-complex-add (cons 0 0) a) a) (equal (lw-complex-add a (cons 0 0)) a)))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-add)))))

(defthm lw-mellin-mesh-sum-append
  (implies (and (lw-mellin-meshp start start prefix cap mesh)
                (lw-mellin-meshp (lw-partition-end start prefix) (lw-partition-end start prefix) suffix cap mesh)
                (rationalp sigma) (<= 0 sigma) (rationalp height) (rationalp error) (< 0 error))
           (equal (lw-mellin-mesh-sum start start (append prefix suffix) sigma height index error)
                  (lw-complex-add (lw-mellin-mesh-sum start start prefix sigma height index error)
                                  (lw-mellin-mesh-sum (lw-partition-end start prefix) (lw-partition-end start prefix)
                                                     suffix sigma height index error))))
  :hints (("Goal" :induct (lw-mellin-meshp start start prefix cap mesh)
                  :in-theory (enable lw-mellin-meshp lw-mellin-mesh-sum lw-partition-end))
          (and stable-under-simplificationp
               '(:use ((:instance lw-mellin-sample-rational (value start) (step 1))
                       (:instance lw-mellin-mesh-sum-rational
                         (anchor (car prefix)) (start (car prefix)) (endpoints (cdr prefix)))
                       (:instance lw-mellin-mesh-sum-rational
                         (anchor (lw-partition-end start prefix)) (start (lw-partition-end start prefix)) (endpoints suffix)))
                 :in-theory (e/d (lw-mellin-meshp lw-mellin-mesh-sum lw-partition-end lw-complex-scale lw-complex-add lw-complexp)
                                 (lw-mellin-mesh-sum-rational))))))

(defun lw-mellin-dyadic-endpoints (start end depth)
  (declare (xargs :measure (nfix depth)))
  (if (<= end start) nil
    (if (zp depth) (list end)
      (append (lw-mellin-dyadic-endpoints start (/ (+ start end) 2) (- depth 1))
              (lw-mellin-dyadic-endpoints (/ (+ start end) 2) end (- depth 1))))))

(defthm lw-mellin-dyadic-endpoints-end
  (implies (and (rationalp start) (rationalp end) (<= start end))
           (equal (lw-partition-end start (lw-mellin-dyadic-endpoints start end depth)) end))
  :hints (("Goal" :induct (lw-mellin-dyadic-endpoints start end depth))))

(local (defthm lw-mm-left-span
         (implies (and (rationalp start) (rationalp end))
                  (equal (- (/ (+ start end) 2) start) (* 1/2 (- end start))))
         :hints (("Goal" :nonlinearp t))))
(local (defthm lw-mm-right-span
         (implies (and (rationalp start) (rationalp end))
                  (equal (- end (/ (+ start end) 2)) (* 1/2 (- end start))))
         :hints (("Goal" :nonlinearp t))))
(local (defthm lw-mm-zero-mesh
         (implies (zp depth) (equal (lw-halved-width width depth) width))
         :hints (("Goal" :in-theory (enable lw-halved-width)))))
(local (defthm lw-mm-empty-mesh-valid
         (implies (and (rationalp start) (<= 0 start) (rationalp cap) (<= start cap) (rationalp mesh) (<= 0 mesh))
                  (lw-mellin-meshp start start nil cap mesh))
         :hints (("Goal" :in-theory (enable lw-mellin-meshp)))))

(defthm lw-mellin-dyadic-endpoints-valid
  (implies (and (rationalp start) (<= 0 start) (rationalp end) (<= start end) (rationalp cap) (<= end cap)
                (rationalp mesh) (<= 0 mesh) (natp depth) (<= (lw-halved-width (- end start) depth) mesh))
           (lw-mellin-meshp start start (lw-mellin-dyadic-endpoints start end depth) cap mesh))
  :hints (("Goal" :induct (lw-mellin-dyadic-endpoints start end depth)
                  :in-theory (disable distributivity lw-mm-left-distribute lw-mm-left-span lw-mm-right-span))
          (and stable-under-simplificationp
               '(:use (lw-mm-left-span lw-mm-right-span
                       (:instance lw-halved-width-half (width (- end start)) (steps (- depth 1)))
                       (:instance lw-mellin-mesh-append-valid
                         (prefix (lw-mellin-dyadic-endpoints start (/ (+ start end) 2) (- depth 1)))
                         (suffix (lw-mellin-dyadic-endpoints (/ (+ start end) 2) end (- depth 1)))))
                 :expand ((lw-mellin-dyadic-endpoints start end depth)
                          (lw-mellin-meshp start start (list end) cap mesh)
                          (lw-mellin-meshp start start nil cap mesh)
                          (lw-halved-width (- end start) depth))
                 :in-theory (disable distributivity lw-mm-left-distribute lw-mm-left-span lw-mm-right-span
                                     lw-halved-width-half lw-mellin-mesh-append-valid)
                 :do-not-induct t))))



(local (defthm lw-mm-midpoint-self
         (implies (rationalp start) (equal (/ (+ start start) 2) start))
         :hints (("Goal" :nonlinearp t))))
(local (defthm lw-mm-dyadic-zero
         (implies (zp depth)
                  (equal (lw-mellin-dyadic-sum start end depth sigma height index error)
                         (lw-complex-scale (- end start) (lw-mellin-sample start sigma height index 1 error))))
         :hints (("Goal" :in-theory (enable lw-mellin-dyadic-sum)))))
(local (defthm lw-mm-scale-rational
         (implies (and (lw-complexp point) (rationalp factor)) (lw-complexp (lw-complex-scale factor point)))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-scale)))))

(defthm lw-mellin-dyadic-empty-interval
  (implies (rationalp start) (equal (lw-mellin-dyadic-sum start start depth sigma height index error) (cons 0 0)))
  :hints (("Goal" :induct (lw-mellin-dyadic-sum start start depth sigma height index error)
                  :in-theory (enable lw-complex-scale lw-complex-add))))

(defthm lw-mellin-mesh-sum-dyadic
  (implies (and (rationalp start) (<= 0 start) (rationalp end) (<= start end) (rationalp cap) (<= end cap)
                (rationalp mesh) (<= 0 mesh) (natp depth) (<= (lw-halved-width (- end start) depth) mesh)
                (rationalp sigma) (<= 0 sigma) (rationalp height) (rationalp error) (< 0 error))
           (equal (lw-mellin-mesh-sum start start (lw-mellin-dyadic-endpoints start end depth) sigma height index error)
                  (lw-mellin-dyadic-sum start end depth sigma height index error)))
  :hints (("Goal" :induct (lw-mellin-dyadic-endpoints start end depth)
                  :in-theory (disable (:definition lw-mellin-dyadic-sum) distributivity lw-mm-left-distribute
                                      lw-mm-left-span lw-mm-right-span lw-mellin-mesh-sum-append))
          (and stable-under-simplificationp
               '(:use (lw-mm-left-span lw-mm-right-span
                       (:instance lw-mellin-sample-rational (value start) (step 1))
                       (:instance lw-halved-width-half (width (- end start)) (steps (- depth 1)))
                       (:instance lw-mellin-dyadic-endpoints-valid (end (/ (+ start end) 2)) (depth (- depth 1)))
                       (:instance lw-mellin-dyadic-endpoints-valid (start (/ (+ start end) 2)) (depth (- depth 1)))
                       (:instance lw-mellin-mesh-sum-append
                         (prefix (lw-mellin-dyadic-endpoints start (/ (+ start end) 2) (- depth 1)))
                         (suffix (lw-mellin-dyadic-endpoints (/ (+ start end) 2) end (- depth 1)))))
                 :expand ((lw-mellin-dyadic-endpoints start end depth)
                          (lw-mellin-dyadic-sum start end depth sigma height index error)
                          (lw-mellin-mesh-sum start start (list end) sigma height index error)
                          (lw-halved-width (- end start) depth))
                 :in-theory (disable (:definition lw-mellin-dyadic-sum) distributivity lw-mm-left-distribute lw-mm-left-span lw-mm-right-span
                                     lw-halved-width-half lw-mellin-dyadic-endpoints-valid lw-mellin-mesh-sum-append)
                 :do-not-induct t))))

(defthm lw-mellin-dyadic-split-comparison
  (implies (and (rationalp cap) (<= 0 cap) (rationalp cut) (<= 0 cut) (<= cut cap)
                (rationalp left-mesh) (<= 0 left-mesh) (rationalp right-mesh) (<= 0 right-mesh)
                (natp depth) (natp prefix-depth) (natp tail-depth)
                (<= (lw-halved-width cap depth) left-mesh)
                (<= (lw-halved-width cut prefix-depth) right-mesh)
                (<= (lw-halved-width (- cap cut) tail-depth) right-mesh)
                (rationalp sigma) (<= 0 sigma) (rationalp height) (natp index)
                (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
           (lw-complex-diskp
            (lw-complex-sub
             (lw-mellin-dyadic-sum 0 cap depth sigma height index left-error)
             (lw-complex-add (lw-mellin-dyadic-sum 0 cut prefix-depth sigma height index right-error)
                             (lw-mellin-dyadic-sum cut cap tail-depth sigma height index right-error)))
            (* cap (lw-mellin-mesh-pair-radius cap sigma height left-mesh right-mesh left-error right-error))))
  :hints (("Goal"
           :use ((:instance lw-mellin-dyadic-endpoints-valid (start 0) (end cap) (mesh left-mesh))
                 (:instance lw-mellin-dyadic-endpoints-valid (start 0) (end cut) (depth prefix-depth) (mesh right-mesh))
                 (:instance lw-mellin-dyadic-endpoints-valid (start cut) (end cap) (depth tail-depth) (mesh right-mesh))
                 (:instance lw-mellin-mesh-append-valid (start 0) (mesh right-mesh)
                   (prefix (lw-mellin-dyadic-endpoints 0 cut prefix-depth)) (suffix (lw-mellin-dyadic-endpoints cut cap tail-depth)))
                 (:instance lw-mellin-mesh-sum-append (start 0) (mesh right-mesh) (error right-error)
                   (prefix (lw-mellin-dyadic-endpoints 0 cut prefix-depth)) (suffix (lw-mellin-dyadic-endpoints cut cap tail-depth)))
                 (:instance lw-mellin-mesh-sum-dyadic (start 0) (end cap) (mesh left-mesh) (error left-error))
                 (:instance lw-mellin-mesh-sum-dyadic (start 0) (end cut) (depth prefix-depth) (mesh right-mesh) (error right-error))
                 (:instance lw-mellin-mesh-sum-dyadic (start cut) (end cap) (depth tail-depth) (mesh right-mesh) (error right-error))
                 (:instance lw-mellin-meshes-compare (left-anchor 0) (right-anchor 0) (start 0)
                   (left (lw-mellin-dyadic-endpoints 0 cap depth))
                   (right (append (lw-mellin-dyadic-endpoints 0 cut prefix-depth) (lw-mellin-dyadic-endpoints cut cap tail-depth)))))
           :in-theory (disable lw-mellin-dyadic-endpoints lw-mellin-dyadic-sum lw-mellin-mesh-sum lw-mellin-meshp
                               lw-mellin-dyadic-endpoints-valid lw-mellin-mesh-append-valid lw-mellin-mesh-sum-append
                               lw-mellin-mesh-sum-dyadic lw-partition-end))))

