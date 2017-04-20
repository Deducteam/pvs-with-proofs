(defcl dpinfo ()       ;;decision proc. information.
  (dpinfo-sigalist :initform nil)
  (dpinfo-findalist :initform nil)
  (dpinfo-context :initform nil)
  (dpinfo-usealist :initform nil))

(newdefcl proofstate ()
  (label :initform " ")
  current-goal         ;;is a sequent
  (current-rule :initform nil)
  (dp-state :initform *init-dp-state*)
  (done-subgoals :initform nil)
  (pending-subgoals :initform nil)
  current-subgoal      
  (remaining-subgoals :initform nil)
  (status :initform (cons nil 'noproof0))
  (subgoalnum :initform 0)
  (justification :initform nil)
  (current-input :initform nil)
  (parsed-input :initform nil)
  (printout :initform nil)
  (comment :initform nil)
  strategy
  (context :initform nil)
  (parent-proofstate :initform nil)
  (proof-dependent-decls :initform nil);;collects decls seen so far
  (dependent-decls :initform nil)
  (current-auto-rewrites :initform nil)
  (tcc-hash :initform (make-pvs-hash-table))
  (subtype-hash :initform (make-pvs-hash-table))
  (rewrite-hash :initform (make-pvs-hash-table))
  (typepred-hash :initform (make-pvs-hash-table))
  (current-xrule :initform nil))

;; to get again a status flag when calling (status-flag ...)
(defmethod status-flag ((ps proofstate))
  (car (status ps)))

(newdefcl apply-proofstate (proofstate)
  (apply-parent-proofstate :initform nil))

(newdefcl tcc-proofstate (proofstate))

(newdefcl top-proofstate (proofstate)
  (in-justification :initform nil)
  declaration)

(newdefcl strat-proofstate (proofstate))
