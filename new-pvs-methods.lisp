(in-package :pvs)

(defmethod copy ((obj strat-proofstate) &rest initargs)
  (with-slots (label current-goal current-rule dp-state done-subgoals
                     pending-subgoals current-subgoal
                     remaining-subgoals status subgoalnum justification
                     current-input parsed-input printout comment
                     strategy context parent-proofstate
                     proof-dependent-decls dependent-decls
                     current-auto-rewrites tcc-hash subtype-hash
                     rewrite-hash typepred-hash current-xrule)
    obj
    (make-instance 'strat-proofstate :label
                   (let* ((get1 (getf initargs 'label '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :label '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) label getfv))
                   :current-goal
                   (let* ((get1 (getf initargs 'current-goal '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :current-goal '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) current-goal getfv))
                   :current-rule
                   (let* ((get1 (getf initargs 'current-rule '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :current-rule '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) current-rule getfv))
                   :dp-state
                   (let* ((get1 (getf initargs 'dp-state '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :dp-state '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) dp-state getfv))
                   :done-subgoals
                   (let* ((get1
                           (getf initargs 'done-subgoals '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :done-subgoals '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) done-subgoals getfv))
                   :pending-subgoals
                   (let* ((get1
                           (getf initargs 'pending-subgoals '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf
                                initargs
                                :pending-subgoals
                                '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) pending-subgoals getfv))
                   :current-subgoal
                   (let* ((get1
                           (getf initargs 'current-subgoal '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf
                                initargs
                                :current-subgoal
                                '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) current-subgoal getfv))
                   :remaining-subgoals
                   (let* ((get1
                           (getf initargs 'remaining-subgoals
                                 '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf
                                initargs
                                :remaining-subgoals
                                '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) remaining-subgoals getfv))
                   :status
                   (let* ((get1 (getf initargs 'status '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :status '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) status getfv))
                   :subgoalnum
                   (let* ((get1 (getf initargs 'subgoalnum '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :subgoalnum '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) subgoalnum getfv))
                   :justification
                   (let* ((get1
                           (getf initargs 'justification '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :justification '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) justification getfv))
                   :current-input
                   (let* ((get1
                           (getf initargs 'current-input '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :current-input '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) current-input getfv))
                   :parsed-input
                   (let* ((get1 (getf initargs 'parsed-input '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :parsed-input '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) parsed-input getfv))
                   :printout
                   (let* ((get1 (getf initargs 'printout '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :printout '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) printout getfv))
                   :comment
                   (let* ((get1 (getf initargs 'comment '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :comment '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) comment getfv))
                   :strategy
                   (let* ((get1 (getf initargs 'strategy '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :strategy '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) strategy getfv))
                   :context
                   (let* ((get1 (getf initargs 'context '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :context '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) context getfv))
                   :parent-proofstate
                   (let* ((get1
                           (getf initargs 'parent-proofstate '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf
                                initargs
                                :parent-proofstate
                                '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) parent-proofstate getfv))
                   :proof-dependent-decls
                   (let* ((get1
                           (getf initargs 'proof-dependent-decls
                                 '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf
                                initargs
                                :proof-dependent-decls
                                '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf)
                         proof-dependent-decls
                       getfv))
                   :dependent-decls
                   (let* ((get1
                           (getf initargs 'dependent-decls '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf
                                initargs
                                :dependent-decls
                                '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) dependent-decls getfv))
                   :current-auto-rewrites
                   (let* ((get1
                           (getf initargs 'current-auto-rewrites
                                 '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf
                                initargs
                                :current-auto-rewrites
                                '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf)
                         current-auto-rewrites
                       getfv))
                   :tcc-hash
                   (let* ((get1 (getf initargs 'tcc-hash '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :tcc-hash '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) tcc-hash getfv))
                   :subtype-hash
                   (let* ((get1 (getf initargs 'subtype-hash '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :subtype-hash '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) subtype-hash getfv))
                   :rewrite-hash
                   (let* ((get1 (getf initargs 'rewrite-hash '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :rewrite-hash '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) rewrite-hash getfv))
                   :typepred-hash
                   (let* ((get1
                           (getf initargs 'typepred-hash '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :typepred-hash '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) typepred-hash getfv))
                   :current-xrule
                   (let* ((get1
                           (getf initargs 'current-xrule '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :current-xrule '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) current-xrule getfv)))))

(defmethod store-object* ((obj strat-proofstate))
  (reserve-space 27
                 (with-slots (label current-goal current-rule dp-state
                                    done-subgoals pending-subgoals
                                    current-subgoal remaining-subgoals
                                    status subgoalnum justification
                                    current-input parsed-input printout
                                    comment strategy context
                                    parent-proofstate
                                    proof-dependent-decls
                                    dependent-decls
                                    current-auto-rewrites tcc-hash
                                    subtype-hash rewrite-hash
                                    typepred-hash current-xrule)
                   obj
                   (push-word (store-obj 'strat-proofstate))
                   (push-word (store-obj label))
                   (push-word (store-obj current-goal))
                   (push-word (store-obj current-rule))
                   (push-word (store-obj dp-state))
                   (push-word (store-obj done-subgoals))
                   (push-word (store-obj pending-subgoals))
                   (push-word (store-obj current-subgoal))
                   (push-word (store-obj remaining-subgoals))
                   (push-word (store-obj status))
                   (push-word (store-obj subgoalnum))
                   (push-word (store-obj justification))
                   (push-word (store-obj current-input))
                   (push-word (store-obj parsed-input))
                   (push-word (store-obj printout))
                   (push-word (store-obj comment))
                   (push-word (store-obj strategy))
                   (push-word (store-obj context))
                   (push-word (store-obj parent-proofstate))
                   (push-word (store-obj proof-dependent-decls))
                   (push-word (store-obj dependent-decls))
                   (push-word (store-obj current-auto-rewrites))
                   (push-word (store-obj tcc-hash))
                   (push-word (store-obj subtype-hash))
                   (push-word (store-obj rewrite-hash))
                   (push-word (store-obj typepred-hash))
                   (push-word (store-obj current-xrule)))))

(defmethod update-fetched ((obj strat-proofstate))
  (with-slots (label current-goal current-rule dp-state done-subgoals
                     pending-subgoals current-subgoal
                     remaining-subgoals status subgoalnum justification
                     current-input parsed-input printout comment
                     strategy context parent-proofstate
                     proof-dependent-decls dependent-decls
                     current-auto-rewrites tcc-hash subtype-hash
                     rewrite-hash typepred-hash current-xrule)
    obj
    (setf label (fetch-obj (stored-word 1)))
    (setf current-goal (fetch-obj (stored-word 2)))
    (setf current-rule (fetch-obj (stored-word 3)))
    (setf dp-state (fetch-obj (stored-word 4)))
    (setf done-subgoals (fetch-obj (stored-word 5)))
    (setf pending-subgoals (fetch-obj (stored-word 6)))
    (setf current-subgoal (fetch-obj (stored-word 7)))
    (setf remaining-subgoals (fetch-obj (stored-word 8)))
    (setf status (fetch-obj (stored-word 9)))
    (setf subgoalnum (fetch-obj (stored-word 10)))
    (setf justification (fetch-obj (stored-word 11)))
    (setf current-input (fetch-obj (stored-word 12)))
    (setf parsed-input (fetch-obj (stored-word 13)))
    (setf printout (fetch-obj (stored-word 14)))
    (setf comment (fetch-obj (stored-word 15)))
    (setf strategy (fetch-obj (stored-word 16)))
    (setf context (fetch-obj (stored-word 17)))
    (setf parent-proofstate (fetch-obj (stored-word 18)))
    (setf proof-dependent-decls (fetch-obj (stored-word 19)))
    (setf dependent-decls (fetch-obj (stored-word 20)))
    (setf current-auto-rewrites (fetch-obj (stored-word 21)))
    (setf tcc-hash (fetch-obj (stored-word 22)))
    (setf subtype-hash (fetch-obj (stored-word 23)))
    (setf rewrite-hash (fetch-obj (stored-word 24)))
    (setf typepred-hash (fetch-obj (stored-word 25)))
    (setf current-xrule (fetch-obj (stored-word 26)))))

(defmethod restore-object* ((obj strat-proofstate))
  (let ((*restore-object-parent* obj))
    (with-slots (label current-goal current-rule dp-state done-subgoals
                       pending-subgoals current-subgoal
                       remaining-subgoals status subgoalnum
                       justification current-input parsed-input
                       printout comment strategy context
                       parent-proofstate proof-dependent-decls
                       dependent-decls current-auto-rewrites tcc-hash
                       subtype-hash rewrite-hash typepred-hash
                       current-xrule)
      obj
      (when label
        (let ((*restore-object-parent-slot* 'label))
          (restore-object* label)))
      (when current-goal
        (let ((*restore-object-parent-slot* 'current-goal))
          (restore-object* current-goal)))
      (when current-rule
        (let ((*restore-object-parent-slot* 'current-rule))
          (restore-object* current-rule)))
      (when dp-state
        (let ((*restore-object-parent-slot* 'dp-state))
          (restore-object* dp-state)))
      (when done-subgoals
        (let ((*restore-object-parent-slot* 'done-subgoals))
          (restore-object* done-subgoals)))
      (when pending-subgoals
        (let ((*restore-object-parent-slot* 'pending-subgoals))
          (restore-object* pending-subgoals)))
      (when current-subgoal
        (let ((*restore-object-parent-slot* 'current-subgoal))
          (restore-object* current-subgoal)))
      (when remaining-subgoals
        (let ((*restore-object-parent-slot* 'remaining-subgoals))
          (restore-object* remaining-subgoals)))
      (when status
        (let ((*restore-object-parent-slot* 'status))
          (restore-object* status)))
      (when subgoalnum
        (let ((*restore-object-parent-slot* 'subgoalnum))
          (restore-object* subgoalnum)))
      (when justification
        (let ((*restore-object-parent-slot* 'justification))
          (restore-object* justification)))
      (when current-input
        (let ((*restore-object-parent-slot* 'current-input))
          (restore-object* current-input)))
      (when parsed-input
        (let ((*restore-object-parent-slot* 'parsed-input))
          (restore-object* parsed-input)))
      (when printout
        (let ((*restore-object-parent-slot* 'printout))
          (restore-object* printout)))
      (when comment
        (let ((*restore-object-parent-slot* 'comment))
          (restore-object* comment)))
      (when strategy
        (let ((*restore-object-parent-slot* 'strategy))
          (restore-object* strategy)))
      (when context
        (let ((*restore-object-parent-slot* 'context))
          (restore-object* context)))
      (when parent-proofstate
        (let ((*restore-object-parent-slot* 'parent-proofstate))
          (restore-object* parent-proofstate)))
      (when proof-dependent-decls
        (let ((*restore-object-parent-slot* 'proof-dependent-decls))
          (restore-object* proof-dependent-decls)))
      (when dependent-decls
        (let ((*restore-object-parent-slot* 'dependent-decls))
          (restore-object* dependent-decls)))
      (when current-auto-rewrites
        (let ((*restore-object-parent-slot* 'current-auto-rewrites))
          (restore-object* current-auto-rewrites)))
      (when tcc-hash
        (let ((*restore-object-parent-slot* 'tcc-hash))
          (restore-object* tcc-hash)))
      (when subtype-hash
        (let ((*restore-object-parent-slot* 'subtype-hash))
          (restore-object* subtype-hash)))
      (when rewrite-hash
        (let ((*restore-object-parent-slot* 'rewrite-hash))
          (restore-object* rewrite-hash)))
      (when typepred-hash
        (let ((*restore-object-parent-slot* 'typepred-hash))
          (restore-object* typepred-hash)))
      (when current-xrule
        (let ((*restore-object-parent-slot* 'current-xrule))
          (restore-object* current-xrule)))
      obj)))

(defmethod copy ((obj top-proofstate) &rest initargs)
  (with-slots (label current-goal current-rule dp-state done-subgoals
                     pending-subgoals current-subgoal
                     remaining-subgoals status subgoalnum justification
                     current-input parsed-input printout comment
                     strategy context parent-proofstate
                     proof-dependent-decls dependent-decls
                     current-auto-rewrites tcc-hash subtype-hash
                     rewrite-hash typepred-hash current-xrule
                     in-justification declaration)
    obj
    (make-instance 'top-proofstate :label
                   (let* ((get1 (getf initargs 'label '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :label '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) label getfv))
                   :current-goal
                   (let* ((get1 (getf initargs 'current-goal '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :current-goal '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) current-goal getfv))
                   :current-rule
                   (let* ((get1 (getf initargs 'current-rule '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :current-rule '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) current-rule getfv))
                   :dp-state
                   (let* ((get1 (getf initargs 'dp-state '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :dp-state '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) dp-state getfv))
                   :done-subgoals
                   (let* ((get1
                           (getf initargs 'done-subgoals '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :done-subgoals '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) done-subgoals getfv))
                   :pending-subgoals
                   (let* ((get1
                           (getf initargs 'pending-subgoals '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf
                                initargs
                                :pending-subgoals
                                '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) pending-subgoals getfv))
                   :current-subgoal
                   (let* ((get1
                           (getf initargs 'current-subgoal '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf
                                initargs
                                :current-subgoal
                                '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) current-subgoal getfv))
                   :remaining-subgoals
                   (let* ((get1
                           (getf initargs 'remaining-subgoals
                                 '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf
                                initargs
                                :remaining-subgoals
                                '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) remaining-subgoals getfv))
                   :status
                   (let* ((get1 (getf initargs 'status '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :status '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) status getfv))
                   :subgoalnum
                   (let* ((get1 (getf initargs 'subgoalnum '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :subgoalnum '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) subgoalnum getfv))
                   :justification
                   (let* ((get1
                           (getf initargs 'justification '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :justification '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) justification getfv))
                   :current-input
                   (let* ((get1
                           (getf initargs 'current-input '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :current-input '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) current-input getfv))
                   :parsed-input
                   (let* ((get1 (getf initargs 'parsed-input '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :parsed-input '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) parsed-input getfv))
                   :printout
                   (let* ((get1 (getf initargs 'printout '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :printout '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) printout getfv))
                   :comment
                   (let* ((get1 (getf initargs 'comment '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :comment '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) comment getfv))
                   :strategy
                   (let* ((get1 (getf initargs 'strategy '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :strategy '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) strategy getfv))
                   :context
                   (let* ((get1 (getf initargs 'context '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :context '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) context getfv))
                   :parent-proofstate
                   (let* ((get1
                           (getf initargs 'parent-proofstate '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf
                                initargs
                                :parent-proofstate
                                '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) parent-proofstate getfv))
                   :proof-dependent-decls
                   (let* ((get1
                           (getf initargs 'proof-dependent-decls
                                 '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf
                                initargs
                                :proof-dependent-decls
                                '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf)
                         proof-dependent-decls
                       getfv))
                   :dependent-decls
                   (let* ((get1
                           (getf initargs 'dependent-decls '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf
                                initargs
                                :dependent-decls
                                '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) dependent-decls getfv))
                   :current-auto-rewrites
                   (let* ((get1
                           (getf initargs 'current-auto-rewrites
                                 '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf
                                initargs
                                :current-auto-rewrites
                                '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf)
                         current-auto-rewrites
                       getfv))
                   :tcc-hash
                   (let* ((get1 (getf initargs 'tcc-hash '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :tcc-hash '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) tcc-hash getfv))
                   :subtype-hash
                   (let* ((get1 (getf initargs 'subtype-hash '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :subtype-hash '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) subtype-hash getfv))
                   :rewrite-hash
                   (let* ((get1 (getf initargs 'rewrite-hash '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :rewrite-hash '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) rewrite-hash getfv))
                   :typepred-hash
                   (let* ((get1
                           (getf initargs 'typepred-hash '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :typepred-hash '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) typepred-hash getfv))
                   :current-xrule
                   (let* ((get1
                           (getf initargs 'current-xrule '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :current-xrule '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) current-xrule getfv))
                   :in-justification
                   (let* ((get1
                           (getf initargs 'in-justification '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf
                                initargs
                                :in-justification
                                '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) in-justification getfv))
                   :declaration
                   (let* ((get1 (getf initargs 'declaration '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :declaration '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) declaration getfv)))))

(defmethod store-object* ((obj top-proofstate))
  (reserve-space 29
                 (with-slots (label current-goal current-rule dp-state
                                    done-subgoals pending-subgoals
                                    current-subgoal remaining-subgoals
                                    status subgoalnum justification
                                    current-input parsed-input printout
                                    comment strategy context
                                    parent-proofstate
                                    proof-dependent-decls
                                    dependent-decls
                                    current-auto-rewrites tcc-hash
                                    subtype-hash rewrite-hash
                                    typepred-hash current-xrule
                                    in-justification declaration)
                   obj
                   (push-word (store-obj 'top-proofstate))
                   (push-word (store-obj label))
                   (push-word (store-obj current-goal))
                   (push-word (store-obj current-rule))
                   (push-word (store-obj dp-state))
                   (push-word (store-obj done-subgoals))
                   (push-word (store-obj pending-subgoals))
                   (push-word (store-obj current-subgoal))
                   (push-word (store-obj remaining-subgoals))
                   (push-word (store-obj status))
                   (push-word (store-obj subgoalnum))
                   (push-word (store-obj justification))
                   (push-word (store-obj current-input))
                   (push-word (store-obj parsed-input))
                   (push-word (store-obj printout))
                   (push-word (store-obj comment))
                   (push-word (store-obj strategy))
                   (push-word (store-obj context))
                   (push-word (store-obj parent-proofstate))
                   (push-word (store-obj proof-dependent-decls))
                   (push-word (store-obj dependent-decls))
                   (push-word (store-obj current-auto-rewrites))
                   (push-word (store-obj tcc-hash))
                   (push-word (store-obj subtype-hash))
                   (push-word (store-obj rewrite-hash))
                   (push-word (store-obj typepred-hash))
                   (push-word (store-obj current-xrule))
                   (push-word (store-obj in-justification))
                   (push-word (store-obj declaration)))))

(defmethod update-fetched ((obj top-proofstate))
  (with-slots (label current-goal current-rule dp-state done-subgoals
                     pending-subgoals current-subgoal
                     remaining-subgoals status subgoalnum justification
                     current-input parsed-input printout comment
                     strategy context parent-proofstate
                     proof-dependent-decls dependent-decls
                     current-auto-rewrites tcc-hash subtype-hash
                     rewrite-hash typepred-hash current-xrule
                     in-justification declaration)
    obj
    (setf label (fetch-obj (stored-word 1)))
    (setf current-goal (fetch-obj (stored-word 2)))
    (setf current-rule (fetch-obj (stored-word 3)))
    (setf dp-state (fetch-obj (stored-word 4)))
    (setf done-subgoals (fetch-obj (stored-word 5)))
    (setf pending-subgoals (fetch-obj (stored-word 6)))
    (setf current-subgoal (fetch-obj (stored-word 7)))
    (setf remaining-subgoals (fetch-obj (stored-word 8)))
    (setf status (fetch-obj (stored-word 9)))
    (setf subgoalnum (fetch-obj (stored-word 10)))
    (setf justification (fetch-obj (stored-word 11)))
    (setf current-input (fetch-obj (stored-word 12)))
    (setf parsed-input (fetch-obj (stored-word 13)))
    (setf printout (fetch-obj (stored-word 14)))
    (setf comment (fetch-obj (stored-word 15)))
    (setf strategy (fetch-obj (stored-word 16)))
    (setf context (fetch-obj (stored-word 17)))
    (setf parent-proofstate (fetch-obj (stored-word 18)))
    (setf proof-dependent-decls (fetch-obj (stored-word 19)))
    (setf dependent-decls (fetch-obj (stored-word 20)))
    (setf current-auto-rewrites (fetch-obj (stored-word 21)))
    (setf tcc-hash (fetch-obj (stored-word 22)))
    (setf subtype-hash (fetch-obj (stored-word 23)))
    (setf rewrite-hash (fetch-obj (stored-word 24)))
    (setf typepred-hash (fetch-obj (stored-word 25)))
    (setf current-xrule (fetch-obj (stored-word 26)))
    (setf in-justification (fetch-obj (stored-word 27)))
    (setf declaration (fetch-obj (stored-word 28)))))

(defmethod restore-object* ((obj top-proofstate))
  (let ((*restore-object-parent* obj))
    (with-slots (label current-goal current-rule dp-state done-subgoals
                       pending-subgoals current-subgoal
                       remaining-subgoals status subgoalnum
                       justification current-input parsed-input
                       printout comment strategy context
                       parent-proofstate proof-dependent-decls
                       dependent-decls current-auto-rewrites tcc-hash
                       subtype-hash rewrite-hash typepred-hash
                       current-xrule in-justification declaration)
      obj
      (when label
        (let ((*restore-object-parent-slot* 'label))
          (restore-object* label)))
      (when current-goal
        (let ((*restore-object-parent-slot* 'current-goal))
          (restore-object* current-goal)))
      (when current-rule
        (let ((*restore-object-parent-slot* 'current-rule))
          (restore-object* current-rule)))
      (when dp-state
        (let ((*restore-object-parent-slot* 'dp-state))
          (restore-object* dp-state)))
      (when done-subgoals
        (let ((*restore-object-parent-slot* 'done-subgoals))
          (restore-object* done-subgoals)))
      (when pending-subgoals
        (let ((*restore-object-parent-slot* 'pending-subgoals))
          (restore-object* pending-subgoals)))
      (when current-subgoal
        (let ((*restore-object-parent-slot* 'current-subgoal))
          (restore-object* current-subgoal)))
      (when remaining-subgoals
        (let ((*restore-object-parent-slot* 'remaining-subgoals))
          (restore-object* remaining-subgoals)))
      (when status
        (let ((*restore-object-parent-slot* 'status))
          (restore-object* status)))
      (when subgoalnum
        (let ((*restore-object-parent-slot* 'subgoalnum))
          (restore-object* subgoalnum)))
      (when justification
        (let ((*restore-object-parent-slot* 'justification))
          (restore-object* justification)))
      (when current-input
        (let ((*restore-object-parent-slot* 'current-input))
          (restore-object* current-input)))
      (when parsed-input
        (let ((*restore-object-parent-slot* 'parsed-input))
          (restore-object* parsed-input)))
      (when printout
        (let ((*restore-object-parent-slot* 'printout))
          (restore-object* printout)))
      (when comment
        (let ((*restore-object-parent-slot* 'comment))
          (restore-object* comment)))
      (when strategy
        (let ((*restore-object-parent-slot* 'strategy))
          (restore-object* strategy)))
      (when context
        (let ((*restore-object-parent-slot* 'context))
          (restore-object* context)))
      (when parent-proofstate
        (let ((*restore-object-parent-slot* 'parent-proofstate))
          (restore-object* parent-proofstate)))
      (when proof-dependent-decls
        (let ((*restore-object-parent-slot* 'proof-dependent-decls))
          (restore-object* proof-dependent-decls)))
      (when dependent-decls
        (let ((*restore-object-parent-slot* 'dependent-decls))
          (restore-object* dependent-decls)))
      (when current-auto-rewrites
        (let ((*restore-object-parent-slot* 'current-auto-rewrites))
          (restore-object* current-auto-rewrites)))
      (when tcc-hash
        (let ((*restore-object-parent-slot* 'tcc-hash))
          (restore-object* tcc-hash)))
      (when subtype-hash
        (let ((*restore-object-parent-slot* 'subtype-hash))
          (restore-object* subtype-hash)))
      (when rewrite-hash
        (let ((*restore-object-parent-slot* 'rewrite-hash))
          (restore-object* rewrite-hash)))
      (when typepred-hash
        (let ((*restore-object-parent-slot* 'typepred-hash))
          (restore-object* typepred-hash)))
      (when current-xrule
        (let ((*restore-object-parent-slot* 'current-xrule))
          (restore-object* current-xrule)))
      (when in-justification
        (let ((*restore-object-parent-slot* 'in-justification))
          (restore-object* in-justification)))
      (when declaration
        (let ((*restore-object-parent-slot* 'declaration))
          (restore-object* declaration)))
      obj)))

(defmethod copy ((obj tcc-proofstate) &rest initargs)
  (with-slots (label current-goal current-rule dp-state done-subgoals
                     pending-subgoals current-subgoal
                     remaining-subgoals status subgoalnum justification
                     current-input parsed-input printout comment
                     strategy context parent-proofstate
                     proof-dependent-decls dependent-decls
                     current-auto-rewrites tcc-hash subtype-hash
                     rewrite-hash typepred-hash current-xrule)
    obj
    (make-instance 'tcc-proofstate :label
                   (let* ((get1 (getf initargs 'label '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :label '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) label getfv))
                   :current-goal
                   (let* ((get1 (getf initargs 'current-goal '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :current-goal '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) current-goal getfv))
                   :current-rule
                   (let* ((get1 (getf initargs 'current-rule '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :current-rule '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) current-rule getfv))
                   :dp-state
                   (let* ((get1 (getf initargs 'dp-state '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :dp-state '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) dp-state getfv))
                   :done-subgoals
                   (let* ((get1
                           (getf initargs 'done-subgoals '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :done-subgoals '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) done-subgoals getfv))
                   :pending-subgoals
                   (let* ((get1
                           (getf initargs 'pending-subgoals '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf
                                initargs
                                :pending-subgoals
                                '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) pending-subgoals getfv))
                   :current-subgoal
                   (let* ((get1
                           (getf initargs 'current-subgoal '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf
                                initargs
                                :current-subgoal
                                '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) current-subgoal getfv))
                   :remaining-subgoals
                   (let* ((get1
                           (getf initargs 'remaining-subgoals
                                 '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf
                                initargs
                                :remaining-subgoals
                                '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) remaining-subgoals getfv))
                   :status
                   (let* ((get1 (getf initargs 'status '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :status '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) status getfv))
                   :subgoalnum
                   (let* ((get1 (getf initargs 'subgoalnum '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :subgoalnum '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) subgoalnum getfv))
                   :justification
                   (let* ((get1
                           (getf initargs 'justification '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :justification '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) justification getfv))
                   :current-input
                   (let* ((get1
                           (getf initargs 'current-input '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :current-input '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) current-input getfv))
                   :parsed-input
                   (let* ((get1 (getf initargs 'parsed-input '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :parsed-input '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) parsed-input getfv))
                   :printout
                   (let* ((get1 (getf initargs 'printout '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :printout '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) printout getfv))
                   :comment
                   (let* ((get1 (getf initargs 'comment '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :comment '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) comment getfv))
                   :strategy
                   (let* ((get1 (getf initargs 'strategy '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :strategy '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) strategy getfv))
                   :context
                   (let* ((get1 (getf initargs 'context '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :context '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) context getfv))
                   :parent-proofstate
                   (let* ((get1
                           (getf initargs 'parent-proofstate '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf
                                initargs
                                :parent-proofstate
                                '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) parent-proofstate getfv))
                   :proof-dependent-decls
                   (let* ((get1
                           (getf initargs 'proof-dependent-decls
                                 '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf
                                initargs
                                :proof-dependent-decls
                                '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf)
                         proof-dependent-decls
                       getfv))
                   :dependent-decls
                   (let* ((get1
                           (getf initargs 'dependent-decls '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf
                                initargs
                                :dependent-decls
                                '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) dependent-decls getfv))
                   :current-auto-rewrites
                   (let* ((get1
                           (getf initargs 'current-auto-rewrites
                                 '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf
                                initargs
                                :current-auto-rewrites
                                '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf)
                         current-auto-rewrites
                       getfv))
                   :tcc-hash
                   (let* ((get1 (getf initargs 'tcc-hash '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :tcc-hash '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) tcc-hash getfv))
                   :subtype-hash
                   (let* ((get1 (getf initargs 'subtype-hash '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :subtype-hash '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) subtype-hash getfv))
                   :rewrite-hash
                   (let* ((get1 (getf initargs 'rewrite-hash '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :rewrite-hash '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) rewrite-hash getfv))
                   :typepred-hash
                   (let* ((get1
                           (getf initargs 'typepred-hash '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :typepred-hash '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) typepred-hash getfv))
                   :current-xrule
                   (let* ((get1
                           (getf initargs 'current-xrule '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :current-xrule '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) current-xrule getfv)))))

(defmethod store-object* ((obj tcc-proofstate))
  (reserve-space 27
                 (with-slots (label current-goal current-rule dp-state
                                    done-subgoals pending-subgoals
                                    current-subgoal remaining-subgoals
                                    status subgoalnum justification
                                    current-input parsed-input printout
                                    comment strategy context
                                    parent-proofstate
                                    proof-dependent-decls
                                    dependent-decls
                                    current-auto-rewrites tcc-hash
                                    subtype-hash rewrite-hash
                                    typepred-hash current-xrule)
                   obj
                   (push-word (store-obj 'tcc-proofstate))
                   (push-word (store-obj label))
                   (push-word (store-obj current-goal))
                   (push-word (store-obj current-rule))
                   (push-word (store-obj dp-state))
                   (push-word (store-obj done-subgoals))
                   (push-word (store-obj pending-subgoals))
                   (push-word (store-obj current-subgoal))
                   (push-word (store-obj remaining-subgoals))
                   (push-word (store-obj status))
                   (push-word (store-obj subgoalnum))
                   (push-word (store-obj justification))
                   (push-word (store-obj current-input))
                   (push-word (store-obj parsed-input))
                   (push-word (store-obj printout))
                   (push-word (store-obj comment))
                   (push-word (store-obj strategy))
                   (push-word (store-obj context))
                   (push-word (store-obj parent-proofstate))
                   (push-word (store-obj proof-dependent-decls))
                   (push-word (store-obj dependent-decls))
                   (push-word (store-obj current-auto-rewrites))
                   (push-word (store-obj tcc-hash))
                   (push-word (store-obj subtype-hash))
                   (push-word (store-obj rewrite-hash))
                   (push-word (store-obj typepred-hash))
                   (push-word (store-obj current-xrule)))))

(defmethod update-fetched ((obj tcc-proofstate))
  (with-slots (label current-goal current-rule dp-state done-subgoals
                     pending-subgoals current-subgoal
                     remaining-subgoals status subgoalnum justification
                     current-input parsed-input printout comment
                     strategy context parent-proofstate
                     proof-dependent-decls dependent-decls
                     current-auto-rewrites tcc-hash subtype-hash
                     rewrite-hash typepred-hash current-xrule)
    obj
    (setf label (fetch-obj (stored-word 1)))
    (setf current-goal (fetch-obj (stored-word 2)))
    (setf current-rule (fetch-obj (stored-word 3)))
    (setf dp-state (fetch-obj (stored-word 4)))
    (setf done-subgoals (fetch-obj (stored-word 5)))
    (setf pending-subgoals (fetch-obj (stored-word 6)))
    (setf current-subgoal (fetch-obj (stored-word 7)))
    (setf remaining-subgoals (fetch-obj (stored-word 8)))
    (setf status (fetch-obj (stored-word 9)))
    (setf subgoalnum (fetch-obj (stored-word 10)))
    (setf justification (fetch-obj (stored-word 11)))
    (setf current-input (fetch-obj (stored-word 12)))
    (setf parsed-input (fetch-obj (stored-word 13)))
    (setf printout (fetch-obj (stored-word 14)))
    (setf comment (fetch-obj (stored-word 15)))
    (setf strategy (fetch-obj (stored-word 16)))
    (setf context (fetch-obj (stored-word 17)))
    (setf parent-proofstate (fetch-obj (stored-word 18)))
    (setf proof-dependent-decls (fetch-obj (stored-word 19)))
    (setf dependent-decls (fetch-obj (stored-word 20)))
    (setf current-auto-rewrites (fetch-obj (stored-word 21)))
    (setf tcc-hash (fetch-obj (stored-word 22)))
    (setf subtype-hash (fetch-obj (stored-word 23)))
    (setf rewrite-hash (fetch-obj (stored-word 24)))
    (setf typepred-hash (fetch-obj (stored-word 25)))
    (setf current-xrule (fetch-obj (stored-word 26)))))

(defmethod restore-object* ((obj tcc-proofstate))
  (let ((*restore-object-parent* obj))
    (with-slots (label current-goal current-rule dp-state done-subgoals
                       pending-subgoals current-subgoal
                       remaining-subgoals status subgoalnum
                       justification current-input parsed-input
                       printout comment strategy context
                       parent-proofstate proof-dependent-decls
                       dependent-decls current-auto-rewrites tcc-hash
                       subtype-hash rewrite-hash typepred-hash
                       current-xrule)
      obj
      (when label
        (let ((*restore-object-parent-slot* 'label))
          (restore-object* label)))
      (when current-goal
        (let ((*restore-object-parent-slot* 'current-goal))
          (restore-object* current-goal)))
      (when current-rule
        (let ((*restore-object-parent-slot* 'current-rule))
          (restore-object* current-rule)))
      (when dp-state
        (let ((*restore-object-parent-slot* 'dp-state))
          (restore-object* dp-state)))
      (when done-subgoals
        (let ((*restore-object-parent-slot* 'done-subgoals))
          (restore-object* done-subgoals)))
      (when pending-subgoals
        (let ((*restore-object-parent-slot* 'pending-subgoals))
          (restore-object* pending-subgoals)))
      (when current-subgoal
        (let ((*restore-object-parent-slot* 'current-subgoal))
          (restore-object* current-subgoal)))
      (when remaining-subgoals
        (let ((*restore-object-parent-slot* 'remaining-subgoals))
          (restore-object* remaining-subgoals)))
      (when status
        (let ((*restore-object-parent-slot* 'status))
          (restore-object* status)))
      (when subgoalnum
        (let ((*restore-object-parent-slot* 'subgoalnum))
          (restore-object* subgoalnum)))
      (when justification
        (let ((*restore-object-parent-slot* 'justification))
          (restore-object* justification)))
      (when current-input
        (let ((*restore-object-parent-slot* 'current-input))
          (restore-object* current-input)))
      (when parsed-input
        (let ((*restore-object-parent-slot* 'parsed-input))
          (restore-object* parsed-input)))
      (when printout
        (let ((*restore-object-parent-slot* 'printout))
          (restore-object* printout)))
      (when comment
        (let ((*restore-object-parent-slot* 'comment))
          (restore-object* comment)))
      (when strategy
        (let ((*restore-object-parent-slot* 'strategy))
          (restore-object* strategy)))
      (when context
        (let ((*restore-object-parent-slot* 'context))
          (restore-object* context)))
      (when parent-proofstate
        (let ((*restore-object-parent-slot* 'parent-proofstate))
          (restore-object* parent-proofstate)))
      (when proof-dependent-decls
        (let ((*restore-object-parent-slot* 'proof-dependent-decls))
          (restore-object* proof-dependent-decls)))
      (when dependent-decls
        (let ((*restore-object-parent-slot* 'dependent-decls))
          (restore-object* dependent-decls)))
      (when current-auto-rewrites
        (let ((*restore-object-parent-slot* 'current-auto-rewrites))
          (restore-object* current-auto-rewrites)))
      (when tcc-hash
        (let ((*restore-object-parent-slot* 'tcc-hash))
          (restore-object* tcc-hash)))
      (when subtype-hash
        (let ((*restore-object-parent-slot* 'subtype-hash))
          (restore-object* subtype-hash)))
      (when rewrite-hash
        (let ((*restore-object-parent-slot* 'rewrite-hash))
          (restore-object* rewrite-hash)))
      (when typepred-hash
        (let ((*restore-object-parent-slot* 'typepred-hash))
          (restore-object* typepred-hash)))
      (when current-xrule
        (let ((*restore-object-parent-slot* 'current-xrule))
          (restore-object* current-xrule)))
      obj)))

(defmethod copy ((obj apply-proofstate) &rest initargs)
  (with-slots (label current-goal current-rule dp-state done-subgoals
                     pending-subgoals current-subgoal
                     remaining-subgoals status subgoalnum justification
                     current-input parsed-input printout comment
                     strategy context parent-proofstate
                     proof-dependent-decls dependent-decls
                     current-auto-rewrites tcc-hash subtype-hash
                     rewrite-hash typepred-hash current-xrule
                     apply-parent-proofstate)
    obj
    (make-instance 'apply-proofstate :label
                   (let* ((get1 (getf initargs 'label '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :label '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) label getfv))
                   :current-goal
                   (let* ((get1 (getf initargs 'current-goal '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :current-goal '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) current-goal getfv))
                   :current-rule
                   (let* ((get1 (getf initargs 'current-rule '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :current-rule '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) current-rule getfv))
                   :dp-state
                   (let* ((get1 (getf initargs 'dp-state '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :dp-state '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) dp-state getfv))
                   :done-subgoals
                   (let* ((get1
                           (getf initargs 'done-subgoals '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :done-subgoals '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) done-subgoals getfv))
                   :pending-subgoals
                   (let* ((get1
                           (getf initargs 'pending-subgoals '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf
                                initargs
                                :pending-subgoals
                                '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) pending-subgoals getfv))
                   :current-subgoal
                   (let* ((get1
                           (getf initargs 'current-subgoal '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf
                                initargs
                                :current-subgoal
                                '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) current-subgoal getfv))
                   :remaining-subgoals
                   (let* ((get1
                           (getf initargs 'remaining-subgoals
                                 '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf
                                initargs
                                :remaining-subgoals
                                '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) remaining-subgoals getfv))
                   :status
                   (let* ((get1 (getf initargs 'status '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :status '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) status getfv))
                   :subgoalnum
                   (let* ((get1 (getf initargs 'subgoalnum '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :subgoalnum '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) subgoalnum getfv))
                   :justification
                   (let* ((get1
                           (getf initargs 'justification '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :justification '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) justification getfv))
                   :current-input
                   (let* ((get1
                           (getf initargs 'current-input '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :current-input '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) current-input getfv))
                   :parsed-input
                   (let* ((get1 (getf initargs 'parsed-input '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :parsed-input '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) parsed-input getfv))
                   :printout
                   (let* ((get1 (getf initargs 'printout '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :printout '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) printout getfv))
                   :comment
                   (let* ((get1 (getf initargs 'comment '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :comment '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) comment getfv))
                   :strategy
                   (let* ((get1 (getf initargs 'strategy '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :strategy '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) strategy getfv))
                   :context
                   (let* ((get1 (getf initargs 'context '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :context '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) context getfv))
                   :parent-proofstate
                   (let* ((get1
                           (getf initargs 'parent-proofstate '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf
                                initargs
                                :parent-proofstate
                                '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) parent-proofstate getfv))
                   :proof-dependent-decls
                   (let* ((get1
                           (getf initargs 'proof-dependent-decls
                                 '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf
                                initargs
                                :proof-dependent-decls
                                '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf)
                         proof-dependent-decls
                       getfv))
                   :dependent-decls
                   (let* ((get1
                           (getf initargs 'dependent-decls '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf
                                initargs
                                :dependent-decls
                                '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) dependent-decls getfv))
                   :current-auto-rewrites
                   (let* ((get1
                           (getf initargs 'current-auto-rewrites
                                 '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf
                                initargs
                                :current-auto-rewrites
                                '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf)
                         current-auto-rewrites
                       getfv))
                   :tcc-hash
                   (let* ((get1 (getf initargs 'tcc-hash '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :tcc-hash '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) tcc-hash getfv))
                   :subtype-hash
                   (let* ((get1 (getf initargs 'subtype-hash '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :subtype-hash '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) subtype-hash getfv))
                   :rewrite-hash
                   (let* ((get1 (getf initargs 'rewrite-hash '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :rewrite-hash '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) rewrite-hash getfv))
                   :typepred-hash
                   (let* ((get1
                           (getf initargs 'typepred-hash '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :typepred-hash '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) typepred-hash getfv))
                   :current-xrule
                   (let* ((get1
                           (getf initargs 'current-xrule '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :current-xrule '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) current-xrule getfv))
                   :apply-parent-proofstate
                   (let* ((get1
                           (getf initargs 'apply-parent-proofstate
                                 '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf
                                initargs
                                :apply-parent-proofstate
                                '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf)
                         apply-parent-proofstate
                       getfv)))))

(defmethod store-object* ((obj apply-proofstate))
  (reserve-space 28
                 (with-slots (label current-goal current-rule dp-state
                                    done-subgoals pending-subgoals
                                    current-subgoal remaining-subgoals
                                    status subgoalnum justification
                                    current-input parsed-input printout
                                    comment strategy context
                                    parent-proofstate
                                    proof-dependent-decls
                                    dependent-decls
                                    current-auto-rewrites tcc-hash
                                    subtype-hash rewrite-hash
                                    typepred-hash current-xrule
                                    apply-parent-proofstate)
                   obj
                   (push-word (store-obj 'apply-proofstate))
                   (push-word (store-obj label))
                   (push-word (store-obj current-goal))
                   (push-word (store-obj current-rule))
                   (push-word (store-obj dp-state))
                   (push-word (store-obj done-subgoals))
                   (push-word (store-obj pending-subgoals))
                   (push-word (store-obj current-subgoal))
                   (push-word (store-obj remaining-subgoals))
                   (push-word (store-obj status))
                   (push-word (store-obj subgoalnum))
                   (push-word (store-obj justification))
                   (push-word (store-obj current-input))
                   (push-word (store-obj parsed-input))
                   (push-word (store-obj printout))
                   (push-word (store-obj comment))
                   (push-word (store-obj strategy))
                   (push-word (store-obj context))
                   (push-word (store-obj parent-proofstate))
                   (push-word (store-obj proof-dependent-decls))
                   (push-word (store-obj dependent-decls))
                   (push-word (store-obj current-auto-rewrites))
                   (push-word (store-obj tcc-hash))
                   (push-word (store-obj subtype-hash))
                   (push-word (store-obj rewrite-hash))
                   (push-word (store-obj typepred-hash))
                   (push-word (store-obj current-xrule))
                   (push-word (store-obj apply-parent-proofstate)))))

(defmethod update-fetched ((obj apply-proofstate))
  (with-slots (label current-goal current-rule dp-state done-subgoals
                     pending-subgoals current-subgoal
                     remaining-subgoals status subgoalnum justification
                     current-input parsed-input printout comment
                     strategy context parent-proofstate
                     proof-dependent-decls dependent-decls
                     current-auto-rewrites tcc-hash subtype-hash
                     rewrite-hash typepred-hash current-xrule
                     apply-parent-proofstate)
    obj
    (setf label (fetch-obj (stored-word 1)))
    (setf current-goal (fetch-obj (stored-word 2)))
    (setf current-rule (fetch-obj (stored-word 3)))
    (setf dp-state (fetch-obj (stored-word 4)))
    (setf done-subgoals (fetch-obj (stored-word 5)))
    (setf pending-subgoals (fetch-obj (stored-word 6)))
    (setf current-subgoal (fetch-obj (stored-word 7)))
    (setf remaining-subgoals (fetch-obj (stored-word 8)))
    (setf status (fetch-obj (stored-word 9)))
    (setf subgoalnum (fetch-obj (stored-word 10)))
    (setf justification (fetch-obj (stored-word 11)))
    (setf current-input (fetch-obj (stored-word 12)))
    (setf parsed-input (fetch-obj (stored-word 13)))
    (setf printout (fetch-obj (stored-word 14)))
    (setf comment (fetch-obj (stored-word 15)))
    (setf strategy (fetch-obj (stored-word 16)))
    (setf context (fetch-obj (stored-word 17)))
    (setf parent-proofstate (fetch-obj (stored-word 18)))
    (setf proof-dependent-decls (fetch-obj (stored-word 19)))
    (setf dependent-decls (fetch-obj (stored-word 20)))
    (setf current-auto-rewrites (fetch-obj (stored-word 21)))
    (setf tcc-hash (fetch-obj (stored-word 22)))
    (setf subtype-hash (fetch-obj (stored-word 23)))
    (setf rewrite-hash (fetch-obj (stored-word 24)))
    (setf typepred-hash (fetch-obj (stored-word 25)))
    (setf current-xrule (fetch-obj (stored-word 26)))
    (setf apply-parent-proofstate (fetch-obj (stored-word 27)))))

(defmethod restore-object* ((obj apply-proofstate))
  (let ((*restore-object-parent* obj))
    (with-slots (label current-goal current-rule dp-state done-subgoals
                       pending-subgoals current-subgoal
                       remaining-subgoals status subgoalnum
                       justification current-input parsed-input
                       printout comment strategy context
                       parent-proofstate proof-dependent-decls
                       dependent-decls current-auto-rewrites tcc-hash
                       subtype-hash rewrite-hash typepred-hash
                       current-xrule apply-parent-proofstate)
      obj
      (when label
        (let ((*restore-object-parent-slot* 'label))
          (restore-object* label)))
      (when current-goal
        (let ((*restore-object-parent-slot* 'current-goal))
          (restore-object* current-goal)))
      (when current-rule
        (let ((*restore-object-parent-slot* 'current-rule))
          (restore-object* current-rule)))
      (when dp-state
        (let ((*restore-object-parent-slot* 'dp-state))
          (restore-object* dp-state)))
      (when done-subgoals
        (let ((*restore-object-parent-slot* 'done-subgoals))
          (restore-object* done-subgoals)))
      (when pending-subgoals
        (let ((*restore-object-parent-slot* 'pending-subgoals))
          (restore-object* pending-subgoals)))
      (when current-subgoal
        (let ((*restore-object-parent-slot* 'current-subgoal))
          (restore-object* current-subgoal)))
      (when remaining-subgoals
        (let ((*restore-object-parent-slot* 'remaining-subgoals))
          (restore-object* remaining-subgoals)))
      (when status
        (let ((*restore-object-parent-slot* 'status))
          (restore-object* status)))
      (when subgoalnum
        (let ((*restore-object-parent-slot* 'subgoalnum))
          (restore-object* subgoalnum)))
      (when justification
        (let ((*restore-object-parent-slot* 'justification))
          (restore-object* justification)))
      (when current-input
        (let ((*restore-object-parent-slot* 'current-input))
          (restore-object* current-input)))
      (when parsed-input
        (let ((*restore-object-parent-slot* 'parsed-input))
          (restore-object* parsed-input)))
      (when printout
        (let ((*restore-object-parent-slot* 'printout))
          (restore-object* printout)))
      (when comment
        (let ((*restore-object-parent-slot* 'comment))
          (restore-object* comment)))
      (when strategy
        (let ((*restore-object-parent-slot* 'strategy))
          (restore-object* strategy)))
      (when context
        (let ((*restore-object-parent-slot* 'context))
          (restore-object* context)))
      (when parent-proofstate
        (let ((*restore-object-parent-slot* 'parent-proofstate))
          (restore-object* parent-proofstate)))
      (when proof-dependent-decls
        (let ((*restore-object-parent-slot* 'proof-dependent-decls))
          (restore-object* proof-dependent-decls)))
      (when dependent-decls
        (let ((*restore-object-parent-slot* 'dependent-decls))
          (restore-object* dependent-decls)))
      (when current-auto-rewrites
        (let ((*restore-object-parent-slot* 'current-auto-rewrites))
          (restore-object* current-auto-rewrites)))
      (when tcc-hash
        (let ((*restore-object-parent-slot* 'tcc-hash))
          (restore-object* tcc-hash)))
      (when subtype-hash
        (let ((*restore-object-parent-slot* 'subtype-hash))
          (restore-object* subtype-hash)))
      (when rewrite-hash
        (let ((*restore-object-parent-slot* 'rewrite-hash))
          (restore-object* rewrite-hash)))
      (when typepred-hash
        (let ((*restore-object-parent-slot* 'typepred-hash))
          (restore-object* typepred-hash)))
      (when current-xrule
        (let ((*restore-object-parent-slot* 'current-xrule))
          (restore-object* current-xrule)))
      (when apply-parent-proofstate
        (let ((*restore-object-parent-slot* 'apply-parent-proofstate))
          (restore-object* apply-parent-proofstate)))
      obj)))

(defmethod copy ((obj proofstate) &rest initargs)
  (with-slots (label current-goal current-rule dp-state done-subgoals
                     pending-subgoals current-subgoal
                     remaining-subgoals status subgoalnum justification
                     current-input parsed-input printout comment
                     strategy context parent-proofstate
                     proof-dependent-decls dependent-decls
                     current-auto-rewrites tcc-hash subtype-hash
                     rewrite-hash typepred-hash current-xrule)
    obj
    (make-instance 'proofstate :label
                   (let* ((get1 (getf initargs 'label '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :label '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) label getfv))
                   :current-goal
                   (let* ((get1 (getf initargs 'current-goal '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :current-goal '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) current-goal getfv))
                   :current-rule
                   (let* ((get1 (getf initargs 'current-rule '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :current-rule '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) current-rule getfv))
                   :dp-state
                   (let* ((get1 (getf initargs 'dp-state '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :dp-state '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) dp-state getfv))
                   :done-subgoals
                   (let* ((get1
                           (getf initargs 'done-subgoals '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :done-subgoals '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) done-subgoals getfv))
                   :pending-subgoals
                   (let* ((get1
                           (getf initargs 'pending-subgoals '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf
                                initargs
                                :pending-subgoals
                                '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) pending-subgoals getfv))
                   :current-subgoal
                   (let* ((get1
                           (getf initargs 'current-subgoal '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf
                                initargs
                                :current-subgoal
                                '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) current-subgoal getfv))
                   :remaining-subgoals
                   (let* ((get1
                           (getf initargs 'remaining-subgoals
                                 '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf
                                initargs
                                :remaining-subgoals
                                '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) remaining-subgoals getfv))
                   :status
                   (let* ((get1 (getf initargs 'status '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :status '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) status getfv))
                   :subgoalnum
                   (let* ((get1 (getf initargs 'subgoalnum '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :subgoalnum '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) subgoalnum getfv))
                   :justification
                   (let* ((get1
                           (getf initargs 'justification '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :justification '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) justification getfv))
                   :current-input
                   (let* ((get1
                           (getf initargs 'current-input '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :current-input '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) current-input getfv))
                   :parsed-input
                   (let* ((get1 (getf initargs 'parsed-input '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :parsed-input '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) parsed-input getfv))
                   :printout
                   (let* ((get1 (getf initargs 'printout '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :printout '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) printout getfv))
                   :comment
                   (let* ((get1 (getf initargs 'comment '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :comment '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) comment getfv))
                   :strategy
                   (let* ((get1 (getf initargs 'strategy '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :strategy '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) strategy getfv))
                   :context
                   (let* ((get1 (getf initargs 'context '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :context '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) context getfv))
                   :parent-proofstate
                   (let* ((get1
                           (getf initargs 'parent-proofstate '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf
                                initargs
                                :parent-proofstate
                                '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) parent-proofstate getfv))
                   :proof-dependent-decls
                   (let* ((get1
                           (getf initargs 'proof-dependent-decls
                                 '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf
                                initargs
                                :proof-dependent-decls
                                '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf)
                         proof-dependent-decls
                       getfv))
                   :dependent-decls
                   (let* ((get1
                           (getf initargs 'dependent-decls '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf
                                initargs
                                :dependent-decls
                                '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) dependent-decls getfv))
                   :current-auto-rewrites
                   (let* ((get1
                           (getf initargs 'current-auto-rewrites
                                 '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf
                                initargs
                                :current-auto-rewrites
                                '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf)
                         current-auto-rewrites
                       getfv))
                   :tcc-hash
                   (let* ((get1 (getf initargs 'tcc-hash '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :tcc-hash '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) tcc-hash getfv))
                   :subtype-hash
                   (let* ((get1 (getf initargs 'subtype-hash '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :subtype-hash '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) subtype-hash getfv))
                   :rewrite-hash
                   (let* ((get1 (getf initargs 'rewrite-hash '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :rewrite-hash '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) rewrite-hash getfv))
                   :typepred-hash
                   (let* ((get1
                           (getf initargs 'typepred-hash '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :typepred-hash '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) typepred-hash getfv))
                   :current-xrule
                   (let* ((get1
                           (getf initargs 'current-xrule '%nogetf))
                          (getfv
                           (if (eq get1 '%nogetf)
                               (getf initargs :current-xrule '%nogetf)
                             get1)))
                     (if (eq getfv '%nogetf) current-xrule getfv)))))

(defmethod store-object* ((obj proofstate))
  (reserve-space 27
                 (with-slots (label current-goal current-rule dp-state
                                    done-subgoals pending-subgoals
                                    current-subgoal remaining-subgoals
                                    status subgoalnum justification
                                    current-input parsed-input printout
                                    comment strategy context
                                    parent-proofstate
                                    proof-dependent-decls
                                    dependent-decls
                                    current-auto-rewrites tcc-hash
                                    subtype-hash rewrite-hash
                                    typepred-hash current-xrule)
                   obj
                   (push-word (store-obj 'proofstate))
                   (push-word (store-obj label))
                   (push-word (store-obj current-goal))
                   (push-word (store-obj current-rule))
                   (push-word (store-obj dp-state))
                   (push-word (store-obj done-subgoals))
                   (push-word (store-obj pending-subgoals))
                   (push-word (store-obj current-subgoal))
                   (push-word (store-obj remaining-subgoals))
                   (push-word (store-obj status))
                   (push-word (store-obj subgoalnum))
                   (push-word (store-obj justification))
                   (push-word (store-obj current-input))
                   (push-word (store-obj parsed-input))
                   (push-word (store-obj printout))
                   (push-word (store-obj comment))
                   (push-word (store-obj strategy))
                   (push-word (store-obj context))
                   (push-word (store-obj parent-proofstate))
                   (push-word (store-obj proof-dependent-decls))
                   (push-word (store-obj dependent-decls))
                   (push-word (store-obj current-auto-rewrites))
                   (push-word (store-obj tcc-hash))
                   (push-word (store-obj subtype-hash))
                   (push-word (store-obj rewrite-hash))
                   (push-word (store-obj typepred-hash))
                   (push-word (store-obj current-xrule)))))

(defmethod update-fetched ((obj proofstate))
  (with-slots (label current-goal current-rule dp-state done-subgoals
                     pending-subgoals current-subgoal
                     remaining-subgoals status subgoalnum justification
                     current-input parsed-input printout comment
                     strategy context parent-proofstate
                     proof-dependent-decls dependent-decls
                     current-auto-rewrites tcc-hash subtype-hash
                     rewrite-hash typepred-hash current-xrule)
    obj
    (setf label (fetch-obj (stored-word 1)))
    (setf current-goal (fetch-obj (stored-word 2)))
    (setf current-rule (fetch-obj (stored-word 3)))
    (setf dp-state (fetch-obj (stored-word 4)))
    (setf done-subgoals (fetch-obj (stored-word 5)))
    (setf pending-subgoals (fetch-obj (stored-word 6)))
    (setf current-subgoal (fetch-obj (stored-word 7)))
    (setf remaining-subgoals (fetch-obj (stored-word 8)))
    (setf status (fetch-obj (stored-word 9)))
    (setf subgoalnum (fetch-obj (stored-word 10)))
    (setf justification (fetch-obj (stored-word 11)))
    (setf current-input (fetch-obj (stored-word 12)))
    (setf parsed-input (fetch-obj (stored-word 13)))
    (setf printout (fetch-obj (stored-word 14)))
    (setf comment (fetch-obj (stored-word 15)))
    (setf strategy (fetch-obj (stored-word 16)))
    (setf context (fetch-obj (stored-word 17)))
    (setf parent-proofstate (fetch-obj (stored-word 18)))
    (setf proof-dependent-decls (fetch-obj (stored-word 19)))
    (setf dependent-decls (fetch-obj (stored-word 20)))
    (setf current-auto-rewrites (fetch-obj (stored-word 21)))
    (setf tcc-hash (fetch-obj (stored-word 22)))
    (setf subtype-hash (fetch-obj (stored-word 23)))
    (setf rewrite-hash (fetch-obj (stored-word 24)))
    (setf typepred-hash (fetch-obj (stored-word 25)))
    (setf current-xrule (fetch-obj (stored-word 26)))))

(defmethod restore-object* ((obj proofstate))
  (let ((*restore-object-parent* obj))
    (with-slots (label current-goal current-rule dp-state done-subgoals
                       pending-subgoals current-subgoal
                       remaining-subgoals status subgoalnum
                       justification current-input parsed-input
                       printout comment strategy context
                       parent-proofstate proof-dependent-decls
                       dependent-decls current-auto-rewrites tcc-hash
                       subtype-hash rewrite-hash typepred-hash
                       current-xrule)
      obj
      (when label
        (let ((*restore-object-parent-slot* 'label))
          (restore-object* label)))
      (when current-goal
        (let ((*restore-object-parent-slot* 'current-goal))
          (restore-object* current-goal)))
      (when current-rule
        (let ((*restore-object-parent-slot* 'current-rule))
          (restore-object* current-rule)))
      (when dp-state
        (let ((*restore-object-parent-slot* 'dp-state))
          (restore-object* dp-state)))
      (when done-subgoals
        (let ((*restore-object-parent-slot* 'done-subgoals))
          (restore-object* done-subgoals)))
      (when pending-subgoals
        (let ((*restore-object-parent-slot* 'pending-subgoals))
          (restore-object* pending-subgoals)))
      (when current-subgoal
        (let ((*restore-object-parent-slot* 'current-subgoal))
          (restore-object* current-subgoal)))
      (when remaining-subgoals
        (let ((*restore-object-parent-slot* 'remaining-subgoals))
          (restore-object* remaining-subgoals)))
      (when status
        (let ((*restore-object-parent-slot* 'status))
          (restore-object* status)))
      (when subgoalnum
        (let ((*restore-object-parent-slot* 'subgoalnum))
          (restore-object* subgoalnum)))
      (when justification
        (let ((*restore-object-parent-slot* 'justification))
          (restore-object* justification)))
      (when current-input
        (let ((*restore-object-parent-slot* 'current-input))
          (restore-object* current-input)))
      (when parsed-input
        (let ((*restore-object-parent-slot* 'parsed-input))
          (restore-object* parsed-input)))
      (when printout
        (let ((*restore-object-parent-slot* 'printout))
          (restore-object* printout)))
      (when comment
        (let ((*restore-object-parent-slot* 'comment))
          (restore-object* comment)))
      (when strategy
        (let ((*restore-object-parent-slot* 'strategy))
          (restore-object* strategy)))
      (when context
        (let ((*restore-object-parent-slot* 'context))
          (restore-object* context)))
      (when parent-proofstate
        (let ((*restore-object-parent-slot* 'parent-proofstate))
          (restore-object* parent-proofstate)))
      (when proof-dependent-decls
        (let ((*restore-object-parent-slot* 'proof-dependent-decls))
          (restore-object* proof-dependent-decls)))
      (when dependent-decls
        (let ((*restore-object-parent-slot* 'dependent-decls))
          (restore-object* dependent-decls)))
      (when current-auto-rewrites
        (let ((*restore-object-parent-slot* 'current-auto-rewrites))
          (restore-object* current-auto-rewrites)))
      (when tcc-hash
        (let ((*restore-object-parent-slot* 'tcc-hash))
          (restore-object* tcc-hash)))
      (when subtype-hash
        (let ((*restore-object-parent-slot* 'subtype-hash))
          (restore-object* subtype-hash)))
      (when rewrite-hash
        (let ((*restore-object-parent-slot* 'rewrite-hash))
          (restore-object* rewrite-hash)))
      (when typepred-hash
        (let ((*restore-object-parent-slot* 'typepred-hash))
          (restore-object* typepred-hash)))
      (when current-xrule
        (let ((*restore-object-parent-slot* 'current-xrule))
          (restore-object* current-xrule)))
      obj)))