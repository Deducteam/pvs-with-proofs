(defclass trace () ())
(defclass not-implemented-trace (trace)
  ((name :initarg :name :accessor name)))
(defclass empty-trace(trace)
  ((name :initarg :name :accessor name)))

;; BUILD TRACES

(defun make-trace (sym &optional params premises)
  (cond ((eq sym 'proof-hole)
	 (assert (null params))
	 (assert (null premises))
	 (make-trace 'hole-rule)
	 )
	((eq sym 'not-implemented)
	 (assert (null premises))
	 (make-instance 'not-implemented-trace
			:name params))
	((eq sym 'empty)
	 (assert (null premises))
	 (make-instance 'empty-trace
			:name params))
	((eq sym 'deep-inference-rule)
	 (assert (trace-list? premises))
	 (assert (eq (list-length premises) 3))
	 (assert (eq (list-length params) 3))
	 (let ((ctx (car params))
	       (newexpr (cadr params))
	       (oldexpr (caddr params))
	       (main-premise (car premises))
	       (old-from-new (cadr premises))
	       (new-from-old (caddr premises)))
	   (make-trace
	    'leibniz-rule
	    (list ctx newexpr oldexpr)
	    (list main-premise
		  (make-trace
		   'extprop-rule;; newexpr = oldexpr
		   (list newexpr oldexpr)
		   (list ;;  newexpr iff oldexpr
		    (make-trace
		     'iff-rule
		     (list newexpr oldexpr)
		     (list (make-trace ;;  newexpr => oldexpr
			    'implication-rule
			    (list newexpr oldexpr)
			    (list old-from-new))
			   (make-trace ;;  oldexpr => newexpr
			    'implication-rule
			    (list oldexpr newexpr)
			    (list new-from-old))))))))))
	((eq sym 'deep-inference2-rule);; old-from-new and new-from-old have exactly one hole each
	 (assert (trace-list? premises))
	 (assert (eq (list-length premises) 3))
	 (assert (eq (list-length params) 3))
	 (let ((ctx (car params))
	       (newexpr (cadr params))
	       (oldexpr (caddr params))
	       (main-premise (car premises))
	       (old-from-new (cadr premises))
	       (new-from-old (caddr premises)))
	   (make-trace
	    'leibniz-rule
	    (list ctx newexpr oldexpr)
	    (list main-premise
		  (make-trace
		   'extprop-rule;; newexpr = oldexpr
		   (list newexpr oldexpr)
		   (list ;;  newexpr iff oldexpr
		    (make-trace
		     'iff-rule
		     (list newexpr oldexpr)
		     (list (make-trace ;;  newexpr => oldexpr
			    'implication-rule
			    (list newexpr oldexpr)
			    (list (apply-trace
				   old-from-new
				   (list (make-trace 'axiom-rule (list newexpr))))))
			   (make-trace ;;  oldexpr => newexpr
			    'implication-rule
			    (list oldexpr newexpr)
			    (list (apply-trace
				   new-from-old
				   (list (make-trace 'axiom-rule (list oldexpr))))))))))))))
	((eq sym 'deep-trusted-rule) ;; handle not-implemented-ctx
	 (assert (trace-list? premises))
	 (assert (and (equal (list-length premises) 1)
		      (equal (list-length params) 4)))
	 (cond
	  ((not-implemented-ctx? (car params))
	   (make-trace 'not-implemented-rule
		       (list (name (car params)))
		       premises))
	  (t
	   (assert (expr-ctx? (car params)))
	   (cond
	    ((some #'empty-trace? premises) (assert (and 'deep-trusted nil)))
	    ((some #'not-implemented-trace? premises)
	     (find-if #'not-implemented-trace? premises))
	    (t
	     (assert-debug (proof-list? premises)
			   "make-trace"
			   (list (cons "sym" sym)
				 (cons "params" params)
				 (cons "premises" premises)))
	     ;; (if (compute-form-eq (caddr params) (cadddr params))
	     ;; 	 (car premises)
	     (make-trace 'trusted-rule
			 (list (cadr params)
			       (list (list
				      (compute-instantiate (expr (car params))
							   (list (cons (car (binds (car params)))
								       (caddr params))))))
			       (list (compute-instantiate (expr (car params))
							  (list (cons (car (binds (car params)))
								      (cadddr params))))))
			 premises)
	     ;;)
	     )))))
	((eq sym 'deep-decision-procedure)
	 ;; (when (dpinfo-context *dp-state*)
	 ;;   (show *dp-state*)
	 ;;   (assert nil))
	 (assert (trace-list? premises))
	 (assert (eq (list-length premises) 1))
	 (assert (eq (list-length params) 3))
	 (let ((ctx (car params))
	       (newexpr (cadr params))
	       (oldexpr (caddr params))
	       (main-premise (car premises)))
	   (make-trace
	    'leibniz-rule
	    (list ctx newexpr oldexpr)
	    (list
	     main-premise
	     (make-trace
	      'trusted-rule
	      (list 'decision-procedure
		    nil
		    (if (expr-ctx? ctx)
			(mapcar #'formula
				(s-forms
				 (cadr (compute-hole-sequents
					(make-trace
					 'leibniz-rule
					 (list ctx newexpr oldexpr)
					 (list (make-trace 'proof-hole)
					       (make-trace 'proof-hole)))
					(compute-sequent
					 (list (compute-s-form
						(compute-instantiate
						 (expr ctx)
						 (list (cons (car (binds ctx))
							     oldexpr))))
					       ;; (mapcar #'compute-s-form
					       ;; 	       (dpinfo-context *dp-state*))
					       )
					 nil)))))
		      (list (compute-equation newexpr oldexpr)))))))))
	((or (eq sym 'leibniz-rule)
	     (eq sym 'rewrite-rule)
	     (eq sym 'rewrite-rule2)) ;; handle not-implemented-ctx
	 (assert (trace-list? premises))
	 (assert (or (eq sym 'rewrite-rule2) (proof-coherent-nb-premises sym (length premises))))
	 (cond
	  ((not-implemented-ctx? (car params))
	   (make-trace 'not-implemented-rule
		       (list (name (car params)))
		       premises))
	  (t
	   (assert (or (eq sym 'rewrite-rule2) (and (expr-ctx? (car params))
			(equal (list-length params) 3))))
	   (cond
	    ((some #'empty-trace? premises) (assert (and 'leibnizrewrite nil)))
	    ((some #'not-implemented-trace? premises)
	     (find-if #'not-implemented-trace? premises))
	    (t
	     (assert-debug (proof-list? premises)
			   "make-trace"
			   (list (cons "sym" sym)
				 (cons "params" params)
				 (cons "premises" premises)))
	     (if (eq sym 'leibniz-rule)
		 ;; (make-proof sym (cons (car params) (cdr params))
		 ;; 	     premises)
		   (make-proof 'leibniz-rule
			       (list (make-ctx 'expr-hole *boolean*)
				     (compute-instantiate (expr (car params))
							  (list (cons (car (binds (car params)))
								      (cadr params))))
				     (compute-instantiate (expr (car params))
							  (list (cons (car (binds (car params)))
								      (caddr params)))))
			       (list (car premises)
				     (apply-trace
				      (instantiate-vars-proof
				       (car (proofs (car params)))
				       (list (cons (car (car (subbinds (car params))))
						   (cadr params))
					     (cons (cdr (car (subbinds (car params))))
						   (caddr params))))
				      (list (cadr premises)))))
	       (if (eq sym 'rewrite-rule)
		   ;; (progn
		     ;; (assert (and 'check-normal1 (tc-eq (compute-normalize (cadr params))
		     ;; 				       (compute-normalize (caddr params)))))
		   ;; (car premises)
		 (make-proof sym (cons (compute-lambda (binds (car params)) (expr (car params)))
		 			 (cdr params))
		 	       premises)
        		 ;;)
		 (if (cadddr params)
		     ;; (progn
		     ;; (assert (and 'check-normal2 (tc-eq (compute-normalize (cadr params))
		     ;; 				       (compute-normalize (caddr params)))))
		     ;; (car premises)
		               (make-proof 'rewrite-rule
			       	 (list (compute-lambda (binds (car params)) (expr (car params)))
			       	       (cadr params) (caddr params))
			       premises)
		     ;;)
		   (make-trace 'trusted-rule
			       (list 'recursive-rewrite
				     (list (list (compute-instantiate
						  (expr (car params))
						  (list (cons (car (binds (car params)))
							      (cadr params))))))
				     (list (compute-instantiate
					    (expr (car params))
					    (list (cons (car (binds (car params)))
							(caddr params))))))
			       premises))))
	     )))))
	((eq sym 'trans-rule) ;; simplify when a premise is refl
	 (assert (trace-list? premises))
	 (assert (proof-coherent-nb-premises sym (length premises)))
	 (cond
	  ((some #'empty-trace? premises)
	   (assert (and 'transruleempty nil)))
	  ((some #'not-implemented-trace? premises)
	   (find-if #'not-implemented-trace? premises))
	  (t
	   (assert-debug (proof-list? premises)
			 "make-trace"
			 (list (cons "sym" sym)
			       (cons "params" params)
			       (cons "premises" premises)))
	   (cond ((compute-form-eq (car params) (cadr params))
		  (cadr premises))
		 ((compute-form-eq (cadr params) (caddr params))
		  (car premises))
		 (t
		  (make-proof sym params premises)))
	   )))
	((eq sym 'congruence-rule) ;; handle not-implemented-ctx
	 (assert (trace-list? premises))
	 (assert (proof-coherent-nb-premises sym (length premises)))
	 (assert (= (list-length params) 3))
	 (cond
	  ((not-implemented-ctx? (car params))
	   (make-trace 'not-implemented-rule
		       (list (name (car params)))
		       premises))
	  (t
	   (cond
	    ((some #'empty-trace? premises)
	     (assert (and 'congruencerule nil)))
	    ((some #'not-implemented-trace? premises)
	     (find-if #'not-implemented-trace? premises))
	    (t
	     (assert-debug (proof-list? premises)
			   "make-trace"
			   (list (cons "sym" sym)
				 (cons "params" params)
				 (cons "premises" premises)))
	     (make-proof sym (cons (expr (car params))
				   (cons (car (binds (car params)))
					 (cdr params)))
			 premises)
	     )))))
	((eq sym 'trans-rule) ;; simplify when a premise is refl
	 (assert (trace-list? premises))
	 (assert (proof-coherent-nb-premises sym (length premises)))
	 (cond
	  ((some #'empty-trace? premises)
	   (assert (and 'transruleempty nil)))
	  ((some #'not-implemented-trace? premises)
	   (find-if #'not-implemented-trace? premises))
	  (t
	   (assert-debug (proof-list? premises)
			 "make-trace"
			 (list (cons "sym" sym)
			       (cons "params" params)
			       (cons "premises" premises)))
	   (cond ((compute-form-eq (car params) (cadr params))
		  (cadr premises))
		 ((compute-form-eq (cadr params) (caddr params))
		  (car premises))
		 (t
		  (make-proof sym params premises)))
	   )))
	((and (eq sym 'trusted-rule)
	      (equal (list-length (cadr params)) 1)
	      (compute-forms-eq (car (cadr params)) (caddr params)))
	 (assert (equal (list-length premises) 1))
	 (car premises))
	((eq sym 'typepred-rule)
	 (assert (equal (list-length premises) 1))
	 (cond ((null (car params))
		(car premises))
	       (t
		(make-trace 'trusted-rule
			    (list 'typepred-proofrule
				  (list (car params))
				  nil)
			    premises))))
	(t
	 (assert (trace-list? premises))
	 (unless (proof-coherent-params sym params)
	   (show sym)
	   (show (car params))
	   (show (cdr params))
	   (assert (and 'coherence-problem nil)))
	 (assert (proof-coherent-nb-premises sym (length premises)))
	 (cond
	  ((some #'empty-trace? premises) (assert (and 'traces nil)))
	  ((some #'not-implemented-trace? premises)
	   (find-if #'not-implemented-trace? premises))
	  (t
	   (assert-debug (proof-list? premises)
			 "make-trace"
			   (list (cons "sym" sym)
				 (cons "params" params)
				 (cons "premises" premises)))
	   (make-proof sym params premises)
	   )))))

(defun cut-list (list n)
  (assert (<= n (length list)))
  (cons (subseq list 0 n)
	(subseq list n (length list))))

(defmethod apply-trace ((empty-trace empty-trace) traces)
  (declare (ignore traces))
  (assert (and 'empty-trace-apply nil)))

(defmethod apply-trace ((not-implemented-trace not-implemented-trace) traces)
  (declare (ignore traces))
  not-implemented-trace)

;; will raise exception if number of holes in proof != number of traces
(defmethod apply-trace ((proof proof) traces)
  (assert (trace-list? traces))
  (cond
   ((some #'empty-trace? traces) (assert (and 'apply-empty nil)))
   ((some #'not-implemented-trace? traces)
    (find-if #'not-implemented-trace? traces)
    )
   (t
    (assert-debug (proof-list? traces)
		  "apply-trace"
		  (list (cons "proof" proof)
			(cons "traces" traces)))
;;    (format t "~%middle ~a" (catch 'apply-trace (apply-trace* proof traces)))
    (let ((result
	   (catch-debug 'apply-trace (apply-trace* proof traces)
			'apply-trace (list (cons "proof" proof)
					   (cons "traces" traces)))))
      (throw-debug (null (cdr result))
		   'apply-trace
		   (list (cons "proof" proof)
			 (cons "traces" traces)))
      (car result)))))

;; (defun catch-debug (tag prog name elts)
;;   (let ((result
;; 	 (multiple-value-list (catch tag prog))))
;;     (assert-debug (not (eq (car result) 'debug-const))
;; 		  name elts)
;;     (values-list result)))


(defmethod apply-trace* ((proof hole-rule) traces)
  (throw-debug (proof-list? traces) 'apply-trace nil)
  (throw-debug (consp traces) 'apply-trace nil)
  traces ;; seen as (cons (car traces) (cdr traces))
  )

(defmethod apply-trace* (proof traces)
  (assert (proof? proof))
  (throw-debug 'apply-trace (proof-list? traces) nil)
  (let* ((cons-rev-npremises-remaining
	  (reduce
	   #'(lambda (cons-done-remaining premise)
	       (let* ((done-traces (car cons-done-remaining))
		      (remaining-traces (cdr cons-done-remaining))
		      (aux (apply-trace* premise remaining-traces)))
		 (cons (cons (car aux) done-traces) ;; done
		       (cdr aux)))) ;; remaining
	   (cons (cons nil traces) (premises proof))))
	 (remaining (cdr cons-rev-npremises-remaining))
	 (npremises (reverse (car cons-rev-npremises-remaining))))
    (let ((newproof
	   (catch-throw-debug 'make-proof
			      (make-proof (name proof)
					  (params proof)
					  npremises)
			      'apply-trace
			      nil)))
      (cons newproof remaining))))


;; TYPING TRACES

(defmethod well-typed-trace ((trace empty-trace) antecedents (consequent sequent))
  (assert-debug (sequent-list? antecedents) "well-typed-empty" nil)
  (format t "~%Empty trace~%")
  nil)

(defmethod well-typed-trace ((trace not-implemented-trace) antecedents (consequent sequent))
  (assert-debug (sequent-list? antecedents) "well-typed-not-implemented"
		(list (cons "antecedents" antecedents)))
  t)

(defun check-traces-recursively (proofstate message)
  (when *check-traces*
    (let* ((subgoals
	    (unless (eq (car (status proofstate)) '!)
	      (append (remaining-subgoals proofstate)
		      (pending-subgoals proofstate)
		      (done-subgoals proofstate)))))
      (assert-debug (or (and (or (eq (car (status proofstate)) '*)
				 (eq (car (status proofstate)) 'X)
				 (eq (car (status proofstate)) 'XX))
			     (null subgoals))
			(null (car (status proofstate)))
			(eq (car (status proofstate)) 0)
			(well-typed-trace
			 (cdr (status proofstate))
			 (mapcar #'(lambda (ps) (current-goal ps))
				 (sort (reduce ;; remove redundancies
					#'(lambda (subs sub)
					    (if (find sub subs
						      :test #'(lambda (s1 s2)
								(equal (label s1) (label s2))))
						subs
					      (cons sub subs)))
					(cons nil subgoals))
				       #'mystring<= :key #'label))
			 (current-goal proofstate)))
		    message (list (cons "sequent" (current-goal proofstate))
				  (cons "hidden" (hidden-s-forms (current-goal proofstate)))
				  (cons "status-flag" (status-flag proofstate))
				  (cons "proof" (cdr (status proofstate)))
				  (cons "subgoals" subgoals)))
      (mapc #'(lambda (ps) (check-traces-recursively ps message)) (remaining-subgoals proofstate))
      (mapc #'(lambda (ps) (check-traces-recursively ps message)) (pending-subgoals proofstate))
      (when (not (null (current-subgoal proofstate)))
	(check-traces-recursively (current-subgoal proofstate) message))
      (mapc #'(lambda (ps) (check-traces-recursively ps message)) (done-subgoals proofstate)))))

(defun check-trace (trace antecedents consequent message)
  (when *check-traces*
    (assert-debug (well-typed-trace trace antecedents consequent)
		  message (list (cons "sequent" consequent)
				(cons "hidden" (hidden-s-forms consequent))
				(cons "proof" trace)
				(cons "subgoals" antecedents)))))

;; PRINT PARTIAL PROOFS

(defmethod print-object ((trace not-implemented-trace) stream)
  (format stream "To be implemented: ~a" (name trace)))

(defmethod print-object ((trace empty-trace) stream)
  (format stream "No proof found: ~a" (name trace)))

;; TESTS

(defmethod trace? ((trace trace))
  t)

(defmethod trace? (expr)
  (declare (ignore expr))
  nil)

(defun trace-list? (traces)
  (and (listp traces)
       (every #'(lambda (trace) (trace? trace)) traces)))

(defmethod empty-trace? ((empty-trace empty-trace))
  t)

(defmethod empty-trace? (expr)
  (declare (ignore expr))
  nil)

(defmethod not-implemented-trace? ((not-implemented-trace not-implemented-trace))
  t)

(defmethod not-implemented-trace? (expr)
  (declare (ignore expr))
  nil)
