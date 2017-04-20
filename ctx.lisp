(defclass ctx () ())
(defclass expr-ctx (ctx)
  ((captured :initarg :captured :accessor captured);;one list per bind
   (binds :initarg :binds :accessor binds)
   (subbinds :initarg :subbinds :accessor subbinds)
   (proofs :initarg :proofs :accessor proofs)
   (expr :initarg :expr :accessor expr)))
(defclass not-implemented-ctx (ctx)
  ((name :initarg :name :accessor name)))

;; BUILD CTX

(defun sub-binds (bind)
  (let* ((leftid (intern (format nil "~a_left" (id bind))))
	 (rightid (intern (format nil "~a_right" (id bind))))
	 (leftbind (compute-binding leftid (type bind)))
	 (rightbind (compute-binding rightid (type bind))))
    (cons leftbind rightbind)))

(defun make-ctx (sym arg &optional params)
  (cond ((eq sym 'not-implemented)
	 (make-instance 'not-implemented-ctx
			:name arg))
	((eq sym 'expr-hole)
	 (let* ((newid (make-new-variable 'ctxvar *true*))
		(binding (compute-binding newid arg)))
	   (make-instance 'expr-ctx
			  :captured (list nil)
			  :binds (list binding)
			  :subbinds (list (sub-binds binding))
			  :proofs (list (make-trace 'proof-hole))
			  :expr (mk-name-expr binding))))
	((eq sym 'expr)
	 (make-instance 'expr-ctx
			:captured nil
			:binds nil
			:subbinds nil
			:proofs nil
			:expr arg))
	(t ;; arg is a list of contexts
	 (if (some #'not-implemented-ctx? arg)
	     (find-if #'not-implemented-ctx? arg)
	   (make-ctx* sym arg params)))))


(defun sub-alist* (oldsubbind newsubbind)
    (list (cons (car oldsubbind) (car newsubbind))
	  (cons (cdr oldsubbind) (cdr newsubbind))))

(defun splits-list (exprs) ;; splits of the form (list, a, list)
  (cond ((null exprs)
	 nil)
	(t
	 (cons (list nil (car exprs) (cdr exprs))
	       (mapcar #'(lambda (split)
			   (list (cons (car exprs) (car split))
				 (cadr split)
				 (caddr split)))
		       (splits-list (cdr exprs)))))))

(defun make-ctx* (sym ctxs &optional params)
  (assert (expr-ctx-list? ctxs))
  (cond ((eq sym 'tuple)
	 (let* ((nctxs (make-compatible-ctxs ctxs)))
	   (make-instance 'expr-ctx
			  :captured (apply #'append (mapcar #'captured nctxs))
	 		  :binds (apply #'append (mapcar #'binds nctxs))
	 		  :subbinds (apply #'append (mapcar #'subbinds nctxs))
	 		  :proofs (apply
				   #'append
				   (mapcar
				    #'(lambda (split)
					(let ((beforectxs (car split))
					      (currentctx (cadr split))
					      (afterctxs (caddr split)))
					  (mapcar
					   #'(lambda (bind subbinds proof)
					       (let* ((nbind
						       (compute-binding
							(id bind)
							(type (expr currentctx)))))
						 (make-proof 'congruence-rule
							     (list (compute-tuple
								    (append
								     (mapcar #'expr beforectxs)
								     (list (mk-name-expr nbind))
								     (mapcar #'expr afterctxs)))
								   nbind
								   (compute-substit
								    (expr currentctx)
								    (list (cons bind
										(mk-name-expr
										 (car subbinds)))))
								   (compute-substit
								    (expr currentctx)
								    (list (cons bind
										(mk-name-expr
										 (cdr subbinds))))))
							     (list proof))))
					   (binds currentctx)
					   (subbinds currentctx)
					   (proofs currentctx))))
				    (splits-list nctxs)))
			  :expr (compute-tuple (mapcar #'expr nctxs)))))
	((eq sym 'application)
	 (assert (null (cddr ctxs)))
	 (let* ((nctxs (make-compatible-ctxs ctxs))
		(functx (car nctxs))
		(argctx (cadr nctxs)))
	   (make-instance 'expr-ctx
			  :captured (append (captured functx)
					    (captured argctx))
			  :binds (append (binds functx)
					 (binds argctx))
	 		  :subbinds (append (subbinds functx)
					    (subbinds argctx))
	 		  :proofs (append
				   (mapcar
				    #'(lambda (bind subbinds proof)
					(let* ((nbind
						(compute-binding
						 (id bind)
						 (type (expr functx)))))
					  (make-proof 'congruence-rule
						      (list (compute-application
							     (mk-name-expr nbind)
							     (expr argctx))
							    nbind
							    (compute-substit
							     (expr functx)
							     (list (cons bind
									 (mk-name-expr
									  (car subbinds)))))
							    (compute-substit
							     (expr functx)
							     (list (cons bind
									 (mk-name-expr
									  (cdr subbinds))))))
						      (list proof))))
				    (binds functx)
				    (subbinds functx)
				    (proofs functx))
				   (mapcar
				    #'(lambda (bind subbinds proof)
					(let* ((nbind
						(compute-binding
						 (id bind)
						 (type (expr argctx)))))
					  (make-proof 'congruence-rule
						      (list (compute-application
							     (expr functx)
							     (mk-name-expr nbind))
							    nbind
							    (compute-substit
							     (expr argctx)
							     (list (cons bind
									 (mk-name-expr
									  (car subbinds)))))
							    (compute-substit
							     (expr argctx)
							     (list (cons bind
									 (mk-name-expr
									  (cdr subbinds))))))
						      (list proof))))
				    (binds argctx)
				    (subbinds argctx)
				    (proofs argctx)))
			  :expr (compute-application (expr functx)
						     (expr argctx))))
	 )
	((eq sym 'if-application)
	 (assert (null (cdddr ctxs)))
	 (let* ((nctxs (make-compatible-ctxs ctxs))
		(testctx (car nctxs))
		(thenctx (cadr nctxs))
		(elsectx (caddr nctxs)))
	   ;; (assert (null (binds textctx))) ;; to be instrumented later
	   (assert (and (name-expr? (car params))
			(eq (id (car params)) 'IF)))
	   (make-instance 'expr-ctx
			  :captured (append (captured testctx)
					    (captured thenctx)
					    (captured elsectx))
			  :binds (append (binds testctx)
					 (binds thenctx)
					 (binds elsectx))
	 		  :subbinds (append (subbinds testctx)
					    (subbinds thenctx)
					    (subbinds elsectx))
	 		  :proofs (append
				   (mapcar
				    #'(lambda (bind subbinds proof)
					(let* ((nbind
						(compute-binding
						 (id bind)
						 (type (expr testctx)))))
					  (make-proof 'congruence-rule
						      (list (compute-application
							     (car params)
							     (compute-tuple
							      (list (mk-name-expr nbind)
								    (expr thenctx)
								    (expr elsectx))))
							    nbind
							    (compute-substit
							     (expr testctx)
							     (list (cons bind
									 (mk-name-expr
									  (car subbinds)))))
							    (compute-substit
							     (expr testctx)
							     (list (cons bind
									 (mk-name-expr
									  (cdr subbinds))))))
						      (list proof))))
				    (binds testctx)
				    (subbinds testctx)
				    (proofs testctx))
				   
				   (mapcar
				    #'(lambda (bind subbinds proof)
					(make-trace 'if-then-congruence-rule
						    (list (car params)
							  (expr testctx)
							  (compute-substit
							   (expr thenctx)
							   (list (cons bind
								       (mk-name-expr
									(car subbinds)))))
							  (compute-substit
							   (expr thenctx)
							   (list (cons bind
								       (mk-name-expr
									(cdr subbinds)))))
							  (expr elsectx))
						    (list proof)))
				    (binds thenctx)
				    (subbinds thenctx)
				    (proofs thenctx))

				   (mapcar
				    #'(lambda (bind subbinds proof)
					(make-trace 'if-else-congruence-rule
						    (list (car params)
							  (expr testctx)
							  (expr thenctx)
							  (compute-substit
							   (expr elsectx)
							   (list (cons bind
								       (mk-name-expr
									(car subbinds)))))
							  (compute-substit
							   (expr elsectx)
							   (list (cons bind
								       (mk-name-expr
									(cdr subbinds))))))
						    (list proof)))
				    (binds elsectx)
				    (subbinds elsectx)
				    (proofs elsectx)))
			  :expr (compute-application (car params)
						     (compute-tuple
						      (list (expr testctx)
							    (expr thenctx)
							    (expr elsectx))))))
	 )
	((eq sym 'negation)
	 (assert (null (cdr ctxs)))
	 (let* ((ctx (car ctxs)))
	   (make-instance 'expr-ctx
			  :captured (captured ctx)
			  :binds (binds ctx)
	 		  :subbinds (subbinds ctx)
	 		  :proofs (mapcar
				   #'(lambda (bind subbinds proof)
				       (let* ((nbind
					       (compute-binding
						(id bind)
						(type (expr ctx)))));; boolean
					 (make-proof 'congruence-rule
						     (list (compute-negation
							    (mk-name-expr nbind))
							   nbind
							   (compute-substit
							    (expr ctx)
							    (list (cons bind
									(mk-name-expr
									 (car subbinds)))))
							   (compute-substit
							    (expr ctx)
							    (list (cons bind
									(mk-name-expr
									 (cdr subbinds))))))
						     (list proof))))
				   (binds ctx) (subbinds ctx) (proofs ctx))
			  :expr (compute-negation (expr ctx)))))
	((eq sym 'forall)
	 (assert (null (cdr ctxs)))
	 (assert (not (null params)))
	 (assert (null (cdr params)))
	 ;; (assert (and 'test (null (cdr (car params)))));; to be changed for multivariable binders
	 (let* ((ctx (car ctxs))
		(binds (binds ctx))
		(subbinds (subbinds ctx)))
	   (make-instance 'expr-ctx
			  :captured (mapcar #'(lambda (capt)
						(append (car params) capt))
					    (captured ctx))
			  :binds (binds ctx)
	 		  :subbinds (subbinds ctx)
	 		  :proofs (mapcar #'(lambda (bind subbind)
					      (make-trace 'extforall-rule
							  (list (car params);;binding list
								(compute-substit
								 (expr ctx)
								 (list (cons bind
									     (mk-name-expr
									      (car subbind)))))
								(compute-substit
								 (expr ctx)
								 (list (cons bind
									     (mk-name-expr
									      (cdr subbind))))))
							  (list (car (proofs (car ctxs))))))
					  binds subbinds)
			  :expr (compute-forall (car params) (expr ctx)))))
	((eq sym 'exists)
	 (assert (null (cdr ctxs)))
	 (assert (not (null params)))
	 (assert (null (cdr params)))
	 ;; (assert (null (cdr (car params))));; to be changed for multivariable binders
	 (let* ((ctx (car ctxs))
		(binds (binds ctx))
		(subbinds (subbinds ctx)))
	   (make-instance 'expr-ctx
			  :captured (mapcar #'(lambda (capt)
						(append (car params) capt))
					    (captured ctx))
			  :binds (binds ctx)
	 		  :subbinds (subbinds ctx)
	 		  :proofs (mapcar #'(lambda (bind subbind)
					      (make-trace 'extexists-rule
							  (list (car params);;binding list
								(compute-substit
								 (expr ctx)
								 (list (cons bind
									     (mk-name-expr
									      (car subbind)))))
								(compute-substit
								 (expr ctx)
								 (list (cons bind
									     (mk-name-expr
									      (cdr subbind))))))
							  (list (car (proofs (car ctxs))))))
					  binds subbinds)
			  :expr (compute-exists (car params) (expr ctx)))))
	((eq sym 'lambda)
	 (assert (null (cdr ctxs)))
	 (assert (not (null params)))
	 (assert (null (cdr params)))
	 ;; (assert (null (cdr (car params))));; to be changed for multivariable binders
	 (let* ((ctx (car ctxs))
		(binds (binds ctx))
		(subbinds (subbinds ctx)))
	   (make-instance 'expr-ctx
			  :captured (mapcar #'(lambda (capt)
						(append (car params) capt))
					    (captured ctx))
			  :binds (binds ctx)
	 		  :subbinds (subbinds ctx)
	 		  :proofs (mapcar #'(lambda (bind subbind)
					      (make-trace 'extlambda-rule
							  (list (car params);;binding list
								(compute-substit
								 (expr ctx)
								 (list (cons bind
									     (mk-name-expr
									      (car subbind)))))
								(compute-substit
								 (expr ctx)
								 (list (cons bind
									     (mk-name-expr
									      (cdr subbind))))))
							  (list (car (proofs (car ctxs))))))
					  binds subbinds)
			  :expr (compute-lambda (car params) (expr ctx)))))
	((eq sym 'typepreds)
	 (assert (null (cdr ctxs)))
	 (assert (not (null params)))
	 (assert (null (cdr params)))
	 (let* ((ctx (car ctxs))
		(binds (binds ctx))
		(subbinds (subbinds ctx))
		(proofs (proofs ctx)))
	   (make-instance 'expr-ctx
			  :captured (captured ctx)
			  :binds (binds ctx)
	 		  :subbinds (subbinds ctx)
	 		  :proofs (mapcar
				   #'(lambda (bind subbind proof)
				       (make-trace 'typepred-rule
						   (list
						    (mapcar
						     #'(lambda (ex)
							 (compute-negation
							  (compute-substit
							  ex
							  (list (cons bind
								      (mk-name-expr
								       (cdr subbind)))))))
						     (car params)))
						   (list proof)))
					  binds subbinds proofs)
			  :expr (expr ctx))))
	(t
	 (assert (and 'missingctxcommand nil)))))

(defmethod make-compatible-ctxs (ctxs)
  (make-compatible-ctxs* (mapcar #'captured ctxs)
			 (mapcar #'binds ctxs)
			 (mapcar #'subbinds ctxs)
			 (mapcar #'proofs ctxs)
			 (mapcar #'expr ctxs)
			 (compute-tuple (mapcar #'expr ctxs))))

(defmethod make-compatible-ctxs* (captured-list
				  binds-list
				  subbinds-list
				  proofs-list
				  exprs
				  fresh-base
				  &optional
				  nbinds
				  nsubbinds
				  ncaptured-list
				  nbinds-list
				  nsubbinds-list
				  nproofs-list
				  nexprs)
  (if (null exprs)
      (mapcar #'(lambda (ncapts nbinds nsubbinds nproofs nexpr) ;;shadowing
		  (make-instance 'expr-ctx
				 :captured ncapts
				 :binds nbinds
				 :subbinds nsubbinds
				 :proofs nproofs
				 :expr nexpr))
	      (nreverse ncaptured-list)
	      (nreverse nbinds-list)
	      (nreverse nsubbinds-list)
	      (nreverse nproofs-list)
	      (nreverse nexprs))
    (let ((binds (car binds-list))
	  (subbinds (car subbinds-list)))
      (if (null binds) ;; (car exprs) is compatible, exprs --> nexprs and (rev nbinds) --> nbinds-list 
	  (make-compatible-ctxs* (cdr captured-list)
				 (cdr binds-list)
				 (cdr subbinds-list)
				 (cdr proofs-list)
				 (cdr exprs)
				 fresh-base
				 nil
				 nil
				 (cons (car captured-list) ncaptured-list)
				 (cons (nreverse nbinds) nbinds-list)
				 (cons (nreverse nsubbinds) nsubbinds-list)
				 (cons (car proofs-list) nproofs-list)
				 (cons (car exprs) nexprs))
	(let* ((expr (car exprs))
	       (nid (make-new-variable 'ctxvar fresh-base))
	       (nbind (compute-binding nid (type (car binds))))
	       (nsubbind (sub-binds nbind))
	       (nproofs (mapcar
			 #'(lambda (proof)
			     (instantiate-vars-proof
			      proof
			      (cons
			       (cons (car binds) (mk-name-expr nbind));;ctx1/ctx
			       (sub-alist*;;ctx1_left/ctx_left, ctx1_right/ctx_right
				(car subbinds) nsubbind;; (mk-name-expr nbind)
				))))
			 (car proofs-list)))
	       (nexpr (compute-substit expr
				       (list (cons (car binds) (mk-name-expr nbind))))))
	  (make-compatible-ctxs* captured-list
				 (cons (cdr binds) (cdr binds-list))
				 (cons (cdr subbinds) (cdr subbinds-list))
				 (cons nproofs (cdr proofs-list))
				 (cons nexpr (cdr exprs))
				 (compute-tuple (list (mk-name-expr nbind) fresh-base))
				 (cons nbind nbinds)
				 (cons nsubbind nsubbinds)
				 ncaptured-list
				 nbinds-list
				 nsubbinds-list
				 nproofs-list
				 nexprs))))))


(defmethod apply-ctx ((ctx not-implemented-ctx) ctxs)
  (declare (ignore ctxs))
  ctx)

(defmethod apply-ctx ((ctx expr-ctx) ctxs)
  (assert (ctx-list? ctxs))
  (cond ((some #'not-implemented-ctx? ctxs)
	 (find-if #'not-implemented-ctx? ctxs))
	(t
	 (assert (expr-ctx-list? ctxs))
	 (apply-ctx* ctx ctxs))))

(defmethod apply-ctx* ((ctx expr-ctx) ctxs)
  (assert (ctx-list? ctxs))
  (assert (expr-ctx-list? ctxs))
  (let* ((bindings (binds ctx))
	 (subbindings (subbinds ctx))
	 (captured (captured ctx))
	 (expression (expr ctx))
	 (proofs (proofs ctx))
	 (captured-list (mapcar #'captured ctxs))
	 (bindings-list (mapcar #'binds ctxs))
	 (subbindings-list (mapcar #'subbinds ctxs))
	 (proofs-list (mapcar #'proofs ctxs))
	 (expression-list (mapcar #'expr ctxs)))
    (assert (equal (list-length bindings) (list-length ctxs)))
    (let* ((fresh-base
	    (compute-tuple (append (list expression)
				   expression-list
				   (mapcar #'mk-name-expr bindings))))
	   (nctxs (make-compatible-ctxs* captured-list bindings-list subbindings-list proofs-list
					 expression-list fresh-base)))
      (assert (tc-eq (apply-ctx-aux expression bindings (mapcar #'expr nctxs));; in order to remove apply-ctx-aux later
		     (compute-instantiate expression
					  (mapcar #'(lambda (bind nctx)
						      (cons bind (expr nctx)))
						  bindings nctxs))))
      (make-instance 'expr-ctx
		     :captured (apply #'append
				      (mapcar #'(lambda (nctx capt)
						  (mapcar #'(lambda (ncapt)
							      (append capt ncapt))
							  (captured nctx)))
					      nctxs captured))
		     :binds (apply #'append (mapcar #'binds nctxs))
		     :subbinds (apply #'append (mapcar #'subbinds nctxs))
		     :proofs
		     (apply
		      #'append
		      (mapcar
		       #'(lambda (funsubbinds funproof argctx)
			   (let* ((argbinds (binds argctx))
				  (argsubbinds (subbinds argctx))
				  (argproofs (proofs argctx))
				  (argexpr (expr argctx)))
			     (mapcar
			      #'(lambda (argbind argsubbinds argproof)
				  (apply-trace
				   (instantiate-vars-proof
				    funproof
				    (cons (cons (car funsubbinds)
						(compute-instantiate
						 argexpr
						 (list (cons argbind
							     (mk-name-expr
							      (car argsubbinds))))))
					  (cons (cons (cdr funsubbinds)
						      (compute-instantiate
						       argexpr
						       (list (cons argbind
								   (mk-name-expr
								    (cdr argsubbinds))))))
						(mapcar #'(lambda (bind nctx)
							    (cons bind (expr nctx)))
							bindings nctxs))))
				   (list argproof))
				  )
			      argbinds argsubbinds argproofs)))
		       subbindings proofs nctxs))
		     :expr
		     (apply-ctx-aux expression bindings (mapcar #'expr nctxs))))))

(defun apply-ctx-aux (expr binds nexprs)
  (assert (equal (list-length binds) (list-length nexprs)))
  (if (null nexprs)
      expr
    (let ((bind (car binds))
	  (nexpr (car nexprs)))
      (apply-ctx-aux (compute-instantiate expr (list (cons bind nexpr)))
		     (cdr binds)
		     (cdr nexprs)))))


;; TESTS

(defmethod ctx? ((ctx ctx))
  t)

(defmethod ctx? (ctx)
  (declare (ignore ctx))
  nil)

(defmethod expr-ctx? ((ctx expr-ctx))
  t)

(defmethod expr-ctx? (ctx)
  (declare (ignore ctx))
  nil)

(defmethod not-implemented-ctx? ((ctx not-implemented-ctx))
  t)

(defmethod not-implemented-ctx? (ctx)
  (declare (ignore ctx))
  nil)

(defun ctx-list? (ctxs)
  (and (listp ctxs)
       (every #'(lambda (ctx) (ctx? ctx)) ctxs)))

(defun expr-ctx-list? (ctxs)
  (and (listp ctxs)
       (every #'(lambda (ctx) (expr-ctx? ctx)) ctxs)))

(defun not-implemented-ctx-list? (ctxs)
  (and (listp ctxs)
       (every #'(lambda (ctx) (not-implemented-ctx? ctx)) ctxs)))
