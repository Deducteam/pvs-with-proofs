;; EQUALITIES

(defmethod compute-sequent-eq ((seq1 sequent) (seq2 sequent))
  (compute-sforms-eq (append (s-forms seq1) (hidden-s-forms seq1))
		     (append (s-forms seq2) (hidden-s-forms seq2)))
  ;; (and (compute-sforms-eq  (s-forms seq2))
  ;;      (compute-sforms-eq (hidden-s-forms seq1) (hidden-s-forms seq2)))
  )

(defun compute-sforms-eq (sforms1 sforms2)
    (compute-forms-eq (mapcar #'formula sforms1) (mapcar #'formula sforms2)))

(defun compute-forms-eq (forms1 forms2)
  (or (and (null forms1) (null forms2))
      (and (member (car forms1) forms2 :test #'compute-form-eq)
	   (compute-forms-eq (cdr forms1)
		     (remove (car forms1) forms2 :test #'compute-form-eq :count 1)))))

(defmethod compute-form-eq (form1 form2)
  ;; (tc-eq (compute-normalize form1)
  ;; 	 (compute-normalize form2))
  (tc-eq form1 form2)
  )


;; COMPUTING FUNCTIONS

(defun compute-sequent (sforms hsforms)
  (make-instance 'sequent
		 :s-forms sforms
		 :hidden-s-forms hsforms))

(defun compute-s-form (form)
  (make-instance 's-formula :formula form))

(defun compute-negation (form)
  (make-instance 'unary-negation
		 :operator (not-operator)
		 :argument form
		 :type *boolean*))

(defun compute-conjunction (form1 form2)
  (make-instance 'infix-conjunction
	     :operator (and-operator)
	     :argument (compute-tuple (list form1 form2))
	     :type *boolean*))

(defun compute-implication (form1 form2)
  (make-instance 'infix-implication
	     :operator (implies-operator)
	     :argument (compute-tuple (list form1 form2))
	     :type *boolean*))

(defun compute-disjunction (form1 form2)
  (make-instance 'infix-disjunction
	     :operator (or-operator)
	     :argument (compute-tuple (list form1 form2))
	     :type *boolean*))

(defun compute-iff (form1 form2)
  (make-instance 'infix-iff
	     :operator (iff-operator)
	     :argument (compute-tuple (list form1 form2))
	     :type *boolean*))

(defun compute-if (cond then else &optional type)
  (let* ((stype (or type
		    (compatible-type (type then) (type else))))
	 (ifoptype (make-instance 'funtype
				  :domain (make-instance 'tupletype
							 :types (list *boolean* stype stype))
				  :range stype))
	 (if-res (mk-resolution (if-declaration)
				(mk-modname '|if_def| (list (mk-actual stype)))
				ifoptype))
	 (if-name (make-instance 'name-expr
				 :id 'IF
				 :type ifoptype
				 :resolutions (list if-res)))
	 (if-args (make-instance 'arg-tuple-expr
				 :exprs (list cond then else)
				 :type (make-instance 'tupletype
						      :types (list *boolean*
								   (type then) (type else))))))
    (make-instance 'mixfix-branch
		   :type stype
		   :operator if-name
		   :argument if-args)))

(defun compute-boolean-if (cond then else)
  (let* ((ifoptype (make-instance 'funtype
				  :domain (make-instance 'tupletype
							 :types (list *boolean*
								      *boolean*
								      *boolean*))
				  :range *boolean*))
	 (if-res (mk-resolution (if-declaration)
				(mk-modname '|if_def| (list (mk-actual *boolean*)))
				ifoptype))
	 (if-name (make-instance 'name-expr
				 :id 'IF
				 :type ifoptype
				 :resolutions (list if-res)))
	 (if-args (make-instance 'arg-tuple-expr
				 :exprs (list cond then else)
				 :type (make-instance 'tupletype
						      :types (list *boolean*
								   *boolean*
								   *boolean*)))))
    (make-instance 'mixfix-branch
		   :operator if-name
		   :argument if-args
		   :type *boolean*)))

(defun compute-lambda (bindings expr)
  (make-instance 'lambda-expr
	     :bindings bindings
	     :expression expr
	     :type (make-formals-funtype (list bindings) (type expr))))

(defun compute-forall (bindings expr)
  (make-instance 'forall-expr
	     :bindings bindings
	     :expression expr
	     :type (type expr);; (make-formals-funtype (list bindings) (type expr))
	     ))

(defun compute-exists (bindings expr)
  (make-instance 'exists-expr
	     :bindings bindings
	     :expression expr
	     :type (type expr);; (make-formals-funtype (list bindings) (type expr))
	     ))

(defun compute-binding (id type)
  (make-bind-decl id type))

(defun compute-tuple (exprs)
  (make-arg-tuple-expr exprs))

(defun compute-equation (arg1 arg2)
  (make!-equation arg1 arg2))

;; (defmethod change-to-propositional-class* ((ex unary-application))
;;   (case (id (operator ex))
;;     ((NOT) (change-class ex 'unary-negation))))

;; (defmethod change-to-propositional-class* ((ex infix-application))
;;   (change-to-infix-propositional-class* ex))

;; (defmethod change-to-propositional-class* ((ex application))
;;   (change-to-appl-propositional-class* ex))

;; (defmethod change-to-propositional-class* (ex)
;;   ex)

;; (defun change-to-appl-propositional-class* (ex)
;;   (case (id (operator ex))
;;     ((NOT ¬) (change-class ex 'negation))
;;     ((AND & ∧) (change-class ex 'conjunction))
;;     ((OR ∨) (change-class ex 'disjunction))
;;     ((IMPLIES => ⇒) (change-class ex 'implication))
;;     ((IFF <=> ⇔) (change-class ex 'iff))
;;     (WHEN (let ((place (place (operator ex))))
;; 	    (change-class ex 'when-expr)
;; 	    (setf (operator ex) (mk-implies-operator))
;; 	    (setf (place (operator ex)) place))
;; 	  (if (tuple-expr? (argument ex))
;; 	      (setf (exprs (argument ex)) (reverse (exprs (argument ex))))
;; 	      (setf (argument ex)
;; 		    (make!-projected-arg-tuple-expr*
;; 		     (reverse (make-projections (argument ex)))))))
;;     (= (if (compatible? (type (args1 ex)) *boolean*)
;; 	   (change-class ex 'boolean-equation)
;; 	   (change-class ex 'equation)))
;;     ((/= ≠) (change-class ex 'disequation)))
;;   ;; (when (and (not (tuple-expr? (argument ex)))
;;   ;; 	     (not (eq (id (operator ex)) 'NOT)))
;;   ;;   (setf (argument ex)
;;   ;; 	  (make!-projected-arg-tuple-expr* (make-projections (argument ex)))))
;;   )

;; (defun change-to-infix-propositional-class* (ex)
;;   (case (id (operator ex))
;;     ((AND & ∧) (change-class ex 'infix-conjunction))
;;     ((OR ∨) (change-class ex 'infix-disjunction))
;;     ((IMPLIES =>) (change-class ex 'infix-implication))
;;     ((IFF <=>) (change-class ex 'infix-iff))
;;     (WHEN (let ((op (operator ex)))
;; 	    (change-class ex 'infix-when-expr
;; 	      'operator (mk-implies-operator))
;; 	    (setf (place (operator ex)) (place op))
;; 	    (setf (exprs (argument ex)) (reverse (exprs (argument ex))))))
;;     (= (if (compatible? (type (args1 ex)) *boolean*)
;; 	   (change-class ex 'infix-boolean-equation)
;; 	   (change-class ex 'infix-equation)))
;;     ((/= ≠) (change-class ex 'infix-disequation)))
;;   ;; (unless (tuple-expr? (argument ex))
;;   ;;   (setf (argument ex)
;;   ;; 	  (make!-projected-arg-tuple-expr* (make-projections (argument ex)))))
;;   )


;; ;; see details in change-application-class-if-needed
;; (defun compute-application (op arg)
;;   (let* ((ex (mk-application op arg)))
;;     (setf (type ex) (range (type op)))
;;     (let ((operator (operator ex))
;; 	  ;; (argument (argument ex))
;; 	  )
;;       (cond ((and (typep operator 'name-expr)
;; 		  (boolean-op? operator '(NOT AND & OR IMPLIES => IFF <=> WHEN)))
;; 	     (change-to-propositional-class* ex))
;; 	    ((and (typep operator 'name-expr)
;; 		  (eq (id operator) '=)
;; 		  (eq (id (module-instance operator)) '|equalities|))
;; 	     (change-to-propositional-class* ex))
;; 	    ((and (typep operator 'name-expr)
;; 		  (eq (id operator) '/=)
;; 		  (eq (id (module-instance operator)) '|notequal|))
;; 	     (change-to-propositional-class* ex))
;; 	    ((and (typep operator 'name-expr)
;; 		  (eq (id operator) 'IF)
;; 		  (eq (id (module-instance operator)) '|if_def|)
;; 		  (not (typep ex 'branch)))
;; 	     (change-class ex 'branch)
;; 	     ;; (unless (tuple-expr? (argument ex))
;; 	     ;;   (setf (argument ex)
;; 	     ;; 	     (make!-projected-arg-tuple-expr*
;; 	     ;; 	      (make-projections argument))))
;; 	     )
;; 	    ;; ((ground-arith-simplifiable? operator argument)
;; 	    ;;  (let ((num (apply (id operator)
;; 	    ;; 		       (if (tuple-expr? argument)
;; 	    ;; 			   (mapcar #'number (exprs argument))
;; 	    ;; 			 (list (number argument))))))
;; 	    ;;    (change-expr-number-class ex num)))
;; 	    ((typep operator 'injection-expr)
;; 	     (change-class ex 'injection-application
;; 			   :index (index operator)
;; 			   :id (id operator)))
;; 	    ((typep operator 'injection?-expr)
;; 	     (change-class ex 'injection?-application
;; 			   :index (index operator)
;; 			   :id (id operator)))))
;;     ex))


;; instead of make!-application to avoid beta reductions
(defun compute-application (op arg)
  (let ((*use-rationals* nil))
    (make!-application-internal op arg)))

(defun compute-number (arg)
  (make!-number-expr arg))


;; inspired from make!-disequation which doesn't work
(defun disequality-decl ()
  (find-if #'(lambda (d) (eq (id (module d)) '|notequal|))
	   (get-declarations '/=)))

(defun compute-disequation (lhs rhs)
  (assert (and (type lhs) (type rhs)))
  (assert (compatible? (type lhs) (type rhs)))
  (let* ((type (find-supertype (type lhs)))
	 (res (mk-resolution (disequality-decl)
		(mk-modname '|notequal| (list (mk-actual type)))
		(mk-funtype (list type type) *boolean*)))
	 (diseqname (make-instance 'name-expr
		      :id '/=
		      :type (type res)
		      :resolutions (list res)))
	 (arg (make!-arg-tuple-expr lhs rhs)))
    (make-instance 'infix-disequation
      :operator diseqname
      :argument arg
      :type *boolean*)))



;; SUBSTITUTION

(defvar *compute-substit* nil)
(defvar *compute-instantiate* nil)

(defun compute-substit (expr alist)
  (let ((*compute-substit* t) ;; see (substit* application) --> simplify-or-copy-app
	(*use-rationals* nil) ;; see (substit* application) --> simplify-or-copy-app
	(*substit-dont-simplify* t))
    (substit expr alist)))

(defun compute-instantiate (expr alist)
  (let ((*compute-instantiate* t) ;; see (substit* binding-expr)
	(*compute-substit* t) ;; see (substit* application) --> simplify-or-copy-app
	(*use-rationals* nil) ;; see (substit* application) --> simplify-or-copy-app
	(*substit-dont-simplify* t))
    (substit expr alist)))


;; (defmethod compute-normalize :around (expr)
;;   ;; (when *mynewtest*
;;   ;; (format t "~%~a~%" expr))
;;   (call-next-method))

(defmethod compute-normalize ((expr application))
  ;; (show (operator expr))
  (cond ((lambda-expr? (operator expr))
	 (cond ((singleton? (bindings (operator expr)))
		(compute-normalize
		 (compute-substit (expression (operator expr))
				 (acons (car (bindings (operator expr))) (argument expr) nil))))
	       (t
		(compute-normalize
		 (compute-substit (expression (operator expr))
				 (pairlis-args (bindings (operator expr))
					       (argument-list (argument expr)))))))
	 ;; (assert (= (list-length (bindings (operator expr))) 1))
	 ;; (compute-normalize
	 ;;  (compute-substit (expression (operator expr))
	 ;; 		   (list (cons (car (bindings (operator expr)))
	 ;; 			       (argument expr)))))
	 )
	((and (name-expr? (operator expr))
	      (eq (id (operator expr)) '=))
	 (let ((arg1 (compute-normalize (car (exprs (argument expr)))))
	       (arg2 (compute-normalize (cadr (exprs (argument expr))))))
	   (cond ((tc-eq arg1 *true*)
		  arg2)
		 ((tc-eq arg1 arg2)
		  *true*)
		 (t
		  (compute-application (operator expr)
				       (compute-tuple (list arg1 arg2)))))))
	((and (name-expr? (operator expr))
	      (eq (id (operator expr)) '<))
	 (let ((arg1 (compute-normalize (car (exprs (argument expr)))))
	       (arg2 (compute-normalize (cadr (exprs (argument expr))))))
	   (cond ((tc-eq arg1 arg2)
		  *false*)
		 (t
		  (compute-application (operator expr)
				       (compute-tuple (list arg1 arg2)))))))
	((and (name-expr? (operator expr))
	      (eq (id (operator expr)) 'IF))
	 (let ((arg1 (compute-normalize (car (exprs (argument expr)))))
	       (arg2 (compute-normalize (cadr (exprs (argument expr)))))
	       (arg3 (compute-normalize (caddr (exprs (argument expr))))))
	   (cond ((tc-eq arg1 *false*)
		  arg3)
		 ((tc-eq arg1 *true*)
		  arg2)
		 ((tc-eq arg2 arg3)
		  arg2)
		 (t
		  (compute-application (operator expr)
				       (compute-tuple (list arg1 arg2 arg3)))))))
	((and (name-expr? (operator expr))
	      (eq (id (operator expr)) '-))
	 (let ((arg (compute-normalize (argument expr))))
	   (cond ;; ((tc-eq arg (compute-number 0))
		 ;;  (compute-number 0))
		 ((and (application? arg)
		       (eq (id (operator arg)) '-))
		  (argument arg))
		 (t
		  (compute-application (operator expr) arg)))))
	((and (name-expr? (operator expr))
	      (eq (id (operator expr)) 'sgn))
	 (let* ((arg (compute-normalize (argument expr)))
		(decl (declaration (car (resolutions (operator expr))))))
	   (compute-normalize
	    (compute-substit
	     (definition decl)
	     (list (cons (car (car (formals decl))) arg))))))
	(t
	 (let* ((newop (compute-normalize (operator expr)))
		(newarg (compute-normalize (argument expr))))
	  (if (tc-eq newop (operator expr))
	      (compute-application newop newarg)
	    (compute-normalize (compute-application newop newarg)))))))


(defmethod compute-normalize ((expr name-expr))
  (cond ((and (def-decl? (declaration expr))
	      (declared-measure (declaration expr)))
	 expr)
	((def-axiom (declaration expr))
	 (compute-normalize (args2
			     (subst-mod-params
			      (car (last (def-axiom
					   (declaration expr))))
			      (module-instance (resolution expr))
			      (module (declaration expr))
			      (declaration expr)))))
	((bind-decl? (declaration expr))
	 expr)
	((formal-const-decl? (declaration expr))
	 expr)
	((and
	  (not (formal-const-decl? (declaration expr)))
	  (null (definition (declaration expr))))
	 expr)
	(t
	 (show (definition (declaration expr)))
	 (assert (and 'compute-normalize nil)))))

(defmethod compute-normalize ((expr number-expr))
  expr)

(defmethod compute-normalize ((expr tuple-expr))
  (compute-tuple (mapcar #'compute-normalize (exprs expr))))

(defmethod compute-normalize ((expr forall-expr))
  (if (null (cdr (bindings expr)))
      (compute-forall
       (bindings expr)
       (compute-normalize (expression expr)))
    (compute-normalize
     (compute-forall
      (list (car (bindings expr)))
      (compute-forall
       (cdr (bindings expr))
       (expression expr))))))

(defmethod compute-normalize ((expr exists-expr))
  (compute-exists
   (bindings expr)
   (compute-normalize (expression expr))))

(defmethod compute-normalize ((expr lambda-expr))
  (compute-lambda
   (bindings expr)
   (compute-normalize (expression expr))))

(defmethod compute-normalize ((expr expr))
  expr;; (show expr)
  ;; (assert (and 'normalize nil))
  )

(defmethod compute-normalize ((expr projappl))
  expr)
