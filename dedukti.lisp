(defclass dk-term () ())
(defclass dk-var (dk-term)
  ((id :initarg :id :accessor id)))
(defclass dk-logic-var (dk-term)
  ((id :initarg :id :accessor id)))
(defclass dk-module-var (dk-term)
  ((module :initarg :module :accessor module)
   (id :initarg :id :accessor id)))
(defclass dk-const (dk-term) ())
(defclass dk-app (dk-term)
  ((fun :initarg :fun :accessor fun)
   (args :initarg :args :accessor args)))
(defclass dk-pi (dk-term)
  ((var :initarg :var :accessor var)
   (type :initarg :type :accessor type)
   (body :initarg :body :accessor body)))
(defclass dk-lam (dk-term)
  ((var :initarg :var :accessor var)
   (type :initarg :type :accessor type)
   (body :initarg :body :accessor body)))
(defclass dk-arrow (dk-term)
  ((domain :initarg :domain :accessor domain)
   (range :initarg :range :accessor range)))

(defun make-lam (var type body)
  (make-instance 'dk-lam
		 :var var
		 :type type
		 :body body))

(defun make-lam-term (var type body)
  (declare (ignore type))
  (make-app dk-lam-term (list (make-lam var dk-type-type body))))


(defun make-pi (var type body)
  (make-instance 'dk-pi
		 :var var
		 :type type
		 :body body))

(defun make-app (fun args)
  (make-instance 'dk-app
		 :fun fun
		 :args args))

(defun make-app-term (fun args)
  (make-app dk-app-term (cons fun args))
  )

(defun make-var (var)
  (make-instance 'dk-var :id var))

(defun make-logic-var (var)
  (make-instance 'dk-logic-var :id var))

(defun make-module-var (id var)
  (make-instance 'dk-module-var :module id :id var))

(defun make-arrow (t1 t2)
  (make-instance 'dk-arrow :domain t1 :range t2))

(defparameter dk-prop-type (make-instance 'dk-const))
(defparameter dk-type-type (make-instance 'dk-const))
(defparameter dk-app-term (make-instance 'dk-const))
(defparameter dk-lam-term (make-instance 'dk-const))
(defparameter dk-imply (make-instance 'dk-const))
(defparameter dk-prf (make-instance 'dk-const))
(defparameter dk-type-term (make-instance 'dk-const))
(defmethod dk-eq ((term1 dk-var) (term2 dk-var))
  (equal (id term1) (id term2)))
(defmethod dk-eq ((term1 dk-logic-var) (term2 dk-logic-var))
  (equal (id term1) (id term2)))
(defmethod dk-eq ((term1 dk-module-var) (term2 dk-module-var))
  (and (equal (id term1) (id term2))
       (equal (module term1) (module term2))))
(defmethod dk-eq ((term1 dk-const) (term2 dk-const))
  (equal term1 term2))
(defmethod dk-eq ((term1 dk-app) (term2 dk-app))
  (and (dk-eq (fun term1) (fun term2))
       (every #'dk-eq (args term1) (args term2))))
(defmethod dk-eq ((term1 dk-lam) (term2 dk-lam))
  (or (and (dk-eq (var term1) (var term2))
	   (dk-eq (body term1) (body term2)))
      (dk-eq (body term1) (dk-substit (body term2)
				      (list (cons (var term2)
						  (var term1)))))))
(defmethod dk-eq ((term1 dk-pi) (term2 dk-pi))
  (or (and (dk-eq (var term1) (var term2))
	   (dk-eq (body term1) (body term2)))
      (dk-eq (body term1) (dk-substit (body term2)
				     (list (cons (var term2)
						 (var term1)))))))
(defmethod dk-eq ((term1 dk-term) (term2 dk-term))
  nil;;   (show term1)
  ;; (show term2)
  ;; (assert (and 'dkeq nil))
  )

(defmethod dk-fv (var (term dk-var))
  (dk-eq var term))
(defmethod dk-fv (var (term dk-logic-var))
  (declare (ignore var))
  (assert (and 'fv2 nil)))
(defmethod dk-fv (var (term dk-module-var))
  (declare (ignore var))
  (assert (and 'fv2b nil)))
(defmethod dk-fv (var (term dk-const))
  (declare (ignore var))
  (assert (and 'fv3 nil)))
(defmethod dk-fv (var (term dk-app))
  (declare (ignore var))
  (assert (and 'fv4 nil)))
(defmethod dk-fv (var (term dk-lam))
  (declare (ignore var))
  (assert (and 'fv5 nil)))
(defmethod dk-fv (var (term dk-pi))
  (declare (ignore var))
  (assert (and 'fv6 nil)))
(defmethod dk-fv (var (term dk-term))
  (declare (ignore var))
  (assert (and 'fv7 nil)))

(defmethod make-free-var (var terms &optional (n 0))
  (if (some
       #'(lambda (term)
	   (dk-fv (make-instance 'dk-var :id (format nil "~a~a" (id var) n)) term))
       terms)
      (make-free-var var terms (+ n 1))
    (make-instance 'dk-var :id (format nil "~a~a" (id var) n))))

(defmethod dk-substit ((term dk-var) alist)
  (if (some #'(lambda (cns)
		(dk-eq term (car cns))) alist)
      (find-env2 term alist)
    term))
(defmethod dk-substit ((term dk-logic-var) alist)
  (declare (ignore alist))
  term)
(defmethod dk-substit ((term dk-module-var) alist)
  (declare (ignore alist))
  term)
(defmethod dk-substit ((term dk-const) alist)
  (declare (ignore alist))
  term)
(defmethod dk-substit ((term dk-app) alist)
  (make-app (dk-substit (fun term) alist)
	    (mapcar #'(lambda (arg)
			(dk-substit arg alist)) (args term))))
(defmethod dk-substit ((term dk-lam) alist)
  (assert (equal (list-length alist) 1))
  (if (some #'(lambda (bind)
		(dk-fv (var term) (cdr bind)))
	    alist)
      (let ((nvar (make-free-var (var term) (mapcar #'cdr alist))))
	(dk-substit
	 (make-lam nvar (type term)
		   (dk-substit (body term)
			       (list (cons var nvar))))
	 alist))
    (if (dk-eq (var term) (car (car alist)))
	(assert (and 'lam2 nil))
      (make-lam (var term)
		(dk-substit (type term) alist)
		(dk-substit (body term) alist)))))
(defmethod dk-substit ((term dk-pi) alist)
  (declare (ignore alist))
  (assert (and 'pi nil)))
(defmethod dk-substit ((term dk-term) alist)
  (declare (ignore alist))
  (assert (and 'dk-substit nil)))



(defclass dk-line () ())
(defclass dk-prelude (dk-line) 
  ((name :initarg :name :accessor name)))
(defclass dk-decl (dk-line)
  ((id :initarg :id :accessor id)
   (type :initarg :type :accessor type)))
(defclass dk-def (dk-line)
  ((id :initarg :id :accessor id)
   (type :initarg :type :accessor type)
   (body :initarg :body :accessor body)))



;; MAKE


(defparameter nb 0)

(defmethod make-new-var ()
  (setq nb (+ nb 1))
  (make-instance 'dk-var :id (format nil "V~a" (- nb 1))))

(defmethod make-dk-not (term)
  (make-app-term (make-logic-var 'NOT) (list term)))

(defmethod make-dk-implies (term1 term2)
  (make-app-term (make-logic-var 'IMPLIES)
	    (list
	     (make-app (make-logic-var 'pair)
		       (list term1 term2)))))

(defmethod make-dk-or (term1 term2)
  (make-app-term (make-logic-var 'OR)
	    (list
	     (make-app (make-logic-var 'pair)
		       (list term1 term2)))))

(defmethod make-dk-and (term1 term2)
  (make-app-term (make-logic-var 'AND)
	    (list
	     (make-app (make-logic-var 'pair)
		       (list term1 term2)))))

(defmethod make-dk-args (term)
  ;; (print-dk-term t (cadr (args term)))
  ;; (assert nil)
  (args (cadr (args term))))

(defmethod make-dk-true ()
  (make-logic-var 'TRUE))

(defmethod make-dk-false ()
  (make-logic-var 'FALSE))

(defmethod make-dk-exists (type term)
  (declare (ignore type))
  (make-app (make-logic-var 'EXISTS)
	    (list term)))

(defmethod make-dk-forall (type term)
  (declare (ignore type))
  (make-app (make-logic-var 'FORALL)
	    (list term)))

(defmethod make-dk-prf (term)
  (make-app dk-prf (list term)))

(defmethod make-dk-term (term)
  (make-app dk-type-term (list term)))

(defmethod dk-domain ((e dk-app))
  (cond ((dk-eq (fun e) (make-logic-var 'arrow))
	 (car (args e)))
	((dk-eq (fun e) (make-logic-var 'deparrow))
	 (car (args e)))
	(t
	 ;; (print-dk-term e)
	 (assert (and 'dk-domain-app nil)))))
(defmethod dk-domain (e)
  (print-dk-term t e)
  (show e)
  (assert (and 'dk-domain nil)))


(defvar *findenv-debug* nil)

(defmethod mk-dk-expr-term :around (e)
  (declare (ignore e))
  (call-next-method)
  ;; (format t "~%begin ~a" e);; (show e)
  ;; (let ((result (call-next-method)))
  ;;   (format t "~%end ~a" e);; (show e)
  ;;   result)
  )

(defmethod mk-dk-expr-term ((e projection-application))
  (cons (make-app (make-logic-var (format nil "proj~a" (index e)))
		  (list (argument e)))
	dk-type-type))

;;EXPRS

(defmethod mk-dk-expr-term ((e application))
  (let ((dkop (mk-dk-expr-term (operator e)))
	(dkarg (mk-dk-expr-term (argument e))))
    (cons (make-app dk-app-term (list (car dkop) (car dkarg)))
	  dk-type-type)))

(defmethod mk-dk-expr-term ((e arg-tuple-expr))
  (assert (and (not (null (exprs e)))
	       (not (null (cdr (exprs e))))))
  (cond ((projappl? (car (exprs e)))
	 (let ((var (argument (car (exprs e)))))
	   (assert (every #'(lambda (expr)
			      (and (projappl? expr)
				   (eq (argument expr) var)))
			  (exprs e)))
	   (mk-dk-expr-term var)))
	((null (cdr (cdr (exprs e))))
	 (let ((dkt1 (mk-dk-expr-term (car (exprs e))))
	       (dkt2 (mk-dk-expr-term (car (cdr (exprs e))))))
	   (cons (make-app
		  (make-logic-var 'pair)
		  (list (car dkt1)
			(car dkt2)))
		 (make-app
		  (make-logic-var 'product)
		  (list (cdr dkt1)
			(cdr dkt2))))))
	((null (cdr (cdr (cdr (exprs e)))))
	 (let ((dkt1 (mk-dk-expr-term (car (exprs e))))
	       (dkt2 (mk-dk-expr-term (car (cdr (exprs e)))))
	       (dkt3 (mk-dk-expr-term (car (cdr (cdr (exprs e)))))))
	   (cons (make-app
		  (make-logic-var 'tuple3)
		  (list (car dkt1)
			(car dkt2)
			(car dkt3)))
		 (make-app
		  (make-logic-var 'product3)
		  (list (cdr dkt1)
			(cdr dkt2)
			(cdr dkt3))))))
	(t
	 (assert (and 'arg-tuple nil)))))

(defmethod mk-dk-expr-term ((e exists-expr))
  ;; (cons (make-dk-forall dk-type-type
  ;; 			(car (mk-dk-expr-term2 (bindings e) (expression e))))
  ;; 	(make-logic-var 'boolean)))
  (cons (reduce #'(lambda (current bind)
		    (make-dk-exists dk-type-type
				    (make-lam bind
					      dk-type-type
					      current)))
	  (cons (car (mk-dk-expr-term (expression e)))
		(mapcar #'(lambda (bind) (car (mk-dk-expr-term bind))) (reverse (bindings e)))))
	dk-type-type))

(defmethod mk-dk-expr-term ((e lambda-expr))
  (let ((dkbinds (mapcar #'(lambda (bind) (car (mk-dk-expr-term bind))) (bindings e)))
  	(dkexpr (car (mk-dk-expr-term (expression e)))))
  (cond ((null (cdr dkbinds))
	 (cons (make-lam-term (car dkbinds)
			      dk-type-type
			      dkexpr)
	       dk-type-type))
	((null (cddr (bindings e)))
	 (let* ((var (make-new-var)))
	   (cons (make-lam-term
		  var
		  dk-type-type
		  (make-app-term
		   (make-app-term
		   (reduce #'(lambda (current dkbind)
			       (make-lam-term dkbind
					      dk-type-type
					      current))
			   (cons dkexpr dkbinds))
		   (list (make-app (make-logic-var "proj2")
				   (list var))))
		   (list (make-app (make-logic-var "proj1")
				   (list var)))))
		 dk-type-type)))
	(t
	 (assert (and 'longlanmbda nil))))
  
  ))

(defmethod mk-dk-expr-term ((e forall-expr))
  ;; (cons (make-dk-forall dk-type-type
  ;; 			(car (mk-dk-expr-term2 (bindings e) (expression e))))
  ;; 	(make-logic-var 'boolean)))
  (cons (reduce #'(lambda (current bind)
		    (make-dk-forall dk-type-type
				    (make-lam bind
					      dk-type-type
					      current)))
	  (cons (car (mk-dk-expr-term (expression e)))
		(mapcar #'(lambda (bind) (car (mk-dk-expr-term bind))) (reverse (bindings e)))))
	dk-type-type))

(defmethod mk-dk-expr-term ((e name-expr))
  (cond ;; ((eq (id e) 'member)
	;;  (show (declaration (car (resolutions e))))
	;;  (assert nil))
	((or (eq (id e) 'IMPLIES)
	     (eq (id e) 'OR)
	     (eq (id e) 'AND)
	     (eq (id e) 'NOT)
	     (eq (id e) 'TRUE)
	     (eq (id e) 'FALSE)
	     (eq (id e) 'sgn)
	     (eq (id e) 'IFF)
	     (eq (id e) 'abs)
	     (eq (id e) 'real_pred)
	     (eq (id e) 'number_field_pred)
	     (eq (id e) 'rational_pred)
	     (eq (id e) 'integer_pred)
	     (eq (id e) 'divides)
	     (eq (id e) 'min)
	     (eq (id e) 'mod)
	     (eq (id e) 'floor))
	 ;; (show e)
	 (cons (make-logic-var (id e))
	       dk-type-type))
	((eq (id e) 'IF)
	 ;; (show (car (mk-dk-expr-term (type e))))
	 (if
	     (and (subtype? (cadr (types (domain (type e)))))
		  (eq (id (print-type (cadr (types (domain (type e)))))) 'real))
	     (cons (make-logic-var 'if)
		   (car (mk-dk-expr-term (type e))))
	   (cons (make-logic-var 'if)
		 (car (mk-dk-expr-term (type e))))
	   ;; (cons (make-logic-var 'IF)
	   ;; 	   (car (mk-dk-expr-term (type e))))
	   ;; (cons (make-logic-var 'propif)
	   ;; 	 (car (mk-dk-expr-term (type e))))
	   ))
	((eq (id e) '=)
	 (if (and (type-name? (car (types (domain (type e)))))
		  (or (eq (id (car (types (domain (type e))))) 'bool)
		      (eq (id (car (types (domain (type e))))) 'boolean)))
	     (cons (make-logic-var 'eq) dk-type-type)
	     (cons (make-logic-var 'eq) dk-type-type)))
	((eq (id e) '>=)
	 (cons (make-logic-var 'geq)
	       (car (mk-dk-expr-term (type e)))))
	((eq (id e) '<=)
	 (cons (make-logic-var 'leq)
	       (car (mk-dk-expr-term (type e)))))
	((eq (id e) '=>)
	 (cons (make-logic-var 'IMPLIES)
	       (car (mk-dk-expr-term (type e)))))
	((eq (id e) '/=)
	 (cons (make-logic-var 'diff)
	       (car (mk-dk-expr-term (type e)))))
	((eq (id e) '<)
	 (cons (make-logic-var 'less)
	       (car (mk-dk-expr-term (type e)))))
	((eq (id e) '>)
	 (cons (make-logic-var 'greater)
	       (car (mk-dk-expr-term (type e)))))
	((eq (id e) '+)
	 (cons (make-logic-var 'plus)
	       (car (mk-dk-expr-term (type e)))))
	((eq (id e) '-)
	 (cons (make-logic-var 'minus)
	       (car (mk-dk-expr-term (type e)))))
	((eq (id e) '*)
	 (cons (make-logic-var 'times)
	       (car (mk-dk-expr-term (type e)))))
	((and (eq (id e) 'max)
	      (equal (id (module-instance (car (resolutions e)))) 'max_upto)
	      (not (equal (id (theory-name *current-context*)) 'max_upto)))
	 (cons (make-module-var "max_upto" (id e))
	       dk-type-type))
	((eq (id e) 'nonempty?)
	 (cons (make-logic-var 'nonempty_63)
	       dk-type-type))
	((eq (id e) 'minimum?)
	 (cons (make-logic-var 'minimum_63)
	       dk-type-type))
	((eq (id e) '/)
	 (cons (make-logic-var 'div)
	       (car (mk-dk-expr-term (type e)))))
        (t
	 (cons (make-var (id e))
	       dk-type-type))))

(defmethod mk-dk-expr-term ((e number-expr))
  (cons (make-logic-var (id e))
	(car (mk-dk-expr-term (type e)))))


;; TYPE TERMS

(defmethod mk-dk-expr-term ((e type-name))
  (if (or (eq (id e) 'boolean)
	  (eq (id e) 'number))
      (cons (make-logic-var (id e))
	    (make-logic-var 'type))
    (cons (make-instance 'dk-var :id (id e))
	  (make-logic-var 'type))
    ))

(defmethod mk-dk-expr-term ((e tupletype))
  (assert (and (not (null (types e)))
	       (not (null (cdr (types e))))))
  (cond ((null (cdr (cdr (types e))))
	 (cons (make-app
		(make-logic-var 'product)
		(list (car (mk-dk-expr-term (car (types e))))
		      (car (mk-dk-expr-term (car (cdr (types e)))))))
	       (make-logic-var 'type)))
	((null (cdr (cdr (cdr (types e)))))
	 (cons (make-app
		(make-logic-var 'product3)
		(list (car (mk-dk-expr-term (car (types e))))
		      (car (mk-dk-expr-term (car (cdr (types e)))))
		      (car (mk-dk-expr-term (car (cdr (cdr (types e))))))))
	       (make-logic-var 'type)))
	(t
	 (show e)
	 (assert (and 'tupletype nil)))))

(defmethod mk-dk-expr-term ((e subtype))
  (if (print-type e)
      (cond ((or (eq (id (print-type e)) 'numfield)
		 (eq (id (print-type e)) 'number_field))
	     (cons (make-instance 'dk-logic-var :id 'numfield)
		   (make-logic-var 'type)))
	    ((or (eq (id (print-type e)) 'real)
		 (eq (id (print-type e)) 'rational)
		 (eq (id (print-type e)) 'int)
		 (eq (id (print-type e)) 'nonneg_real)
		 (eq (id (print-type e)) 'nat))
	     (cons (make-instance 'dk-logic-var :id (id (print-type e)))
		   (make-logic-var 'type)))
	    (t 
	     (cons (make-instance 'dk-var :id (id (print-type e)))
		   (make-logic-var 'type))))
    (cons (make-app (make-logic-var 'subtype)
	      (list (car (mk-dk-expr-term (supertype e)))
		    (car (mk-dk-expr-term (predicate e)))))
	  (make-logic-var 'type))))

(defmethod mk-dk-expr-term ((e funtype))
  (cond ((typep (domain e) 'dep-binding)
	 ;; (assert (and 'type-pi nil))
	 (cons 
	  (make-app (make-logic-var 'deparrow)
		    (list (car (mk-dk-expr-term (type (domain e))))
			  (make-lam (make-var (id (domain e)))
				    (make-app (make-logic-var 'term)
					      (list (car (mk-dk-expr-term (type (domain e))))))
				    (car (mk-dk-expr-term (range e))))))
	  (make-logic-var 'type)))
	(t
	 (cons 
	  (make-app (make-logic-var 'arrow)
		    (list (car (mk-dk-expr-term (domain e)))
			  (car (mk-dk-expr-term (range e)))))
	  (make-logic-var 'type)))))


(defmethod mk-dk-expr-term ((e dep-binding))
  ;; (show (domain e))
  ;; (mk-dk-expr-term (type e))
  (assert (and 'dep-binding nil)))


(defun mk-dk-expr-term2 (binds expr)
  ;; (assert (and 'test (equal (list-length binds) 1)))
  (reduce #'(lambda (current bind)
	      (cons (make-lam bind
			      dk-type-type
			      (car current))
		    (make-arrow dk-type-type (cdr current))))
	  (cons (cons (car (mk-dk-expr-term expr)) dk-type-type)
		(mapcar #'(lambda (bind) (car (mk-dk-expr-term bind))) binds))))

  ;; (cons (make-lam (car (mk-dk-expr-term (car binds)))
  ;; 		  dk-type-type
  ;; 		  (car (mk-dk-expr-term expr)))
  ;; 	(make-arrow dk-type-type dk-type-type)))

;; A ENLEVER?
(defmethod mk-dk-type-term ((e type-name))
  (make-app dk-type-term (list (car (mk-dk-expr-term e)))))

(defmethod mk-dk-type-term ((e funtype))
  (make-arrow (mk-dk-type-term (domain e))
	      (mk-dk-type-term (range e))))

(defmethod mk-dk-type-term ((e subtype))
  (make-app dk-type-term (list (car (mk-dk-expr-term e)))))

;; (defmethod mk-dk-expr-term ((e infix-disjunction))
;;   (show e)
;;   (make-instance
;;    'dk-app :fun dk-imply :args (mapcar #'mk-dk-expr-term (exprs (argument e)))))

;; (defmethod mk-dk-expr-term ((e expr))
;;   (make-instance 'dk-var :id (id e)))

;; PROOF TERMS

(defun find-env (term env)
  (when *findenv-debug*
    (format t "~%~%~%")
    (print-dk-term t term)
    (format t "~%~%")
    (print-dk-term t (car (car env)))
    (format t "~%~%"))
  (when (eq env nil) (assert (and 'findenv nil)))
  (if (dk-eq (car (car env)) term)
      (cdr (car env))
    (find-env term (cdr env))))

(defun find-env2 (term env)
  ;; (format t "~%~%~%")
  ;; (print-dk-term t term)
  ;; (format t "~%~%")
  ;; (print-dk-term t (car (car env)))
  ;; (format t "~%~%")
  (when (eq env nil) (assert (and 'findenv2 nil)))
  (if (dk-eq (car (car env)) term)
      (cdr (car env))
    (find-env2 term (cdr env))))


(defun remove-env (term env)
  ;; (format t "~%~%~%")
  ;; (print-dk-term t term)
  ;; (format t "~%~%")
  ;; (print-dk-term t (car (car env)))
  (remove-if #'(lambda (pair) (dk-eq (car pair) term)) env :count 1))


(defmethod mk-dk-proof-term :around (proof sequent env)
  (declare (ignore proof sequent env))
  (call-next-method)
  ;; (declare (ignore sequent env))
  ;; (format t "~%begin ~a" (name proof))
  ;; (let ((result (call-next-method)))
  ;;   (format t "~%end ~a" (name proof))
  ;;   result)
  )

(defmethod mk-dk-proof-term ((proof implication-rule) sequent env)
  (let* ((a (car (mk-dk-expr-term (car (params proof)))))
	 (b (car (mk-dk-expr-term (cadr (params proof)))))
	 (hnna (make-new-var))
	 (tnna (make-dk-not (make-dk-not a)))
	 (hnb (make-new-var))
	 (tnb (make-dk-not b))
	 (prem (car (premises proof)))
	 (ante (car (antecedents proof sequent)))
	 (nenv (cons (cons tnna hnna)
	 	     (cons (cons tnb hnb)
	 		   env)))
	 (hab (find-env (make-dk-not (make-dk-implies a b)) env))
	 )
    (make-app (make-instance 'dk-logic-var :id (mk-dk-rule proof))
	      (append (list a b hab)
	      	      (list (make-lam hnna
				      (make-app dk-prf (list tnna))
				      (make-lam hnb
						(make-app dk-prf (list tnb))
						(mk-dk-proof-term prem ante nenv))))))
    ))

(defmethod mk-dk-proof-term ((proof not-not-rule) sequent env)
  (let* ((a (car (mk-dk-expr-term (car (params proof)))))
	 (hna (make-new-var))
	 (tna (make-dk-not a))
	 (prem (car (premises proof)))
	 (ante (car (antecedents proof sequent)))
	 (nenv (cons (cons tna hna)
		     env))
	 (hnnna (find-env (make-dk-not (make-dk-not (make-dk-not a))) env))
	 )
    (make-app (make-instance 'dk-logic-var :id (mk-dk-rule proof))
	      (append (list a hnnna)
	      	      (list (make-lam hna
				      (make-app dk-prf (list tna))
				      (mk-dk-proof-term prem ante nenv)))))))

(defmethod mk-dk-proof-term ((proof or-rule) sequent env)
  (let* ((a (car (mk-dk-expr-term (car (params proof)))))
	 (b (car (mk-dk-expr-term (cadr (params proof)))))
	 (hna (make-new-var))
	 (tna (make-dk-not a))
	 (hnb (make-new-var))
	 (tnb (make-dk-not b))
	 (prem (car (premises proof)))
	 (ante (car (antecedents proof sequent)))
	 (nenv (cons (cons tna hna)
	 	     (cons (cons tnb hnb)
	 		   env)))
	 (hab (find-env (make-dk-not (make-dk-or a b)) env))
	 )
    (make-app (make-instance 'dk-logic-var :id (mk-dk-rule proof))
	      (append (list a b hab)
	      	      (list (make-lam hna
				      (make-app dk-prf (list tna))
				      (make-lam hnb
						(make-app dk-prf (list tnb))
						(mk-dk-proof-term prem ante nenv))))))
   ))

(defmethod mk-dk-proof-term ((proof and-rule) sequent env)
  (let* ((a (car (mk-dk-expr-term (car (params proof)))))
	 (b (car (mk-dk-expr-term (cadr (params proof)))))
	 (hna (make-new-var))
	 (tna (make-dk-not a))
	 (hnb (make-new-var))
	 (tnb (make-dk-not b))
	 (prema (car (premises proof)))
	 (antea (car (antecedents proof sequent)))
	 (premb (cadr (premises proof)))
	 (anteb (cadr (antecedents proof sequent)))
	 (nenva (cons (cons tna hna)
		      env))
	 (nenvb (cons (cons tnb hnb)
		      env))
	 (hab (find-env (make-dk-not (make-dk-and a b)) env))
	 )
    (make-app (make-instance 'dk-logic-var :id (mk-dk-rule proof))
	      (append (list a b hab)
	      	      (list (make-lam hna
				      (make-app dk-prf (list tna))
				      (mk-dk-proof-term prema antea nenva))
			    (make-lam hnb
				      (make-app dk-prf (list tnb))
				      (mk-dk-proof-term premb anteb nenvb))))))
   )


(defmethod mk-dk-proof-term ((proof axiom-rule) sequent env)
  (declare (ignore sequent))
  (let* ((a (car (mk-dk-expr-term (car (params proof)))))
	 (tna (make-dk-not a))
	 (tnna (make-dk-not tna))
	 (hna (find-env tna env))
	 (hnna (find-env tnna env))
	 )
    (make-app (make-instance 'dk-logic-var :id (mk-dk-rule proof))
	      (append (list a hna hnna)
	      	      nil)))
   )

(defmethod mk-dk-proof-term ((proof not-and-rule) sequent env)
  (let* ((a (car (mk-dk-expr-term (car (params proof)))))
	 (b (car (mk-dk-expr-term (cadr (params proof)))))
	 (hnna (make-new-var))
	 (tnna (make-dk-not (make-dk-not a)))
	 (hnnb (make-new-var))
	 (tnnb (make-dk-not (make-dk-not b)))
	 (prem (car (premises proof)))
	 (ante (car (antecedents proof sequent)))
	 (nenv (cons (cons tnna hnna)
	 	     (cons (cons tnnb hnnb)
	 		   env)))
	 (hab (find-env (make-dk-not (make-dk-not (make-dk-and a b))) env)))
    (make-app (make-instance 'dk-logic-var :id (mk-dk-rule proof))
	      (append (list a b hab)
	      	      (list (make-lam hnna
				      (make-app dk-prf (list tnna))
				      (make-lam hnnb
						(make-app dk-prf (list tnnb))
						(mk-dk-proof-term prem ante nenv))))))
   ))

(defmethod mk-dk-proof-term ((proof not-or-rule) sequent env)
  (let* ((a (car (mk-dk-expr-term (car (params proof)))))
	 (b (car (mk-dk-expr-term (cadr (params proof)))))
	 (hna (make-new-var))
	 (tna (make-dk-not (make-dk-not a)))
	 (hnb (make-new-var))
	 (tnb (make-dk-not (make-dk-not b)))
	 (prema (car (premises proof)))
	 (antea (car (antecedents proof sequent)))
	 (premb (cadr (premises proof)))
	 (anteb (cadr (antecedents proof sequent)))
	 (nenva (cons (cons tna hna)
		      env))
	 (nenvb (cons (cons tnb hnb)
		      env))
	 (hab (find-env (make-dk-not (make-dk-not (make-dk-or a b))) env))
	 )
    (make-app (make-instance 'dk-logic-var :id (mk-dk-rule proof))
	      (append (list a b hab)
	      	      (list (make-lam hna
				      (make-app dk-prf (list tna))
				      (mk-dk-proof-term prema antea nenva))
			    (make-lam hnb
				      (make-app dk-prf (list tnb))
				      (mk-dk-proof-term premb anteb nenvb))))))
   )

(defmethod mk-dk-proof-term ((proof true-rule) sequent env)
  (declare (ignore sequent))
  (let* ((tnt (make-dk-not (make-dk-true)))
	 (hnt (find-env tnt env)))
    (make-app (make-instance 'dk-logic-var :id (mk-dk-rule proof))
	      (list hnt))))

(defmethod mk-dk-proof-term ((proof false-rule) sequent env)
  (let* ((tnt (make-dk-not (make-dk-false)))
	 (hnt (make-new-var))
	 (prem (car (premises proof)))
	 (ante (car (antecedents proof sequent)))
	 (nenv (cons (cons tnt hnt)
    	 	     env)))
    (make-app (make-instance 'dk-logic-var :id (mk-dk-rule proof))
	      (list (make-lam hnt
			      (make-app dk-prf (list tnt))
			      (mk-dk-proof-term prem ante nenv))))))

(defmethod mk-dk-proof-term ((proof not-false-rule) sequent env)
  (declare (ignore sequent))
  (let* ((tnnf (make-dk-not (make-dk-not (make-dk-false))))
	 (hnnf (find-env tnnf env)))
    (make-app (make-instance 'dk-logic-var :id (mk-dk-rule proof))
	      (list hnnf))))

(defmethod mk-dk-proof-term ((proof contr-rule) sequent env)
  (let* ((prem (car (premises proof)))
	 (ante (car (antecedents proof sequent)))
	 )
    (mk-dk-proof-term prem ante env)))

(defmethod mk-dk-proof-term ((proof weak-rule) sequent env)
  (let* ((prem (car (premises proof)))
	 (ante (car (antecedents proof sequent)))
	 )
    (mk-dk-proof-term prem ante env)))

(defmethod mk-dk-proof-term ((proof not-forall-rule) sequent env)
  (if (equal (list-length (cadr (params proof))) 1)
  (let* ((qp (argument (car (rule-conclusions proof))))
 	 (p (car (mk-dk-expr-term2 (bindings qp) (expression qp)))
	  ;; (car (mk-dk-expr-term (compute-lambda (bindings qp) (expression qp))))
	  )
    	 (*current-context* (context *current-theory*))
	 (pt (car (mk-dk-expr-term (compute-substit (expression qp)
						    (list (cons (car (bindings qp))
								(cdr (car (cadr (params proof))))))))))
    	 (term (car (mk-dk-expr-term (cdr (car (cadr (params proof)))))))
    	 (hnnpt (make-new-var))
    	 (tnnpt (make-dk-not (make-dk-not pt)))
    	 (prem (car (premises proof)))
	 (ante (car (antecedents proof sequent)))
    	 (nenv (cons (cons tnnpt hnnpt)
    	 	     env))
    	 (hnnqp (find-env (make-dk-not
			   (make-dk-not
			    (make-dk-forall dk-type-type
					    p))) env))
    	 )
    (make-app (make-instance 'dk-logic-var :id (mk-dk-rule proof))
    	      (append (list p term hnnqp)
    	      	      (list (make-lam hnnpt
    				      (make-app dk-prf (list tnnpt))
    				      (mk-dk-proof-term prem ante nenv)))))
    )
  (let* ((qp (argument (car (rule-conclusions proof))))
	 (new-proof
	    (car (reduce
	     #'(lambda (proof-binds-assocs bind-assoc)
		 (let* ((proof (car proof-binds-assocs))
			(binds (cadr proof-binds-assocs))
			(assocs (caddr proof-binds-assocs))
			(bind (car bind-assoc))
			(assoc (cdr bind-assoc)))
		   (list
		    (make-proof 'not-forall-rule
				(list
				 (compute-substit
				  (compute-foralls binds (expression qp))
				  (cdr assocs))
				 (list assoc))
				(list proof))
		    (cons bind binds)
		    (cdr assocs))))
	     (cons (list (car (premises proof)) nil (reverse (cadr (params proof))))
		   (reverse (mapcar #'cons (bindings qp) (cadr (params proof)))))))))
    (mk-dk-proof-term
       new-proof
       (replace-sequent sequent
			(car (rule-conclusions proof))
			(compute-negation (compute-foralls
			     (bindings qp)
			     (expression qp))))
       env))
  ))

(defmethod mk-dk-proof-term ((proof exists-rule) sequent env)
  (assert (and 'exists (equal (list-length (cadr (params proof))) 1)))
  (assert (equal (list-length (bindings (car (rule-conclusions proof)))) 1))
  (let* ((qp (car (rule-conclusions proof)))
    	 (p (car (mk-dk-expr-term2 (bindings qp) (expression qp))))
    	 ;; (p (car (mk-dk-expr-term (compute-lambda (bindings qp) (expression qp)))))
    	 (*current-context* (context *current-theory*))
	 (pt (car (mk-dk-expr-term (compute-substit (expression qp)
						    (list (cons (car (bindings qp))
								(cdr (car (cadr (params proof))))))))))
    	 (term (car (mk-dk-expr-term (cdr (car (cadr (params proof)))))))
    	 (hnnpt (make-new-var))
    	 (tnnpt (make-dk-not pt))
    	 (prem (car (premises proof)))
	 (ante (car (antecedents proof sequent)))
    	 (nenv (cons (cons tnnpt hnnpt)
    	 	     env))
    	 (hnnqp (find-env (make-dk-not
			    (make-dk-exists dk-type-type
					    p)) env))
    	 )
    (make-app (make-instance 'dk-logic-var :id (mk-dk-rule proof))
    	      (append (list p term hnnqp)
    	      	      (list (make-lam hnnpt
    				      (make-app dk-prf (list tnnpt))
    				      (mk-dk-proof-term prem ante nenv)))))
    ))

(defmethod mk-dk-proof-term ((proof not-implication-rule) sequent env)
  (let* ((a (car (mk-dk-expr-term (car (params proof)))))
	 (b (car (mk-dk-expr-term (cadr (params proof)))))
	 (hna (make-new-var))
	 (tna (make-dk-not a))
	 (hnb (make-new-var))
	 (tnb (make-dk-not (make-dk-not b)))
	 (prema (cadr (premises proof)))
	 (antea (cadr (antecedents proof sequent)))
	 (premb (car (premises proof)))
	 (anteb (car (antecedents proof sequent)))
	 (nenva (cons (cons tna hna)
		      env))
	 (nenvb (cons (cons tnb hnb)
		      env))
	 (hab (find-env (make-dk-not (make-dk-not (make-dk-implies a b))) env))
	 )
    (make-app (make-instance 'dk-logic-var :id (mk-dk-rule proof))
	      (append (list a b hab)
	      	      (list (make-lam hnb
				      (make-app dk-prf (list tnb))
				      (mk-dk-proof-term premb anteb nenvb))
			    (make-lam hna
				      (make-app dk-prf (list tna))
				      (mk-dk-proof-term prema antea nenva))
			    ))))
   )


(defmethod mk-dk-proof-term ((proof not-exists-rule) sequent env)
  (assert (and 'not-exists (equal (list-length (cadr (params proof))) 1)))
  (let* ((qp (argument (car (rule-conclusions proof))))
    	 (p (car (mk-dk-expr-term2 (bindings qp) (expression qp))))
    	 (*current-context* (context *current-theory*))
	 (pt (car (mk-dk-expr-term (compute-substit (expression qp)
						    (list (cons (car (bindings qp))
								(cdr (car (cadr (params proof))))))))))
    	 (term (car (mk-dk-expr-term (cdr (car (cadr (params proof)))))))
    	 (hnnpt (make-new-var))
    	 (tnnpt (make-dk-not (make-dk-not pt)))
    	 (prem (car (premises proof)))
	 (ante (car (antecedents proof sequent)))
    	 (nenv (cons (cons tnnpt hnnpt)
    	 	     env))
    	 (hnnqp (find-env (make-dk-not
			   (make-dk-not
			    (make-dk-exists dk-type-type
					    p))) env))
    	 )
    (make-app (make-instance 'dk-logic-var :id (mk-dk-rule proof))
    	      (append (list p hnnqp)
    	      	      (list (make-lam term
				      dk-type-type
				      (make-lam hnnpt
						(make-app dk-prf (list tnnpt))
						(mk-dk-proof-term prem ante nenv)))))
    )))

(defun compute-foralls (bindings expr)
  (cond ((not (null bindings))
	 (compute-forall (list (car bindings))
			 (compute-foralls (cdr bindings) expr)))
	(t
	 expr)))

(defmethod mk-dk-proof-term ((proof forall-rule) sequent env)
  (if (equal (list-length (cadr (params proof))) 1)
      (let* ((qp (car (rule-conclusions proof)))
	 (p (car (mk-dk-expr-term2 (bindings qp) (expression qp))))
	 (*current-context* (context *current-theory*))
	 (pt (car (mk-dk-expr-term (compute-substit (expression qp)
						    (list (cons (car (bindings qp))
								(cdr (car (cadr (params proof))))))))))
	 (term (car (mk-dk-expr-term (cdr (car (cadr (params proof)))))))
	 (hnnpt (make-new-var))
	 (tnnpt (make-dk-not pt))
	 (prem (car (premises proof)))
	 (ante (car (antecedents proof sequent)))
	 (nenv (cons (cons tnnpt hnnpt)
		     env))
	 (hnnqp (find-env (make-dk-not
			   (make-dk-forall dk-type-type
					   p)) env))
	 )
	(make-app (make-instance 'dk-logic-var :id (mk-dk-rule proof))
		  (append (list p hnnqp)
			  (list (make-lam term
					  dk-type-type
					  (make-lam hnnpt
						    (make-app dk-prf (list tnnpt))
						    (mk-dk-proof-term prem ante nenv)))))))
    (let* ((qp (car (rule-conclusions proof)))
	   (new-proof
	    (car (reduce
	     #'(lambda (proof-binds-assocs bind-assoc)
		 (let* ((proof (car proof-binds-assocs))
			(binds (cadr proof-binds-assocs))
			(assocs (caddr proof-binds-assocs))
			(bind (car bind-assoc))
			(assoc (cdr bind-assoc))
			(expr (compute-substit
			       (compute-forall (list (car assoc)) (compute-foralls binds (expression qp)))
			       (cdr assocs))))
		   (list
		    (make-proof 'forall-rule
				(list
				 (expression expr)
				 ;; (compute-substit
				 ;;  (compute-foralls binds (expression qp))
				 ;;  (cdr assocs))
				 (list (cons (car (bindings expr))
					     (compute-substit (cdr assoc) (cdr assocs))))
				 ;; (list (cons (car (bindings;; substitution of assoc
				 ;; 	     	   (compute-substit
				 ;; 	     	    (compute-lambda
				 ;; 	     	     (list (car assoc))
				 ;; 	     	     *true*)
				 ;; 	     	    (cdr assocs))))
				 ;; 	     (compute-substit
				 ;; 	      (cdr assoc)
				 ;; 	      (cdr assocs))))
				 )
				(list proof))
		    (cons bind binds)
		    (cdr assocs))))
	     (cons (list (car (premises proof)) nil (reverse (cadr (params proof))))
		   (reverse (mapcar #'cons (bindings qp) (cadr (params proof)))))))))
      (mk-dk-proof-term
       new-proof
       (replace-sequent sequent
			(car (rule-conclusions proof))
			(compute-foralls
			     (bindings qp)
			     (expression qp)))
       env))))

(defmethod mk-dk-proof-term ((proof leibniz-rule) sequent env)
  (let* ((ctx (car (params proof)))
	 (u (cadr (params proof)))
	 (v (caddr (params proof)))
	 (dkpred (car (mk-dk-expr-term2 (binds ctx) (expr ctx))))
	 (dku (car (mk-dk-expr-term u)))
	 (dkv (car (mk-dk-expr-term v)))
	 (conc (car (rule-conclusions proof)))
	 ;; (dummy (setq *findenv-debug* t))
	 (hconc (find-env (make-dk-not (car (mk-dk-expr-term conc))) env))
	 (hyp1 (car (car (rule-hypotheses proof))))
	 (hyp2 (car (cadr (rule-hypotheses proof))))
	 (hhyp1 (car (mk-dk-expr-term hyp1)))
	 (hhyp2 (car (mk-dk-expr-term hyp2)))
	 (hnhyp1 (make-new-var))
	 (hnhyp2 (make-new-var))
	 (prem1 (car (premises proof)))
	 (ante1 (car (antecedents proof sequent)))
	 (prem2 (cadr (premises proof)))
	 (ante2 (cadr (antecedents proof sequent)))
	 (nenv1 (cons (cons (make-dk-not hhyp1) hnhyp1) env))
	 (nenv2 (cons (cons (make-dk-not hhyp2) hnhyp2) env)))
    (assert (eq (list-length (binds ctx)) 1))
    (assert (eq (list-length (captured ctx)) 1))
    (let ((leibniz-name
	   (format nil "RLeibniz1~a" (list-length (car (captured ctx))))))
      (assert (< (list-length (car (captured ctx))) 2))
      (if (= (list-length (car (captured ctx))) 0)
	  (make-app
	   (make-logic-var leibniz-name)
	   (list dkpred
		 dku
		 dkv
		 hconc
		 (make-lam hnhyp1
			   (make-dk-prf (make-dk-not hhyp1))
			   (mk-dk-proof-term prem1 ante1 nenv1))
		 (make-lam hnhyp2
			   (make-dk-prf (make-dk-not hhyp2))
			   (mk-dk-proof-term prem2 ante2 nenv2))))
	(let* ((capt (car (car (captured ctx))))
	       (bind (car (binds ctx)))
	       (nid (make-new-variable 'ctxvar (expr ctx)))
	       (nbind (compute-binding nid (mk-funtype (type capt) (type bind))))
	       (dkpred (car (mk-dk-expr-term2
			      (list nbind)
			      (compute-instantiate
			       (expr ctx)
			       (list (cons bind
					   (compute-application
						    (make-variable-expr nbind)
						    (make-variable-expr capt))))))))
	       (dkvar (car (mk-dk-expr-term capt)))
	       (dktype (cdr (mk-dk-expr-term capt)))
	       ;; (dkctxvar (car (mk-dk-expr-term nbind)))
	       ;; (dkctxtype (cdr (mk-dk-expr-term nbind)))
	       )
	  ;; (show bind)
	  (assert (and 'abc5 nil))
	  (make-app
	   (make-logic-var leibniz-name)
	   (list dktype
		 dkpred
		 (make-lam dkvar
			   (make-dk-term dktype)
			   dku)
		 (make-lam dkvar
			   (make-dk-term dktype)
			   dkv)
		 hconc
		 (make-lam hnhyp1
			   (make-dk-prf (make-dk-not hhyp1))
			   (mk-dk-proof-term prem1 ante1 nenv1))
		 (make-lam dkvar
			   (make-dk-term dktype)
			   (make-lam hnhyp2
				     (make-dk-prf (make-dk-not hhyp2))
				     (mk-dk-proof-term prem2 ante2 nenv2))))))))))


(defmethod mk-dk-proof-term ((proof cut-rule) sequent env)
  (let* ((prop (car (params proof)))
	 (dkprop (car (mk-dk-expr-term prop)))
	 (dkvar1 (make-new-var))
	 (dkvar2 (make-new-var))
	 (prem1 (car (premises proof)))
	 (ante1 (car (antecedents proof sequent)))
	 (prem2 (cadr (premises proof)))
	 (ante2 (cadr (antecedents proof sequent)))
	 (nenv1 (cons (cons (make-dk-not dkprop) dkvar1) env))
	 (nenv2 (cons (cons (make-dk-not (make-dk-not dkprop)) dkvar2) env)))
    (make-app
     (make-logic-var "RCut")
     (list dkprop
	   (make-lam dkvar1
		     (make-dk-prf (make-dk-not dkprop))
		     (mk-dk-proof-term prem1 ante1 nenv1))
	   (make-lam dkvar2
		     (make-dk-prf (make-dk-not (make-dk-not dkprop)))
		     (mk-dk-proof-term prem2 ante2 nenv2))))))

(defmethod mk-dk-proof-term ((proof not-true-rule) sequent env)
  (let* ((dkvar (make-new-var))
	 (prem (car (premises proof)))
	 (ante (car (antecedents proof sequent)))
	 (nenv (cons (cons (make-dk-not (make-dk-not (make-dk-true))) dkvar) env)))
    (make-app
     (make-logic-var "RNotTrue")
     (list (make-lam dkvar
		     (make-dk-prf (make-dk-not (make-dk-not (make-dk-true))))
		     (mk-dk-proof-term prem ante nenv))))))


(defmethod mk-dk-proof-term ((proof rewrite-rule) sequent env)
  (let* ((hyp (car (car (rule-hypotheses proof))))
	 (conc (car (rule-conclusions proof)))
	 (dkhyp (car (mk-dk-expr-term hyp)))
	 (dkconc (car (mk-dk-expr-term conc)))
	 (prem (car (premises proof)))
	 (ante (car (antecedents proof sequent)))
	 (dkconcprf (find-env (make-dk-not dkconc) env))
	 (nenv
	  (cons (cons (make-dk-not dkhyp) dkconcprf)
		(remove-env (make-dk-not dkconc) env))))
    ;; (when (application? (caddr (params proof)))
    ;; 	(show (caddr (params proof))))
    (cond ((tc-eq (compute-normalize hyp) (compute-normalize conc))
	   (mk-dk-proof-term prem ante nenv))
	  ((and (application? (caddr (params proof)))
		(name-expr? (operator (caddr (params proof))))
		(eq (id (operator (caddr (params proof)))) 'abs))
	   (let* ((rewritten (operator (caddr (params proof)))))
	     (assert (null (cdr (resolutions rewritten))))
	     (mk-dk-proof-term prem ante nenv)))
	  ((and (application? (caddr (params proof)))
		(name-expr? (operator (caddr (params proof))))
		(eq (id (operator (caddr (params proof)))) 'IF))
	   (let* ((rewritten (operator (caddr (params proof)))))
	     (assert (null (cdr (resolutions rewritten))))
	     (mk-dk-proof-term prem ante nenv)))
	  (t 
	   (call-next-method)))))

(defmethod mk-dk-proof-term ((proof extprop-rule) sequent env)
  (let* ((a (car (mk-dk-expr-term (car (params proof)))))
	 (b (car (mk-dk-expr-term (cadr (params proof)))))
	 (prem (car (premises proof)))
	 (ante (car (antecedents proof sequent)))
	 (dkhyp (car (mk-dk-expr-term (car (car (rule-hypotheses proof))))))
	 (dkconc (car (mk-dk-expr-term (car (rule-conclusions proof)))))
	 (dkhypprf (make-new-var))
	 (dkconcprf (find-env (make-dk-not dkconc) env))
	 (nenv (cons (cons (make-dk-not dkhyp)
			   dkhypprf)
		     env)))
    ;; (format t "~%~%~%~%")
    ;; (print-dk-term t dkhyp)
    ;; (format t "~%~%~%~%")
    ;; (print-dk-term t dkconc)
    (make-app (make-logic-var "RExtProp")
    	      (list a b dkconcprf
		    (make-lam dkhypprf
			      (make-app dk-prf (list (make-dk-not dkhyp)))
			      (mk-dk-proof-term prem ante nenv))))))


(defmethod mk-dk-proof-term ((proof trans-rule) sequent env)
  (let* ((dkhyp1 (car (mk-dk-expr-term (car (car (rule-hypotheses proof))))))
	 (dkhyp2 (car (mk-dk-expr-term (car (cadr (rule-hypotheses proof))))))
	 (dkconc (car (mk-dk-expr-term (car (rule-conclusions proof)))))
	 (a (car (mk-dk-expr-term (car (params proof)))))
	 (b (car (mk-dk-expr-term (cadr (params proof)))))
	 (c (car (mk-dk-expr-term (caddr (params proof)))))
	 (hn1 (make-new-var))
	 (tn1 (make-dk-not dkhyp1))
	 (hn2 (make-new-var))
	 (tn2 (make-dk-not dkhyp2))
	 (prem1 (car (premises proof)))
	 (ante1 (car (antecedents proof sequent)))
	 (prem2 (cadr (premises proof)))
	 (ante2 (cadr (antecedents proof sequent)))
	 (nenv1 (cons (cons tn1 hn1)
		      env))
	 (nenv2 (cons (cons tn2 hn2)
		      env))
	 (dkconcprf (find-env (make-dk-not dkconc) env))
	 )
    (make-app (make-logic-var "RTrans")
	      (list a
		    b
		    c
		    dkconcprf
		    (make-lam hn1
			      (make-app dk-prf (list tn1))
			      (mk-dk-proof-term prem1 ante1 nenv1))
		    (make-lam hn2
			      (make-app dk-prf (list tn2))
			      (mk-dk-proof-term prem2 ante2 nenv2)))))
   )

(defmethod mk-dk-proof-term ((proof congruence-rule) sequent env)
  ;; (call-next-method)
  (let* ((dkhyp (car (mk-dk-expr-term (car (car (rule-hypotheses proof))))))
  	 (dkconc (car (mk-dk-expr-term (car (rule-conclusions proof)))))
	 ;; (dummy1 (print-dk-term t dkconc))
  	 (expr (car (params proof)))
  	 (bind (cadr (params proof)))
  	 (dkexpr (car (mk-dk-expr-term expr)))
  	 (dkbind (car (mk-dk-expr-term bind)))
  	 (dka (car (mk-dk-expr-term (caddr (params proof)))))
	 (dkb (car (mk-dk-expr-term (cadddr (params proof)))))
  	 (prem (car (premises proof)))
  	 (ante (car (antecedents proof sequent)))
  	 (dkhypprf (make-new-var))
  	 (dkconcprf (find-env (make-dk-not dkconc) env))
  	 (nenv (cons (cons (make-dk-not dkhyp)
  			   dkhypprf)
  		     env)))
    (make-app (make-logic-var "RCongruence")
    	      (list (make-lam dkbind
  			      dk-type-type
  			      dkexpr)
  		    dka
  		    dkb
  		    dkconcprf
  		    (make-lam dkhypprf
  			      (make-app dk-prf (list (make-dk-not dkhyp)))
  			      (mk-dk-proof-term prem ante nenv)))))
  )

(defmethod mk-dk-proof-term ((proof if-then-congruence-rule) sequent env)
  (let* ((dktest (car (mk-dk-expr-term (cadr (params proof)))))
	 (dkhyp1 (car (mk-dk-expr-term (car (car (rule-hypotheses proof))))))
	 (dkhyp2 (car (mk-dk-expr-term (cadr (car (rule-hypotheses proof))))))
	 (dka (car (mk-dk-expr-term (caddr (params proof)))))
	 (dkb (car (mk-dk-expr-term (cadddr (params proof)))))
	 (dkelse (car (mk-dk-expr-term (caddddr (params proof)))))
	 (prem (car (premises proof)))
	 (ante (car (antecedents proof sequent)))
	 (dkconc (car (mk-dk-expr-term (car (rule-conclusions proof)))))
	 (dkhypprf1 (make-new-var))
	 (dkhypprf2 (make-new-var))
	 (dkconcprf (find-env (make-dk-not dkconc) env))
	 (nenv (cons (cons (make-dk-not dkhyp1)
			   dkhypprf1)
		     (cons (cons (make-dk-not dkhyp2)
				 dkhypprf2)
			   env))))
    ;; (print-dk-term t dktype)
    (make-app (make-logic-var "RIfThenCongruence")
    	      (list dktest
		    dka
		    dkb
		    dkelse
		    dkconcprf
		    (make-lam dkhypprf1
			      (make-app dk-prf (list (make-dk-not dkhyp1)))
			      (make-lam dkhypprf2
					(make-app dk-prf (list (make-dk-not dkhyp2)))
					(mk-dk-proof-term prem ante nenv)))))))

(defmethod mk-dk-proof-term ((proof if-else-congruence-rule) sequent env)
  (let* ((dktest (car (mk-dk-expr-term (cadr (params proof)))))
	 (dkhyp1 (car (mk-dk-expr-term (car (car (rule-hypotheses proof))))))
	 (dkhyp2 (car (mk-dk-expr-term (cadr (car (rule-hypotheses proof))))))
	 (dka (car (mk-dk-expr-term (cadddr (params proof)))))
	 (dkb (car (mk-dk-expr-term (caddddr (params proof)))))
	 (dkthen (car (mk-dk-expr-term (caddr (params proof)))))
	 (prem (car (premises proof)))
	 (ante (car (antecedents proof sequent)))
	 (dkconc (car (mk-dk-expr-term (car (rule-conclusions proof)))))
	 (dkhypprf1 (make-new-var))
	 (dkhypprf2 (make-new-var))
	 (dkconcprf (find-env (make-dk-not dkconc) env))
	 (nenv (cons (cons (make-dk-not dkhyp1)
			   dkhypprf1)
		     (cons (cons (make-dk-not dkhyp2)
				 dkhypprf2)
			   env))))
    ;; (print-dk-term t dktype)
    (make-app (make-logic-var "RIfElseCongruence")
    	      (list dktest
		    dkthen
		    dka
		    dkb
		    dkconcprf
		    (make-lam dkhypprf1
			      (make-app dk-prf (list (make-dk-not dkhyp1)))
			      (make-lam dkhypprf2
					(make-app dk-prf (list (make-dk-not dkhyp2)))
					(mk-dk-proof-term prem ante nenv)))))))


(defmethod mk-dk-proof-term ((proof extforall-rule) sequent env)
  (let* ((binds (car (params proof)))
	 (dkbinds (mapcar #'(lambda (bind)
			      (car (mk-dk-expr-term bind)))
			  binds))
	 (dka (car (mk-dk-expr-term (cadr (params proof)))))
	 (dkb (car (mk-dk-expr-term (caddr (params proof)))))
	 (prem (car (premises proof)))
	 (ante (car (antecedents proof sequent)))
	 (dkhyp (car (mk-dk-expr-term (car (car (rule-hypotheses proof))))))
	 (dkconc (car (mk-dk-expr-term (car (rule-conclusions proof)))))
	 (dkhypprf (make-new-var))
	 (dkconcprf (find-env (make-dk-not dkconc) env))
	 (nenv (cons (cons (make-dk-not dkhyp)
			   dkhypprf)
		     env)))
    (assert (= (list-length binds) 1))
    ;; (format t "~%~%~%~%")
    ;; (print-dk-term t dkhyp)
    ;; (format t "~%~%~%~%")
    ;; (print-dk-term t dkconc)
    (make-app (make-logic-var "RExtForall")
    	      (list (make-lam (car dkbinds)
			      dk-type-type
			      dka)
		    (make-lam (car dkbinds)
			      dk-type-type
			      dkb)
		    dkconcprf
		    (make-lam (car dkbinds)
			      dk-type-type
			      (make-lam dkhypprf
					(make-app dk-prf (list (make-dk-not dkhyp)))
					(mk-dk-proof-term prem ante nenv)))))))

(defmethod mk-dk-proof-term ((proof extexists-rule) sequent env)
  (let* ((binds (car (params proof)))
	 (dkbinds (mapcar #'(lambda (bind)
			      (car (mk-dk-expr-term bind)))
			  binds))
	 (dkbindtypes (mapcar #'(lambda (bind)
				  (cdr (mk-dk-expr-term bind)))
			      binds))
	 (dka (car (mk-dk-expr-term (cadr (params proof)))))
	 (dkb (car (mk-dk-expr-term (caddr (params proof)))))
	 (prem (car (premises proof)))
	 (ante (car (antecedents proof sequent)))
	 (dkhyp (car (mk-dk-expr-term (car (car (rule-hypotheses proof))))))
	 (dkconc (car (mk-dk-expr-term (car (rule-conclusions proof)))))
	 (dkhypprf (make-new-var))
	 (dkconcprf (find-env (make-dk-not dkconc) env))
	 (nenv (cons (cons (make-dk-not dkhyp)
			   dkhypprf)
		     env)))
    (assert (= (list-length binds) 1))
    ;; (format t "~%~%~%~%")
    ;; (print-dk-term t dkhyp)
    ;; (format t "~%~%~%~%")
    ;; (print-dk-term t dkconc)
    (assert (and 'abc12 nil))
    (make-app (make-logic-var "RExtExists")
    	      (list (car dkbindtypes)
		    (make-lam (car dkbinds)
			      (make-dk-term (car dkbindtypes))
			      dka) 
		    (make-lam (car dkbinds)
			      (make-dk-term (car dkbindtypes))
			      dkb)
		    dkconcprf
		    (make-lam (car dkbinds)
			      (make-dk-term (car dkbindtypes))
			      (make-lam dkhypprf
					(make-app dk-prf (list (make-dk-not dkhyp)))
					(mk-dk-proof-term prem ante nenv)))))))


(defmethod mk-dk-proof-term ((proof iff-rule) sequent env)
  (let* ((a (car (mk-dk-expr-term (car (params proof)))))
	 (b (car (mk-dk-expr-term (cadr (params proof)))))
	 (prem1 (car (premises proof)))
	 (ante1 (car (antecedents proof sequent)))
	 (prem2 (cadr (premises proof)))
	 (ante2 (cadr (antecedents proof sequent)))
	 (dkhyp1 (car (mk-dk-expr-term (car (car (rule-hypotheses proof))))))
	 (dkhyp2 (car (mk-dk-expr-term (car (cadr (rule-hypotheses proof))))))
	 (dkconc (car (mk-dk-expr-term (car (rule-conclusions proof)))))
	 (dkhypprf1 (make-new-var))
	 (dkhypprf2 (make-new-var))
	 (dkconcprf (find-env (make-dk-not dkconc) env))
	 (nenv1 (cons (cons (make-dk-not dkhyp1)
			    dkhypprf1)
		      env))
	 (nenv2 (cons (cons (make-dk-not dkhyp2)
			    dkhypprf2)
		      env)))
    (make-app (make-logic-var "RIFF")
    	      (list a b dkconcprf
		    (make-lam dkhypprf1
			      (make-app dk-prf (list (make-dk-not dkhyp1)))
			      (mk-dk-proof-term prem1 ante1 nenv1))
		    (make-lam dkhypprf2
			      (make-app dk-prf (list (make-dk-not dkhyp2)))
			      (mk-dk-proof-term prem2 ante2 nenv2))))))

(defmethod mk-dk-proof-term ((proof not-iff-rule) sequent env)
  (let* ((a (car (mk-dk-expr-term (car (params proof)))))
	 (b (car (mk-dk-expr-term (cadr (params proof)))))
	 (prem (car (premises proof)))
	 (ante (car (antecedents proof sequent)))
	 (dkhyp1 (car (mk-dk-expr-term (car (car (rule-hypotheses proof))))))
	 (dkhyp2 (car (mk-dk-expr-term (cadr (car (rule-hypotheses proof))))))
	 (dkconc (car (mk-dk-expr-term (car (rule-conclusions proof)))))
	 (dkhypprf1 (make-new-var))
	 (dkhypprf2 (make-new-var))
	 (dkconcprf (find-env (make-dk-not dkconc) env))
	 (nenv (cons (cons (make-dk-not dkhyp1) dkhypprf1)
		      (cons (cons (make-dk-not dkhyp2) dkhypprf2)
			    env))))
    (make-app (make-logic-var "RNotIFF")
    	      (list a b dkconcprf
		    (make-lam dkhypprf1
			      (make-app dk-prf (list (make-dk-not dkhyp1)))
			      (make-lam dkhypprf2
					(make-app dk-prf (list (make-dk-not dkhyp2)))
					(mk-dk-proof-term prem ante nenv)))))))

(defmethod mk-dk-proof-term ((proof if-rule) sequent env)
  (let* ((a (car (mk-dk-expr-term (car (params proof)))))
	 (b (car (mk-dk-expr-term (cadr (params proof)))))
	 (c (car (mk-dk-expr-term (caddr (params proof)))))
	 (prem1 (car (premises proof)))
	 (ante1 (car (antecedents proof sequent)))
	 (prem2 (cadr (premises proof)))
	 (ante2 (cadr (antecedents proof sequent)))
	 (dkhyp1 (car (mk-dk-expr-term (car (car (rule-hypotheses proof))))))
	 (dkhyp2 (car (mk-dk-expr-term (car (cadr (rule-hypotheses proof))))))
	 (dkconc (car (mk-dk-expr-term (car (rule-conclusions proof)))))
	 (dkhypprf1 (make-new-var))
	 (dkhypprf2 (make-new-var))
	 (dkconcprf (find-env (make-dk-not dkconc) env))
	 (nenv1 (cons (cons (make-dk-not dkhyp1)
			    dkhypprf1)
		      env))
	 (nenv2 (cons (cons (make-dk-not dkhyp2)
			    dkhypprf2)
		      env)))
    (make-app (make-logic-var "RIF")
    	      (list a b c dkconcprf
		    (make-lam dkhypprf1
			      (make-app dk-prf (list (make-dk-not dkhyp1)))
			      (mk-dk-proof-term prem1 ante1 nenv1))
		    (make-lam dkhypprf2
			      (make-app dk-prf (list (make-dk-not dkhyp2)))
			      (mk-dk-proof-term prem2 ante2 nenv2))))))

(defmethod mk-dk-proof-term ((proof not-if-rule) sequent env)
  (let* ((a (car (mk-dk-expr-term (car (params proof)))))
	 (b (car (mk-dk-expr-term (cadr (params proof)))))
	 (c (car (mk-dk-expr-term (caddr (params proof)))))
	 (prem1 (car (premises proof)))
	 (ante1 (car (antecedents proof sequent)))
	 (prem2 (cadr (premises proof)))
	 (ante2 (cadr (antecedents proof sequent)))
	 (dkhyp1 (car (mk-dk-expr-term (car (car (rule-hypotheses proof))))))
	 (dkhyp2 (car (mk-dk-expr-term (car (cadr (rule-hypotheses proof))))))
	 (dkconc (car (mk-dk-expr-term (car (rule-conclusions proof)))))
	 (dkhypprf1 (make-new-var))
	 (dkhypprf2 (make-new-var))
	 (dkconcprf (find-env (make-dk-not dkconc) env))
	 (nenv1 (cons (cons (make-dk-not dkhyp1)
			    dkhypprf1)
		      env))
	 (nenv2 (cons (cons (make-dk-not dkhyp2)
			    dkhypprf2)
		      env)))
    (make-app (make-logic-var "RNotIF")
    	      (list a b c dkconcprf
		    (make-lam dkhypprf1
			      (make-app dk-prf (list (make-dk-not dkhyp1)))
			      (mk-dk-proof-term prem1 ante1 nenv1))
		    (make-lam dkhypprf2
			      (make-app dk-prf (list (make-dk-not dkhyp2)))
			      (mk-dk-proof-term prem2 ante2 nenv2))))))


(defmethod mk-dk-proof-term ((proof refl-rule) sequent env)
  (declare (ignore sequent))
  (make-app (make-logic-var "RTrue")
	    (list
	     (find-env (make-dk-not (car (mk-dk-expr-term (car (rule-conclusions proof))))) env))))

(defmethod mk-dk-proof-term ((proof trusted-rule) sequent env)
  (assert (= (list-length (premises proof)) (list-length (cadr (params proof)))))
  (cond ((or (eq (car (params proof)) 'decision-procedure)
	     (eq (car (params proof)) 'truefalsecond))
	 (assert (null (premises proof)))
	 (let* ((concs (mapcar #'formula (append (s-forms sequent) (hidden-s-forms sequent) nil)))
	 	(dkconcs (mapcar #'(lambda (conc) (car (mk-dk-expr-term conc)))
	 			 concs))
	 	(disjconcs (reduce #'compute-disjunction concs))
	 	(dkdisjconcs (reduce #'make-dk-or dkconcs))
	 	(hconcs (mapcar #'(lambda(dkconc)
	 			    (find-env (make-dk-not dkconc) env))
	 			dkconcs)))
	   (make-app
	    (make-logic-var "RNotImplication3")
	    (list dkdisjconcs;; (car (mk-dk-expr-term conc))
	 	  (produce-hole proof
	 			disjconcs
	 			dkdisjconcs)
	 	  (elim-not-disj dkdisjconcs (reverse hconcs))))))
	((and (null (premises proof))
	      (null (cdr (caddr (params proof)))))
	 ;; (show (car (caddr (params proof))))
	 ;; (tc-eq (compute-normalize conc) *true*))
	 (let* ((conc (car (rule-conclusions proof)))
		(dkconcprf (find-env (make-dk-not (car (mk-dk-expr-term conc))) env)))
	   (cond ((compute-form-eq conc (compute-equation *false* *false*))
		  (make-app (make-logic-var "RTrue") (list dkconcprf)))
		 ((eq (car (params proof)) 'nat_induction)
		  (make-app (make-logic-var "RNatInduction")
			    (list dkconcprf)))
		 (t
		  (if (tc-eq (compute-normalize conc) *true*)
		      (make-app (make-logic-var "RTrue") (list dkconcprf))
		    (call-next-method))))))
	((and (= (list-length (premises proof)) 1)
	      (= (list-length (car (cadr (params proof)))) 1)
	      (= (list-length (rule-conclusions proof)) 1)
	      (null (cdr (caddr (params proof)))))
	 (let* ((hyp (car (car (cadr (params proof)))))
		(dkhyp (car (mk-dk-expr-term hyp)))
		(conc (car (rule-conclusions proof)))
		(dkconc (car (mk-dk-expr-term conc)))
		(dkconcprf (find-env (make-dk-not dkconc) env))
		(prem (car (premises proof)))
		(ante (car (antecedents proof sequent)))
		(nenv
		 (cons (cons (make-dk-not dkhyp) dkconcprf)
		       (remove-env (make-dk-not dkconc) env))))
	   (if (tc-eq (compute-normalize hyp) (compute-normalize conc))
	       (mk-dk-proof-term prem ante nenv)
	       (call-next-method))))
	(t
	 (call-next-method))))

(defun elim-conj (conjhyps revphyps)
  (cond ((null (cdr revphyps)) 
	 (car revphyps))
	(t
	 (let ((hnconj (make-new-var))
	       (hhyp1 (car (make-dk-args conjhyps)));; conjunction
	       (hhyp2 (cadr (make-dk-args conjhyps))))
	   (make-lam hnconj
		     (make-dk-prf (make-dk-not conjhyps))
		     (make-app (make-logic-var "RAnd")
			       (list hhyp1
				     hhyp2
				     hnconj
				     (elim-conj hhyp1 (cdr revphyps))
				     (car revphyps))))))))

(defun elim-disj (disjhyps phyp revhhyps)
  (cond ((null (cdr revhhyps))
				       ;; (reduce #'(lambda (current hhyp-hnhyp)
				       ;; 	       (make-lam (cdr hhyp-hnhyp)
				       ;; 			 (make-dk-prf
				       ;; 			  (make-dk-not
				       ;; 			   (car hhyp-hnhyp)))
				       ;; 			 current))
				       ;; 	   (cons (mk-dk-proof-term prem nenv)
				       ;; 		 (mapcar #'cons hhyps hnhyps))))
	 (make-lam (car revhhyps)
		   (make-dk-prf (make-dk-not disjhyps))
		   phyp))
	(t
	 (let ((hndisj (make-new-var))
	       (hhyp1 (car (make-dk-args disjhyps)));; disjunction
	       (hhyp2 (cadr (make-dk-args disjhyps))))
	   (make-lam hndisj
		     (make-dk-prf (make-dk-not disjhyps))
		     (make-app (make-logic-var "ROr2")
			       (list hhyp1
				     hhyp2
				     hndisj
				     (make-lam
				      (car revhhyps)
				      (make-dk-prf (make-dk-not hhyp2))
				      (elim-disj hhyp1 phyp (cdr revhhyps))))))))))

(defun elim-conj2 (conjhyps revphyps revhhyps)
  (cond ((null (cdr revphyps))
	 (elim-disj conjhyps (car revphyps) (car revhhyps)))
	(t
	 (let ((hnconj (make-new-var))
	       (hhyp1 (car (make-dk-args conjhyps)));; conjunction
	       (hhyp2 (cadr (make-dk-args conjhyps))));; disjunction
	   (make-lam hnconj
		     (make-dk-prf (make-dk-not conjhyps))
		     (make-app (make-logic-var "RAnd")
			       (list hhyp1
				     hhyp2
				     hnconj
				     (elim-conj2 hhyp1 (cdr revphyps) (cdr revhhyps))
				     (elim-disj hhyp2 (car revphyps) (car revhhyps)))))))))


(defun elim-not-disj (disjconcs hconcs)
  (cond ((null (cdr hconcs))
	 (car hconcs))
	(t
	 (let ((hhyp1 (car (make-dk-args disjconcs)));; disjunction
	       (hhyp2 (cadr (make-dk-args disjconcs))))
	   (make-app (make-logic-var "RNotOr2")
		     (list hhyp1
			   hhyp2
			   (elim-not-disj hhyp1 (cdr hconcs))
			   (car hconcs)))))))

(defmethod mk-dk-proof-term ((proof proof) sequent env)
  ;; (show proof)
  (let ((hyps (rule-hypotheses proof))
	(concs (rule-conclusions proof)))
    (if (equal (list-length concs) 1)
	(let* ((conc (car concs))
	       (hconc (find-env (make-dk-not (car (mk-dk-expr-term conc))) env)))
	  (cond ((and (>= (list-length hyps) 1)
		      (every #'(lambda (hyp) (>= (list-length hyp) 1)) hyps))
		 (let* ((hhyps (mapcar #'(lambda (hyps)
					   (mapcar #'(lambda (hyp)
						       (car (mk-dk-expr-term hyp)))
						   hyps))
				       hyps))
			(hnhyps (mapcar #'(lambda (hhyps)
					    (mapcar #'(lambda (hyp )
							(declare (ignore hyp))
							(make-new-var))
						    hhyps))
					hhyps))
			(pvsconjhyps (reduce #'compute-conjunction
					     (mapcar #'(lambda (hyps)
							 (reduce #'compute-disjunction hyps))
						     hyps)))
			(conjhyps (reduce #'make-dk-and
					  (mapcar #'(lambda (hhyps)
						      (reduce #'make-dk-or hhyps))
						  hhyps)));; (and (and (and () ()) ()) ())
			(prems (premises proof))
			(antes (antecedents proof sequent))
			(nenvs (mapcar #'(lambda (hhyps hnhyps)
					   (append (mapcar #'(lambda (hhyp hnhyp)
							       (cons (make-dk-not hhyp) hnhyp))
							   hhyps
							   hnhyps)
						   env))
				       hhyps hnhyps))
			(phyps (mapcar #'mk-dk-proof-term prems antes nenvs)))
		   (make-app
		    (make-logic-var "RNotImplication2")
		    (list ;; (progn (when (and (null (cdr hhyps))
			  ;; 		    (null (cdr (car hhyps))))
			  ;; 	   (show (operator (car (car hyps))))
			  ;; 	   (print-dk-term t (car (car hhyps))))
		     conjhyps;;)
			  (car (mk-dk-expr-term conc))
			  (produce-hole proof
					(compute-implication pvsconjhyps
							     conc)
					(make-dk-implies conjhyps
							 (car (mk-dk-expr-term conc))))
			  hconc
			  (elim-conj2 conjhyps
				      (reverse phyps)
				      (reverse (mapcar #'reverse hnhyps)))))))
		((null hyps)
		 (make-app (make-instance 'dk-logic-var :id "RAxiom")
			   (list (car (mk-dk-expr-term conc))
				 hconc
				 (produce-hole proof
					       (compute-negation
						(compute-negation
						 conc))
					       (make-dk-not
						(make-dk-not
						 (car (mk-dk-expr-term conc)))))
				 )))
		(t
		 (assert (and 'dedukti nil))
		 )))
      (cond ((and (>= (list-length concs) 1)
		  (>= (list-length hyps) 1)
		  (every #'(lambda (hyp) (>= (list-length hyp) 1)) hyps))
	     (let* ((dkconcs (mapcar #'(lambda (conc) (car (mk-dk-expr-term conc)))
				     concs))
		    (disjconcs (reduce #'compute-disjunction concs))
		    (dkdisjconcs (reduce #'make-dk-or dkconcs))
		    ;; (dummy (mapcar #'(lambda(dkconc)
		    ;; 		       (print-dk-term t (make-dk-not dkconc))
		    ;; 		       (find-env (make-dk-not dkconc) env))
		    ;; 		    dkconcs))
		    ;; (dummy (format t "~%test1"))
		    (hconcs (mapcar #'(lambda(dkconc)
		    			(find-env (make-dk-not dkconc) env))
		    		    dkconcs))
		    (hhyps (mapcar #'(lambda (hyps)
				       (mapcar #'(lambda (hyp)
						   (car (mk-dk-expr-term hyp)))
					       hyps))
				   hyps))
		    (hnhyps (mapcar #'(lambda (hhyps)
					(mapcar #'(lambda (hyp )
						    (declare (ignore hyp))
						    (make-new-var))
						hhyps))
				    hhyps))
		    (pvsconjhyps (reduce #'compute-conjunction
					 (mapcar #'(lambda (hyps)
						     (reduce #'compute-disjunction hyps))
						 hyps)))
		    (dkconjhyps (reduce #'make-dk-and
				      (mapcar #'(lambda (hhyps)
						  (reduce #'make-dk-or hhyps))
					      hhyps)));; (and (and (and () ()) ()) ())
		    (prems (premises proof))
		    (antes (antecedents proof sequent))
		    (nenvs (mapcar #'(lambda (hhyps hnhyps)
				       (append (mapcar #'(lambda (hhyp hnhyp)
							   (cons (make-dk-not hhyp) hnhyp))
						       hhyps
						       hnhyps)
					       env))
				   hhyps hnhyps))
		    (phyps (mapcar #'mk-dk-proof-term prems antes nenvs)))
	       (make-app
		(make-logic-var "RNotImplication2")
		(list dkconjhyps
		      dkdisjconcs;; (car (mk-dk-expr-term conc))
		      (produce-hole proof
				    (compute-implication pvsconjhyps
							 disjconcs)
				    (make-dk-implies dkconjhyps
						     dkdisjconcs))
		      (elim-not-disj dkdisjconcs (reverse hconcs));;hconc
		      (elim-conj2 dkconjhyps
				  (reverse phyps)
				  (reverse (mapcar #'reverse hnhyps)))))))
	    ((and (= (list-length concs) 0)
		  (>= (list-length hyps) 1)
		  (every #'(lambda (hyp) (>= (list-length hyp) 1)) hyps))
	     (let* ((hhyps (mapcar #'(lambda (hyps)
	     			       (mapcar #'(lambda (hyp)
	     					   (car (mk-dk-expr-term hyp)))
	     				       hyps))
	     			   hyps))
	     	    (hnhyps (mapcar #'(lambda (hhyps)
	     				(mapcar #'(lambda (hyp )
	     					    (declare (ignore hyp))
	     					    (make-new-var))
	     					hhyps))
	     			    hhyps))
	     	    (pvsconjhyps (reduce #'compute-conjunction
	     				 (mapcar #'(lambda (hyps)
	     					     (reduce #'compute-disjunction hyps))
	     					 hyps)))
	     	    (dkconjhyps (reduce #'make-dk-and
	     			      (mapcar #'(lambda (hhyps)
	     					  (reduce #'make-dk-or hhyps))
	     				      hhyps)));; (and (and (and () ()) ()) ())
	     	    (prems (premises proof))
		    (antes (antecedents proof sequent))
	     	    (nenvs (mapcar #'(lambda (hhyps hnhyps)
	     			       (append (mapcar #'(lambda (hhyp hnhyp)
	     						   (cons (make-dk-not hhyp) hnhyp))
	     					       hhyps
	     					       hnhyps)
	     				       env))
	     			   hhyps hnhyps))
	     	    (phyps (mapcar #'mk-dk-proof-term prems antes nenvs)))
	       (make-app
	     	(make-logic-var "RNotImplication2")
	     	(list dkconjhyps
	     	      ;; dkdisjconcs
		      (car (mk-dk-expr-term *false*))
	     	      (produce-hole proof
	     			    (compute-implication pvsconjhyps
	     						 *false*)
	     			    (make-dk-implies dkconjhyps
	     					     (car (mk-dk-expr-term *false*))))
	     	      (make-logic-var "RNotFalse2");; (elim-not-disj dkdisjconcs (reverse hconcs))
		      ;;hconc
	     	      (elim-conj2 dkconjhyps
	     			  (reverse phyps)
	     			  (reverse (mapcar #'reverse hnhyps))))))
	     )
	    ((and (>= (list-length concs) 1)
		  (= (list-length hyps) 0))
	     (let* ((dkconcs (mapcar #'(lambda (conc) (car (mk-dk-expr-term conc)))
				     concs))
		    (disjconcs (reduce #'compute-disjunction concs))
		    (dkdisjconcs (reduce #'make-dk-or dkconcs))
		    (hconcs (mapcar #'(lambda(dkconc)
					(find-env (make-dk-not dkconc) env))
				    dkconcs)))
	       (make-app
		(make-logic-var "RNotImplication3")
		(list dkdisjconcs;; (car (mk-dk-expr-term conc))
		      (produce-hole proof
				    disjconcs
				    dkdisjconcs)
		      (elim-not-disj dkdisjconcs (reverse hconcs))))))
	    (t ;; (list-length concs) > 1
	     (show (list-length concs))
	     (show (list-length hyps))
	     (show (mapcar #'(lambda (hyp) (list-length hyp)) hyps))
	     (assert (and 'mk-dk-expr-term2 nil))
	     )))))

(defmethod mk-dk-proof-term ((proof tcc-rule) sequent env)
  ;; (show proof)
  (let* ((hhyps (mapcar #'(lambda (hyps)
			    (mapcar #'(lambda (hyp)
					(car (mk-dk-expr-term hyp)))
				    hyps))
			(cdr (rule-hypotheses proof))))
	 (hnhyps (mapcar #'(lambda (hhyps)
			     (mapcar #'(lambda (hyp )
					 (declare (ignore hyp))
					 (make-new-var))
				     hhyps))
			 hhyps))
	 (prems (cdr (premises proof)))
	 (antes (cdr (antecedents proof sequent)))
	 (nenvs (mapcar #'(lambda (hhyps hnhyps)
			    (append (mapcar #'(lambda (hhyp hnhyp)
						(cons (make-dk-not hhyp) hnhyp))
					    hhyps
					    hnhyps)
				    env))
			hhyps hnhyps))
	 (nbinds (mapcar #'(lambda (hhyps hnhyps)
			     (mapcar #'(lambda (hhyp hnhyp)
					 (cons (make-dk-not hhyp) hnhyp))
				     hhyps
				     hnhyps))
			hhyps hnhyps))
	 (arrow-prems
	  (mapcar
	   #'(lambda (prem ante nenv nbinds)
	       (reduce
		#'(lambda (current nbind)
		    (cons (make-dk-implies (car nbind) (car current))
			  (make-app
			   (make-logic-var "Rimplication3")
			   (list (car nbind)
				 (car current)
				 (make-lam
				  (cdr nbind)
				  (make-dk-prf (car nbind))
				  (cdr current))))))
		(cons (cons (make-dk-false)
			    (mk-dk-proof-term prem ante nenv))
		      nbinds)))
	   prems antes nenvs nbinds)))
    (reduce
     #'(lambda (proof arrow-prem)
	 (make-app
	  (make-logic-var "RTcc")
	  (list proof
		(car arrow-prem)
		(cdr arrow-prem))))
     (cons (mk-dk-proof-term (car (premises proof)) sequent env)
	   arrow-prems))))

(defun produce-hole (proof pvshyp dkhyp)
  (let ((source (or (and (eq (name proof) 'trusted-rule)
			 (car (params proof))))))
    (when (null source) (show proof) (assert (and 'nullsource nil)))
    (assert (dk-eq (car (mk-dk-expr-term pvshyp)) dkhyp))
    ;; (when (= *tptp-count* 2)
    ;;   (show pvshyp)
    (when *tptp*
      (format *tptp-stream* "%~a~a~%" *tptp-count* source)
      (format *tptp-stream* "~a~%" (translate-to-tptp pvshyp source)))
    (setq *tptp-count* (+ *tptp-count* 1))
    (make-app (make-logic-var "RHole")
	      (list dkhyp))))

(defmethod mk-dk-rule ((proof hole-rule))
  "RCheck")
(defmethod mk-dk-rule ((proof true-rule))
  "RTrue")
(defmethod mk-dk-rule ((proof not-false-rule))
  "RNotFalse")
(defmethod mk-dk-rule ((proof not-not-rule))
  "RNotNot")
(defmethod mk-dk-rule ((proof and-rule))
  "RAnd")
(defmethod mk-dk-rule ((proof weak-rule))
  "RWeak")
(defmethod mk-dk-rule ((proof axiom-rule))
  "RAxiom")
(defmethod mk-dk-rule ((proof implication-rule))
  "Rimply")
(defmethod mk-dk-rule ((proof or-rule))
  "ROr")
(defmethod mk-dk-rule ((proof not-and-rule))
  "RNotAnd")
(defmethod mk-dk-rule ((proof not-or-rule))
  "RNotOr")
(defmethod mk-dk-rule ((proof contr-rule))
  "RContr")
(defmethod mk-dk-rule ((proof not-forall-rule))
  "RNotForall")
(defmethod mk-dk-rule ((proof not-implication-rule))
  "RNotImplication")
(defmethod mk-dk-rule ((proof not-exists-rule))
  "RNotExists")
(defmethod mk-dk-rule ((proof false-rule))
  "RFalse")
(defmethod mk-dk-rule ((proof not-true-rule))
  "RNotTrue")
(defmethod mk-dk-rule ((proof exists-rule))
  "RExists")
(defmethod mk-dk-rule ((proof forall-rule))
  "RForall")
(defmethod mk-dk-rule ((proof cut-rule))
  "RCut")
(defmethod mk-dk-rule ((proof refl-rule))
  "RRefl")

;; DECLARATIONS AND DEFINITIONS

;; no need to declare variables, they don't appear free
(defmethod mk-dk-context-line ((d var-decl))
  nil)

;; no need to declare variables, they don't appear free
(defmethod mk-dk-context-line ((d auto-rewrite-plus-decl))
  nil)

;; to be done later
(defmethod mk-dk-context-line ((d formal-const-decl))
  (make-instance 'dk-decl :id (id d) :type dk-type-type))

;; to be done later
(defmethod mk-dk-context-line ((d importing))
  nil)

(defmethod mk-dk-context-line ((d type-decl))
  nil;; (make-instance 'dk-decl :id (id d) :type dk-type-type)
  )

(defmethod mk-dk-context-line ((d const-decl))
  (if (definition d)
      (if (equal (list-length (def-axiom d)) 1)
	  (progn (make-instance 'dk-def :id (id d) :type dk-type-type
				:body (car (mk-dk-expr-term (cadr (arguments (car (def-axiom d))))))))
	(progn ;; (when (equal (id d) 'maximum?)
	       ;; 	   (show (cadr (arguments (cadr (def-axiom d)))))
	       ;; 	   (assert nil))
	       (assert (equal (list-length (def-axiom d)) 2))
	       (make-instance 'dk-def :id (id d) :type dk-type-type
			      :body (car (mk-dk-expr-term (cadr (arguments (cadr (def-axiom d)))))))))
    (make-instance 'dk-decl :id (id d) :type dk-type-type)))

(defmethod mk-dk-context-line ((d formula-decl))
  (make-instance 
   'dk-def :id (id d) :type dk-type-type :body (car (mk-dk-expr-term (closed-definition d)))))

(defmethod mk-dk-proof-line ((d formula-decl) (p proof))
  ;; (let ((var (make-new-var)))
  ;;   (make-instance 
  ;;    'dk-decl
  ;;    :id (id (default-proof d))
  ;;    :type
  ;;    (make-app dk-prf (list (make-instance 'dk-var :id (id d))))))

  (let ((var (make-new-var)))
    ;; (make-app dk-prf (list (make-dk-not (make-var (id d)))))
    ;; (show p)
    (make-instance 
     'dk-def
     :id (id (default-proof d))
     :type
     (make-app dk-prf (list (make-instance 'dk-var :id (id d))))
     :body
     (make-app
      (make-logic-var 'RHead)
      (list (make-var (id d))
    	    (make-lam var
		      (make-app dk-prf (list (make-dk-not (make-var (id d)))))
		      (mk-dk-proof-term
		       p
		       (compute-sequent (list (compute-s-form (closed-definition d)))
					nil)
		       (list
			(cons (make-dk-not (car (mk-dk-expr-term (closed-definition d))))
			      var)))))))))

