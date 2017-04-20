;;FG inspired from defcl.lisp

(defvar *new-slot-info* nil)

(defmacro newdefcl (name classes &rest args)
  (setf args (mapcar #'(lambda (a) (if (consp a) a (list a))) args))
  `(progn ,@(mapcar #'(lambda (a)
			#+(or allegro sbcl)
				  `(declaim (ftype (function
						    (t)
						    ,(cadr (member :type a)))
						   ,(car a)))
			#-(or allegro sbcl)
				  `(proclaim '(function ,(car a) (t)
					       ,(cadr (member :type a)))))
		    (remove-if-not #'(lambda (a) (member :type a))
		      args))
    (defclass ,name ,classes
      ,(mapcar #'(lambda (a)
		   (setq a (remove-keyword
			    :parse
			    (remove-keyword
			     :ignore
			     (remove-keyword
			      :store-as
			      (remove-keyword
			       :restore-as
			       (remove-keyword
				:fetch-as a))))))
		   (append a (list :accessor (car a)
				   :initarg (intern (string (car a))
						    'keyword)
				   :initarg (car a))
			   (unless (memq :initform a)
			     (list :initform nil))))
	       args))
    (declare-make-instance ,name)
    (proclaim '(inline ,(intern (format nil "~a?" name))))
    (defun ,(intern (format nil "~a?" name)) (obj)
      (typep obj ',name))
    (eval-when (:execute :compile-toplevel :load-toplevel)
      (setq *slot-info*
	    (cons (cons ',name
			'(,classes ,args))
		   (delete (assoc ',name *slot-info*)
			   *slot-info*))))
    (eval-when (:execute :compile-toplevel :load-toplevel)
      (setq *new-slot-info*
	    (cons (cons ',name
			'(,classes ,args))
		   (delete (assoc ',name *new-slot-info*)
			   *new-slot-info*))))
;;     (defmethod untc*
;; 	,@(when classes (list :around))
;; 	((obj ,name))
;; 	,@(when classes (list '(call-next-method)))
;; 	,@(mapcar #'(lambda (a)
;; 		      (let ((slot (car a)))
;; 			(if (cadr (memq :parse a))
;; 			    `(untc* (slot-value obj ',slot))
;; 			    `(setf (slot-value obj ',slot)
;; 			      ,(cadr (memq :initform a))))))
;; 		  args))
    ',name))

(defun write-new-deferred-methods-to-file ()
  (let ((mfile (format nil "~a/new-pvs-methods.lisp" *pvs-with-proofs-path*)))
    (with-open-file (out mfile :direction :output :if-exists :supersede)
		    (let ((*print-case* :downcase))
		      (write '(in-package :pvs) :stream out)
		      (dolist (si *new-slot-info*)
			(write-deferred-methods (car si) out))))))
