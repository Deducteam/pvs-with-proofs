;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; -*- Mode: Lisp -*- ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; equantifiers.lisp -- Quantifier rules
;; Author          : Natarajan Shankar
;; Created On      : Fri Oct  8 12:57:34 1993
;; Last Modified By: Sam Owre
;; Last Modified On: Thu May 20 21:17:17 2004
;; Update Count    : 35
;; Status          : Stable
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; --------------------------------------------------------------------
;; PVS
;; Copyright (C) 2006, SRI International.  All Rights Reserved.

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License
;; as published by the Free Software Foundation; either version 2
;; of the License, or (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; if not, write to the Free Software
;; Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
;; --------------------------------------------------------------------

(in-package :pvs)

;;resolution for name is not copied in classes.lisp
(defun copy-name-expr (name-expr new-id)
  (lcopy name-expr
    'id new-id
    'resolutions (resolutions name-expr)))
						   
(defun declared-type-module-instance (mi)
  (let ((nacts (mapcar #'(lambda (act)
			   (if (type-value act)
			       (if (name-expr? (expr act))
				   (copy act
				     'type-value
				     (mk-type-name (expr act)))
				   (copy act
				     'type-value
				     (expr act)))
			       act))
		 (actuals mi))))
    (if (equal nacts (actuals mi))
	mi
	(copy mi 'actuals nacts))))

(defun gen-symbol (name  char counter)    
  (let* ((string (string  (op-to-id  name)))
	 (pos (position-if #'(lambda (x)(member x (list char #\! #\_)))
			   string :from-end t));;NSH(4-11-94) $ to _.
	 ;;(1/21/91) Changed
	 (prefix (subseq string 0 pos))
	 (suffix (when pos (subseq string (1+ pos))))
	 (prestring (if (and pos (every #'digit-char-p suffix))
			prefix
			string)))
    (format nil "~a~a~a" prestring char (funcall counter))))

(defun symbol-index (name)
  (let* ((name  (intern  (string  (op-to-id  name))))
	 (string (format nil "~a" name))
	 (pos (position-if #'(lambda (x)(member x (list  #\! #\$))) string))
         (index (when pos (parse-integer string :start (1+ pos)
					 :junk-allowed t))))
    index))

(defun symbol-prefix (id)
  (let* ((string (string (op-to-id id)))
	 (pos (position #\_ string :from-end t))
	 (prefix (if pos (subseq string 0 pos)
		     string))
	 (index (when pos  ;;NSH(9.20.95)
		  (parse-integer string :start (1+ pos) :junk-allowed t))))
    (if index (intern prefix) id)))
	

(defun pvs-gentemp (string &optional (count 0))
  (let ((next (format nil "~a~a" string count)))
    (if (find-symbol next)
	(pvs-gentemp string (1+ count))
	(intern next))))

(defun new-boundvar-id (id expr)
  (let* ((string (string (op-to-id id)))
	 (pos (position #\_ string :from-end t))
	 (prefix (if pos (subseq string 0 pos)
		     string))
	 (suffix (if pos (subseq string (1+ pos) ) "")))
    (if (every #'digit-char-p suffix)
	(new-boundvar-id* prefix expr 1)
	(new-boundvar-id* string expr 1))))

(defun new-boundvar-id* (idstr expr num)
  (let ((id (makesym "~a_~d" idstr num)))
    (if (id-occurs-in id expr)
	(new-boundvar-id* idstr expr (1+ num))
	id)))
         

(defun new-symbol (name counter)
  (intern (gen-symbol name #\$ counter)))

(defun new-sko-symbol (name context &optional counter symbols &key keep-underscore?)
  (unless counter (newcounter *skofun-counter*))
  (let* ((symb (if keep-underscore?
		   (concatenate 'string
		     (string name)
		     "!"
		     (princ-to-string (funcall *skofun-counter*)))
		   (gen-symbol name #\! *skofun-counter*)))
	 (isymb (intern symb)))
    (if (or (declared? isymb context)
	    (member symb symbols :test #'same-id))
	(new-sko-symbol name context *skofun-counter* symbols
			:keep-underscore? keep-underscore?)
	symb)))

(defun new-sko-symbol-list (names context &optional counter symbols
				  &key keep-underscore?) 
  (cond ((null names) (nreverse symbols))
	(t (let ((symb1 (new-sko-symbol (car names)
					context counter symbols
					:keep-underscore? keep-underscore?)))
	     (new-sko-symbol-list (cdr names) context counter
				  (cons symb1 symbols)
				  :keep-underscore?
				  keep-underscore?)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defun make-skofun (boundvar governing-vars context)
  (let* ((id (new-symbol (format nil "~a~a"  "#" (id boundvar))
			 *skofun-counter*))
	 (type (if (null governing-vars)
		   (type boundvar)
		 (make-instance 'funtype
		   :domain (loop for x in governing-vars
				 collect (type x))
		   :range (type boundvar))))
	 (const-decl (make-instance 'const-decl
		       :id id
		       :module (module context)
		       :type type)))
    (add-decl const-decl  context)
    (typecheck (pc-parse id 'expr)
	       :expected type
	       :context context)))

;  (make-instance 'name-expr
;    :type (cond ((null governing-vars)
;		 (type boundvar))
;		(t (make-instance 'funtype
;		     'domain (loop for x in governing-vars collect (type x))
;		     'range (type boundvar))))
;    :name (make-instance 'name
;	    :id (new-symbol (format nil "~a~a"  "#" (id (name boundvar)))
;			    *skofun-counter*))))
;;(NSH4-19: make-skoterm and make-skofun not used any more.
;(defun make-skoterm (skofun governing-vars context)
;  (if (null governing-vars) skofun
;    (let ((skoterm (make-instance 'application
;				  :operator skofun
;				  :arguments governing-vars)))
;      (typecheck skoterm
;		 :expected (range (type skofun))
;		 :context context)
;      skoterm)))

;(defun make-skovar (boundvar context)
;  (let* ((id (new-symbol (format nil "~a~a"  "?" (id boundvar))
;			 *skovar-counter*))
;	 (var-decl (make-instance 'var-decl
;				  :id id
;				  :module (module context)
;				  :type (type boundvar))))
;    (add-decl var-decl context)
;    (typecheck (pc-parse id 'expr) :context context)))
				  
;  (make-instance 'name-expr
;    :type (type boundvar)
;    :name (make-instance 'name
;	    :id (new-symbol (format nil "~a~a"  "?" (id (name boundvar)))
;			    *skovar-counter*))))

(defun declared? (id context)
  (some #'(lambda (d)
	     (and (not (var-decl? d))
		  (eq (module d) (current-theory))))
	(get-declarations id (declarations-hash context))))

(defun one-to-one (alist)
  (if (consp alist)
      (if (consp (car alist))
	  (and (null (assoc (caar alist) (cdr alist)))
	       (not (member (cdar alist)(cdr alist)
			    :test #'(lambda (x y)(if (consp y)
						     (equal x (cdr y))
						     nil))))
	       (one-to-one (cdr alist)))
	  (one-to-one (cdr alist)))
      t))

(defun makeskoconst (id type context)
  (setf (declarations-hash context) (copy (declarations-hash context)))
  (let ((ctype (lcopy type 'from-conversion nil)))
    (put-decl (make-instance 'skolem-const-decl
		:id (id id)
		:type ctype
		:module (theory context))
	      (declarations-hash context))
    (typecheck id
      :expected ctype
      :context context)))

(defmethod quantifier-step ((expr quant-expr)  context sign terms ps)
  (declare (ignore ps))
  (let* ((preterms (if (listp terms) terms (list terms)))
	 (terms (loop for x in preterms
		      collect (pc-parse x 'expr)))
	 (boundvars (bindings expr))
	 (sub-boundvars (loop for x in boundvars
			      as y in terms
			      when (not (and (typep y 'name-expr)
					     (eq (id y) '_)))
			      collect x))
	 (id-boundvars  (loop for x in boundvars ;; will not be substituted
			      as y in terms
			      when (and (typep y 'name-expr)
					(eq (id y) '_))
			      collect x))
	 (sub-freevars (loop for x in sub-boundvars
			     append (freevars x)))
	 (overlap (intersection sub-freevars id-boundvars
				:test #'same-declaration))
	 (subterms (loop for y in terms
			 when (not (and (typep y 'name-expr)
					 (eq (id y) '_)))
			 collect y))
	 (make-quant-result (unless overlap
			      (make-quant-alist sub-boundvars subterms)))
	 (qalist (unless overlap 
		   (car make-quant-result)))
	 (freevars (unless (stringp qalist) ;; Error message
		     (loop for (nil . y) in qalist
			   append (freevars y)))));;(break "quantifier-step")
    (cond ((stringp qalist)
	   (format-if qalist)
	   (cons expr
		 (make-trace 'not-implemented 'p151)))
	  (freevars
	   (error-format-if "~%The supplied terms should not contain free variables.
The following irrelevant free variables occur in the terms: ~a"
		      freevars)
	   (cons expr
		 (make-trace 'not-implemented 'p152)))
	  (overlap
	   (error-format-if
	    "~%The types of the substituted variables contain free occurrences
of the following quantified variables: ~a.
Please provide substitutions for these variables." overlap)
	   (cons expr
		 (make-trace 'not-implemented 'p153))) 
	  (t (let* ((newexpr
		     (if id-boundvars
			 (if (eql (length id-boundvars)
				  (length boundvars))
			     expr
			     (lcopy expr
			       'bindings id-boundvars))
		       (expression expr)))
		    (ctx (if sign
			     (make-ctx 'expr-hole *boolean*)
			   (make-ctx 'negation (list (make-ctx 'expr-hole *boolean*)))))
		    (result (substit-with-proofs newexpr qalist ctx))
		    (proved-qbody
		     (if (eq newexpr expr)
			 (cons expr
			       (make-trace 'not-implemented 'p154))
		       (cons (car result)
			     (if (cdr make-quant-result) ;; simplification in make-skolem-alist
				 (make-trace 'not-implemented 'p155)
			       (if (not (eq (length subterms) (length terms)));; '_ is used
				   (if (every #'eq subterms terms)
				       ;; '_ is only at the end, to be merged with case below
				       (if sign
					   (make-trace 'not-implemented 'p27)
					 (make-trace 'rewrite-rule
						     (list ctx
							   (compute-forall
							    sub-boundvars
							    (compute-forall
							     id-boundvars
							     (expression expr)))
							   expr)
						     (list (make-trace 'not-forall-rule
								       (list newexpr qalist)
								       (list (cdr result))))))
				     (if sign
					 (make-trace 'not-implemented 'p33)
				       (let* ((quant-id
					       (compute-forall id-boundvars (expression expr)))
					      (quant-sub-id
					       (compute-forall sub-boundvars quant-id))
					      (quant-subid
					       (compute-forall (append sub-boundvars id-boundvars nil)
							       (expression expr)))
					      (make-skolem-result*
					       (make-skolem-alist*
					      	boundvars
					      	(mapcar
					      	 #'(lambda (var)
					      	     (declare (ignore var))
					      	     'pvs_with_proofs_id)
					      	 boundvars)
					      	context))
					      (sortedalist
					       (sort-skolem-alist
						(car make-skolem-result*)
						id-boundvars))
					      (newexpr* (compute-substit
							 (expression expr)
							 (car make-skolem-result*))))
					 (if (cdr make-skolem-result*)
					     (make-trace 'not-implemented 'p63)
					   (make-trace
					    'cut-rule
					    (list quant-sub-id)
					    (list
					     (make-trace
						   'rewrite-rule
						   (list (make-ctx 'expr-hole *boolean*)
							 quant-subid quant-sub-id)
						   (list (make-trace
							  'forall-rule
							  (list (expression expr) sortedalist)
							  (list (make-trace
								 'not-forall-rule
								 (list (expression expr)
								       (car make-skolem-result*))
								 (list (make-trace
									'axiom-rule
									(list newexpr*))))))))
						  (make-trace
						   'weak-rule
						   (list (compute-negation expr))
						   (list (make-trace
							  'not-forall-rule
							  (list newexpr qalist)
							  (list (cdr result)))))))))))
				 (if (or (not (eq (length boundvars) 1)) ;; > 1 binding per quantifier
					 (not (eq (length terms) 1))) ;; > 1 instant. per quantifier 
				     (if sign
					 (make-trace 'exists-rule
						   (list newexpr qalist)
						   (list (cdr result)))
				       (make-trace 'not-forall-rule
						   (list newexpr qalist)
						   (list (cdr result))))
				   (if sign;; to be merged with case above
				       (make-trace 'exists-rule
						   (list newexpr (list (car qalist)))
						   (list (cdr result)))
				     (make-trace 'not-forall-rule
						 (list newexpr (list (car qalist)))
						 (list (cdr result))))))))))
		    (qbody (car proved-qbody)))
	       (unless (exequal qbody expr)
		 (push-references-list qalist *dependent-decls*))
	       proved-qbody)))))


(defun make-quant-alist (boundvars terms &optional alist simplified)
  (if (null boundvars)
      (cons (nreverse alist) simplified)
      (multiple-value-bind (newterm error)
	  ;; Make sure we catch any type-errors
	  (with-no-type-errors
	   (internal-pc-typecheck (car terms)
	     :tccs 'all
	     :expected (substit (type (car boundvars)) alist)))
	(if newterm
	    (make-quant-alist (cdr boundvars)
			      (cdr terms)
			      (acons (car boundvars) newterm alist)
			      (or simplified
				  (not (tc-eq (compute-substit (type (car boundvars)) alist)
					      (substit (type (car boundvars)) alist)))))
	    (cons error (or simplified
				  (not (tc-eq (compute-substit (type (car boundvars)) alist)
					      (substit (type (car boundvars)) alist)))))))))

(defmethod skolemize-step ((expr quant-expr)  context sign terms)
  (let* ((preterms (if (listp terms) terms (list terms)))
	 (terms (loop for x in preterms
		      collect (pc-parse x 'expr)))
	 (boundvars (bindings expr))
	 (sub-boundvars (loop for x in boundvars
			      as y in terms
			      when (not (and (typep y 'name-expr)
					     (eq (id y) '_)))
			      collect x))
	 (id-boundvars  (loop for x in boundvars
			      as y in terms
			      when (and (typep y 'name-expr)
					(eq (id y) '_))
			      collect x))
	 (sub-freevars (loop for x in sub-boundvars
			     append (freevars x)))
	 (overlap (intersection sub-freevars id-boundvars
				:test #'same-declaration))
	 (subterms (loop for y in terms
			 when (not (and (typep y 'name-expr)
					(eq (id y) '_)))
			 collect y))
	 (check (loop for y in subterms
		      as x in sub-boundvars
		      when (or (not (typep y 'name-expr))
			       (declared? (id y) context)
			       (not (every #'(lambda (r)
					       (or (typep (declaration r) 'var-decl)
						   (not (compatible? (type r) (type x)))))
					   (resolve y 'expr nil context))))
		      collect y))
	 (*current-context* context))
    (cond (check
	   (error-format-if "~%The supplied skolem constants must all be new names.
The following are either not names or are previously declared: ~a" check)
	   (cons expr (make-trace 'not-implemented 'p162)))
	  ((duplicates? subterms :test #'same-id)
	   (error-format-if "~%Duplicate use of skolem constants.")
	   (cons expr (make-trace 'not-implemented 'p163)))
	  (overlap
	   (error-format-if
	    "~%The types of the skolemized variables contain free occurrences
of the following quantified variables: ~a.
Please provide skolem constants for these variables." overlap)
	   (cons expr (make-trace 'not-implemented 'p164)))
	  (t (let* ((newexpr (if id-boundvars
				(if (eql (length id-boundvars)
					 (length boundvars))
				    expr
				    (lcopy expr
				      'bindings id-boundvars))
			       (expression expr)))
		    (ctx (if sign
		    	     (make-ctx 'expr-hole *boolean*)
		    	   (make-ctx 'negation (list (make-ctx 'expr-hole *boolean*)))))
		    (make-skolem-result (make-skolem-alist sub-boundvars subterms context))
		    (result (substit-with-proofs
			     newexpr (car make-skolem-result)
			     (make-ctx 'not-implemented 'c129))));;FG take sign into account
	       (if (eq newexpr expr)
		   (cons expr (make-trace 'not-implemented 'p161))
		 (cons (car result)
		       (if (cdr make-skolem-result) ;; simplification in make-skolem-alist 
			   (make-trace 'not-implemented 'p13)
			 (if (not (eq (length subterms) (length terms))) ;; '_ is used
			     (if (every #'eq subterms terms)
				 ;; '_ is only at the end, to be merged with case at bottom
			       (if sign
				   (make-trace 'rewrite-rule
					       (list ctx
						     (compute-forall
						      sub-boundvars
						      (compute-forall
						       id-boundvars
						       (expression expr)))
						     expr)
					       (list (make-trace
						      'forall-rule
						      (list newexpr (car make-skolem-result))
						      (list (cdr result)))))
				 (make-trace 'not-implemented 'p43))
			       ;; (if (every #'eq (loop for y in terms
			       ;; 			     when (and (typep y 'name-expr) (eq (id y) '_))
			       ;; 			     collect y) terms)
				   ;; '_ is only at the beginning, to be extended to general case
				   (if sign
				       (let* ((quant-id
					       (compute-forall id-boundvars (expression expr)))
					      (quant-sub-id
					       (compute-forall sub-boundvars quant-id))
					      (quant-subid
					       (compute-forall (append sub-boundvars id-boundvars nil)
							       (expression expr)))
					      (make-skolem-result*
					       (make-skolem-alist*
					      	boundvars
					      	(mapcar
					      	 #'(lambda (var)
					      	     (declare (ignore var))
					      	     'pvs_with_proofs_id)
					      	 boundvars)
					      	context))
					      (sortedalist
					       (sort-skolem-alist
						(car make-skolem-result*)
						id-boundvars))
					      ;; (dummy
					      ;;  (format t "~%TEST1 ~a" (car make-skolem-result*)))
					      ;; (dummy
					      ;;  (format t "~%TEST1 ~a" sortedalist))
					      (newexpr* (compute-substit
							 (expression expr)
							 (car make-skolem-result*))))
					 (if (cdr make-skolem-result*)
					     (make-trace 'not-implemented 'p63)
					   (make-trace
					    'cut-rule
					    (list quant-sub-id)
					    (list (make-trace
						   'weak-rule
						   (list expr)
						   (list (make-trace
							  'forall-rule
							  (list newexpr (car make-skolem-result))
							  (list (cdr result)))))
						  (make-trace
						   'forall-rule
						   (list (expression expr) (car make-skolem-result*))
						   (list (make-trace
							  'rewrite-rule
							  (list (make-ctx
								 'negation
								 (list
								  (make-ctx 'expr-hole *boolean*)))
								quant-subid quant-sub-id)
							  (list (make-trace
								 'not-forall-rule
								 (list (expression expr) sortedalist)
								 (list (make-trace
									'axiom-rule
									(list newexpr*))))))))))))
				     (make-trace 'not-implemented 'p53))
				 ;; (make-trace 'not-implemented 'p50))
			       )
			   (if (or (not (eq (length boundvars) 1)) ;; > 1 binding per quantifier
				   (not (eq (length terms) 1))) ;; > 1 instantiation per quantifier 
			       (if sign
				   (make-trace 'forall-rule
					       (list newexpr (car make-skolem-result))
					       (list (cdr result)))
				 (make-trace 'not-exists-rule
					       (list newexpr (car make-skolem-result))
					       (list (cdr result))))
			     (if sign ;; FG to be merged with first case
				 (make-trace 'forall-rule
					     (list newexpr (list (car (car make-skolem-result))))
					     (list (cdr result)))
			       (make-trace 'not-exists-rule
					   (list newexpr (list (car (car make-skolem-result))))
					   (list (cdr result))))))))))))))

;;FG
(defun sort-skolem-alist (alist idvars)
  (let ((revcut
	 (reduce #'(lambda (current bind)
		     (if (member (car bind) idvars)
			 (cons (car current)
			       (cons bind (cdr current)))
		       (cons (cons bind (car current))
			     (cdr current))))
		 (cons
		  (cons nil nil)
		  alist))))
    (append (reverse (car revcut)) (reverse (cdr revcut)) nil)))

(defun make-skolem-alist* (boundvars skoids context &optional alist simplified)
  (cond ((null boundvars)
	 (loop for (nil . y) in alist
	       do (record-type-constraints y))
	 (cons (nreverse alist) simplified))
	(t (let* ((subst (substit (type (car boundvars)) alist))
		  (binding (cons (car boundvars)
				 (makeskoconst (pc-parse
						(new-sko-symbol (car skoids) context)
						'expr)
					       subst
					       context))))
	     (make-skolem-alist* (cdr boundvars)(cdr skoids)
				 context
				 (cons binding alist)
				 (or simplified
				     (not (tc-eq (compute-substit (type (car boundvars)) alist)
						 subst))))))))

(defun make-skolem-alist (boundvars skoconstants context &optional alist simplified)
  (cond ((null boundvars)
	 (loop for (nil . y) in alist
	       do (record-type-constraints y))
	 (cons (nreverse alist) simplified))
	(t (let* ((subst (substit (type (car boundvars)) alist))
		  (binding (cons (car boundvars)
				 (makeskoconst (car skoconstants) subst context))))
	     (make-skolem-alist (cdr boundvars)(cdr skoconstants)
				context
				(cons binding alist)
				(or simplified
				    (not (tc-eq (compute-substit (type (car boundvars)) alist)
						subst))))))))

;(defun quant-rule (sformnum substs)
;  (make-instance 'rule
;    :rule-part (quant-rule-fun sformnum substs)
;    :rule-input `(quant ,sformnum ,substs)))

(defun quant-rule-fun ( sformnum  terms &optional copy?)
  #'(lambda (ps)
      (let* ((terms (if (listp terms) terms (list terms)))
	     (sformnum (find-quant sformnum terms ps)))
	(quant-step sformnum ps terms copy?))))

(defun find-quant (sformnum terms ps)
  (find-sform (s-forms (current-goal ps)) sformnum
	      #'(lambda (sform)
		  (or (and (exists-expr? (formula sform))
			   (eql (length (bindings (formula sform)))
				(length terms)))
		      (and (negation? (formula sform))
			   (forall-expr?
			    (args1 (formula sform)))
			   (eql (length (bindings
					 (args1 (formula sform))))
				(length terms)))))))

(defun skolem-rule-fun (&optional sformnum terms skolem-typepreds? dont-simplify?)
  #'(lambda (ps)
	(skolem-step sformnum ps terms skolem-typepreds? dont-simplify?)))

(defun make-alist (substs)
  (if (and (consp substs)(consp (cdr substs)))
      (cons (cons (car substs)(cadr substs))
	    (make-alist (cddr substs)))
    nil))

(defun quant-step-sform (ps sform terms copy?)
  (let* ((fmla (formula sform))
	 (sign (not (negation? fmla)))
	 (body (if sign fmla (args1 fmla)))
	 (terms (if (listp terms) terms (list terms)))
	 (instantiable?
	  (or (and sign (typep body 'exists-expr))
	      (and (not sign)(typep body 'forall-expr))))
	 (length-check (and instantiable?
			    (eql (length (bindings body))
				 (length terms))))
	 (proved-qbody (if length-check
		    (quantifier-step body *current-context* sign
				     terms ps)
		    (cons body (make-trace 'not-implemented 'p149))))
	 (qbody (car proved-qbody)))
    (if (not instantiable?)
	(error-format-if "~%Formula ~a is not instantiable." body)
	(when (not length-check)
	  (error-format-if "Expecting ~a terms, but ~a terms provided."
		      (length (bindings body)) (length terms))))
    (if (exequal qbody body)
	(values (cons 'X (make-trace 'not-implemented 'p47)) sform)
      (let ((proved-sform
	     (if sign
		 (cons (copy sform 'formula qbody)
		   (cdr proved-qbody))
	       (let ((proved-neg-qbody (negate-with-proofs qbody)))
		 (cons (copy sform 'formula
		   (car proved-neg-qbody))
		       (apply-trace (cdr proved-qbody)
				    (list (car (cdr proved-neg-qbody)))))))))
	(if copy?
	    (values (cons '?
			  (make-trace 'contr-rule
				      (list (formula sform))
				      (list (cdr proved-sform))))
		    (list sform (car proved-sform)))
	  (values (cons '? (cdr proved-sform)) (car proved-sform)))))))

(defun skolem-step-sform (ps sform  new-context &optional terms)
  (declare (ignore ps))
  (let* ((fmla (formula sform))
	 (sign (not (negation? fmla)))
	 (body (if sign fmla (args1 fmla)))
	 (skolemizable? (or (and sign (forall-expr? body))
			    (and (not sign)(exists-expr? body))))
	 (length-check (and skolemizable?
			    (eql (length (bindings body))
				 (length terms))))
	 (proved-skobody (if length-check
			     (skolemize-step body new-context sign
					     terms)
			   (cons body (make-trace 'not-implemented 'p1)))))
    (if (not skolemizable?)
	(error-format-if "~%Formula~%~a~% is not skolemizable." body)
      (when (not length-check)
	(error-format-if "Expecting ~a skolem constant(s), but ~a supplied."
			 (length (bindings body)) (length terms))))
    (if (exequal (car proved-skobody) body)
	(values (cons 'X (make-trace 'not-implemented 'p160)) sform)
      (if sign
	  (values (cons '? (cdr proved-skobody))
		  (copy sform 'formula
			(car proved-skobody)))
	(let ((proved-neg-skobody (negate-with-proofs (car proved-skobody))))
	  (values (cons '?
			(apply-trace (cdr proved-skobody)
				     (list (car (cdr proved-neg-skobody)))))
		  (copy sform 'formula
			(car proved-neg-skobody))))))))


(defmethod tc-eq* ((x s-formula)(y s-formula) bindings)
  (tc-eq* (formula x)(formula y) bindings))
	

(defun quant-step (sformnum ps &optional terms copy?)
  (cond ((or (null sformnum)(null terms))
	 (error-format-if "~%No suitable (+ve EXISTS/-ve FORALL) quantified formula found.")
	 (values (cons 'X
		       (make-trace 'empty 'np4))
		 nil
		 nil))
	(t (let ((*tccforms* nil)
		 (*dependent-decls* nil))
	     (multiple-value-bind (signal subgoal)
		 (sequent-reduce-with-proofs
		  (current-goal ps)
		  #'(lambda (sform)
		      (quant-step-sform ps sform
					terms
					copy?))  
		  (list sformnum))
	       (let ((qsforms (select-seq (s-forms (current-goal ps))
					  (list sformnum)))
		     (other-sforms (delete-seq (s-forms (current-goal ps))
					       (list sformnum)))
		     (trace (cdr signal)))
		 (when (and (eq (car signal) '?) (not copy?))
		   (loop for sf in qsforms
			 do
			 (unless (find sf (hidden-s-forms subgoal)
				       :test #'tc-eq)
			     (pushnew sf (hidden-s-forms subgoal)
				     :test #'tc-eq)
			     (setq trace (make-trace 'contr-rule
						     (list (formula sf))
						     (list trace))))))
		 (let* ((*tccforms* (remove-duplicates *tccforms*
				      :test #'tc-eq
				      :key #'tccinfo-formula))
			(tccforms (assert-tccforms *tccforms* ps)))
		   (if (some #'(lambda (tccf)
				 (tc-eq (tccinfo-formula tccf) *false*))
			     tccforms)
		       (values (cons 'X (make-trace 'empty 'np21)) nil)
		       (let* ((tcc-subgoals
			       (loop for tccinfo in tccforms
				     collect
				     (let ((newgoal
					    (change-class
					     (copy subgoal
					       's-forms
					       (cons (make-instance 's-formula
						       :formula
						       (tccinfo-formula tccinfo))
						     other-sforms))
					     'tcc-sequent))
					   (references nil))
				       (setf (tcc newgoal)(tccinfo-formula tccinfo)
					     (reason newgoal)(tccinfo-reason tccinfo)
					     (expr newgoal)(tccinfo-expr tccinfo)
					     (kind newgoal)(tccinfo-kind tccinfo)
					     (type newgoal)(tccinfo-type tccinfo))
				       (list newgoal
					     'dependent-decls
					     (push-references-list
					      (tccinfo-formula tccinfo)
					      references)))
				     ))
			      );(break "quant-step")
			 ;;(push-references-list *tccforms* dependent-decls*)
			 (if (null tcc-subgoals)
			     (values (cons (car signal) trace)
				 (cons (list subgoal
					     'dependent-decls
					     *dependent-decls*)
				       tcc-subgoals))
			   (values (cons (car signal)
					 (make-trace
					  'tcc-rule
					  (list
					   (mapcar
					    #'(lambda (subgoal)
						(mapcar #'formula
							(append (s-forms
								 (if (consp subgoal)
								     (car subgoal)
								   subgoal))
								(hidden-s-forms
								 (if (consp subgoal)
								     (car subgoal)
								   subgoal))
								nil)))
					    tcc-subgoals)
					   (mapcar #'formula
						   (append (s-forms (current-goal ps))
							   (hidden-s-forms (current-goal ps))
							   nil)))
					  (cons trace
						(mapcar #'(lambda (subgoal)
							    (declare (ignore subgoal))
							    (make-trace 'proof-hole))
							tcc-subgoals))))
				 (cons (list subgoal
					     'dependent-decls
					     *dependent-decls*)
				       tcc-subgoals))))))))))))

(defun skolem-step (sformnum ps &optional terms skolem-typepreds? dont-simplify?)
  (let* ((*assert-typepreds* nil)
	 (*subtype-hash* (copy (subtype-hash ps)))
	 (*dp-state* (dp-state ps))
	 (*substit-dont-simplify* dont-simplify?)
	 (new-context (copy-prover-context))
	 (terms (if (consp terms) terms (list terms)))
	 (sformnum (find-sform (s-forms (current-goal ps)) sformnum
			       #'(lambda (sform)
				   (skolem-step-sform? sform terms)))))
    (protecting-cong-state
     ((*dp-state* *dp-state*))
     (cond ((null sformnum)
	    (error-format-if "~%No suitable (+ve FORALL/-ve EXISTS) quantified expression found.")
	    (values (cons 'X (make-trace 'not-implemented 'p150))
		    nil nil))
	   (t (multiple-value-bind
	       (signal subgoal)
	       (sequent-reduce-with-proofs
		(current-goal ps)
		#'(lambda (sform)
		    (skolem-step-sform ps sform
				       new-context
				       terms))
		(list sformnum))
		  (if (eq (car signal) 'X)
		      (values (cons 'X (make-trace 'not-implemented 'p157))
			      nil nil)
		    (if (some #'skolem-step-assert-typepred *assert-typepreds*)
			(values (cons '!
				      (make-trace
				       'typepred-rule
				       (list (list *true*))
				       (list (make-trace 'true-rule))))
				sformnum) ; SO - changed from sform
			(multiple-value-bind (nsubgoal references)
			    (let ((*current-context* new-context))
			      (skolem-typepreds-subgoal subgoal terms ps
							skolem-typepreds?))
			    (let ((ntrace
				   (if skolem-typepreds?
				       (make-trace 'not-implemented 'p159)
				     (make-trace 'proof-hole))))
			      (values
			       (cons (car signal)
				     (apply-trace (cdr signal)
						  (list ntrace)))
			       (list
				(cons nsubgoal
				      (list 'context new-context
					    'subtype-hash *subtype-hash*
					    'dp-state *dp-state*
					    'references references))))))))))))))
		      
(defun skolem-step-assert-typepred (fmla)
  (let* ((*sequent-typealist* nil)
	 (sign (not (negation? fmla)))
	 (body (if sign
		   fmla
		   (args1 fmla))))
    (top-translate-to-prove body t)
    (and (not (connective-occurs? body))
	 (let ((res (call-process fmla *dp-state*)))
	   (when (consp res)
	     (loop for x in res
		   do (push x *process-output*)))
	   (false-p res)))))

(defun skolem-step-sform? (sform terms)
  (or (and (forall-expr? (formula sform))
	   (= (length (bindings (formula sform))) (length terms)))
      (and (negation? (formula sform))
	   (exists-expr? (args1 (formula sform)))
	   (= (length (bindings (args1 (formula sform)))) (length terms)))))

(defun skolem-typepreds-subgoal (subgoal terms ps skolem-typepreds?)
  (if skolem-typepreds?
      (let ((preds (loop for expr in terms
			 unless (equal expr "_")
			 append (collect-typepreds expr ps))))
	(if preds
	    (let* ((new-sforms
		    (mapcar #'(lambda (fmla)
				(make-instance 's-formula
				  :formula (car (negate-with-proofs fmla))))
		      preds))
		   (references nil))
	      (push-references-list
	       (mapcar #'formula new-sforms)
	       references)
	      (copy subgoal
		's-forms (append new-sforms
				 (s-forms subgoal))))
	    subgoal))
      subgoal))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defun find-!quant (sformnum ps)
  (find-sform (s-forms (current-goal ps)) sformnum
	      #'(lambda (sform)
		  (or (forall-expr? (formula sform))
		      (and (negation? (formula sform))
			   (exists-expr?
			    (args1 (formula sform))))))))

(defun fill-up-terms (sformnum terms ps &optional keep-underscore?)
  (let* ((sforms (select-seq (s-forms (current-goal ps)) (list sformnum)))
	 (sform (when sforms (car sforms)))
	 (fmla (when sforms (formula sform)))
	 (boundvars (when sforms
		      (if (forall-expr? fmla)
			  (bindings fmla)
			  (bindings (args1 fmla))))))
    (if (< (length terms) (length boundvars))
	(let* ((extra-boundvars
		(if terms (nthcdr (1- (length terms)) boundvars)
		    boundvars))
	       (skonames (new-sko-symbol-list
			  (mapcar #'id extra-boundvars)
			  *current-context*
			  nil nil
			  :keep-underscore? keep-underscore?)))
	  (append terms skonames))
	terms)))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun all-or-best? (if-match)(memq if-match '(all best)))

(defun all-or-best-or-first*? (if-match)
  (memq if-match '(all best first*)))

(defun all-or-first*? (if-match)
  (memq if-match '(all first*)))

(defun make-inst?-rule (fnum newterms copy? if-match)
  (if (all-or-first*? if-match)
      (if newterms
	  (if (cdr newterms)
	      `(then ,(make-copy-quant-rule fnum (car newterms))
		,(make-inst?-rule fnum (cdr newterms) copy? if-match))
	      (if copy?
		  (make-copy-quant-rule fnum (car newterms))
		  (make-quant-rule fnum (car newterms))))
	  '(skip))
      (if copy?
	  (make-copy-quant-rule fnum newterms)
	  (make-quant-rule fnum newterms))))

(defun  make-copy-quant-rule (fnum newterms)
  (let* ((badterm (find-if #'(lambda (nt)
			       (member "_" nt))
		    newterms))
	 (nterms (ldiff newterms (cdr (memq badterm newterms)))))
    (cons 'then*
	  (cons `(instantiate ,fnum  ;;NSH(10.4.96)instantiate-one
			              ;;is not well-behaved; causes
			              ;;grind to fail.  
			      ,(car nterms) t)
		(loop for qterms in (cdr nterms)
		      collect `(instantiate  ;;NSH(4.2.95)was quant
				,(if (< fnum 0)
				     (1- fnum)
				     (1+ fnum))
				,qterms))))))

(defun make-quant-rule (fnum newterms)
  (let* ((badterm (find-if #'(lambda (nt)
			       (member "_" nt :test #'equal))
		    newterms))
	 (nterms (ldiff newterms (cdr (memq badterm newterms)))))
    (cons 'then*
	  (loop for qterms in nterms
		collect `(instantiate ,fnum ,qterms)))))


;;find-?quant finds quantified formula where outer variables contain
;;those in subst.
(defun find-?quant (sformnum subst ps)
  (let* ((subalist (make-alist subst))
	 (subnames (loop for (x . nil) in subalist
			 collect (pc-parse x 'expr)))
	 (badnames (loop for x in subnames
			 when (not (typep x 'name-expr))
			 collect x)))
    (cond (badnames
	   (error-format-if "~%Substitution ~a is ill-formed" subst)
	   nil)
	  (t (find-sform (s-forms (current-goal ps)) sformnum
			 #'(lambda (sform)
			     (or (and (exists-expr? (formula sform))
				      (subsetp subnames
					       (quant-bndvars*
						(formula sform) t)
					       :test #'format-equal))
				 (and (negation? (formula sform))
				      (forall-expr?
				       (args1 (formula sform)))
				      (subsetp subnames
					       (quant-bndvars*
						(args1 (formula sform)) nil)
					       :test #'format-equal)))))))))

(defun quant-body* (fmla sign)
  (if sign
      (if (exists-expr? fmla)
	  (quant-body* (expression fmla) sign)
	  fmla)
      (if (forall-expr? fmla)
	  (quant-body* (expression fmla) sign)
	  fmla)))

(defun quant-bndvars* (fmla sign)
  (if sign
      (when (exists-expr? fmla)
	(append (bindings fmla)
		(quant-bndvars* (expression fmla) sign)))
      (when (forall-expr? fmla)
	(append (bindings fmla)
		(quant-bndvars* (expression fmla) sign)))))

(defun order-subst (subst boundvars)
  (if (null boundvars)
      nil
      (let ((entry (assoc (car boundvars) subst
			  :key #'declaration)))
	(if entry
	    (cons entry (order-subst subst (cdr boundvars)))
	    (order-subst subst (cdr boundvars))))))

(defun filter-subst-false-tccs (subst-list boundvars)
  (if (consp subst-list)
      (let ((*tccforms* nil)
	    (*evaluate-tccs* nil))
	(tc-alist (order-subst (cdr (car subst-list)) boundvars))
	(let ((tccforms (assert-tccforms *tccforms* *ps*)))
	  (if (some #'(lambda (tccf)
			(tc-eq (tccinfo-formula tccf) *false*))
		    tccforms)
	      (filter-subst-false-tccs (cdr subst-list) boundvars)
	      (cons (car subst-list)
		    (filter-subst-false-tccs (cdr subst-list) boundvars)))))
      nil))

(defun filter-best (tcc-all-subst boundvars i)
  (if (consp tcc-all-subst)
      (if (eql (length (caar tcc-all-subst)) i)
	  (let ((*tccforms* nil)
		(y (cdar tcc-all-subst))
		(*evaluate-tccs* nil))
	    (tc-alist (order-subst (cdr y) boundvars))
	    (let ((tccforms (assert-tccforms *tccforms* *ps*)))
	      (if (some #'(lambda (tccf)
			    (tc-eq (tccinfo-formula tccf) *false*))
			tccforms)
		  (filter-best (cdr tcc-all-subst) boundvars i)
		  y)))
	  (filter-best (cdr tcc-all-subst) boundvars i))
      nil))

(defun filter-subst-all-or-best-false-tccs
  (subst-list tcc-all-subst boundvars if-match tcc?) 
  (if tcc?
      (let* ((tcc-lengths (loop for (x . nil) in tcc-all-subst
				collect (length x)))
	     (min (if tcc-lengths (apply #'min tcc-lengths) 0))
	     (max (if tcc-lengths (apply #'max tcc-lengths) 0)))
	(if (eq if-match 'best)
	    (loop for i from min to max
		  thereis
		  (filter-best tcc-all-subst boundvars i)
		  )
	    (filter-subst-false-tccs subst-list boundvars)))
      (let ((all-non-tcc-substs
	     (loop for (x . y) in tcc-all-subst
		   when (null x)
		   collect y)))
	(if (eq if-match 'best)
	    (and all-non-tcc-substs (car all-non-tcc-substs))
	    all-non-tcc-substs))))

(defun filter-subst (fmla subst sign boundvars if-match tcc?)
  (if (all-or-best-or-first*? if-match)
      (let ((subst (rem-dups
		    subst
		    :test #'tc-eq
		    :key #'(lambda (sub) (quant-subs* fmla sub sign nil)))))
	(if (and tcc? (all-or-first*? if-match))
	    (filter-subst-false-tccs subst boundvars)
	  (let (
		(tcc-all-subst
		 (loop for sub in subst
		       collect
		       (let ((*tccforms* nil)
			     (*evaluate-tccs* nil))
			 (tc-alist (order-subst (cdr sub) boundvars))
			 (cons *tccforms* sub)))))
	    (filter-subst-all-or-best-false-tccs subst tcc-all-subst
						 boundvars if-match tcc?))))
	  (let ((*tccforms* nil)
		(*evaluate-tccs* nil))
	    (tc-alist (order-subst (cdr subst) boundvars))
	    (let ((tccforms (assert-tccforms *tccforms* *ps*)))
	      (if (some #'(lambda (tccf)
			    (tc-eq (tccinfo-formula tccf) *false*))
			tccforms)
		  nil
		  (if tcc? subst
		      (if *tccforms* nil subst)))))))

(defun quant-subs* (fmla subst sign if-match)
  (if (all-or-first*? if-match)
      (loop for sub in subst
	    collect (quant-subs* fmla sub sign nil))
      (if sign
	  (if (exists-expr? fmla)
	      (cons (loop for var in (bindings fmla)
			  collect
			  (let ((entry
				 (assoc var (cdr subst) :key #'declaration)))
			    (if entry (cdr entry)
				"_")))
		    (quant-subs* (expression fmla) subst sign if-match))
	      nil)
	  (if (forall-expr? fmla)
	      (cons (loop for var in (bindings fmla)
			  collect
			  (let ((entry
				 (assoc var (cdr subst) :key #'declaration)))
			    (if entry (cdr entry)
				"_")))
		    (quant-subs* (expression fmla) subst sign if-match))
	      nil))))
	       
 
(defun find-quant-terms (sforms subst where if-match polarity? tcc? ps)
  (cond ((null sforms)
	 (error-format-if "~%Couldn't find a suitable quantified formula.")
	 nil)
	(t (let* ((*dp-state* (dp-state ps))
		  (if-match (if (or (all-or-best-or-first*? if-match)
				    tcc?)
				if-match
				'best)))
	     (nprotecting-cong-state
	      ((*dp-state* *dp-state*))
	      (find-quant-terms* sforms subst where if-match polarity? tcc? ps))))))

(defun forall-sform?  (sform)
  (let ((formula  (formula sform)))
    (if (negation? formula)
	(exists-expr? (args1 formula))
	(forall-expr? formula))))

(defun exists-sform? (sform)
  (let ((formula  (formula sform)))
    (if (negation? formula)
	(forall-expr? (args1 formula))
	(exists-expr? formula))))

(defun find-quant-terms* (sforms subst where if-match polarity? tcc? ps)
  (cond ((null sforms)
	 (error-format-if "~%Couldn't find a suitable instantiation for any
quantified  formula.  Please provide partial instantiation.")
	 nil)
	((or (not (listp subst))
	     (oddp (length subst)))
	 (error-format-if "~%Given substitution ~a
is not of the form: (<var> <term>...)" subst)
	 nil)
	((not (quant-expr? (if (negation? (formula (car sforms)))
			       (args1 (formula (car sforms)))
			       (formula (car sforms)))))
	 (find-quant-terms* (cdr sforms) subst where if-match
			    polarity? tcc? ps))
	(t 
	 (let* ((sform (car sforms))
		(formula (formula sform))
		(sign (not (negation? formula)))
		(fmla (quant-body* (if sign formula (args1 formula)) sign))
		(qboundvars (quant-bndvars* (if sign formula (args1 formula))
					    sign))
		(pre-alist (mapcar #'(lambda (sb)
				       (cons (pc-parse (car sb) 'name)
					     (cdr sb)))
			     (make-alist subst)))
		(nonsubs (loop for (x . y) in pre-alist
			       when (or (eq y '_) (equal y "_"))
			       collect x))
		(sub-alist (remove-if #'(lambda (sb)
					  (or (eq (cdr sb) '_)
					      (equal (cdr sb) "_")))
			     pre-alist))
		(bad-subst (loop for (x . nil) in pre-alist
				 thereis
				 (unless (member x qboundvars
						 :test #'format-equal)
				   x)))
		(boundvars (remove-if #'(lambda (bv)
					  (member bv nonsubs :test #'same-id))
			     qboundvars)))
	   (cond (bad-subst
		  (find-quant-terms* (cdr sforms) subst where
				     if-match polarity? tcc? ps))
		 (t (let ((sub
			   (find-quant-subst (car sforms) sub-alist
					     nonsubs boundvars sign fmla
					     where if-match
					     polarity? tcc? ps)))
		      (if sub
			  ;; Note that find-quant-subst may have found matches
			  ;; for variables in nonsubs - we simply remove them
			  (cons (find-sform (s-forms
					     (current-goal *ps*))
					    '*
					    #'(lambda (x)
						(eq x (car sforms))))
				sub)
			  (find-quant-terms* (cdr sforms) subst
					     where if-match
					     polarity? tcc? ps)))))
	   ))))


(defun find-quant-subst (sform pre-alist nonsubs boundvars sign fmla
			       where if-match polarity? tcc? ps)
  (let* ((alist
	  (loop for (x . y) in pre-alist
		collect
		(let* ((v (find x boundvars :test #'format-equal))
		       (term (pc-parse y 'expr)))
		  (cons v term))))
	 (alist (tc-alist alist))
	 (*all-boundvars* boundvars) ;;NSH(11.6.95) for use in template?
	 (rest-boundvars
	  (loop for v in boundvars
		when (not (assoc v alist))
		collect v))
	 ;;(freevars (freevars formula))
	 ;;	 (allvars (append freevars boundvars))
	 (other-sforms 
	  (gather-seq (s-forms (current-goal ps))
		      where
		      nil
		      #'(lambda (x) (not (eq x sform)))
		      ;;NSH(11.6.94): to allow self-instantiation
		      ;;of quantified formulas (not (eq x sform))
		      ))
	 (all-sforms (gather-seq (s-forms (current-goal ps))
				 where
				 nil))
	 (all-fmlas
	  (if (memq sform all-sforms)
	      (mapcar #'formula (append other-sforms (list sform)))
	      (mapcar #'formula other-sforms))))
    (find-quant-subst* sform sign fmla
		       all-fmlas alist nonsubs rest-boundvars if-match
		       polarity? tcc?
		       (length rest-boundvars))))

(defun top-find-match-list (template fmlas alist if-match polarity polarity?)
  (if polarity?
      (find-match-list-with-polarity template fmlas
				     alist if-match polarity)
      (let ((fmlas (if (variable? template) ;;NSH(11-2-05)
		       (let ((skolem-consts ;;matches hidden skolem constants 
			      (loop for cd in (collect-skolem-constants)
				    collect (mk-name-expr (id cd)
					      nil nil 
					      (mk-resolution
						  cd (current-theory-name)
						  (type cd))))))
			 (if skolem-consts
			     (append fmlas
				     skolem-consts)
			     fmlas))
		       fmlas)))
	(find-match-list template fmlas alist if-match))))

(defun top-find-match-list-templates
  (templates fmlas alist if-match polarity polarity?)
  (if (consp templates)
      (let* ((temp (car templates))
	     (result
	      (top-find-match-list temp
				   fmlas
				   alist
				   if-match 'positive polarity?)))
	(if (all-or-best-or-first*? if-match)
	    (nconc (mapcar #'(lambda (x) (cons temp x))
		     result)
		   (top-find-match-list-templates
		    (cdr templates) fmlas alist if-match
		    polarity polarity?))
	    (if result
		(cons temp result)
		(top-find-match-list-templates
		 (cdr templates) fmlas alist if-match
		 polarity polarity?))))
      nil))

(defun find-quant-subst* (sform sign fmla
				other-fmlas alist nonsubs rest-boundvars
				if-match polarity? tcc? n)
  (let* ((polarity (if sign 'positive 'negative))
	 (templates (find-templates fmla rest-boundvars n nil polarity
				    polarity?))
	 ;;(freevars-sub (mapcar #'(lambda (x) (cons x x)) freevars))
	 (*modsubst* t)
	 (temp-subst (top-find-match-list-templates
		      templates other-fmlas alist if-match
		      'positive polarity?))
	 (pre-subst (if nonsubs
			(when temp-subst
			  (if (all-or-best? if-match)
			      (let ((temp (remove-if
					      #'(lambda (tmp)
						  (and (variable? (car tmp))
						       (member (car tmp)
							       nonsubs
							       :test #'same-id)))
					    temp-subst)))
				(mapcar #'(lambda (tmp)
					    (cons (car tmp)
						  (remove-if
						      #'(lambda (sb)
							  (member (car sb)
								  nonsubs
								  :test #'same-id))
						    (cdr tmp))))
				  temp))
			      (unless (and (variable? (car temp-subst))
					   (member (car temp-subst)
						   nonsubs
						   :test #'same-id))
				(cons (car temp-subst)
				      (remove-if
					  #'(lambda (sb)
					      (member (car sb)
						      nonsubs
						      :test #'same-id))
					(cdr temp-subst))))))
			temp-subst))
	 (subst (filter-subst (if sign
				  (formula sform)
				  (args1 (formula sform)))
			      (if pre-subst pre-subst
				  (when alist
				    (if (all-or-best? if-match)
					(list (cons nil alist))
					(cons nil alist)))) ;for null template
			      sign rest-boundvars if-match tcc?))
	 (subs (quant-subs* (if sign
				(formula sform)
				(args1 (formula sform)))
			    (if subst subst
				(when alist (if (all-or-best? if-match)
						(list (cons nil alist))
						(cons nil alist))))
			    sign if-match)))
    (cond ((and (null subst) (or if-match (null alist)(null subs)))
	   (if  (and (> n 1) ;;NSH(5.23.95) used to be n>2.
		     (not (eq if-match 'all)))
		(find-quant-subst* sform sign fmla other-fmlas
				   alist nonsubs rest-boundvars
				   if-match polarity? tcc? (1- n))
					;(format-if "~%Couldn't find a matching substitution.")
		nil))
	  ((and (null subst) subs)
	   (format-if "~%Using supplied substitutions")
	   subs)
	  (t (cond ((all-or-first*? if-match)
		    (loop for sub in subst as index from 1
			  do (format-if "~%Found substitution ~a:"
					index)
			  (loop for (x . y) in (cdr sub)
				do (format-if "~%~a gets ~a," x y))
			  (format-if "~%Using template: ~a" (car sub))))
		   (t (format-if "~%Found substitution:")
		      (loop for (x . y) in (cdr subst)
			    do (format-if "~%~a gets ~a," x y))
		      (format-if "~%Using template: ~a" (car subst))))
	     subs))))

(defun find-match-list-with-polarity (template fmlas subst if-match polarity)
  (when fmlas
    (let ((match-list1
	   (if (all-or-best-or-first*? if-match)
	       (mapcar #'car
		 (find-all-matches-polarity
		  template (car fmlas)
		  nil subst nil polarity))
	       (let ((sub (find-match-polarity template (car fmlas) nil
					       subst nil polarity)))
		 (if (eq sub 'fail) nil sub)))))
      (if (all-or-best-or-first*? if-match)
	  (nconc match-list1
		 (find-match-list-with-polarity template (cdr fmlas) subst
						if-match polarity))
	  (or match-list1
	      (find-match-list-with-polarity template (cdr fmlas) subst
					     if-match polarity))))))

(defun find-match-list (template fmlas subst if-match)
  (when fmlas
    (let ((match-list1
	   (if (all-or-best-or-first*? if-match)
	       (mapcar #'car
		 (find-all-matches template (car fmlas) nil subst nil))
	       (let ((sub (find-match template (car fmlas) nil subst nil)))
		 (if (eq sub 'fail) nil sub)))))
      (if (all-or-best-or-first*? if-match)
	  (nconc match-list1
		 (find-match-list template (cdr fmlas) subst if-match))
	  (if match-list1
	      match-list1
	      (find-match-list template (cdr fmlas) subst if-match))))))

(defun template? (fmla boundvars)
  (let ((freevars (freevars fmla)))
    (and (subsetp freevars *all-boundvars* :test #'same-declaration)
	 (eql (length (intersection freevars boundvars
				    :key #'declaration))
	      *template-num*))))

(defun find-templates (expr boundvars n &optional accum polarity polarity?)
  (let* ((*template-num* n)
	 (templates
	  (if polarity?
	      (rem-dups
	       (find-templates-with-polarity
		expr boundvars polarity)
	       :test #'tc-eq
	       :key #'template-expression)
	      (rem-dups (find-templates* expr boundvars accum)
			:test #'tc-eq))))
    (if (and (eq n 1)(null polarity?))
	(let* ((nonvars (remove-if #'variable? templates))
	       (vars (remove-if #'(lambda (x) (not (variable? x)))
		       templates))
	       (boundvars-not-in-vars
		(loop for x in boundvars
		      when (not (member x vars :test #'same-declaration))
		      collect (make!-name-expr
			       (id x) nil nil
			       (make-resolution x nil (type x))))))
	  (nconc nonvars vars
		 boundvars-not-in-vars))
	templates)))

(defun subset-expr-freevars-against-arg-templates
  (expr-freevars arg-template)
  (subsetp expr-freevars
	   (freevars arg-template)
	   :test #'same-declaration))

(defun subsumed-expr-against-arg-templates
  (expr arg-templates)
  (member (freevars expr)
	  arg-templates
	  :test #'subset-expr-freevars-against-arg-templates))

(defun connective-expr? (expr)
  (or ;;NSH(4.8.96) (negation? expr)
	(implication? expr)(conjunction? expr)
	(disjunction? expr)(iff? expr)))

(defun toggle (polarity)
  (if (eq polarity 'positive) 'negative
      (if (eq polarity 'negative) 'positive
	  (if (eq polarity 'less) 'more
	      (if (eq polarity 'more) 'less
		  polarity)))))

(defstruct template ;;NSH(3.10.97) find-templates returns templates
  expression        ;;with polarity instead of expressions. 
  polarity)

(defun mk-template (expr polarity)
  (make-template :expression expr :polarity polarity))

(defun arith-polarity? (polarity)
  (memq polarity '(less more)))

(defun arith-polarity (bpolarity apolarity)
  (if (eq bpolarity 'positive)
      apolarity
      (if (eq bpolarity 'negative)
	  (toggle apolarity)
	  nil)))

(defmethod find-templates-with-arithmetic-polarity
  ((expr application) boundvars polarity accum)
  (let* ((op (operator expr))
	 (arg-templates 
	  (if (and (name-expr? op)
		   (interpreted? op))
	      (cond
	       ((memq (id (operator expr)) '(< <=))
		(find-templates-with-arithmetic-polarity
		 (args1 expr) boundvars
		 (arith-polarity polarity 'less)
		 (find-templates-with-arithmetic-polarity (args2 expr)
							  boundvars
							  (arith-polarity
							   polarity 'more)
							  accum)))
	       ((memq (id (operator expr)) '(> >=))
		(find-templates-with-arithmetic-polarity
		 (args1 expr) boundvars
		 (arith-polarity polarity 'more)
		 (find-templates-with-arithmetic-polarity (args2 expr)
							  boundvars
							  (arith-polarity
							   polarity 'less)
							  accum)))
	       ((is-plus? op)
		(find-templates-with-arithmetic-polarity
		 (args1 expr) boundvars polarity
		 (find-templates-with-arithmetic-polarity
		  (args2 expr) boundvars polarity accum)))
	       ((is-sub-minus? op)
		(find-templates-with-arithmetic-polarity
		 (args1 expr)
		 boundvars
		 polarity
		 (find-templates-with-arithmetic-polarity
		  (args2 expr)
		  boundvars (toggle polarity) accum)))
	       ((is-minus? op)
		(find-templates-with-arithmetic-polarity
		 (argument expr)
		 boundvars (toggle polarity) accum))
	       (t accum))
	      accum)))
    (if (template? expr boundvars)
	(cons (mk-template expr polarity)
	      arg-templates)
	arg-templates)))

(defmethod find-templates-with-arithmetic-polarity
    ((expr list)  boundvars polarity accum)
  (if (consp expr)
      (find-templates-with-arithmetic-polarity
       (car expr)
       boundvars polarity
       (find-templates-with-arithmetic-polarity
	(cdr expr) boundvars polarity accum))
      accum))

(defmethod find-templates-with-arithmetic-polarity
    ((expr t)  boundvars polarity accum)
  (if (template? expr boundvars)
      (cons (mk-template expr polarity) accum)
      accum))

(defmethod find-templates-with-polarity ((expr application) boundvars
      polarity &optional accum)
  (let ((argument-templates
	 (cond ((implication? expr)
		(find-templates-with-polarity
		 (args2 expr) boundvars polarity
		 (find-templates-with-polarity (args1 expr)
				  boundvars (toggle polarity))
		 ))
	       ((negation? expr)
		(find-templates-with-polarity (args1 expr) boundvars
				(toggle polarity)))
	       ((or (conjunction? expr)(disjunction? expr))
		(find-templates-with-polarity (arguments expr) boundvars
				 polarity))
	       (t
		(find-templates-with-arithmetic-polarity
		 expr boundvars polarity nil)))))
    (if (template? expr boundvars)
	(if (and (connective-expr? expr)
		 (subsumed-expr-against-arg-templates expr argument-templates))
	    (append argument-templates accum)
	    (cons (mk-template expr polarity)
		  (append argument-templates accum)))
	(append argument-templates accum))))

(defmethod find-templates-with-polarity ((expr binding-expr) boundvars
					 polarity &optional accum)
  (let* ((argument-templates
	  (find-templates-with-polarity  (expression expr) boundvars polarity))
	 (argument-templates
	  (loop for fmla in argument-templates
		when (null (intersection (freevars fmla)
					 (bindings expr)
					 :key #'declaration))
		collect fmla)))
    (if (template? expr boundvars)
	(cons (mk-template expr polarity)
	      (append argument-templates accum))
	(append argument-templates accum))))

(defmethod find-templates-with-polarity ((expr list) boundvars
			    polarity &optional accum)
  (cond ((null expr) accum)
	(t (find-templates-with-polarity (car expr) boundvars polarity
			   (find-templates-with-polarity (cdr expr) boundvars
					    polarity accum)))))

(defmethod find-templates-with-polarity ((expr name-expr) boundvars
					 polarity &optional accum)
  (if (and (variable? expr)
	   (subsetp boundvars
	       (list expr)
	       :key #'declaration))
      (cons (mk-template expr polarity) accum)
      accum))

(defmethod find-templates-with-polarity ((expr t) boundvars polarity
					 &optional accum)
  (declare (ignore boundvars polarity))
  accum)

(defun rem-dups* (list accum &key (test #'eql) (key #'identity))
  ;;NSH(10.2.95) needed to preserve order
  (if (null list)(nreverse accum)
      (rem-dups* (delete (funcall key (car list)) (cdr list) :test test :key key)
		(cons (car list) accum)
		:test test :key key)))

(defun rem-dups (list &key (test #'eql) (key #'identity))
  (rem-dups* list nil :test test :key key))


(defmethod find-templates* ((expr application) boundvars &optional accum)
  (let ((argument-templates
	 (if (implication? expr)
	     (find-templates* (args2 expr) boundvars
			     (find-templates* (args1 expr) boundvars))
	     (find-templates* (cons (operator expr)
			       (arguments expr))
			 boundvars))))
    (if (template? expr boundvars)
	(if (and (connective-expr? expr)
		 (subsumed-expr-against-arg-templates expr argument-templates))
	    (append argument-templates accum)
	    (cons expr (append argument-templates accum)))
	(append argument-templates accum))))

(defmethod find-templates* ((expr field-application) boundvars &optional accum)
  (find-templates* (argument expr) boundvars accum))

(defmethod find-templates* ((expr projection-expr) boundvars &optional accum)
  (declare (ignore boundvars))
  accum)

(defmethod find-templates* ((expr injection-expr) boundvars &optional accum)
  (declare (ignore boundvars))
  accum)

(defmethod find-templates* ((expr injection?-expr) boundvars &optional accum)
  (declare (ignore boundvars))
  accum)

(defmethod find-templates* ((expr extraction-expr) boundvars &optional accum)
  (declare (ignore boundvars))
  accum)

(defmethod find-templates* ((expr projection-application) boundvars
			    &optional accum) 
  (find-templates* (argument expr) boundvars accum))

(defmethod find-templates* ((expr injection-application) boundvars
			    &optional accum) 
  (find-templates* (argument expr) boundvars accum))

(defmethod find-templates* ((expr injection?-application) boundvars
			    &optional accum) 
  (find-templates* (argument expr) boundvars accum)) 

(defmethod find-templates* ((expr extraction-application) boundvars
			    &optional accum) 
  (find-templates* (argument expr) boundvars accum))

(defmethod find-templates* ((expr record-expr) boundvars &optional accum)
  (let ((argument-templates
	 (find-templates* (assignments expr) boundvars)))
    (if (null argument-templates)
	(if (template? expr boundvars)
	    (cons expr accum)
	    accum)
	(cons expr (append argument-templates accum)))))

(defmethod find-templates* ((expr assignment) boundvars &optional
			    accum)
  (find-templates* (expression expr)
		  boundvars
		  (find-templates* (arguments expr)
				   boundvars accum)))

(defmethod find-templates* ((expr tuple-expr) boundvars &optional accum)
  (let ((argument-templates
	 (find-templates* (exprs expr) boundvars)))
    (if (null argument-templates)
	(if (template? expr boundvars)
	    (cons expr accum)
	    accum)
	(cons expr (append argument-templates accum)))))

(defmethod find-templates* ((expr cases-expr) boundvars &optional accum)
  (let ((argument-templates
	 (find-templates* (cons (expression expr)
			       (append (mapcar #'expression
					       (selections expr))
				       (else-part expr)))
				boundvars)))
    (if (null argument-templates)
	(if (template? expr boundvars)
	    (cons expr accum)
	    accum)
	(cons expr (append argument-templates accum)))))

(defmethod find-templates* ((expr binding-expr) boundvars &optional accum)
  (let* ((argument-templates
	  (find-templates*  (expression expr) boundvars))
	 (argument-templates
	  (loop for fmla in argument-templates
		when (null (intersection (freevars fmla)
					 (bindings expr)
					 :key #'declaration))
		collect fmla)))
    (if (template? expr boundvars)
	(cons expr (append argument-templates accum))
	(append argument-templates accum))))


(defmethod find-templates* ((expr update-expr) boundvars &optional accum)
  (let ((argument-templates
	 (find-templates*  (cons (expression expr)
				(loop for asgn in (assignments expr)
				      nconc (list (arguments asgn)
						  (expression asgn))))
				boundvars)))
	(if (null argument-templates)
	    (if (template? expr boundvars)
		(cons expr accum)
		accum)
	    (cons expr (append argument-templates accum)))))

(defmethod find-templates* ((expr list) boundvars &optional accum)
  (cond ((null expr) accum)
	(t (find-templates* (car expr) boundvars 
			   (find-templates* (cdr expr) boundvars accum)))))

(defmethod find-templates* ((expr name-expr) boundvars &optional accum)
  (if (and (variable? expr)
	   (subsetp boundvars
	       (list expr)
	       :key #'declaration))
      (cons expr accum)
      accum))

(defmethod find-templates* ((expr t) boundvars &optional accum)
  (declare (ignore boundvars))
  accum)



;(defmethod find-templates ((expr record-expr) boundvars &optional accum)
;  (let ((argument-templates
;	 (find-templates (assignments expr) boundvars)))
;    (if (null argument-templates)
;	(if (subsetp boundvars
;			(freevars expr)
;			:key #'declaration)
;	       (cons expr accum)
;	       accum)
;	(append argument-templates accum))))
;
;(defmethod find-templates ((expr tuple-expr) boundvars &optional accum)
;  (let ((argument-templates
;	 (find-templates (exprs expr) boundvars)))
;    (if (null argument-templates)
;	(if (subsetp boundvars
;			(freevars expr)
;			:key #'declaration)
;	       (cons expr accum)
;	       accum)
;	(append argument-templates accum))))
;
;(defmethod find-templates ((expr cases-expr) boundvars &optional accum)
;  (let ((argument-templates
;	 (find-templates (cons (expression expr)
;			       (append (mapcar #'expression
;					       (selections expr))
;				       (else-part expr)))
;				boundvars)))
;    (if (null argument-templates)
;	(if (subsetp boundvars
;			(freevars expr)
;			:key #'declaration)
;	       (cons expr accum)
;	       accum)
;	(append argument-templates accum))))
;
;(defmethod find-templates ((expr binding-expr) boundvars &optional accum)
;  (let ((argument-templates
;	 (find-templates  (expression expr) boundvars)))
;	(if (null argument-templates)
;	    (if (subsetp boundvars
;			 (freevars expr)
;			 :key #'declaration)
;		(cons expr accum)
;		accum)
;	    (append argument-templates accum))))
;
;(defmethod find-templates ((expr update-expr) boundvars &optional accum)
;  (let ((argument-templates
;	 (find-templates  (cons (expression expr)
;				(loop for asgn in (assignments expr)
;				      nconc (list (arguments asgn)
;						  (expression asgn))))
;				boundvars)))
;	(if (null argument-templates)
;	    (if (subsetp boundvars
;			 (freevars expr)
;			 :key #'declaration)
;		(cons expr accum)
;		accum)
;	    (append argument-templates accum))))
;
;(defmethod find-templates ((expr list) boundvars &optional accum)
;  (cond ((null expr) accum)
;	(t (find-templates (car expr) boundvars
;			   (find-templates (cdr expr) boundvars accum)))))
;
;;(defmethod find-templates ((expr name-expr) boundvars &optional accum)
;;  accum)
;
;;(defmethod find-templates ((expr expr) boundvars &optional accum)
;;  accum)
;
;(defmethod find-templates ((expr t) boundvars &optional accum)
;  accum)


;(defun find-templates (fmla  boundvars &optional accum)
;  (cond ((null fmla) accum)
;	((consp fmla)
;	 (find-templates (car fmla) boundvars
;			 (find-templates (cdr fmla) boundvars accum)))
;	((or (negation? fmla)
;	     (conjunction? fmla)
;	     (disjunction? fmla)
;	     (iff? fmla))
;	 (find-templates (arguments fmla) boundvars accum))
;	((or (implication? fmla)
;	     (branch? fmla))
;	 (find-templates (reverse (arguments fmla)) boundvars accum))
;	((or (equation? fmla)(disequation? fmla))
;	 (append (when (subsetp boundvars
;			      (freevars fmla)
;			      :key #'declaration)
;		   (list fmla))
;	 (find-templates (arguments fmla) boundvars  accum)))
;	(t (if (subsetp boundvars
;			(freevars fmla)
;			:key #'declaration)
;	       (cons fmla accum)
;	       accum))))

			 

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



(defun reveal-step (fnums)
  #'(lambda (ps)
      (let* ((sequent (current-goal ps))
	     (fnums (loop for fn in fnums
		    append (if (consp fn) fn (list fn))))
	     (hforms (select-seq (hidden-s-forms sequent) fnums)))
	(cond ((null hforms)
	       (values 'X nil))
	      (t 
	       (values '?
		       (list
			(copy sequent
			     's-forms (append hforms
					     (s-forms sequent))))))))))




(defun hide-step (sformnums)
  #'(lambda (ps)
      (let* ((sformnums (if (singleton? sformnums)
			    (car sformnums)
			    sformnums))
	     (sforms (select-seq (s-forms (current-goal ps))
				 sformnums))
	     (remaining-sforms (delete-seq (s-forms (current-goal ps))
					   sformnums))
	     (result (appendnew sforms
				(hidden-s-forms (current-goal ps))
				(make-trace 'proof-hole)
				:test
				#'(lambda (x y)
				    (and (subsetp (label x)(label y))
					 (tc-eq (formula x)(formula y))))))
	     (hforms (car result)))
	(cond ((null sforms)(values (cons 'X (make-trace 'empty 'np28)) nil))
	      (t (values (cons '? (cdr result))
			 (list (copy (current-goal ps)
				 's-forms remaining-sforms
				 'hidden-s-forms hforms))))))))

(defun appendnew (list1 list2 trace &key test)
  (if list1
      (let* ((result (appendnew (cdr list1) list2 trace :test test))
	     (rest (car result)))
	(if (member (car list1) rest
		    :test test)
	    (cons rest
		  (apply-trace trace
			       (list (make-trace 'weak-rule
						 (list (formula (car list1)))
						 (list (make-trace 'proof-hole))))))
	  (cons (cons (car list1) rest)
		trace)))
    (cons list2
	  trace)))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;substitution rule (1-7-91):
;; add-subst adds a substitution pair to the alist, the variable
;;part of the substitution must be a Skolem var.
;; apply-subst applies a substitution to the current goal and 
;;substitution.
;; apply-subst* applies all the substitutions.
	
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;add-subst should mainly check that there is no circularity in the 
;;;substitution
;	
;(addrule 'add-subst (varname term) nil (add-subst-rule varname term)
;	 "(add-subst <var> <term>): Adds the substitution to the
;current substitution alist.  See apply-subst.")
;
;(defun add-subst-rule (varname term)
;  (make-instance 'rule
;    :rule-part (add-subst-fun varname term)
;    :rule-input `(add-subst ,varname ,term)))
;
;(defun add-subst-fun (varname term)
;  #'(lambda (ps) (add-subst-step varname term ps)))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defun make-equality (lhs rhs)
  (make-equation lhs rhs))

;(defun add-subst-step (varname term ps)
;  (let ((var-rep (typecheck (pc-parse varname 'expr)
;			    :context *current-context*)))
;    ;;How should typecheck errors be handled here?
;    ;;(break)
;  (cond ((or (null var-rep)
;	     (not (skovar? var-rep)))
;	 (format t "~%~a is not a good Skolem variable.~%" varname)
;	 (values 'X nil nil)) ;;var not a Herbrand variable.
;	(t (let* ((term-rep (parse :string 
;				      (format nil "~a" term)
;				      :nt 'expr))
;		  (typed-term (typecheck term-rep
;				      :context *current-context*
;				      :expected (type var-rep))))
;	     (cond ((null typed-term) (values 'X nil nil))
;		   ((sub-occursin var-rep typed-term (substitution ps))
;		    (format t "~%Substitution violates occurs check.")
;		    (values 'X nil nil))
;		   (t
;		    (multiple-value-bind
;		     (signal subgoals subst updates)
;		     (do-assert (negate       ;;assert as an assumption
;				 (make-equality var-rep typed-term)) ps)
;		     (if (eq signal '!)
;			 (values '! nil
;				 (cons (cons var-rep typed-term)
;				       (substitution ps))
;				 updates)
;		       (values '? (list (current-goal ps))
;			       (cons (cons var-rep typed-term)
;				     (substitution ps))
;			       updates))))))))))

;(defun skovar? (x)    
;  (char= (char (string (id x)) 0) #\?))
;
;
;(defmethod sub-occursin (varname (term name-expr) subst)
;  (cond ((exequal varname term) t)
;	((not (skovar? term)) nil)
;	(t (let ((pair (assoc term subst :test #'exequal)))
;	     (if (null pair) nil
;		 (sub-occursin varname (cdr pair) subst))))))
;
;(defmethod sub-occursin (varname (term application) subst)
;  (or (sub-occursin varname (operator term) subst)
;      (loop for arg in (arguments term)
;	    thereis (sub-occursin varname arg subst))))
;
;(defmethod sub-occursin (varname (term binding-expr) subst)
;  (sub-occursin varname (expression term) subst))
;
;
;(defmethod sub-occursin (varname (term expr) subst)
;  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;apply-subst
;
;	
;(addrule 'apply-subst (varname) nil (apply-subst-rule varname)
;	 "(apply-subst <var>): Substitutes the binding for variable in the sequent.")
;
;(defun apply-subst-rule (varname )
;  (make-instance 'rule
;    :rule-part (apply-subst-fun varname)
;    :rule-input `(apply-subst ,varname)))
;
;(defun apply-subst-fun (varname )
;  #'(lambda (ps) (apply-subst-step varname ps)))
;
;(defun apply-subst-step (varname  ps)
;  (let ((pair (assoc varname (substitution ps)
;		     :test #'(lambda (x y)(eq x (id (name y)))))))
;    (cond ((null pair)
;	   (format t "~%No such substitution. ~%")
;	   (values 'X nil nil))
;	  (t (let* ((alist (list pair))
;		    (new-s-forms (loop for sform in (s-forms
;						     (current-goal ps))
;				       collect
;				       (copy sform 'formula
;					     (substit (formula sform)
;						      alist))))
;		    (new-subst (loop for sub in (substitution ps)
;				     collect (cons (car sub)
;						   (substit (cdr sub) alist)))))
;	   (values '?
;		     (list
;		      (copy (current-goal ps)
;			    's-forms
;			    new-s-forms))
;		     new-subst))))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;useful operations (courtesy Sam).
(defmethod args1 ((expr application))
  (args1* (argument expr)))

(defmethod args1 ((expr assignment))
  (car (arguments expr)))

(defmethod args1 ((expr projection-application))
  (args1* (argument expr)))

(defmethod args1 ((expr injection-application))
  (args1* (argument expr)))

(defmethod args1 ((expr injection?-application))
  (args1* (argument expr)))

(defmethod args1 ((expr extraction-application))
  (args1* (argument expr)))

(defmethod args1* ((expr tuple-expr))
  (car (exprs expr)))

(defmethod args1* (expr)
  expr)

(defmethod args2 ((expr application))
  (args2* (argument expr)))

(defmethod args2 ((expr projection-application))
  (args2* (argument expr)))

(defmethod args2 ((expr injection-application))
  (args2* (argument expr)))

(defmethod args2 ((expr injection?-application))
  (args2* (argument expr)))

(defmethod args2 ((expr extraction-application))
  (args2* (argument expr)))

(defmethod args2* ((expr tuple-expr))
  (cadr (exprs expr)))

(defmethod args2* (expr)
  (declare (ignore expr))
  nil)
