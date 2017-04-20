;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; -*- Mode: Lisp -*- ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; expand.lisp -- 
;; Author          : N. Shankar and Sam Owre
;; Created On      : Sat Oct 31 02:31:26 1998
;; Last Modified By: Sam Owre
;; Last Modified On: Thu May 20 21:20:29 2004
;; Update Count    : 2
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

(defvar *count-occurrences* 0)
(defvar *if-simplifies*)
(defvar *expand-in-actuals?* nil)
;(defvar *dependent-decls*)


(defun expand (name &optional sformnum occurrence if-simplifies
		    assert? actuals?)
  #'(lambda (ps)
      (expand-step name ps sformnum occurrence if-simplifies
		   assert? actuals?)))

(defun expand-step (name ps sformnum occurrence if-simplifies assert? actuals?)
  (let* ((goalsequent (current-goal ps))
	 (*assert-flag* (if (eq assert? 'none) 'none
			    (if assert? 'assert 'simplify)))
	 (*hash-rewrites?* t)
	 (*rewrite-hash* ;;if *hash-rewrites?*
	  (copy (rewrite-hash ps)))
	 (*sequent-typealist* nil)
	 ;(*quant-simp?* nil)
	 (sformnums (if (memq sformnum '(* + -))
			sformnum
		       (list sformnum)))
	 (sforms (s-forms goalsequent))
	 (lnames (if (listp name) name (list name)))
	 (nnames (mapcar #'(lambda (n)
			     (let ((nn (pc-parse n 'bname)))
			       (if (number-expr? nn)
				   (change-class nn 'name-expr 'id (number nn))
				   nn)))
		   lnames))
	 (occurrence (if (numberp occurrence)
			 (list occurrence)
			 occurrence))
	 (*max-occurrence* (if (consp occurrence)
			       (apply #'max occurrence)
			       0))
	 (*dependent-decls* nil)
	 (*if-simplifies* if-simplifies)
	 (*expand-in-actuals?* actuals?))
    (dolist (pname nnames)
      (when (and (name? pname)
		 (or (mod-id pname)
		     (actuals pname)
		     (mappings pname)
		     (target pname)))
	(pc-typecheck pname)))
    (cond ((not (or (null occurrence)
		    (and (listp occurrence)
			 (every #'(lambda (x)
				    (and (numberp x)
					 (plusp x)))
				occurrence))))
	   (error-format-if "Occurrence ~a must be nil, a positive number or a 
list of positive numbers" occurrence)
	   (values (cons 'X (make-trace 'not-implemented 'p284)) nil nil))
	  ((and occurrence
		(cdr nnames))
	   (error-format-if "Occurrence should not be given with multiple names")
	   (cons nil  (make-trace 'not-implemented '309)))
	  (t 
	   (let* ((result
		   (expand-sforms nnames sforms sformnums occurrence))
		  (new-sforms (car result)))
	     (cond ((every #'eq sforms new-sforms)
		    (values (cons 'X (make-trace 'not-implemented 'p312)) nil nil))
		   (t (mapcar #'(lambda (x)
				  (pushnew x (dependent-decls ps)))
			      *dependent-decls*)
		      (values (cons '? (cdr result))
			      (list
			       (list (lcopy goalsequent
					    's-forms new-sforms)
				     'dependent-decls
				     *dependent-decls*))))))))))

(defun expand-sforms (name sforms sformnums occurrence)
  (expand-sforms* name sforms (cleanup-fnums sformnums) occurrence +1 -1 nil
		  (make-trace 'proof-hole)))

(defun expand-sforms* (name sforms sformnums occurrence pos neg accum trace)
  (if (null sforms)
      (cons (nreverse accum) trace)
      (let* ((*count-occurrences* 0)
	     (fmla (formula (car sforms)))
	     (new-result
	      (if (in-sformnums? (car sforms) pos neg sformnums)
		  (expand-defn-i name fmla occurrence (make-ctx 'expr-hole *boolean*))
		(cons fmla (make-trace 'not-implemented 'p315))))
	     (new-fmla (car new-result))
	     )
	#+pvsdebug (assert (fully-instantiated? new-fmla))
	#+pvsdebug (assert (fully-typed? new-fmla))
	(if (eq fmla new-fmla)
	    (expand-sforms* name (cdr sforms)
			    sformnums occurrence
			    (if (not (negation? fmla))
				(1+ pos)
				pos)
			    (if (negation? fmla)
				(1- neg)
				neg)
			    (cons (car sforms) accum)
			    trace)
	    (multiple-value-bind (sig result)
		(if (eq *assert-flag* 'none)
		    (values (cons 'X (make-trace 'not-implemented 'p83))
			    new-fmla) ;;NSH(1/16/97): Myla Archer
		    ;;wanted no-simplification option.
		    (let ((*use-rationals* t))
		      (assert-if-inside new-fmla)))
	      (let ((new-sform (lcopy (car sforms)
				 'formula (if (eq (car sig) 'X)
					      new-fmla
					      result))))
		(if occurrence
		    (cons (append (nreverse accum)
				  (cons new-sform (cdr sforms)))
			  (apply-trace
				     trace
				     (list (apply-trace
					    (cdr new-result)
					    (list (cdr sig))))))
		    ;;since only one formula is
		    ;;processed when occurrence is
		    ;;given.  
		    (expand-sforms* name (cdr sforms)
				    sformnums occurrence
				    (if (not (negation? fmla))
					(1+ pos)
				      pos)
				    (if (negation? fmla)
					(1- neg)
				      neg)
				    (cons new-sform accum)
				    (apply-trace
				     trace
				     (list (apply-trace
					    (cdr new-result)
					    (list (cdr sig)))))))))))))

(defun match-defns (expr def-axioms)
  (cond ((null def-axioms) 'fail)
	(t (let* ((*modsubst* t)
		  (ax (car def-axioms))
		  (def-expr (if (forall-expr? ax)
				(expression ax)
				ax))
		  (lhs (args1 def-expr))
		  (rhs (args2 def-expr))
		  (sub 
		   (call-match lhs expr nil nil)))
	     (if (not (eq sub 'fail))
		 (values sub rhs)
		 'fail)))))


(defmethod expand-defn :around (name expr occurrence)
  (declare (ignore name expr occurrence))
  (assert nil))

(defmethod expand-defn-application :around (name expr occurrence)
  (declare (ignore name expr occurrence))
  (assert nil))


(defmethod expand-defn-i (name (expr projection-expr) occurrence ctx)
  (declare (ignore name occurrence ctx))
  (cons expr (make-trace 'proof-hole)))

(defmethod expand-defn-i (name (expr injection-expr) occurrence ctx)
  (declare (ignore name occurrence ctx))
  (cons expr (make-trace 'proof-hole)))

(defmethod expand-defn-i (name (expr injection?-expr) occurrence ctx)
  (declare (ignore name occurrence ctx))
  (cons expr (make-trace 'proof-hole)))

(defmethod expand-defn-i (name (expr extraction-expr) occurrence ctx)
  (declare (ignore name occurrence ctx))
  (cons expr (make-trace 'proof-hole)))

(defmethod expand-defn-i (name (expr projection-application) occurrence ctx)
  (declare (ignore ctx))
  (if (and (plusp *max-occurrence*)
	   (< *max-occurrence* *count-occurrences*))
      (cons expr (make-trace 'proof-hole))
      (let* ((arg (argument expr))
	     (newarg (car (expand-defn-i name arg occurrence
				       (make-ctx 'not-implemented 'c132)))))
	(cons (lcopy expr 'argument newarg) (make-trace 'not-implemented 'p313)))))

(defmethod expand-defn-i (name (expr injection-application) occurrence ctx)
  (declare (ignore ctx))
  (if (and (plusp *max-occurrence*)
	   (< *max-occurrence* *count-occurrences*))
      (cons expr (make-trace 'proof-hole))
      (let* ((arg (argument expr))
	     (newarg (car (expand-defn-i name arg occurrence
				       (make-ctx 'not-implemented 'c133)))))
	(cons (lcopy expr 'argument newarg) (make-trace 'not-implemented 'p316)))))

(defmethod expand-defn-i (name (expr injection?-application) occurrence ctx)
  (declare (ignore ctx))
  (if (and (plusp *max-occurrence*)
	   (< *max-occurrence* *count-occurrences*))
      (cons expr (make-trace 'proof-hole))
      (let* ((arg (argument expr))
	     (newarg (car (expand-defn-i name arg occurrence
				       (make-ctx 'not-implemented 'c134)))))
	(cons (lcopy expr 'argument newarg) (make-trace 'not-implemented 'p317)))))

(defmethod expand-defn-i (name (expr extraction-application) occurrence ctx)
  (declare (ignore ctx))
  (if (and (plusp *max-occurrence*)
	   (< *max-occurrence* *count-occurrences*))
      (cons expr (make-trace 'proof-hole))
      (let* ((arg (argument expr))
	     (newarg (car (expand-defn-i name arg occurrence
				       (make-ctx 'not-implemented 'c135)))))
	(cons (lcopy expr 'argument newarg) (make-trace 'not-implemented 'p318)))))

(defmethod expand-defn-i (name (expr field-application) occurrence ctx)
  (declare (ignore ctx))
  (if (and (plusp *max-occurrence*)
	   (< *max-occurrence* *count-occurrences*))
      (cons expr (make-trace 'proof-hole))
      (let* ((arg (argument expr))
	     (newarg (car (expand-defn-i name arg occurrence
				       (make-ctx 'not-implemented 'c136)))))
	(cons (lcopy expr 'argument newarg) (make-trace 'not-implemented 'p319)))))

(defmethod expand-defn-i (name (expr application) occurrence ctx)
  (if (and (plusp *max-occurrence*)
	   (< *max-occurrence* *count-occurrences*))
      (cons expr (make-trace 'proof-hole))
      (let* ((op* (operator* expr)))
	(if (and (name? op*)
		 (same-expand-name op* name)
		 (null occurrence)
		 *if-simplifies*)
	    (let* ((def-axioms (create-formulas (resolution op*))))
	      (multiple-value-bind (subst rhs)
		  (match-defns expr def-axioms)
		(if (not (eq subst 'fail))
		    (let* ((xsubst
			    (loop for (x . y) in subst
				  collect
				  (cons x (car (expand-defn-i name y occurrence
							    (make-ctx 'not-implemented 'c137))))))
			   (subexpr (substit rhs xsubst)))
		      (multiple-value-bind (sig value)
			  (lazy-assert-if-i subexpr (make-ctx 'not-implemented 'c53))
			(cond ((and (or (typep subexpr 'cases-expr)
					(branch? subexpr))
				    (eq (car sig) 'X))
			       (cons (car (expand-defn-application-i name expr
								   occurrence
								   (make-ctx 'not-implemented 'c138)))
				      (make-trace 'not-implemented 'p320)))
			      (t (pushnew (declaration (resolution op*))
					  *dependent-decls*)
				 (cons value (make-trace 'not-implemented 'p321))))))
		  (cons (car (expand-defn-application-i name expr occurrence
						      (make-ctx 'not-implemented 'c139)))
			 (make-trace 'not-implemented 'p322)))))
	  (expand-defn-application-i name expr occurrence ctx)))))

; (defmethod expand-defn-i (name (expr infix-application) occurrence)
;   (let ((nexpr (call-next-method)))
; ;    (unless (eq nexpr expr)
; ;      (setf (parens nexpr) 1))
;     nexpr))
				       
(defmethod expand-defn-application-i (name (expr application) occurrence ctx)
  (let* ((oper (operator expr))
	 (arg (argument expr))
	 (op* (operator* expr))
	 (resoper (expand-defn-i name oper occurrence
				 (apply-ctx ctx
					    (list (make-ctx
						   'application
						   (list (make-ctx 'expr-hole (type oper))
							 (make-ctx 'expr arg)))))))
	 (newoper (car resoper))
	 (resargs (expand-defn-i name arg occurrence
				 (apply-ctx ctx
					    (list (make-ctx
						   'application
						   (list (make-ctx 'expr newoper)
							 (make-ctx 'expr-hole (type arg))))))))
	 (newargs (car resargs)))
    (if (and (not (eq oper newoper))
	     (typep  op* 'name-expr)
	     (same-expand-name op* name)
	     (typep newoper 'lambda-expr))
	(let* ((ressubst
		(cond ((singleton? (bindings newoper))
		       (substit-with-proofs (expression newoper)
					    (acons (car (bindings newoper)) newargs nil)
					    ctx))
		      (t
		       (substit-with-proofs (expression newoper)
					    (pairlis-args (bindings newoper)
							  (argument-list newargs))
					    ctx))))
	       (compsubst
		(cond ((singleton? (bindings newoper))
		       (compute-substit (expression newoper)
					    (acons (car (bindings newoper)) newargs nil)))
		      (t
		       (compute-substit (expression newoper)
					    (pairlis-args (bindings newoper)
							  (argument-list newargs)))))))
	  (cons (car ressubst)
		(apply-trace
		 (cdr resoper)
		 (list (apply-trace
			(cdr resargs)
			(list (make-trace
			       'rewrite-rule
			       (list ctx
				     compsubst
				     (compute-application newoper newargs))
			       (list (cdr ressubst)))))))))
      (if (and (eq oper newoper)
	       (eq arg newargs))
	    (cons expr (make-trace 'proof-hole))
	    (let* ((stype (find-supertype (type newoper)))
		   (result
		    (simplify-or-copy-app
		     expr newoper newargs
		     (if (typep (domain stype) 'dep-binding)
			 (substit (range stype)
				  (acons (domain stype) newargs nil))
		       (range stype))))
		   (nex (car result)))
	      (unless (eq newoper (operator expr))
		(change-application-class-if-necessary expr nex))
	      (cons nex
		    (apply-trace
			(cdr resoper)
			(list (apply-trace
			       (cdr resargs)
			       (list (cdr result)))))))))))

(defmethod expand-defn-application-i (name (expr infix-application) occurrence ctx)
  (if (and occurrence
	   ;; Check that it prints as an infix
	   (valid-infix-application? expr))
      (let* ((oper (operator expr))
	     (lhs (args1 expr))
	     (rhs (args2 expr))
	     (reslhs (expand-defn-i name lhs occurrence
				    (apply-ctx
				     ctx
				     (list
				      (make-ctx 'application
						(list (make-ctx 'expr oper)
						      (make-ctx 'tuple
								(list
								 (make-ctx 'expr-hole (type lhs))
								 (make-ctx 'expr rhs)))))))))
	     (newlhs (car reslhs))
	     (resoper (expand-defn-i name oper occurrence (make-ctx 'not-implemented 'c144)))
	     (newoper (car resoper))
	     (resrhs (expand-defn-i name rhs occurrence (make-ctx 'not-implemented 'c145)))
	     (newrhs (car resrhs)))
	(if (and (eq oper newoper)
		 (eq lhs newlhs)
		 (eq rhs newrhs))
	    (cons expr (make-trace 'proof-hole))
	    (if (typep newoper 'lambda-expr)
		(cons (substit (expression newoper)
			       (pairlis-args (bindings newoper)
					     (list newlhs newrhs)))
		       (make-trace 'not-implemented 'p343))
		(let* ((stype (find-supertype (type newoper)))
		       (newargs (make!-arg-tuple-expr newlhs newrhs))
		       (result (simplify-or-copy-app
				expr newoper newargs
				(if (typep (domain stype) 'dep-binding)
				    (substit (range stype)
					     (acons (domain stype) newargs nil))
				  (range stype))))
		       (nex (car result)))
		  (unless (eq newoper (operator expr))
		    (change-application-class-if-necessary expr nex))
		  (cons nex
			(apply-trace
			 (cdr reslhs)
			 (list (apply-trace
				(cdr resoper)
				(list (apply-trace
				       (cdr resrhs)
				       (list (cdr result))))))))))))
      (call-next-method)))


(defmethod expand-defn-i (name (expr name-expr) occurrence ctx)
  (if (and (plusp *max-occurrence*)
	   (< *max-occurrence* *count-occurrences*))
      (cons expr (make-trace 'proof-hole))
      (cond ((same-expand-name expr name)
	     (setf *count-occurrences* (1+ *count-occurrences*))
	     (if (or (null occurrence)
		     (member *count-occurrences* occurrence
			     :test #'eql))
		 (cond ((def-axiom (declaration expr))
			(let ((rhs (args2
				    (subst-mod-params
				     (car (last (def-axiom
						  (declaration expr))))
				     (module-instance (resolution expr))
				     (module (declaration expr))
				     (declaration expr)))))
			  (cond ((not *if-simplifies*)
				 (pushnew (declaration expr)
					  *dependent-decls*)
				 (when
				     (not (and (def-decl? (declaration expr))
					       (measure (declaration expr))))
				   ;; (unless (tc-eq (compute-normalize rhs)
				   ;; 		  (compute-normalize expr))
				   ;;   (show (declaration expr))
				   ;;   (assert nil))
				   )
				 (cons rhs
				       (make-trace 'rewrite-rule2
						   (list ctx
							 rhs
							 expr
							 (not (and (def-decl? (declaration expr))
								   (measure (declaration expr)))))
						   (list (make-trace 'proof-hole)))))
				((typep rhs 'lambda-expr)
				 (cons expr (make-trace 'proof-hole)))
				((or (typep rhs 'cases-expr)
				     (branch? rhs))
				 (multiple-value-bind
				     (sig result)
				     (lazy-assert-if-i rhs (make-ctx 'not-implemented 'c130))
				   (cond ((eq (car sig) 'X)
					  (cons expr (make-trace 'proof-hole)))
					 (t (pushnew (declaration expr)
						     *dependent-decls*)
					    (cons result (make-trace 'not-implemented 'p325))))))
				(t (pushnew (declaration expr)
					    *dependent-decls*)
				   (cons rhs (make-trace 'not-implemented 'p326))))))
		       ((mappings (module-instance expr))
			(cons (subst-mod-params expr (module-instance expr))
			       (make-trace 'not-implemented 'p327)))
		       (t (cons expr (make-trace 'proof-hole))))
		 (cons expr (make-trace 'proof-hole))))
	    ((and *expand-in-actuals?*
		  (or (actuals expr)
		      (mappings expr)))
	     (let ((eacts (car (expand-defn-i name (actuals expr) occurrence
					    (make-ctx 'not-implemented 'c146))))
		   (emaps (car (expand-defn-i name (mappings expr) occurrence
					    (make-ctx 'not-implemented 'c147)))))
	       (if (and (eq eacts (actuals expr))
			(eq emaps (mappings expr)))
		   (cons expr (make-trace 'proof-hole))
		   (let* ((thinst (copy (module-instance expr)
				    'actuals eacts 'mappings emaps))
			  (res (make-resolution (declaration expr) thinst)))
		     (cons (copy expr
				 'actuals eacts
				 'mappings emaps
				 'resolutions (list res))
			   (make-trace 'not-implemented 'p328))))))
	    (t (cons expr (make-trace 'proof-hole))))))

(defmethod expand-defn-i (name (expr actual) occurrence ctx)
  (declare (ignore ctx))
  (if (type-value expr)
      (cons expr (make-trace 'proof-hole))
    (cons (lcopy expr
		 'expr (car (expand-defn-i name (expr expr) occurrence
					 (make-ctx 'not-implemented 'c148))))
	  (make-trace 'not-implemented 'p329))))

(defmethod expand-defn-i (name (expr mapping) occurrence ctx)
  (declare (ignore ctx))
  (cons (lcopy expr
	       'rhs (car (expand-defn-i name (rhs expr) occurrence
				      (make-ctx 'not-implemented 'c149))))
	(make-trace 'not-implemented 'p330)))

(defmethod expand-defn-i (name (expr binding-expr) occurrence ctx)
  (if (and (plusp *max-occurrence*)
	   (< *max-occurrence* *count-occurrences*))
      (cons expr (make-trace 'proof-hole))
    (let ((result
	   (expand-defn-i name (expression expr) occurrence
			  (cond ((forall-expr? expr)
				 (apply-ctx
				  ctx
				  (list (make-ctx 'forall
						  (list (make-ctx 'expr-hole
								  (type (expression expr))))
						  (list (bindings expr))))))
				((exists-expr? expr)
				 (apply-ctx
				  ctx
				  (list (make-ctx 'exists
						  (list (make-ctx 'expr-hole
								  (type (expression expr))))
						  (list (bindings expr))))))				(t
				 (make-ctx 'not-implemented 'c150))))))
      (cons (lcopy expr
		   'expression (car result))
	    (cdr result)))))

(defmethod expand-defn-i (name (expr lambda-expr) occurrence ctx)
  (if (and (plusp *max-occurrence*)
	   (< *max-occurrence* *count-occurrences*))
      (cons expr (make-trace 'proof-hole))
    (let* ((res-expr
	    (expand-defn-i name (expression expr) occurrence
			   (apply-ctx
			    ctx
			    (list (make-ctx 'lambda
					    (list (make-ctx 'expr-hole
							    (type (expression expr))))
					    (list (bindings expr)))))))
	   (exp-expr (car res-expr)))
	(if (eq exp-expr (expression expr))
	    (cons expr (make-trace 'proof-hole))
	  (cons (copy expr
		      'expression exp-expr
		      'type (if (tc-eq (range (type expr)) (type exp-expr))
				(type expr)
			      (lcopy (type expr) 'range (type exp-expr))))
		(cdr res-expr))))))

(defmethod expand-defn-i (name (expr tuple-expr) occurrence ctx)
  (if (and (plusp *max-occurrence*)
	   (< *max-occurrence* *count-occurrences*))
      (cons expr (make-trace 'proof-hole))
    (let* ((nresults (expand-defn-i name (exprs expr) occurrence
				    (apply-ctx ctx
					       (list
						(make-ctx 'tuple
							  (mapcar
							   #'(lambda (ex)
							       (make-ctx 'expr-hole (type ex)))
							   (exprs expr)))))))
	   (nexprs (car nresults)))
	(if (eq nexprs (exprs expr))
	    (cons expr (make-trace 'proof-hole))
	  (cons (copy expr
		      'exprs nexprs
		      'type (mk-tupletype (mapcar #'type nexprs)))
		(cdr nresults))))))

(defmethod expand-defn-i (name (expr record-expr) occurrence ctx)
  (declare (ignore ctx))
  (if (and (plusp *max-occurrence*)
	   (< *max-occurrence* *count-occurrences*))
      (cons expr (make-trace 'proof-hole))
    (cons (lcopy expr
		 'assignments
		 (car (expand-defn-i name (assignments expr) occurrence
				   (make-ctx 'not-implemented 'c153))))
	   (make-trace 'not-implemented 'p334))))

(defmethod expand-defn-i (name (expr assignment) occurrence ctx)
  (declare (ignore ctx))
  (cons (lcopy expr
	       'arguments (car (expand-defn-i name (arguments expr) occurrence
					    (make-ctx 'not-implemented 'c154)))
	       'expression (car (expand-defn-i name (expression expr) occurrence
					     (make-ctx 'not-implemented 'c155))))
	 (make-trace 'not-implemented 'p335)))

(defmethod expand-defn-i (name (expr field-assignment-arg) occurrence ctx)
  (declare (ignore name occurrence ctx))
  (cons expr (make-trace 'proof-hole)))

(defmethod expand-defn-i (name (expr list) occurrence ctx)
  (cond ((null expr) 
	 (cons expr (make-trace 'proof-hole)))
	(t
	 (let* ((rescar
		 (expand-defn-i name (car expr)
				occurrence
				(apply-ctx ctx
					   (cons (make-ctx 'expr-hole (type (car expr)))
						 (mapcar #'(lambda (ex)
							     (make-ctx 'expr ex))
							 (cdr expr))))))
		(newcar (car rescar))
		(rescdr
		 (expand-defn-i name (cdr expr)
				occurrence
				(apply-ctx ctx
					   (cons (make-ctx 'expr newcar)
						 (mapcar #'(lambda (ex)
							     (make-ctx 'expr-hole (type ex)))
							 (cdr expr))))))
		(newcdr (car rescdr)))
	   (if (and (eq (car expr) newcar) (every #'eq (cdr expr) newcdr))
	       (cons expr (make-trace 'proof-hole))
	     (cons (cons newcar newcdr)
		   (apply-trace (cdr rescar)
				(list (cdr rescdr)))))))))

(defmethod expand-defn-i (name (expr update-expr) occurrence ctx)
  (declare (ignore ctx))
  (if (and (plusp *max-occurrence*)
	   (< *max-occurrence* *count-occurrences*))
      (cons expr (make-trace 'proof-hole))
    (cons (lcopy expr
		 'expression (car (expand-defn-i name (expression expr) occurrence
					       (make-ctx 'not-implemented 'c157)))
		 'assignments (car (expand-defn-i name (assignments expr) occurrence
						(make-ctx 'not-implemented 'c158))))
	   (make-trace 'not-implemented 'p338))))

(defmethod expand-defn-i (name (expr cases-expr) occurrence ctx)
  (declare (ignore ctx))
  (if (and (plusp *max-occurrence*)
	   (< *max-occurrence* *count-occurrences*))
      (cons expr (make-trace 'proof-hole))
    (cons (lcopy expr
		 'expression (car (expand-defn-i name (expression expr) occurrence
					       (make-ctx 'not-implemented 'c159)))
		 'selections (car (expand-defn-i name (selections expr) occurrence
					       (make-ctx 'not-implemented 'c160)))
		 'else-part (car (expand-defn-i name (else-part expr) occurrence
					      (make-ctx 'not-implemented 'c161))))
	   (make-trace 'not-implemented 'p339))))

(defmethod expand-defn-i (name (expr selection) occurrence ctx)
  (declare (ignore ctx))
  (cons (lcopy expr
	       'expression (car (expand-defn-i name (expression expr) occurrence
					     (make-ctx 'not-implemented 'c162))))
	 (make-trace 'not-implemented 'p340)))

(defmethod expand-defn-i (name (expr expr) occurrence ctx)
  (declare (ignore name occurrence ctx))
  (cons expr (make-trace 'proof-hole)))

;;; Compares the tgt-name from the sequent to the pat-name given by the user
;;; Whatever is not nil in the pat-name must match.
(defun same-expand-name (tgt-name pat-names)
  (and pat-names
       (or (same-expand-name* tgt-name (car pat-names))
	   (same-expand-name tgt-name (cdr pat-names)))))

(defun same-expand-name* (tgt-name pat-name)
  (and (eq (id tgt-name) (id pat-name))
       (or (null (library pat-name))
	   (eq (library tgt-name) (library pat-name))
	   (and (resolution pat-name)
		(eq (library tgt-name) (library (module-instance pat-name)))))
       (or (null (mod-id pat-name))
	   (eq (id (module-instance tgt-name)) (mod-id pat-name))
	   (and (resolution pat-name)
		(eq (id (module-instance tgt-name))
		    (id (module-instance pat-name)))))
       (or (null (actuals pat-name))
	   (tc-eq (actuals (module-instance tgt-name)) (actuals pat-name))
	   (and (resolution pat-name)
		(tc-eq (actuals (module-instance tgt-name))
		       (actuals (module-instance pat-name)))))
       (or (null (mappings pat-name))
	   (tc-eq (mappings tgt-name) (mappings pat-name))
	   (and (resolution pat-name)
		(tc-eq (mappings tgt-name)
		       (mappings (module-instance pat-name)))))
       (or (null (target pat-name))
	   (tc-eq (target tgt-name) (target pat-name))
	   (and (resolution pat-name)
		(tc-eq (target tgt-name)
		       (target (module-instance pat-name)))))))
