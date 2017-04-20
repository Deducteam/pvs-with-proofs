;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; -*- Mode: Lisp -*- ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; assert.lisp -- 
;; Author          : Natarajan Shankar
;; Created On      : Fri Oct  8 12:10:11 1993
;; Last Modified By: Sam Owre
;; Last Modified On: Thu May 20 16:38:12 2004
;; Update Count    : 104
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

;;assert-sformnums calls sequent-reduce with a list of sformnums and
;;invokes assert-sform on each selected sform.  assert-sform invokes
;;the decision procedure on each sform.  rewrite-flag is used to direct
;;simplification to only the lhs or rhs of a rewrite so that a match
;;is not destroyed through simplification.  flush? = T flushes the
;;ground-prover database for a fresh start.  linear? = T makes nonlinear
;;multiplication uninterpreted.  flag is either note, simplify,
;;assert, or *rewrite.

(defun invoke-simplification (sformnums record? rewrite?
				   rewrite-flag flush? linear?
				   cases-rewrite? type-constraints?
				   ignore-prover-output? let-reduce?
				   quant-simp? implicit-typepreds?
				   ignore-typepreds?)
  #'(lambda (ps)
      (let ((*cases-rewrite* cases-rewrite?)
	    (*false-tcc-error-flag* nil)
	    (*ignore-prover-output?* ignore-prover-output?)
	    (*ignore-typepreds?* ignore-typepreds?)
	    (*let-reduce?* let-reduce?)
	    (*quant-simp?* quant-simp?)
	    (*implicit-typepreds?* implicit-typepreds?))
	(if record?
	    (if rewrite?
		(assert-sformnums
		 sformnums rewrite-flag flush? linear? nil
		 t type-constraints? ps)
		(assert-sformnums
		 sformnums rewrite-flag flush? linear? 'record
		 t type-constraints? ps))
	    (if rewrite?
		(assert-sformnums
		 sformnums rewrite-flag flush? linear? 'rewrite
		 t type-constraints? ps)
		(assert-sformnums
		 sformnums rewrite-flag flush? linear? 'simplify
		 t type-constraints? ps))))))
      

;; (defparameter *countxyz* 0)

(defun assert-sformnums (sformnums 
			 rewrite-flag flush? linear?
			 flag hash-rewrites?
			 type-constraints? ps)
  (let* ((*printerpmult* (if linear? 'normal *printerpmult*))
	 (*printerpdivide* (if linear? 'no *printerpdivide*))
	 ;; translate-to-prove adds to this from the sequent, e.g.,
	 ;; hypothesis integer_pred(x), where x is of type real.
	 (*sequent-typealist* nil)
	 (*assert-flag* flag)
	 (*top-assert-flag* flag)
	 (*process-output* nil)
	 (goalsequent (current-goal ps))
	 (*dependent-decls* nil)
	 (*hash-rewrites?* hash-rewrites?)
	 (*rewrite-hash* (if *hash-rewrites?*
			     (copy (rewrite-hash ps))
			     (rewrite-hash ps)))
	 (*subtype-hash* (if flush?
			     (make-pvs-hash-table)
			     (copy (subtype-hash ps))))
	 (*assert-typepreds-off* (not type-constraints?))
	 (*dp-state* (dp-state ps)))
    ;; (setq *countxyz* (+ *countxyz* 1))
    (unwind-protect
	(protecting-cong-state
	 ((*dp-state* (if flush?
			  *init-dp-state*
			  *dp-state*)))
	 (assert-sequent goalsequent sformnums rewrite-flag))
      (when *subst-type-hash*
	(cons (clrhash *subst-type-hash*)
	      (make-trace 'not-implemented 'p46))))))

(defun assert-sequent (sequent sformnums &optional rewrite-flag)
  (let* ((quant-sformnums
	  (find-all-sformnums (s-forms sequent) sformnums
			      #'top-quant?))
	 (simplifiable-sformnums
	  (find-all-sformnums (s-forms sequent) sformnums
			      #'(lambda (fmla)
				  (if (negation? fmla)
				      (connective-occurs? (args1 fmla))
				      (connective-occurs? fmla)))))
	 (other-sformnums
	  (find-remaining-sformnums (s-forms sequent) sformnums
				    (append quant-sformnums
					    simplifiable-sformnums))))
    (multiple-value-bind (signal subgoal)
	(sequent-reduce-with-proofs sequent
			#'(lambda (sform) (assert-sform sform rewrite-flag))
			other-sformnums)
	 (cond ((eq (car signal) '!)
	     (dpi-pop-state *dp-state*)
	     (values (cons '! (cdr signal))
		     nil
		     (list 'dependent-decls *dependent-decls*)))
	    (t (multiple-value-bind (qsignal qsubgoal)
		   (sequent-reduce-around
		    (if (eq (car signal) 'X) sequent subgoal)
		    #'(lambda (sform) (assert-sform sform rewrite-flag))
		    quant-sformnums)
		 (cond ((eq (car qsignal) '!)
			(dpi-pop-state *dp-state*)
			(values (cons '!
				      (apply-trace
				       (cdr signal)
				       (list (cdr qsignal))))
				nil
				(list 'dependent-decls *dependent-decls*)))
		       (t (multiple-value-bind (newsignal newsubgoal)
			      (if (eq *assert-flag* 'record)
				  (values (cons 'X
						(make-trace 'not-implemented 'p69))
					  (if (and (eq (car signal) 'X)(eq (car qsignal) 'X))
					      sequent qsubgoal))
				  (sequent-reduce-around
				   (if (and (eq (car signal) 'X)(eq (car qsignal) 'X))
				       sequent
				       qsubgoal)
				   #'(lambda (sform)
				       (assert-sform sform
						     rewrite-flag
						     t))
				   simplifiable-sformnums))
			    (cond ((eq (car newsignal) '!)
				   (dpi-pop-state *dp-state*)
				   (values (cons '!
						 (apply-trace
						  (cdr signal)
						  (list (apply-trace
							 (cdr qsignal)
							 (list (cdr newsignal))))))
					   nil
					   (list 'dependent-decls
						 *dependent-decls*)))
				  ((and (eq (car signal) 'X)
					(eq (car qsignal) 'X)
					(eq (car newsignal) 'X))
				   (values (cons 'X (make-trace 'empty 'np20))
					   nil
					   nil))
				  (t
				     (values
				      (cons '? (apply-trace
						  (cdr signal)
						  (list (apply-trace
							 (cdr qsignal)
							 (list (cdr newsignal))))))
				      (list
				       (cons newsubgoal 
					     (list 'rewrite-hash *rewrite-hash*
						   'subtype-hash *subtype-hash*
						   'dependent-decls
						   *dependent-decls*
						   'dp-state
						   *dp-state*)))))))))))))))

;;this is needed to take care of the output from process.
(defun sequent-reduce-around (sequent simplifier sformnums)
  (multiple-value-bind (signal newsequent)
      (sequent-reduce-with-proofs sequent simplifier sformnums)
    (cond ((eq (car signal) '!)
	   (values signal newsequent))
	  ((or (memq *assert-flag* '(simplify rewrite))
	       *ignore-prover-output?*)
	   (values signal newsequent))
	  (t (assert-process-output signal newsequent)))))

(defun assert-process-output (signal sequent)
  (nprotecting-cong-state
   ((*dp-state* *dp-state*))
   (let ((result (catch 'context (process-assert *process-output*))))
     (if (false-p result)
	 (values ;; (assert (and 'assert1 nil));; FG to be modified later
		 (cons '!
		       (make-trace 'not-implemented 'p1)
		       ;; (make-trace
		       ;; 	'typepred-rule
		       ;; 	(list (list *true*))
		       ;; 	(list (make-trace 'true-rule)))
		       )
		 sequent)
       (values signal sequent)))))

;;; Forms here is a list of terms of the underlying decision procedure
;;; Hence dpi-process-term is invoked rather than call-process (which
;;; invokes dpi-process).

(defun process-assert (forms)
  (if (null forms)
      nil
      (let* ((fmla (car forms))
	     ;;(op (when (consp fmla) (car fmla)))
	     )
	(cond ((dpi-disjunction? fmla) ;(eq op 'or)
	       (when (loop for x in (dpi-term-arguments fmla) ;(cdr fmla)
			   always (nprotecting-cong-state
				   ((*dp-state* *dp-state*))
				   (let* ((result
					   (catch 'context 
					     (process-assert
					      (cons x (cdr forms))))))
				     (false-p result))))
		 (retfalse)))
	      ((dpi-proposition? fmla) ;(memq op '(if if* implies not and iff))
	       (process-assert (cdr forms)))
	      (t (let ((result (call-process fmla *dp-state*)))
		   (if (false-p result)
		       (throw 'context *false*)
		       (process-assert (cdr forms)))))))))

(defmethod unit-recognizer? (rec) ;recognizer for 0-ary constructor.
  (declare (ignore rec))
  nil)

(defmethod unit-recognizer? ((rec recognizer-name-expr))
  (if (eq (unit? rec) 'unbound)
      (setf (unit? rec)
	    (let* ((constructor (constructor rec))
		   (accessors (accessors constructor)))
	      (when (null accessors) constructor)))
      (unit? rec)))

(defun unit-derecognize (expr)
  (cond ((negation? expr)
	 (car (negate-with-proofs (unit-derecognize (args1 expr)))))
	((application? expr)
	 (let ((unit (unit-recognizer? (operator expr))))
	   (if (or (not unit)(tc-eq (args1 expr) unit))
	       expr
	       ;;multiple-value-bind (sig fmla);;assert-if too slow
	       ;;  (assert-if unit);;to get its subtype constraint.
	       (progn (record-type-constraints unit)
		      (make!-equation (args1 expr) unit)))))
	(t expr)))

(defun assert-sform (sform &optional rewrite-flag simplifiable?)
  (let ((*assert-typepreds* nil)
	(*auto-rewrite-depth* 0)
	(*use-rationals* t))
    (multiple-value-bind (signal sform)
	(assert-sform* sform rewrite-flag simplifiable?)
	(cond ((eq (car signal) '!)
	       (values (cons (car signal)
			     (cdr signal))
		       sform))
	      ((or (eq (car signal) '?) *assert-typepreds*)
	       ;;(break "assert-typepreds")
	       ;; For some formulas (e.g., large, with lots of arithmetic)
	       ;; the *assert-typepreds* can get very large, and take
	       ;; a long time to process; hence the *ignore-typepreds?* flag.
	       (if (and (null *ignore-typepreds?*)
			(some #'process-typepred *assert-typepreds*))
		   (values (cons '!
				 (apply-trace (cdr signal)
					      (list (make-trace 'deep-trusted-rule
								(list (make-ctx 'expr-hole *boolean*)
								      'hashed
								      *true* (formula sform))
								(list (make-trace 'true-rule))))))
			   sform)
		 (values (cons '? (cdr signal)) sform))) ; should be signal, but fails for the example
					; from Cesar 2012-12-10/aaaa.pvs
	      (t (values signal sform))))))

(defun process-typepred (fmla)
  (let* ((sign (not (negation? fmla)))
	 (body (if sign fmla (args1 fmla))))
    (and (not (connective-occurs? body))
	 (let* ((res (call-process fmla *dp-state*)))
	   (when (and (consp res)
		      (not (update-or-connective-occurs? body)))
	     (loop for x in res
		   do (push x *process-output*)))
	   (false-p res)))))

(defun assert-typepreds (typepreds)
  (when (consp typepreds)
    (let* ((fmla (car typepreds))
	   (sign (not (negation? fmla)))
	   (body (if sign fmla (args1 fmla))))
      (or (and (not (update-or-connective-occurs? body))
	       (let* ((res (call-process fmla *dp-state*)))
		 (when (consp res)
		   (loop for x in res
			 do (push x *process-output*)))
		 (false-p res)))
	  (assert-typepreds (cdr typepreds))))))

(defun assert-sform* (sform &optional rewrite-flag simplifiable?)
  (let* ((fmla (formula sform))
	 (sign (not (negation? fmla)))
	 (body (if sign fmla (args1 fmla)))
	 (*bound-variables* nil)
	 (*top-rewrite-hash* *rewrite-hash*)
	 (*top-dp-state* *dp-state*)
	 (ctx
	  (if sign
	      (make-ctx 'expr-hole *boolean*);;positif
	    (make-ctx 'negation (list (make-ctx 'expr-hole *boolean*))))));;negatif
    ;;(break "0")
    (cond (rewrite-flag
	   (multiple-value-bind (sig newbodypart)
	       (if (or (iff? body)(equation? body))
		   (if (eq rewrite-flag 'rl)
		       (assert-if-i (args1 body) (make-ctx 'not-implemented 'c54));;caution sign
		     (assert-if-i (args2 body)
				  (apply-ctx
				   ctx
				   (list
				    (make-ctx
				     'application
				     (list (make-ctx 'expr (operator body))
					   (make-ctx 'tuple
						     (list
						      (make-ctx 'expr (args1 body))
						      (make-ctx 'expr-hole
								(type (args2 body)))))))))))
		   (values (cons 'X (make-trace 'not-implemented 'p177)) body))
	     (if (eq (car sig) 'X)
		 (if (or (and sign (tc-eq fmla *false*))
			 (and (not sign)(tc-eq body *true*)))
		     (values (cons '?
				   (make-trace 'not-implemented 'p4))
			     nil)
		   (values (cons 'X (make-trace 'proof-hole)) sform))
		 (let ((newbody
			(copy body
			  'argument
			  (make!-arg-tuple-expr*
			   (if (eq rewrite-flag 'rl)
			       (list newbodypart (args2 body))
			       (list (args1 body) newbodypart))))))
		   (values (cons '? (cdr sig))
			   (copy sform
				'formula
				(if sign newbody
				    (copy fmla
				      'argument
				      newbody))))))))
	  (simplifiable?		;(connective-occurs? body)
	   (multiple-value-bind (sig newfmla)
	       ;;NSH(7.27.96): I've been going back and forth
	       ;;on  assert-if-inside vs. assert-if here.
	       ;;assert-if fails because for an enum type
	       ;;red?(expr) triggers check-all-recognizers
	       ;;which causes self-simplification.  I don't
	       ;;recall when assert-if-inside misbehaves.
	       (if (if sign (application? fmla)
		     (application? (args1 fmla)))
		   (assert-if-inside fmla)
		 (multiple-value-bind (nsig nnewfmla)
				      (assert-if-i fmla (make-ctx 'not-implemented 'c3));;sign?
				      (values (cons (car nsig)
						    (make-trace 'not-implemented 'p10))
					      nnewfmla)))
	       (cond ((eq (car sig) 'X)
		      (if (or (and sign (tc-eq fmla *false*))
			    (and (not sign)(tc-eq body *true*)))
			(values (cons '?
				      (make-trace 'not-implemented 'p62))
				nil)
		      (values (cons 'X (make-trace 'proof-hole)) sform)))
		   ((and (not (eq *assert-flag* 'simplify))
			 (not (connective-occurs? newfmla)))
		    (process-sform sform newfmla sig))
		   (t (values (cons '? (cdr sig))
			      (copy sform 'formula newfmla))))))
	  (t				;(break "1")
	   (multiple-value-bind (sig newfmla)
	       (assert-if-inside fmla)
					;(break "2")
	     (if (or (connective-occurs? newfmla)
		     (memq *assert-flag* '(simplify rewrite)))
		 (values sig (if (eq (car sig) '?) (copy sform
						     'formula newfmla)
				 sform))
	       (process-sform sform
			      (if (eq (car sig) '?) newfmla fmla)
			      sig)))))))

;; newfmla, sig = simplification of (formula sform)
(defun process-sform (sform newfmla sig)
  ;;(when (connective-occurs? newfmla)(break))
  (let* ((*bindings* nil)
	 (neg-result (negate-with-proofs newfmla))
	 (result (call-process (car neg-result) *dp-state*))
	 (ctx (make-ctx 'negation (list (make-ctx 'expr-hole *boolean*)))))
    ;;(break "cp")
      (setf (dpinfo-context *dp-state*)
    	    (cons (formula sform) (dpinfo-context *dp-state*)))
    ;; (when (and (eq *countxyz* 4)
    ;; 	       (infix-application? (formula sform)))
    ;;   (show sform)
    ;;   (show *dp-state*)
    ;;   (assert nil))
    (when (and (consp result)
	       (not (update-or-connective-occurs? newfmla)))
      (loop for x in result do (push x *process-output*)))
    (if (false-p result)
	(let ((dp-trace
	       (make-trace 'deep-decision-procedure
			   (list ctx *false* (car neg-result))
			   (list
			    (make-trace 'proof-hole)))))
	  (values
	   (cons '!
		 (apply-trace
		  (cdr sig)
		  (list (make-trace 'cut-rule ; from newfmla to not (negate newfmla)
				    (list (car neg-result))
				    (list
				     (apply-trace (cdr (cdr neg-result))
						  (list (make-trace 'axiom-rule
								    (list newfmla))))
				     (make-trace 'weak-rule
						 (list newfmla)
						 (list ; from not (negate newfmla) to the end
						  (apply-trace dp-trace 
							       (list
								(make-trace 'not-false-rule))))))))))
	   sform))
	(if (eq (car sig) '?)
	    (let ((new-sform (copy sform
			       'formula newfmla)))
	      (values sig new-sform))
	    ;; ***Need a flag to check if *top-dp-state* was changed,
	    ;; namely, is the new stuff essentially empty.  
	    (if (dpi-state-changed? *top-dp-state* *dp-state*)
		(values (cons '? (make-trace 'proof-hole)) sform)
	      (values (cons 'X (make-trace 'proof-hole)) sform))))))

(defun top-translate-to-old-prove (expr)
  (top-translate-to-prove expr))

(defun translate-from-prove (expr)
  (cond
   ((true-p expr) *true*)
   ((false-p expr) *false*)
   (t expr)))

(defun translate-from-prove-list (list)
  (if (listp list)
      (mapcar #'translate-from-prove list)
      (translate-from-prove list)))

(defmethod top-quant? ((expr negation))
  (with-slots (argument) expr
  (top-quant? argument)))

(defmethod top-quant? ((expr quant-expr))
  t)

(defmethod top-quant? ((expr t))
  nil)

(defmethod quant-occurs? ((expr projection-expr))
  nil)

(defmethod quant-occurs? ((expr injection-expr))
  nil)

(defmethod quant-occurs? ((expr injection?-expr))
  nil)

(defmethod quant-occurs? ((expr extraction-expr))
  nil)

(defmethod quant-occurs? ((expr projection-application))
  (with-slots (argument) expr
    (quant-occurs? argument)))

(defmethod quant-occurs? ((expr injection-application))
  (with-slots (argument) expr
    (quant-occurs? argument)))

(defmethod quant-occurs? ((expr injection?-application))
  (with-slots (argument) expr
    (quant-occurs? argument)))

(defmethod quant-occurs? ((expr extraction-application))
  (with-slots (argument) expr
    (quant-occurs? argument)))

(defmethod quant-occurs? ((expr field-application))
  (with-slots (argument) expr
    (quant-occurs? argument)))

(defmethod quant-occurs? ((expr application))
  (with-slots (operator argument) expr
    (or (quant-occurs? operator)
	(quant-occurs? argument))))

(defmethod quant-occurs? ((expr branch))
  (or (quant-occurs? (condition expr))
      (quant-occurs? (then-part expr))
      (quant-occurs? (else-part expr))))

(defmethod quant-occurs? ((expr list))
  (cond ((null expr) nil)
	(t (or (quant-occurs? (car expr))
	       (quant-occurs? (cdr expr))))))

;(defmethod quant-occurs? ((expr quant-expr))
;  t)

(defmethod quant-occurs? ((expr binding-expr))
  t)
;;   (quant-occurs? (expression expr))
;;(NSH:10/25): I'm not sure whether this should be just true
;;or as above.
;;(NSH:2/92): I've changed it to true since the ground prover
;;forgets the type constraints on binding-exprs and erroneously
;;declares two
;;nonequal binding exprs to be the same.

(defmethod quant-occurs? ((expr record-expr))
  (with-slots (assignments) expr
  (quant-occurs? assignments)))

(defmethod quant-occurs? ((assignment assignment))
  (with-slots (expression arguments) assignment
    (or (quant-occurs? arguments)
	(quant-occurs? expression))))

(defmethod quant-occurs? ((expr tuple-expr))
  (with-slots (exprs) expr
    (quant-occurs? exprs)))

(defmethod quant-occurs? ((expr update-expr))
  (with-slots (expression assignments) expr
    (or (quant-occurs? expression)
	(quant-occurs? assignments))))

(defmethod quant-occurs? ((expr expr))
  nil)

;;connective-occurs? tests if there are any propositional
;;connectives or IF-exprs in the expression that the decision
;;procedure could be used to simplify.

(defun connective-occurs? (expr)
  (connective-occurs?* expr nil))

(defmacro accum-connective-occurs?* (accum)
  `(when (consp ,accum)
       (connective-occurs?* (car ,accum)(cdr ,accum))))


(defmethod connective-occurs?* ((expr name-expr) accum)
  (accum-connective-occurs?* accum))

(defmethod connective-occurs?* ((expr branch) accum)
  (declare (ignore accum))
    t)

(defmethod connective-occurs?* ((expr cases-expr) accum)
  (declare (ignore accum))
  t)

(defmethod connective-occurs?* ((expr projection-expr) accum)
  (accum-connective-occurs?* accum))

(defmethod connective-occurs?* ((expr injection-expr) accum)
  (accum-connective-occurs?* accum))

(defmethod connective-occurs?* ((expr injection?-expr) accum)
  (accum-connective-occurs?* accum))

(defmethod connective-occurs?* ((expr extraction-expr) accum)
  (accum-connective-occurs?* accum))

(defmethod connective-occurs?* ((expr projection-application) accum)
  (with-slots (argument) expr
    (connective-occurs?* argument accum)))

(defmethod connective-occurs?* ((expr injection-application) accum)
  (with-slots (argument) expr
    (connective-occurs?* argument accum)))

(defmethod connective-occurs?* ((expr injection?-application) accum)
  (with-slots (argument) expr
    (connective-occurs?* argument accum)))

(defmethod connective-occurs?* ((expr extraction-application) accum)
  (with-slots (argument) expr
    (connective-occurs?* argument accum)))

(defmethod connective-occurs?* ((expr tuple-expr) accum)
  (with-slots (exprs) expr
    (connective-occurs?* exprs accum)))

(defmethod connective-occurs?* ((expr record-expr) accum)
  (with-slots (assignments) expr
    (connective-occurs?* assignments accum)))

(defmethod connective-occurs?* ((expr assignment) accum)
  (with-slots (arguments expression) expr
    (connective-occurs?* arguments (cons expression accum))))


(defmethod connective-occurs?* ((expr field-application) accum)
  (with-slots (argument) expr
      (connective-occurs?* argument accum)))

(defmethod connective-occurs?* ((expr propositional-application) accum)
  (declare (ignore accum))
  t)

(defmethod connective-occurs?* ((expr negation) accum)
  (with-slots (argument) expr
  (connective-occurs?* argument accum)));;exception to prop-app.

(defmethod connective-occurs?* ((expr boolean-equation) accum)
  (with-slots (argument) expr
    (connective-occurs?* argument accum)))

(defmethod connective-occurs?* ((expr application) accum)
  (with-slots (operator argument) expr
   (connective-occurs?* operator (cons argument accum))))


(defmethod connective-occurs?* ((expr list) accum)
  (if (consp expr)
      (connective-occurs?* (cdr expr)
			  (cons (car expr) accum))
      (if (consp accum)
	  (connective-occurs?* (car accum)(cdr accum))
	  nil)))
      
;  (some #'connective-occurs?* expr))
;  (cond ((null  expr) nil)
;	(t (or (connective-occurs? (car expr))
;	       (connective-occurs? (cdr expr)))))

(defmethod connective-occurs?* ((expr binding-expr) accum)
  (accum-connective-occurs?* accum))
  ;(connective-occurs? (expression expr))


(defmethod connective-occurs?* 
    ((expr update-expr) accum)
  (with-slots (expression assignments) expr
    (connective-occurs?* assignments (cons expression accum))))
;    (or (connective-occurs? expression)
;	(connective-occurs? assignments))))
   ;;NSH(5/8/99): update-or-connective-occurs? is t on updates.
   ;;NSH(6/2/99): changed from nil to look inside for connectives.

(defmethod connective-occurs?* ((expr expr) accum)
  (accum-connective-occurs?* accum))

;;Separated connective-occurs? from update-or-connective-occurs?.
;;The latter is used for typepreds and process-assert, and the
;;former is used everywhere else.

(defun update-or-connective-occurs? (expr)
  (update-or-connective-occurs?* expr nil))

(defmacro accum-update-or-connective-occurs?* (accum)
  `(when (consp ,accum)
       (update-or-connective-occurs?* (car ,accum)(cdr ,accum))))


(defmethod update-or-connective-occurs?* ((expr name-expr) accum)
  (accum-update-or-connective-occurs?* accum))

(defmethod update-or-connective-occurs?* ((expr branch) accum)
  (declare (ignore accum))
    t)

(defmethod update-or-connective-occurs?* ((expr cases-expr) accum)
  (declare (ignore accum))
  t)

(defmethod update-or-connective-occurs?* ((expr projection-expr) accum)
  (accum-update-or-connective-occurs?* accum))

(defmethod update-or-connective-occurs?* ((expr injection-expr) accum)
  (accum-update-or-connective-occurs?* accum))

(defmethod update-or-connective-occurs?* ((expr injection?-expr) accum)
  (accum-update-or-connective-occurs?* accum))

(defmethod update-or-connective-occurs?* ((expr extraction-expr) accum)
  (accum-update-or-connective-occurs?* accum))

(defmethod update-or-connective-occurs?* ((expr projection-application) accum)
  (with-slots (argument) expr
    (update-or-connective-occurs?* argument accum)))

(defmethod update-or-connective-occurs?* ((expr injection-application) accum)
  (with-slots (argument) expr
    (update-or-connective-occurs?* argument accum)))

(defmethod update-or-connective-occurs?* ((expr injection?-application) accum)
  (with-slots (argument) expr
    (update-or-connective-occurs?* argument accum)))

(defmethod update-or-connective-occurs?* ((expr extraction-application) accum)
  (with-slots (argument) expr
    (update-or-connective-occurs?* argument accum)))

(defmethod update-or-connective-occurs?* ((expr tuple-expr) accum)
  (with-slots (exprs) expr
    (update-or-connective-occurs?* exprs accum)))

(defmethod update-or-connective-occurs?* ((expr record-expr) accum)
  (with-slots (assignments) expr
    (update-or-connective-occurs?* assignments accum)))

(defmethod update-or-connective-occurs?* ((expr assignment) accum)
  (with-slots (arguments expression) expr
    (update-or-connective-occurs?* arguments (cons expression accum))))


(defmethod update-or-connective-occurs?* ((expr field-application) accum)
  (with-slots (argument) expr
    (update-or-connective-occurs?* argument accum)))

(defmethod update-or-connective-occurs?* ((expr propositional-application) accum)
  (declare (ignore accum))
  t)

(defmethod update-or-connective-occurs?* ((expr negation) accum)
  (with-slots (argument) expr
    (update-or-connective-occurs?* argument accum)))

(defmethod update-or-connective-occurs?* ((expr application) accum)
  (with-slots (operator argument) expr
    (update-or-connective-occurs?* operator (cons argument accum))))

(defmethod update-or-connective-occurs?* ((expr list) accum)
    (if (consp expr)
      (update-or-connective-occurs?* (cdr expr)
			  (cons (car expr) accum))
      (if (consp accum)
	  (update-or-connective-occurs?* (car accum)(cdr accum))
	  nil)))

(defmethod update-or-connective-occurs?* ((expr binding-expr) accum)
  (accum-update-or-connective-occurs?* accum)
  )

(defmethod update-or-connective-occurs?* ;;NSH(5.13.97) needed for updates
    ;;or the translations get HUGE.
    ((expr update-expr) accum)
  (declare (ignore accum))
  t)

(defmethod update-or-connective-occurs?* ((expr expr) accum)
  (accum-update-or-connective-occurs?* accum))


(defun cond-assert-if (expr ctx &optional conditions)
  (if (number-expr? expr);;NSH(4.7.96)
      (values (cons 'X (make-trace 'proof-hole)) expr)
      (nprotecting-cong-state
       ((*dp-state* *dp-state*))
       (let ((*rewrite-hash* (if *hash-rewrites?*
				 (copy *rewrite-hash*)
				 *rewrite-hash*))
	     (conditions (if (not (listp conditions))
			     (list conditions)
			     conditions))
	     (condition-result nil))
	 (loop for condition
	       in conditions;;NSH(5.18.97):restored check to catch
	       ;;nested updates.
	       when (and (not (false-p condition)) ;;; DAC: condition
			;;;should never be false
			 (not (check-for-connectives? condition)))
	       do (setq condition-result
			(call-process condition *dp-state*)))
	 ;;    (format t "~%  Simplifying ~a under conditions ~{~a, ~}"
	 ;;	       expr conditions);;NSH(10.10.94)omitting for now.
	 (if (false-p condition-result)
	     (nprotecting-cong-state
	      ((*dp-state* *top-dp-state*))
	      (assert-if-i expr (make-ctx 'not-implemented 'c4)))
	   (assert-if-i expr ctx))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;assert-if-inside rewrites only inside the expression but leaves
;;the topmost level alone.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmethod assert-if-inside ((expr name-expr))
  (do-auto-rewrite expr (cons 'X (make-trace 'proof-hole))
		   (make-ctx 'expr-hole *boolean*)))
;;  (values 'X expr) ;;NSH(2.28.94)

;NSH(9.13.94): not needed. handled by default case. 
;(defmethod assert-if-inside ((expr projection-application))
;  (multiple-value-bind (sig newarg)
;      (assert-if (argument expr))
;    (if (typep newarg 'tuple-expr)
;	(nth (1- (index expr)) (exprs newarg))
;	(do-auto-rewrite (lcopy expr 'argument newarg) sig))))
  
(defmethod assert-if-inside ((expr quant-expr))
  (with-slots (expression) expr
    (multiple-value-bind (sig newexpr)
	(assert-if-inside-sign expr t)
	(if (eq (car sig) 'X)
	    (values (cons 'X (make-trace 'proof-hole)) expr)
	  (values sig newexpr)))))

(defmethod assert-if-inside ((expr application))
  (cond ((negation? expr)
	 (multiple-value-bind (sig newarg)
	     (assert-if-inside-sign (args1 expr) nil) ;;NSH(3.21.94) sign.
	   (if (eq (car sig) '?)
	       (if (tc-eq  newarg *true*)
		   (values (cons 'X
				 (make-trace 'not-implemented 'p71))
			   expr)
		   (values (cons '? (cdr sig))
			   (lcopy expr
			     'argument newarg)))
	     (values (cons 'X (make-trace 'proof-hole)) expr))))
	(t (assert-if-inside-sign expr t))))   ;;NSH(3.21.94) sign.

;;NSH(11.22.94)
(defmethod assert-if-inside ((expr field-application))
  (with-slots (id argument) expr
	      (multiple-value-bind (sigarg newarg)
		  (assert-if-i argument (make-ctx 'not-implemented 'c6))
		  (multiple-value-bind (nsigarg nnewarg)
		      (reduce-field-application (car sigarg) newarg id)
		      (values (cons nsigarg
				    (make-trace 'not-implemented 'p75))
			      nnewarg)))))

(defmethod assert-if-inside ((expr projection-application))
  (with-slots (index argument) expr
    (multiple-value-bind (sigarg newarg)
	(assert-if-i argument (make-ctx 'not-implemented 'c7))
      ;;NSH(2.28.95) correction: field->proj
	(multiple-value-bind (nsigarg nnewarg)
	    (reduce-proj-application (car sigarg) newarg index)
	    (values (cons nsigarg
			  (make-trace 'not-implemented 'p76))
		    nnewarg)))))

(defmethod assert-if-inside ((expr injection-application))
  (with-slots (index argument) expr
    (multiple-value-bind (sigarg newarg)
	(assert-if-i argument (make-ctx 'not-implemented 'c8))
      (if (and (extraction-application? newarg)
	       (= (index newarg) index))
	  (values (cons '?
			(make-trace 'not-implemented 'p77))
		  (argument newarg))
	  (let ((new-expr (lcopy expr 'argument newarg)))
	    (multiple-value-bind
	     (nsigarg nnewarg)
	     (do-auto-rewrite new-expr (cons (car sigarg)
					     (make-trace 'not-implemented 'p136))
			      (make-ctx 'not-implemented 'c66))
	     (values (cons (car nsigarg)
			   (make-trace 'not-implemented 'p78))
		     nnewarg)))))))

(defmethod assert-if-inside ((expr injection?-application))
  (multiple-value-bind (sigarg newarg)
      (assert-if-inside-sign expr t)
      (values (cons (car sigarg)
		    (make-trace 'not-implemented 'p79))
	      newarg)))

(defmethod assert-if-inside ((expr extraction-application))
  (with-slots (index argument) expr
    (multiple-value-bind (sigarg newarg)
	(assert-if-i argument (make-ctx 'not-implemented 'c9))
      (if (and (injection-application? newarg)
	       (= (index newarg) index))
	  (values (cons '?
			(make-trace 'not-implemented 'p80))
		  (argument newarg))
	  (let ((new-expr (lcopy expr 'argument newarg)))
	    (multiple-value-bind
	     (nsigarg nnewarg)
	     (do-auto-rewrite new-expr (cons (car sigarg) (make-trace 'not-implemented 'p203))
			      (make-ctx 'not-implemented 'c67))
	     (values (cons (car nsigarg)
			   (make-trace 'not-implemented 'p81))
		     nnewarg)))))))

(defun assert-if-inside-sign (expr sign)
  (assert-if-inside-sign* expr sign))

(defmethod assert-if-inside-sign* ((expr application) sign)
  (let ((ctx
	 (if sign
	     (make-ctx 'expr-hole *boolean*);;positif
	   (make-ctx 'negation (list (make-ctx 'expr-hole *boolean*))))));;negatif
    (multiple-value-bind (sigop newop)
      (assert-if-i (operator expr) (make-ctx 'not-implemented 'c10))
    (multiple-value-bind (sigargs newargs)
	(assert-if-arg expr sign)
      (let* ((sig (if (eq (car sigop) '?) '? (car sigargs)))
	     (expr ;;shadowing expr
	      (lcopy expr
		'operator (if (eq (car sigop) '?) newop (operator expr))
		'argument (if (eq (car sigargs) '?) newargs (argument expr))))
	     (trace (apply-trace (cdr sigop) ;; to be merged with sig?
				 (list (cdr sigargs)))))
	(cond ((and (eq (car sigop) '?)
		    (typep newop 'lambda-expr)
		    (or *let-reduce?*
			(not (let-expr? expr))))
	       (multiple-value-bind (sig val)
		   (assert-if-i (substit (expression newop) ;; FG caution with substit
				(pvs-pairlis (bindings newop)
					     (argument-list newargs)))
				(make-ctx 'not-implemented 'c11))
		 (declare (ignore sig))
		 (values (cons '?
			       (make-trace 'not-implemented 'p74))
			 val)))
	      ((and (is-predicate? newop)
		    (adt? (find-supertype (type newargs)))
		    (typep newop 'name-expr)
		    (recognizer? newop))
	       (let ((result (check-other-recognizers newop newargs t)))
		 (if (and (false-p result) (null sign))
		     (values (cons '?
				   (make-trace 'not-implemented 'p84))
			     *false*)
		     (if (and (true-p result) sign)
			 (values (cons '?
				       (make-trace 'not-implemented 'p85))
				 *true*)
		       (multiple-value-bind
			(newsig newval)
			(do-auto-rewrite expr (cons sig (make-trace 'not-implemented 'p229))
					 (make-ctx 'not-implemented 'c68))
			(values (cons (car newsig)
				      (make-trace 'not-implemented 'p86))
				newval))))))
	      ((and sign
		    (is-predicate? newop)
		    (member expr (type-constraints newargs t)
			    :test #'tc-eq))
	       (values
		;; (assert (and 'assert2 nil));; FG to be modified later
		(cons '?
		      (make-trace 'not-implemented 'p2)
		      ;; (apply-trace
		      ;;  trace
		      ;;  (list
		      ;; 	(make-trace
		      ;; 	 'deep-decision-procedure
		      ;; 	 (list ctx *true* expr)
		      ;; 	 (list (make-trace 'proof-hole)))
		      ;; 	))

		      ;; (apply-trace
		      ;;  trace
		      ;;  (list
		      ;; 	(make-trace
		      ;; 	 'deep-inference-rule
		      ;; 	 (list ctx *true* expr)
		      ;; 	 (list (make-trace 'proof-hole)
		      ;; 	       (make-trace
		      ;; 		'typepred-rule
		      ;; 		(list (list (compute-negation expr)))
		      ;; 		(list (make-trace 'axiom-rule (list expr))))
		      ;; 	       (make-trace 'true-rule)))))
		      )
		*true*))
	      (t
	       (multiple-value-bind (newsig newval)
		   (assert-if-application expr newop newargs
					  (if (eq (car sigop) '?) ;; FG: then combine sigop and sigargs
					      (cons '? (make-trace 'not-implemented 'p56))
					    sigargs) ctx)
		 (if (eq (car newsig) '?)
		     (if (if sign
			     (tc-eq newval *false*)
			     (tc-eq newval *true*))
			 (values (cons sig trace) expr)
		       (if (eq (car sigop) 'X) ; added for instrumentation
			   (values (cons '? (cdr newsig))
				   newval)
			 (values (cons '?
				       (make-trace 'not-implemented 'p166))
				 newval)))
		   (values (cons sig trace) expr))))))))))

(defmethod assert-if-inside-sign* ((expr branch) sign)
  (assert-if-i expr
	       (if sign
		   (make-ctx 'expr-hole *boolean*);;positif
		 (make-ctx 'negation (list (make-ctx 'expr-hole *boolean*))))));;negative

(defmethod assert-if-inside-sign* ((expr quant-expr) sign)
  (let ((ctx
	 (if sign
	     (make-ctx 'expr-hole *boolean*);;positif
	   (make-ctx 'negation (list (make-ctx 'expr-hole *boolean*))))));;negatif
    (with-slots (expression) expr
      (multiple-value-bind
       (sig newexpr)
       (assert-if-i expr ctx)
       (if (or (and sign (tc-eq newexpr *false*))
	       (and (null sign)(tc-eq newexpr *true*)))
	   (values (cons 'X
			 (make-trace 'not-implemented 'p92))
		   expr)
	 (values sig newexpr))))))

(defmethod assert-if-inside-sign* ((expr injection?-application) sign)
  (with-slots (index argument) expr
    (multiple-value-bind (sig newarg)
	(assert-if-i argument (make-ctx 'not-implemented 'c14))
      (let* ((newexpr (lcopy expr 'argument newarg))
	     (result (check-other-injection?s newexpr t)))
	(if (and (false-p result) (null sign))
	    (values (cons '?
			  (make-trace 'not-implemented 'p94))
		    *false*)
	    (if (and (true-p result) sign)
		(values (cons '?
			      (make-trace 'not-implemented 'p95))
			*true*)
	      (values (cons (car sig)
			    (make-trace 'not-implemented 'p96))
		      newexpr)))))))
  

(defmethod assert-if-inside-sign* ((expr t) sign)
  (declare (ignore sign))
  (multiple-value-bind (sigarg newarg)
      (assert-if-i expr (make-ctx 'not-implemented 'c15))
      (values (cons (car sigarg)
		    (make-trace 'not-implemented 'p97))
	      newarg)))

(defmethod assert-if-inside-sign* ((expr name-expr) sign)
  (declare (ignore sign))
  (multiple-value-bind
   (sigarg newarg)
   (do-auto-rewrite expr (cons 'X (make-trace 'not-implemented 'p321))
		    (make-ctx 'not-implemented 'c69))
   (values (cons (car sigarg)
		 (make-trace 'not-implemented 'p98))
	   newarg)))

(defmethod assert-if-inside ((expr branch))
  (assert-if-i expr (make-ctx 'expr-hole *boolean*)))

(defmethod assert-if-inside ((expr expr))
  (multiple-value-bind (sig newexpr)
      (assert-if-i expr (make-ctx 'not-implemented 'c17))
      (values (cons (car sig)
		    (make-trace 'not-implemented 'p82))
	      newexpr)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;NSH(7/23/93): The functions for recognizers below are meant to;;
;;speed up the simplification of case expressions which right   ;;
;;now make quadratic number of calls to process.                ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun check-all-recognizers (arg)
  (let* ((stype (find-supertype (type arg)))
	 (recs (when (adt? stype) (recognizers stype)))
	 (constructor
	  (if (and (name-expr? arg) (constructor? arg))
	      arg
	      (if (and (application? arg)
		       (constructor? (operator arg)))
		  (operator arg)
		  nil))))
    (if constructor
	(let ((cons-rec (recognizer constructor)))
	  (loop for rec in recs
		collect
		(if (same-id cons-rec rec)
		    (cons rec *true*)
		    (cons rec *false*))))
	(loop for rec in recs
	      collect
	      (cons rec (assert-test (make!-application rec arg)))))))


(defun check-rest-recognizers (rec all-result &optional indirect)
  (cond ((null all-result) 'restfalse)
        ((same-id rec (caar all-result))
         (if (and (or (true-p (cdar all-result))
		      (false-p (cdar all-result)))
		  (null indirect))
             (cdar all-result)
             (check-rest-recognizers rec (cdr all-result) indirect)))
        (t (if (true-p (cdar all-result))
                *false*
               (let ((rest (check-rest-recognizers rec (cdr all-result)
						   indirect))) 
                  (cond ((or (true-p rest)
			     (false-p rest))
			 rest)
                        ((eq rest 'restfalse)
                         (if (false-p (cdar all-result))
                             'restfalse
                             nil))
                        (t nil)))))))

(defun check-some-recognizer (rec all-result &optional indirect) ;;;all-result comes from
					      ;;;check-all-recognizers
    (let ((rest (check-rest-recognizers rec all-result indirect)))
       (if (eq rest 'restfalse) *true*
           rest)))


(defun check-other-recognizers (recog arg &optional indirect)
  (check-some-recognizer recog (check-all-recognizers arg) indirect))


;;; The following are like check-*-recognizers, but for
;;; injection?-applications
(defun check-other-injection?s (inj?-appl &optional indirect)
  (check-some-injection? inj?-appl
			 (check-all-injection?s (argument inj?-appl))
			 indirect))

(defun check-all-injection?s (arg)
  (let ((cotupletype (find-supertype (type arg)))
	(index (when (injection-application? arg)
		 (index arg)))
	(i 0))
    (if index
	(mapcar #'(lambda (ty)
		    (declare (ignore ty))
		    (incf i)
		    (cons i (if (= i index) *true* *false*)))
	  (types cotupletype))
	(mapcar #'(lambda (ty)
		    (declare (ignore ty))
		    (let ((inj?-appl (make!-injection?-application (incf i) arg)))
		      (cons i (assert-test inj?-appl))))
	  (types cotupletype)))))

(defun check-some-injection? (inj?-appl all-result &optional indirect)
    (let ((rest (check-rest-injection?s inj?-appl all-result indirect)))
       (if (eq rest 'restfalse)
	   *true*
           rest)))

(defun check-rest-injection?s (inj?-appl all-result &optional indirect)
  (cond ((null all-result) 'restfalse)
        ((= (index inj?-appl) (caar all-result))
         (if (and (or (true-p (cdar all-result))
		      (false-p (cdar all-result)))
		  (null indirect))
             (cdar all-result)
             (check-rest-injection?s inj?-appl (cdr all-result) indirect)))
        (t (if (true-p (cdar all-result))
	       *false*
               (let ((rest (check-rest-injection?s inj?-appl (cdr all-result)
						   indirect))) 
		 (cond ((or (true-p rest)
			    (false-p rest))
			rest)
		       ((eq rest 'restfalse)
			(if (false-p (cdar all-result))
			    'restfalse
			    nil))
		       (t nil)))))))

(defmethod assert-if-i ((expr update-expr) ctx)
  (declare (ignore ctx))
  (with-slots (expression assignments) expr
    (let* ((newexpr (nth-value 1 (assert-if-i expression (make-ctx 'not-implemented 'c18))))
	   (newassign (nth-value 1 (assert-if-i assignments (make-ctx 'not-implemented 'c19))))
	   (new-update-expr (simplify-nested-updates newexpr newassign expr)))
      (if (eq new-update-expr expr)
	  (multiple-value-bind
	   (sig newexpr)
	   (do-auto-rewrite expr (cons 'X (make-trace 'not-implemented 'p232))
			    (make-ctx 'not-implemented 'c70))
	   (values (cons (car sig) (make-trace 'not-implemented 'p168)) newexpr))	  
	(multiple-value-bind
	 (sig newexpr)
	 (do-auto-rewrite new-update-expr (cons '? (make-trace 'not-implemented 'p234))
			  (make-ctx 'not-implemented 'c71))
	 (values (cons (car sig) (make-trace 'not-implemented 'p178)) newexpr))))))

(defmethod simplify-nested-updates ((expr record-expr) outer-assignments
				    update-expr)
  (with-slots (assignments) expr
    (let* ((new-expr-assigns
	    (loop for assign in assignments
		  collect (make-updated-assign assign outer-assignments)))
	   (new-outer-assigns
	    (collect-new-outer-assigns assignments outer-assignments))
	   (outer-to-inner-assigns
	    (loop for assign in new-outer-assigns
		  when (singleton? (arguments assign))
		  collect assign))
	   (outer-outer-assigns
	    (loop for assign in new-outer-assigns
		  when (not (singleton? (arguments assign)))
		  collect assign))
	   (new-expr (if (and (equal new-expr-assigns assignments)
			      (null outer-to-inner-assigns))
			 expr
			 (lcopy expr 'assignments
				(nconc new-expr-assigns
				       outer-to-inner-assigns)))))
      (if (null outer-outer-assigns)
	  new-expr
	  (if (equal outer-outer-assigns outer-assignments)
	      (lcopy update-expr 'expression new-expr)
	      (lcopy update-expr
		'expression new-expr
		'assignments outer-outer-assigns))))))

(defmethod simplify-nested-updates ((expr tuple-expr) outer-assignments
				    update-expr)
  (declare (ignore update-expr))
  (with-slots (exprs) expr
    (let ((new-exprs (copy-list exprs))
	  (assignment-parts (partition-tup-assignments outer-assignments)))
      (dolist (assigns assignment-parts)
	(let* ((index (car assigns))
	       (tupexpr (nth index exprs))
	       (new-expr (create-tup-nested-update (cdr assigns) tupexpr)))
	  (setf (nth index new-exprs) new-expr)))
      (lcopy expr 'exprs new-exprs))))

(defun create-tup-nested-update (assigns expr &optional new-assigns)
  (if (null assigns)
      (if (null new-assigns)
	  expr
	  (make!-update-expr expr (nreverse new-assigns)))
      (let ((args (cdr (arguments (car assigns))))
	    (aexpr (expression (car assigns))))
	(if (null args)
	    (create-tup-nested-update nil aexpr new-assigns)
	    (create-tup-nested-update (cdr assigns) expr
				      (cons (mk-assignment nil args aexpr)
					    new-assigns))))))

(defun partition-tup-assignments (assignments &optional parts)
  (if (null assignments)
      parts
      (let* ((index (1- (number (caar (arguments (car assignments))))))
	     (part (assoc index parts :test #'=)))
	(partition-tup-assignments
	 (cdr assignments)
	 (cond (part
		(nconc part (list (car assignments)))
		parts)
	       (t (acons index (list (car assignments)) parts)))))))

(defmethod simplify-nested-updates ((expr application) outer-assignments
				    update-expr)
  (declare (ignore update-expr))
  (if (constructor-name-expr? (operator expr))
      (simplify-constructor-nested-update outer-assignments expr)
      (call-next-method)))

(defun simplify-constructor-nested-update (assigns expr)
  (if (null assigns)
      expr
      (let* ((ass-args (arguments (car assigns)))
	     (acc (caar ass-args))
	     (value (expression (car assigns)))
	     (pos (position acc (accessors (operator expr)) :test #'same-id))
	     (expr-args (arguments expr))
	     (expr-arg (nth pos expr-args))
	     (new-arg (if (cdr ass-args)
			  (let ((assign (make-assignment (cdr ass-args) value)))
			    (simplify-nested-updates
			     expr-arg (list assign)
			     (make!-update-expr expr-arg (list assign))))
			  value))
	     (new-expr (if (tc-eq expr-arg new-arg)
			   expr
			   (copy expr
			     'argument (if (tuple-expr? (argument expr))
					   (copy (argument expr)
					     'exprs (let ((nargs
							   (copy-list expr-args)))
						      (setf (nth pos nargs)
							    new-arg)
						      nargs))
					   new-arg)))))
	(simplify-constructor-nested-update (cdr assigns) new-expr))))

(defun simplify-constructor-nested-update* (arguments value expr)
  (let* ((acc (caar arguments))
	 (pos (position acc (accessors (operator expr)) :test #'same-id))
	 (expr-args (arguments expr))
	 (expr-arg (nth pos expr-args))
	 (new-arg (if (cdr arguments)
		      (let ((assign (make-assignment (cdr arguments) value)))
			(simplify-nested-updates
			 expr-arg assign (make!-update-expr expr-arg assign)))
		      value))
	 (new-expr (if (tc-eq expr-arg new-arg)
		       expr
		       (copy expr
			 'argument (if (tuple-expr? (argument expr))
				       (copy (argument expr)
					 'exprs (let ((nargs
						       (copy-list expr-args)))
						  (setf (nth pos nargs)
							new-arg)
						  nargs))
				       new-arg)))))
    new-expr))

(defmethod simplify-nested-updates ((expr update-expr) outer-assignments
				    update-expr)
  (declare (ignore update-expr))
  (with-slots (expression assignments) expr
    (let* ((new-expr-assigns
	    (loop for assign in assignments
		  collect (make-updated-assign assign outer-assignments)))
	   (new-outer-assigns
	    (collect-new-outer-assigns assignments outer-assignments))
	   (new-merged-assignments
	    (nconc new-expr-assigns new-outer-assigns)))
      (lcopy expr
	'assignments new-merged-assignments))))

(defun make-updated-assign (assignment outer-assignment)
  (with-slots (arguments expression) assignment
    (lcopy assignment
      'expression (make-updated-assign-expr arguments expression
					    outer-assignment nil))))

;;checks if assign-args are reassigned in outer-assignments and
;;returns the updated or overridden assign-expr.
(defun make-updated-assign-expr (assign-args assign-expr outer-assignments
					     accum-assignments)
  (if (consp outer-assignments)
      (let* ((outer-args1 (arguments (car outer-assignments)))
	     (outer-assgn1 (expression (car outer-assignments)))
	     (match (match-update-args-prefix? assign-args outer-args1)))
	(if match
	    (make-updated-assign-expr assign-args assign-expr
				      (cdr outer-assignments)
				      (cons (cons match outer-assgn1)
					    accum-assignments))
	    (make-updated-assign-expr assign-args assign-expr
				      (cdr outer-assignments)
				      accum-assignments)))
      (if accum-assignments
	  (let ((final-override
		 (some #'(lambda (x)
			   (and (eq (car x) t) x)) accum-assignments)))
	    (if final-override
		(cdr final-override)
		(let* ((naccum-assignments (nreverse accum-assignments))
		       (tc-naccum-assignments
			(loop for (x . y) in naccum-assignments
			      collect (make-assignment x y))))
		  (simplify-nested-updates
		   assign-expr
		   tc-naccum-assignments
		   (make!-update-expr assign-expr tc-naccum-assignments)))))
	  assign-expr)))

(defun collect-new-outer-assigns (assignments outer-assignments)
  (when (consp outer-assignments)
      (if (member (arguments (car outer-assignments))
		  assignments
		  :test #'(lambda (x y)
			    (match-update-args-prefix? y x))
		  :key #'arguments)
	  (collect-new-outer-assigns assignments
				     (cdr outer-assignments))
	  (cons (car outer-assignments)
		(collect-new-outer-assigns assignments
					   (cdr outer-assignments))))))

;;checks if assignment lhs args1 is a prefix of lhs args2 and returns
;;the remainder of args2.
(defun match-update-args-prefix? (args1 args2)
  (if (and (consp args1)
	   (consp args2)
	   (tc-eq (car args1)(car args2)))
    (match-update-args-prefix? (cdr args1)(cdr args2))
    (when (null args1) (if (null args2) t args2))))

(defmethod simplify-nested-updates
    (expr outer-assignments update-expr)
  (lcopy update-expr
    'expression expr
    'assignments outer-assignments))
  
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun collect-type-constraints (expr)
  (when (and (not (null *subtype-hash*))
	     (not (gethash expr *subtype-hash*)))
    (collect-type-constraints* expr)))


;;(NSH:12-20-09): Now uses find-non-false-recognizer to add this
;;recognizer as a type constraint.  The constraint can be *false*
;;when there are multiple true recognizers. 
(defun collect-type-constraints* (ex)
  ;; SO 2004-09-17: Added implicit-type-predictes
  (if *implicit-typepreds?*
      (implicit-type-predicates ex t (type-constraints ex t))
      (if (and (type ex)(adt? (find-supertype (type ex))))
          (let* ((all-recs (check-all-recognizers ex))
	         (rec (find-non-false-recognizer all-recs)))
            (if (consp rec)
		(if (eq (cdr rec) *true*)
		    (type-constraints ex (not *pseudo-normalizing*))
		    (cons (make!-reduced-application (car rec) ex)
			  (type-constraints ex (not *pseudo-normalizing*))))
		(if (eq rec *false*)
		    (cons *false* (type-constraints ex (not *pseudo-normalizing*)))
		    (type-constraints ex (not *pseudo-normalizing*)))))
        (type-constraints ex (not *pseudo-normalizing*)))))

;;computes the only non-false recognizer from the result of
;;check-all-recognizers.  Returns *true* (one true recognizer),
;;*false* (more than one true recognizer), rec (the one non-false
;;recognizer), or nil (more than one non-false recognizer). 
(defun find-non-false-recognizer (all-recs)
  (if (consp all-recs)
      (let ((rec 
	     (find-non-false-recognizer* (cdr all-recs)
					 (if (eq (cdar all-recs) *false*)
					     nil
					     (car all-recs)))))
	(cond ((and (not *assert-typepreds-off*)
		 (tc-eq rec *false*))
	       (pushnew *false* *assert-typepreds* :test #'tc-eq)
	       rec)
	    (t rec)))
      nil))

;body of find-non-false-recognizer: scans the entries in
;check-all-recognizers returns *false* if all are false, or
;recognizer which is the only non-false one that is nil
;or nil, if there is a true recognizer
;We have a contradiction if all are false or more than one true
;Note: non-false-rec is either *true*, *false* or the first recognizer
(defun find-non-false-recognizer* (all-recs non-false-rec)
  (if (consp all-recs)
     (cond ((eq (cdar all-recs) *true*)
	    (if (and (consp non-false-rec)
		     (eq (cdr non-false-rec) *true*)) ; then two true recognizers
		*false*;;else (cdr non-false-rec) is nil
		(find-non-false-recognizer* (cdr all-recs) (car all-recs))))
           ((eq (cdar all-recs) *false*);keep looking
	    (find-non-false-recognizer* (cdr all-recs) non-false-rec))
	   (t ;(cdar all-recs) is nil
	     (and (null non-false-rec);;else multiple nils, return nil
	          (find-non-false-recognizer* (cdr all-recs)(car all-recs)))))
     (or non-false-rec *false*)))

;;NSH(7.11.94): old code triggered a loop since collect-type-constraints
;;calls substit which calls pseudo-normalize which calls
;;collect-type-constraints.  Probably should turn off collect-type-preds
;;for pseudo-normalize.
(defun record-type-constraints (expr)
  (unless  *assert-typepreds-off*
	   ;;   (update-or-connective-occurs? expr)
    (let ((constraints (collect-type-constraints expr)))
      (when (and *subtype-hash* constraints)
	(dolist (constraint constraints)
	  (pushnew constraint *assert-typepreds* :test #'tc-eq))
	(setf (gethash expr *subtype-hash*) t)))))

;; FG make sure assert-if is not used again
(defmethod assert-if :around (expr)
  (declare (ignore expr))
  (assert nil))

(defmethod assert-if-i :around ((expr expr) ctx)
  (declare (ignore ctx))
  (record-type-constraints expr)
  (call-next-method))

(defun rewrite-declaration (expr)
  (if (constant? expr) (declaration expr) expr))


(defmethod assert-if-i ((expr name-expr) ctx)
  (cond ((tc-eq (find-supertype (type expr)) *boolean*)
	 (if (or (tc-eq expr *true*) (tc-eq expr *false*))
	     (values (cons 'X (make-trace 'proof-hole)) expr)
	     (let ((result
		    (assert-test expr)))
	       (cond ((true-p result)
		      (multiple-value-bind
		       (sig newexpr)
		       (values-assert-if '? *true* expr)
		       (values (cons sig (make-trace 'not-implemented 'p180)) newexpr)))
		     ((false-p result)
		      (multiple-value-bind
		       (sig newexpr)
		       (values-assert-if '? *false* expr)
		       (values (cons sig (make-trace 'not-implemented 'p181)) newexpr)))
		     (t
		      (multiple-value-bind
		       (sig newexpr)
		       (do-auto-rewrite expr (cons 'X (make-trace 'not-implemented 'p235))
					(make-ctx 'not-implemented 'c72))
		       (values (cons (car sig) (make-trace 'not-implemented 'p182)) newexpr)))))))
	((and (not (memq *assert-flag* '(record simplify)))
	      (gethash (declaration expr) *auto-rewrites-ops*))
	  (do-auto-rewrite expr (cons 'X (make-trace 'proof-hole)) ctx))
	(t (values (cons 'X (make-trace 'proof-hole)) expr))))

(defmethod assert-if-i ((expr theory-name-expr) ctx)
  (declare (ignore ctx))
  (values (cons 'X (make-trace 'not-implemented 'p185)) expr))

(defmethod assert-if-i ((expr field-name-expr) ctx)
  (declare (ignore ctx))
  (values (cons 'X (make-trace 'not-implemented 'p186)) expr))

(defmethod assert-if-i ((expr projection-expr) ctx)
  (declare (ignore ctx))
  (values (cons 'X (make-trace 'not-implemented 'p187)) expr))

(defmethod assert-if-i ((expr injection-expr) ctx)
  (declare (ignore ctx))
  (values (cons 'X (make-trace 'not-implemented 'p188)) expr))

(defmethod assert-if-i ((expr injection?-expr) ctx)
  (declare (ignore ctx))
  (values (cons 'X (make-trace 'not-implemented 'p189)) expr))

(defmethod assert-if-i ((expr extraction-expr) ctx)
  (declare (ignore ctx))
  (values (cons 'X (make-trace 'not-implemented 'p190)) expr))

;; nexpr is the current expression, not expr
(defun assert-then-else (test expr condition-flg ctx)
  (let ((nexpr (lcopy expr;;FG caution with lcopy eta expansion
		      'argument
		      (lcopy (argument expr)
			     'exprs
			     (cons test (cdr (arguments expr)))))))
    ;;condition-flg indicates whether test is assertable.
    ;; (when (and condition-flg
    ;; 	       (not (tc-eq (car (and+ test)) test)))
    ;;   (assert (and (= (list-length (car (and+ test))) 1);; FG to be instrumented later
    ;; 		   (tc-eq (car (car (and+ test))) test))))
    (if (and condition-flg
	     (not (tc-eq (car (and+ test)) test))
	     (not (and (= (list-length (car (and+ test))) 1)
		       (tc-eq (car (car (and+ test))) test))))
    (multiple-value-bind;; FG to be instrumented later
       (sigthen newthen)
	;;(progn (format t "~% Assuming test ~a true." test))
	    (cond-assert-if (then-part expr)
			    (make-ctx 'not-implemented 'condition)
			    (if  condition-flg
				 (car (and+ test))
				 nil))
   (multiple-value-bind
	 (sigelse newelse)
       ;(progn (format t "~%Assuming test ~a false." test))
	      (cond-assert-if (else-part expr)
			      (make-ctx 'not-implemented 'condition)
			      (if  (and condition-flg
					(not (cond-expr? expr))) ;NSH(4.7.96)
				   (car (and+ (car (negate-with-proofs test))))
				   nil))
     (cond ((tc-eq newthen newelse)
	    (values (cons '?
			  (make-trace 'not-implemented 'condition))
		    newthen))
	   ((and (tc-eq test (condition expr)) ;;sigtest is irrelevant
		 (eq (car sigthen) 'X)(eq (car sigelse) 'X))
	    (values (cons 'X (make-trace 'proof-hole)) expr));; FG here nexpr is expr
	   (t (values (cons '?
			    (make-trace 'not-implemented 'condition))
		      (let ((nex (copy expr;;FG caution with copy eta expansion
				       'argument (make!-arg-tuple-expr
						  test newthen newelse))))
			(if (cond-table-expr? nex)
			    (change-class nex 'cond-expr)
			  nex)))))))
    (multiple-value-bind
       (sigthen newthen)
	;;(progn (format t "~% Assuming test ~a true." test))
	    (cond-assert-if (then-part expr)
			    (apply-ctx
			       ctx
			       (list
				(if condition-flg
				    (make-ctx 'if-application
					      (list
					       (make-ctx 'expr test)
					       (make-ctx 'expr-hole
							 (type (then-part nexpr)))
					       (make-ctx 'expr
							 (else-part nexpr)))
					      (list (operator nexpr)))
				  (make-ctx 'application
					    (list (make-ctx 'expr (operator nexpr))
						  (make-ctx 'tuple
							    (list
							     (make-ctx 'expr test)
							     (make-ctx 'expr-hole
								       (type (then-part nexpr)))
							     (make-ctx 'expr
								       (else-part nexpr)))))))
					  ))
			    (if  condition-flg
				 (car (and+ test))
				 nil))
   (multiple-value-bind
	 (sigelse newelse)
       ;(progn (format t "~%Assuming test ~a false." test))
	      (cond-assert-if (else-part expr)
			      (apply-ctx
			       ctx
			       (list
				(if condition-flg
				    (make-ctx 'if-application
					      (list
					       (make-ctx 'expr test)
					       (make-ctx 'expr newthen)
					       (make-ctx 'expr-hole
							 (type (else-part nexpr))))
					      (list (operator nexpr)))
				  (make-ctx 'application
					    (list (make-ctx 'expr (operator nexpr))
						  (make-ctx 'tuple
							    (list
							     (make-ctx 'expr test)
							     (make-ctx 'expr newthen)
							     (make-ctx 'expr-hole
								       (type (else-part nexpr))))))))
								       ))
			      (if  (and condition-flg
					(not (cond-expr? expr))) ;NSH(4.7.96)
				   (car (and+ (car (negate-with-proofs test))))
				   nil))
     (cond ((tc-eq newthen newelse)
	    (values (cons '?
			  (apply-trace
			   (cdr sigthen)
			   (list (apply-trace
				  (cdr sigelse)
				  (list
				   (make-trace 'deep-trusted-rule
				   	       (list ctx 'ifthenelse1
						     newthen
						     (lcopy nexpr
							       'argument
							       (lcopy
								(argument nexpr)
								'exprs
								(list test newthen newelse))))
				   	       (list (make-trace 'proof-hole))))))))
		    newthen))
	   ((and (tc-eq test (condition expr)) ;;sigtest is irrelevant
		 (eq (car sigthen) 'X)(eq (car sigelse) 'X))
	    (values (cons 'X (make-trace 'proof-hole)) expr));; FG here nexpr is expr
	   (t (values (cons '?
			    (apply-trace
			     (cdr sigthen)
			     (list (apply-trace
				    (cdr sigelse)
				    (list (make-trace 'proof-hole))))))
		      (let ((nex (copy expr;;FG caution with copy eta expansion
				       'argument (make!-arg-tuple-expr
						  test newthen newelse))))
			(if (cond-table-expr? nex)
			    (change-class nex 'cond-expr)
			  nex))))))))))


(defmethod assert-if-i ((expr assignment) ctx)
  (declare (ignore ctx))
  (multiple-value-bind
	(asig newarguments)
      (assert-if-i (arguments expr) (make-ctx 'not-implemented 'c20))
    (multiple-value-bind
	  (sig newexpression)
	(assert-if-i (expression expr) (make-ctx 'not-implemented 'c21))
      (if (or (eq (car asig) '?)(eq (car sig) '?))
	  (values (cons '? (make-trace 'not-implemented 'p191))
		  (lcopy expr 'arguments
			 (if (eq (car asig) '?) newarguments
			     (arguments expr))
			 'expression
			 (if (eq (car sig) '?)
			     newexpression
			     (expression expr))))
	  (values (cons 'X (make-trace 'not-implemented 'p192)) expr)))))

(defun assert-if-simplify (expr ctx)
  (let ((*top-assert-flag* nil))
  (multiple-value-bind (sig newexpr)
      (assert-if-i expr ctx)
      (if (eq (car sig) 'X)
	  (cons expr (make-trace 'proof-hole))
	(cons newexpr (cdr sig))))))

(defun assert-if-simp (expr ctx)
  (let ((*top-assert-flag* nil))
    (assert-if-i expr ctx)))

(defmethod assert-if-i ((expr branch) ctx)  ;;;change to rec. branch?
  (if (eq *assert-flag* 'rewrite)
      (call-next-method expr)
    (multiple-value-bind
     (sigtest newtest)
     (assert-if-simp (condition expr)
		     (apply-ctx
		      ctx
		      (list
		       (make-ctx 'application
				 (list (make-ctx 'expr (operator expr))
				       (make-ctx 'tuple
						 (list
						  (make-ctx 'expr-hole *boolean*)
						  (make-ctx 'expr
							    (cadr (exprs (argument expr))))
						  (make-ctx 'expr
							    (caddr (exprs (argument expr)))))))))))
     (cond ((tc-eq newtest *true*)
	    (multiple-value-bind
	     (sigthen newthen)
	     (assert-if-i (then-part expr) ctx)
	     (values-assert-if (cons '?
				     (apply-trace
				      (cdr sigtest)
				      (list
				       (make-trace 'deep-trusted-rule
						   (list ctx
							 'ithenelse2
							 (then-part expr)
							 (lcopy expr
								 'argument
								 (lcopy (argument expr)
									'exprs
									(cons
									 newtest
									 (cdr (arguments expr))))))
						   (list (cdr sigthen))))))
			       newthen expr)))
	   ((tc-eq newtest *false*)
	    (multiple-value-bind
	     (sigelse newelse)
	     (assert-if-i (else-part expr) ctx)
	     (values-assert-if (cons '?
				     (apply-trace
				      (cdr sigtest)
				      (list
				       (make-trace 'deep-trusted-rule
						   (list ctx
							 'ithenelse3
							 (else-part expr)
							 (lcopy expr
								 'argument
								 (lcopy (argument expr)
									'exprs
									(cons
									 newtest
									 (cdr (arguments expr))))))
						   (list (cdr sigelse))))))
			       newelse expr)))
	   ;;DAC(6.23.94) The typereds of expressions in the
	   ;;then and else partmay not be valid in the top level
	   ;;context and thus should not be asserted.
	   ;;NSH(7.25.94): The above change should be rolled back
	   ;;once the typechecker becomes consistent about type
	   ;;assignment. 
	   (t (let ((*assert-typepreds-off* t))
		(multiple-value-bind
		 (sig newexpr)
		 (assert-then-else newtest expr t ctx)
		 (values (cons (car sig)
			       (apply-trace
				(cdr sigtest)
				(list (cdr sig))))
			 newexpr))))))))


(defun find-selection (constructor-id args cases-expr)
  (let ((selection
	 (find constructor-id (selections cases-expr)
	       :test #'(lambda (x y) (eq x (id (constructor y)))))))
    (cond ((null selection)
	   (else-part cases-expr))
	  (t (substit (expression selection) ;; FG caution with substit
		      (pvs-pairlis (args selection)
			       args))))))

(defun get-adt (type)
  (cond ((adt? type) type)
	((typep type 'subtype) (get-adt (supertype type)))))

(defun values-assert-if (sig result input)
  (declare (ignore input))
  (values sig result))

(defmethod assert-if-i ((expr cases-expr) ctx)
  (declare (ignore ctx))
  (with-slots (expression selections else-part)
      expr
    (multiple-value-bind (sigexpr newexpr)
	(cond-assert-if expression (make-ctx 'not-implemented 'c52))
      (let ((expression (if (eq (car sigexpr) '?) newexpr expression)))
;	(cond ((eq *assert-flag* 'rewrite)
;	       (if (eq sigexpr '?)
;		   (values-assert-if
;		    '?
;		    (lcopy expr
;		      'expression newexpr
;		      )
;		    expr)
;		   (values 'X expr)))
;	      (t)
	(multiple-value-bind (sig selected-expr)
	    (if (eq *assert-flag* 'rewrite)
		(values 'X nil)
		(assert-cases expression expr)) ; ((selections expr))
					;((else-part expr) t)
	  (if (eq sig 'X)
	      (if *cases-rewrite*
		  (multiple-value-bind (sigsel newselections)
		      (assert-if-i (selections expr) (make-ctx 'not-implemented 'c26))
		    (multiple-value-bind (sigelse newelse)
			(assert-if-i (else-part expr) (make-ctx 'not-implemented 'c27))
		      (if (memq '? (list (car sigexpr) (car sigsel) (car sigelse)))
			  (values (cons '? (make-trace 'not-implemented 'p196))
				  (let ((nex (lcopy expr
					       'expression newexpr
					       'selections newselections
					       'else-part newelse)))
				    (if (and (not (eq expr nex))
					     (table-expr? nex))
					(change-class nex 'cases-expr)
					nex)))
			  (values (cons 'X (make-trace 'not-implemented 'p197)) expr))))
		  (if (eq (car sigexpr) 'X)
		      (values (cons 'X (make-trace 'not-implemented 'p198)) expr)
		    (multiple-value-bind
		     (sig newexpr)
		     (values-assert-if
		      '? (lcopy expr
				'expression newexpr)
		      expr)
		     (values (cons sig (make-trace 'not-implemented 'p199)) newexpr))))
	    (multiple-value-bind
	     (sig newexpr)
	     (values-assert-if '?
			       selected-expr expr)
	     (values (cons sig (make-trace 'not-implemented 'p200)) newexpr))))))))

(defmethod assert-if-i ((expr selection) ctx)
  (declare (ignore ctx))
  (multiple-value-bind (sig val)
      (assert-if-i (expression expr) (make-ctx 'not-implemented 'c28))
      (if (eq (car sig) '?)
	  (multiple-value-bind
	   (sig newexpr)
	   (values-assert-if
	    '? (lcopy expr 'expression val) expr)
	   (values (cons sig (make-trace 'not-implemented 'p201)) newexpr))
	(values (cons 'X (make-trace 'not-implemented 'p202)) expr))))


(defun assert-subgoal (expr)
  (multiple-value-bind (sig newexpr)
      (assert-if-i expr (make-ctx 'not-implemented 'c29))
    (if (eq (car sig) 'X)(values '? expr)
	(values '? newexpr))))

(defmethod assert-cases (expression case-expr)
  (let* ((all-result (check-all-recognizers expression))
         (selections (selections case-expr))
         (select (loop for sel in selections
		       thereis
		       (let ((check
			      (check-some-recognizer
			       (recognizer (constructor sel))
			       all-result)))
			 (when (true-p check) sel)))));;(break "cases")
    (cond ((null select)
	   (if (else-part case-expr)
	       (if (loop for sel in selections
			 always (false-p
				 (check-some-recognizer
				  (recognizer (constructor sel))
				  all-result)))
		   (assert-subgoal (else-part case-expr))
		   (values 'X case-expr))
	       (values 'X case-expr)))
	  ((and (name-expr? expression)(constructor? expression))
	   (assert-subgoal (expression select)))
	  ((and (application? expression)(constructor? (operator expression)))
	   (assert-subgoal (substit (expression select) ;; FG caution with substit
			     (pvs-pairlis (args select)
					  (arguments expression)))))
	  (t (assert-subgoal (subst-accessors-in-selection expression
							   select))))))

(defmethod assert-cases ((expression injection-application)
			 (case-expr unpack-expr))
  (let ((sel (find (index expression) (selections case-expr) :key #'index)))
    (assert (or sel (else-part case-expr)))
    (if sel
	(assert-subgoal
	 (substit (expression sel) ;; FG caution with substit
	   (pvs-pairlis (args sel)
			(argument-list (argument  expression)))))
	;; Nothing to substitute in else-part
	(assert-subgoal (else-part case-expr)))))

(defmethod assert-cases (expression (case-expr unpack-expr))
  (assert (selections case-expr))
  (let* ((all-result (check-all-injection?s expression))
	 (selections (selections case-expr))
	 (select (loop for sel in selections
		       thereis
		       (let ((check
			      (check-some-injection?
			       (recognizer (constructor sel))
			       all-result)))
			 (when (true-p check) sel)))))
    (if (null select)
	;; In this case all we can do is see if every selection expression
	;; is the same, in which case that is the result.
	(let ((result (expression (car (selections case-expr)))))
	  (if (and (every #'(lambda (sel)
			      (tc-eq (expression sel) result))
			  (selections case-expr))
		   (or (null (else-part case-expr))
		       (tc-eq (else-part case-expr) result)))
	      (assert-subgoal result)
	      (values 'X case-expr)))
	(assert-subgoal (subst-accessors-in-selection expression select)))))


;;pvs-pairlis is careful to treat tuples as lists in pairing
;;formals and actuals. 
(defun pvs-pairlis (list1 list2)
  (if (and (singleton? list1)
	   (typep (find-supertype (type (car list1))) 'tupletype)
	   (not (singleton? list2)))
      (list (cons (car list1)
		  (make!-tuple-expr list2)))
      (if (and (not (singleton? list1))
	       (singleton? list2)
	       (typep (find-supertype (type (car list2)))
		      'tupletype))
	  (if (typep (car list2) 'tuple-expr)
	      (pairlis list1 (exprs (car list2)))
	      (pairlis list1 (make!-projections (car list2))))
	  (pairlis list1 list2))))
      

;;; SO 9/2/94 - changed record-redex? to handle field-applications

(defmethod record-redex? (expr)
  (declare (ignore expr))
  nil)

(defmethod record-redex? ((expr field-application))
  (typep (argument expr) 'record-expr))


(defun function-update-redex? (expr)
  (and (typep expr 'application)
       (typep (operator expr) 'update-expr)))
       ;;I'm  making use of the fact that an operator
       ;;must be a function and not a record.

(defun simplify-function-update-redex (expr &optional in-beta-reduce?)
  (let* ((op (operator expr))
	 (args (arguments expr))
	 (fun (expression op))
	 (updates (reverse (assignments op))))
    (reduce-update expr fun       ;;NSH(8.23.94)
		   (check-update-args*  updates args
				       in-beta-reduce?)
		   args
		   in-beta-reduce? nil)))

(defun accessor-update-redex? (expr)
  (and (typep expr 'application)
       (typep (operator expr) 'accessor-name-expr)
       (typep (argument expr) 'update-expr)))

(defun check-update-args* (updates args in-beta-reduce?)
  ;;returns a list of matching updates, or 'NOIDEA if there
  ;;is an assignment that does resolve to TRUE or FALSE.
  (if (null updates)
      nil
      (let* ((update-args (arguments (car updates)))
	     ;;(update-expr (expression (car updates)))
	     (first (check-update-args
		     (if (and (cdr (car update-args))
			      (null (cdr args)))
			 (list (make!-tuple-expr* (car update-args)))
			 (car update-args))
		     (if (and (null (cdr (car update-args)))
			      (cdr args))
			 (list (make!-tuple-expr* args))
			 args)
		     in-beta-reduce?)))
	(if (eq first 'noidea)
	    'noidea
	    (if (false-p first)
		(check-update-args* (cdr updates)
				    args
				    in-beta-reduce?)
		(if (singleton?  update-args)
		    (list (car updates))
		    (let ((rest (check-update-args* (cdr updates)
						    args
						    in-beta-reduce?)))
		      (if (eq rest 'noidea)
			  'noidea
			  (cons (car updates)
				rest)))))))))

;;;Given that updates comes from check-update-args*.
(defun reduce-update (redex expr updates args in-beta-reduce?
			    new-updates)
  ;;reduce-update constructs the reduced form of the given
  ;;update redex.
  (let ((*generate-tccs* 'none)));;NSH(9.15.94): prevents TCCS.
    (if (eq updates 'noidea)
	redex
	(if (null updates)
	    (let* ((newexpr (make!-application* expr args))
		   (newexpr
		    (if in-beta-reduce?
			(beta-reduce newexpr)
			(multiple-value-bind (sig value)
			    (assert-if-application
			     newexpr expr
			     (make!-arg-tuple-expr* args)
			     (cons '?;; FG caution with make!-application*
				   (make-trace 'not-implemented 'p165))
			     (make-ctx 'not-implemented 'c55))
			  (if (eq (car sig) '?) value newexpr)))))
	      (if new-updates
		  (make!-update-expr newexpr new-updates)
		  newexpr))
	    (let ((update-expr (expression (car updates)))
		  (update-args (arguments (car updates))))
	      (if (singleton? update-args)
		  (if new-updates
		      (make!-update-expr
		       update-expr
		       new-updates)
		      update-expr)
		  (reduce-update redex expr (cdr updates)
				 args in-beta-reduce?
				 (cons (lcopy (car updates)
					 'arguments
					 (cdr update-args))
				       new-updates)))))))
		       

(defun scalar? (expr)
  (and (enum-adt? (find-supertype (type expr))) expr))

(defun scalar-constant? (x)
  (and (constructor? x)(scalar? x)))			 

(defun check-update-args (update-args args &optional in-beta-reduce?)
  (if (null update-args) 'true
      (let* ((uarg1 (car update-args))
	     (arg1 (car args))
	     (equality (make!-equation uarg1 arg1))
	     (result
	      (if in-beta-reduce?
		  (if (tc-eq uarg1 arg1)
		      'true
		      (if (or (and (integer-expr? uarg1)
				   (integer-expr? arg1))
			      (and (scalar-constant? uarg1)
				   (scalar-constant? arg1)))
			  'false
			  'noidea))
		  (if (connective-occurs? equality)
		      'noidea
		      (let ((newresult (nth-value 1
					 (assert-equality
					  equality (list uarg1 arg1)
					  (cons 'X (make-trace 'not-implemented 'p175))
					  (make-ctx 'not-implemented 'c63)))))
			(assert-test newresult))))))
	(cond ((true-p result)
	       (check-update-args (cdr update-args) (cdr args)))
	      ((false-p result) 'false)
	      (t 'noidea)))))

(defmethod integer-expr? ((ex number-expr))
  t)

(defmethod integer-expr? ((ex application))
  (and (is-unary-minus? ex)
       (integer-expr? (argument ex))))

(defmethod integer-expr? (ex)
  (declare (ignore ex))
  nil)

(defmethod assert-if-i ((expr tuple-expr) ctx)
  (multiple-value-bind
   (sig newexprs)
   (assert-if-i (exprs expr)
		(apply-ctx ctx
			   (list
			    (make-ctx 'tuple
				      (mapcar #'(lambda (ex)
						  (make-ctx 'expr-hole (type ex)))
					      (exprs expr))))))
   ;; (format t "~%exprs: ~a" (exprs expr))
   ;; (format t "~%newexprs: ~a" newexprs)
   ;; (format t "~%proof: ~a" sig)
   (if (eq (car sig) '?)
       (do-auto-rewrite
	(if (eq newexprs (exprs expr))
	    expr
	  (lcopy expr
		 'exprs newexprs
		 'type (mk-tupletype (mapcar #'type newexprs))))
	(cons '? (cdr sig)) (make-ctx 'not-implemented 'c74))
     (do-auto-rewrite expr (cons 'X (make-trace 'proof-hole))
		      (make-ctx 'not-implemented 'c75)))))

(defmethod assert-if-i ((expr record-expr) ctx)
  (declare (ignore ctx))
  (multiple-value-bind  (sig newassign)
	(assert-if-i (assignments expr) (make-ctx 'not-implemented 'c31))
    (if (eq (car sig) '?)
	(multiple-value-bind
	 (sig newexpr)
	 (do-auto-rewrite (lcopy expr 'assignments newassign)
			  (cons '? (make-trace 'not-implemented 'p239))
			  (make-ctx 'not-implemented 'c76))
	 (values (cons (car sig) (make-trace 'not-implemented 'p205)) newexpr))      
      (multiple-value-bind
       (sig newexpr)
       (do-auto-rewrite expr (cons 'X (make-trace 'not-implemented 'p240))
			(make-ctx 'not-implemented 'c77))
       (values (cons (car sig) (make-trace 'not-implemented 'p206)) newexpr)))))
       
(defmethod record-update-redex? (expr)
  (declare (ignore expr))
  nil)

(defmethod record-update-redex? ((expr field-application))
  (with-slots (argument) expr
    (typep argument 'update-expr)))


(defun make-record-update-reduced-application (op arg)
  (let* ((new-application (make!-field-application op arg)))
    (if (record-update-redex? new-application)
	(nth-value 1 (record-update-reduce new-application op arg))
	new-application)))

(defun make-accessor-update-reduced-application (op arg)
  (let* ((new-application (make!-application op arg)))
    (if (accessor-update-redex? new-application)
	(nth-value 1 (accessor-update-reduce new-application op arg))
	new-application)))


(defun record-update-reduce (expr op arg);;NSH(7.15.94):removed sig
  ;;expr applies record-access to record-update: a(exp WITH [..])
  ;;new-application ensures that any newly created redexes are reduced.
  (declare (ignore expr))
  (let ((updates
	 (loop for assn in (assignments arg)
	       when (eq op (id (caar (arguments assn))))
	       collect assn))
	(expr-of-arg (expression arg)))
    (if updates
	(if (every #'(lambda (x) (cdr (arguments x)))
		   updates) ;;;a curried update::
	                             ;;;a(exp WITH [((a)(i)):= e])
	    (let ((newexpr;;NSH(9.15.94): otherwise TCCs
		   ;;are generated when domain is subtype.
		   ;;(let ((*generate-tccs* 'none)))
		   (make!-update-expr
		    (make-record-update-reduced-application
		     op expr-of-arg)
		    (mapcar #'(lambda (x)
				(lcopy x 'arguments
				       (cdr (arguments x))))
		      updates))))
	      (multiple-value-bind
	       (newsig newexpr)
	       (do-auto-rewrite
		newexpr
		(cons '? (make-trace 'not-implemented 'p241))
		(make-ctx 'not-implemented 'c78)) 
	       (values (car newsig) newexpr))
	      );;return a(exp) WITH [(i) := e] simplified.
	    (make-update-expr-from-updates
	     updates))
	(multiple-value-bind
	 (newsig newexpr)
	 (do-auto-rewrite  (make-record-update-reduced-application
			    op expr-of-arg)
			   (cons '? (make-trace 'not-implemented 'p242))
			   (make-ctx 'not-implemented 'c79))
	 (values (car newsig) newexpr)))))

;;assumes that at least one update has an empty cdr arguments
;;invoked from record-update-reduce.  Makes sure that all
;;previous updates from last single update are irrelevant.
;;NSH(10.10.07) moved values '? in here and added do-auto-rewrite
(defun make-update-expr-from-updates (updates)
  (if (and (consp updates)
	   (null (cdr (arguments (car updates))))
	   (every #'(lambda (x) (cdr (arguments x)))
		  (cdr updates)))
      (if (null (cdr updates))
	  (values '? (expression (car updates)))
	(multiple-value-bind
	 (newsig newexpr)
	 (do-auto-rewrite
	  (make!-update-expr
	   (expression (car updates))
	   (mapcar #'(lambda (x) (lcopy x 'arguments
					(cdr (arguments x))))
		   (cdr updates)))
	  (cons '? (make-trace 'not-implemented 'p243)) (make-ctx 'not-implemented 'c80))
	 (values (car newsig) newexpr)))
    (make-update-expr-from-updates (cdr updates))))

(defun is-predicate? (expr)
  (predtype? (type expr)))

(defmethod arity ((decl typed-declaration))
  (if (funtype? (type decl))
      (arity (type decl))
      0))

(defmethod arity ((expr expr))
  (arity (type expr)))

;;; SO 7/19/94 - modified for new form of domain.
(defmethod arity ((te funtype))
  (with-slots (domain) te
    (arity* domain)))

(defmethod arity* ((te dep-binding))
  (with-slots (type) te
    (arity* type)))

(defmethod arity* ((te tupletype))
  (with-slots (types) te
    (length types)))

(defmethod arity* ((te type-expr))
  1)

(defmethod arith ((expr t))
  0)

(defun is-plus? (op)
  (and (typep op 'name-expr)
       (interpreted? op)
       (eq (id op) '+)))

(defun is-minus? (op)
  (and (typep op 'name-expr)
       (interpreted? op)
       (eq (id op) '-)))

(defun is-sub-minus? (op)
  (and (is-minus? op)
       (equal (arity op) 2)))

(defun is-mult? (op)
  (and (typep op 'name-expr)
       (interpreted? op)
       (eq (id op) '*)))

(defun is-div? (op)
  (and (typep op 'name-expr)
       (interpreted? op)
       (eq (id op) '/)))

(defmethod is-division? ((expr application))
  (with-slots (operator) expr
    (and (is-div? operator)
	 (= (length (arguments expr)) 2))))

(defmethod is-division? ((expr t))
  nil)

(defmethod is-addition? ((expr application))
  (with-slots (operator) expr
    (and (is-plus? operator)
	 (= (length (arguments expr)) 2))))

(defmethod is-addition? ((expr t))
  nil)

(defmethod is-subtraction? ((expr application))
  (with-slots ((op operator)(arg argument))
      expr
    (and (is-minus? op)
	 (tuple-expr? arg)
	 (= (length (exprs arg)) 2))))

(defmethod is-subtraction? ((expr t))
  nil)

(defmethod is-unary-minus? ((expr application))
  (with-slots ((op operator) (arg argument)) expr
    (and (is-minus? op)
	 (not (tuple-expr? arg)))))

(defmethod is-unary-minus? ((expr t))
  nil)

(defmethod is-multiplication? ((expr application))
  (with-slots (operator)
      expr
    (and (is-mult? operator)
	 (= (length (arguments expr)) 2))))

(defmethod is-multiplication? ((expr t))
  nil)

(defun norm-addition (expr)
  (if (or (is-addition? expr)(is-subtraction? expr))
      (simplify-addition expr)
      expr))

;;assumes that expr is an addition.  newargs is for use from
;;assert-if-application
(defun simplify-addition (expr &optional newargs)
  (assert *use-rationals*)
  (let* ((hashvalue (gethash expr *assert-if-arith-hash*))
	 (msum (or hashvalue
		   (get-merged-sum expr newargs))));;(break "simp-add")
    (unless hashvalue
      (setf (gethash expr *assert-if-arith-hash*) msum)
      (unless (eq expr msum)
	(setf (gethash msum *assert-if-arith-hash*) msum)))
    msum))

(defun get-merged-sum (expr newargs)
  (let* ((nargs (if newargs
		    (argument-list newargs)
		    (arguments expr)))
	 (lhs (car nargs))
	 (rhs (cadr nargs))
	 (lsums (addends lhs))
	 (rsums (if (is-addition? expr)
		    (addends rhs)
		    (mapcar #'make-minus (addends rhs))))
	 (msum (mergesums lsums rsums *real*)))
    (if (tc-eq msum expr) expr msum)))


(defun assert-if-addition  (expr newargs sig);;expr must be
					     ;;addition/subtraction.
  (assert *use-rationals*)
  (let* ((hashvalue (gethash expr *assert-if-arith-hash*))
	 (msum (or hashvalue
		   (let* ((nargs (argument-list newargs))
			  (lhs (car nargs))
			  (rhs (cadr nargs))
			  (lsums (addends lhs))
			  (rsums (if (is-addition? expr)
				     (addends rhs)
				     (mapcar #'make-minus (addends rhs))))
			  (ctype (compatible-type
				  (type expr)
				  (compatible-type (type lhs) (type rhs))))
			  (type (if (or (null *integer*)
					(is-addition? expr))
				    ctype
				    (compatible-type ctype *integer*))))
		     (if (subtype-of? type *real*)
			 (mergesums lsums rsums type)
			 (mergesums lsums rsums *real*))))))
;    (when hashvalue (format t "~%arith"))
    (unless hashvalue
      (setf (gethash expr *assert-if-arith-hash*)
	    msum)
      (unless (eq expr msum)
	(setf (gethash msum *assert-if-arith-hash*)
	      msum)))
    (if (tc-eq msum expr)
	(multiple-value-bind
	 (newsig newexpr)
	 (do-auto-rewrite expr (cons sig (make-trace 'not-implemented 'p244))
			  (make-ctx 'not-implemented 'c81))
	 (values (car newsig) newexpr))
      (multiple-value-bind
       (newsig newexpr)
       (do-auto-rewrite msum (cons '? (make-trace 'not-implemented 'p245))
			(make-ctx 'not-implemented 'c82))
       (values (car newsig) newexpr)))))

(defun make-minus (expr)
  (let* ((coef (coefficient expr))
	 (body (noncoefficient expr))
	 (newcoeffexpr (if (minusp coef)
			   (make!-number-expr (- coef))
			   (make!-minus (make!-number-expr coef)))))
    (if (null body)
	newcoeffexpr
	(make-prod (list newcoeffexpr body)
		   (compatible-type (type newcoeffexpr) (type body))))))

(defun addends (expr)
  (multiple-value-bind (pos neg)
      (addends* expr)
    (nconc pos (mapcar #'make-minus neg))))

(defun addends* (expr)
  (if (typep expr 'application)
      (if (is-addition? expr)
	  (multiple-value-bind (pos1 neg1)
	      (addends* (args1 expr))
	    (multiple-value-bind (pos2 neg2)
		(addends* (args2 expr))
	      (values (nconc pos1 pos2)(nconc neg1 neg2))))
	  ;; SO - 5/11/93 changed is-minus? to is-subtraction?
	  ;;NSH - 5/25/93 changed is-subtraction? to is-sub-minus?
	  (if (is-subtraction? expr)
	      (multiple-value-bind (pos1 neg1)
		  (addends* (args1 expr))
		(multiple-value-bind (pos2 neg2)
		    (addends* (args2 expr))
		  (values (nconc pos1 neg2)(nconc neg1 pos2))))
	      (list expr)))
      (list expr)))

(defun multiplicands (expr)
  (with-slots ((op operator)(arg argument))
      expr
  (if (and (typep expr 'application)
	   (is-mult? op))
      (multiplicands*
       (if (tuple-expr? arg)
	   (exprs arg)
	   (list arg)))
      (list expr))))

(defun multiplicands* (expr-list)
  (if (consp expr-list)
      (nconc (multiplicands (car expr-list))
	     (multiplicands* (cdr expr-list)))
      nil))

(defun make-sum (list type)
  (if (connective-occurs? list)
      (make-sum* list type)
      (make-sum* (sort list #'arith-ord-translate) type)))

(defun make-sum* (list type)
  (cond ((null list) (make!-number-expr 0))
	((null (cdr list)) (car list))
	(t 
	 (let* ((a1 (car list))
		(a2 (cadr list))
		(e1 (cond ((<  (coefficient a2) 0)
			   (make!-difference a1 (make-minus a2)))
			  ((<  (coefficient a1) 0)
			   (make!-difference a2 (make-minus a1)))
			  ((eql (coefficient a2) 0) a1)
			  ((eql (coefficient a1) 0) a2)
			  (t (make!-plus a1 a2)))))
	   (make-sum* (cons e1 (cddr list)) type)))))

(defun make-prod (list type)
  (make-prod* (sort list #'arith-ord-translate)
	      type))

(defun arith-ord-translate (x y)
  (let ((*sequent-typealist* nil))
    (old-arithord (top-translate-to-prove x t)
		  (top-translate-to-prove y t))))

(defun make-prod* (list type)
  (cond ((null list) (make!-number-expr 1))
	((null (cdr list)) (car list))
	((or (eql (coefficient (car list)) 0)
	     (eql (coefficient (cadr list)) 0))
	 (make!-number-expr 0))
	(t (let* ((a1 (car list))
		  (a2 (cadr list))
		  (prod (* (coefficient a1) (coefficient a2)))
		  (coeff (if (minusp prod)
			     (make!-minus (make!-number-expr (- prod)))
			     (make!-number-expr prod)))
		  (a1b (noncoefficient a1))
		  (a2b (noncoefficient a2))
		  (body (if (null a1b)
			    a2b
			    (if (null a2b)
				a1b
				(make!-times a1b a2b))))
		      (e (if (null body) coeff
			     (if (and (typep coeff 'number-expr)
				      (eql (number coeff) 1))
				 body
				 (make!-times coeff body)))))
	     (make-prod* (cons e (cddr list)) type)))))

(defun negative-number? (expr)
  (and (typep  expr 'unary-application)
       (is-minus? (operator  expr))
       (typep (args1  expr) 'rational-expr)))

(defun coefficient (expr)
  (if (is-multiplication? expr)
      (if (typep (args1 expr) 'rational-expr)
	  (number (args1 expr))
	  (if (negative-number? (args1 expr))
	      (- 0 (number (args1 (args1 expr))))
	      1))
      (if (typep expr 'rational-expr)
	  (number expr)
	  (if (negative-number? expr)
	      (- 0 (number (args1 expr)))
	      1))))

(defun noncoefficient (expr)
  (if (and (is-multiplication? expr)
	   (or (typep (args1 expr) 'rational-expr)
	       (negative-number? (args1 expr))))
      (args2 expr)
      (if (or (typep expr 'rational-expr)
	      (negative-number? expr))
	  nil
	  expr)))

(defun mergesums* (list1 list2 type)
  (cond ((null list1) list2)
	((null list2) list1)
	(t (let* ((l1 (car list1))
		  (l1c (coefficient l1))
		  (l1b (noncoefficient l1))
		  (l1blist2 (loop for exp in list2
				  sum
				  (if (tc-eq l1b (noncoefficient exp))
				      (coefficient exp)
				      0)))
		  (newlist2 (loop for exp in list2
				  when (not (tc-eq l1b (noncoefficient exp)))
				  collect exp))
		  (newcoeff (+ l1c l1blist2))
		  (ncoeff (if (minusp newcoeff)
			      (make!-minus (make!-number-expr (- newcoeff)))
			      (make!-number-expr newcoeff)))
		  (newterm (if (null l1b)
			       ncoeff
			       (if (eql newcoeff 1)
				   l1b
				   (make-prod (list ncoeff l1b)
					      type))))
		  (restlist (if (or (cdr list1) newlist2)
				(mergesums* (cdr list1) newlist2 type)
				nil)));;NSH(11.14.95)
	     ;;was (list (make-number-expr 0))
	     (if (equal newcoeff 0)
		 restlist 
		 (cons newterm restlist))))))

(defun mergesums (list1 list2 type)
  (make-sum (mergesums* list1 list2 type) type))


(defun merge-products (l r type)
  (cond ((or (is-addition? l)
	     (is-subtraction? l))
	 (let ((list (loop for x in (addends l)
			  collect
			  (merge-products x r type))))
	   (make-sum list type)))
	((or (is-addition? r)
	     (is-subtraction? r))
	 (let ((list (loop for x in (addends r)
			  collect
			  (merge-products l x type))))
	   (make-sum list type)))
	(t (let* ((lcoeff (coefficient l))
		  (lb (noncoefficient l))
		  (rcoeff (coefficient r))
		  (rb (noncoefficient r))
		  (newcoeff (* lcoeff rcoeff))
		  (prodlist (if lb (if rb (append (multiplicands lb)
						  (multiplicands rb))
				       (multiplicands lb))
				(if rb (multiplicands rb) nil))))
	     (if (eql newcoeff 0)
		 (make!-number-expr 0)
		 (if (eql newcoeff 1)
		     (make-prod prodlist type)
		     (make-prod (list (if (minusp newcoeff)
					  (make!-minus (make!-number-expr
							(- newcoeff)))
					  (make!-number-expr newcoeff))
				      (make-prod prodlist type))
				type)))))))
		    

(defun assert-if-multiplication (expr newargs sig)
  (assert *use-rationals*)
  (let* ((hashvalue (gethash expr *assert-if-arith-hash*))
	 (prod (if hashvalue hashvalue
		   (let* ((nargs (argument-list newargs))
			  (lhs (car nargs))
			  (rhs (cadr nargs))
			  (type (compatible-type (type lhs)(type rhs))))
		     (if (or (is-multiplication? lhs)
			     (is-addition? lhs)
			     (is-subtraction? lhs)
			     (loop for x in (multiplicands rhs)
				   thereis (or (is-addition? x)
					       (is-subtraction? x)
					       ;;(is-division? x)
					       (typep x 'rational-expr))))
			 (merge-products lhs rhs type)
			 expr)))))
;    (when hashvalue (format t "~%arith"))
    (unless hashvalue
      (setf (gethash expr *assert-if-arith-hash*) prod)
      (unless (eq expr prod)
	(setf (gethash prod *assert-if-arith-hash*) prod)))
    (if (tc-eq prod expr)
	(multiple-value-bind
	 (newsig newexpr)
	 (do-auto-rewrite expr (cons sig (make-trace 'not-implemented 'p246))
			  (make-ctx 'not-implemented 'c83))
	 (values (car newsig) newexpr))
      (multiple-value-bind
       (newsig newexpr)
       (do-auto-rewrite prod (cons '? (make-trace 'not-implemented 'p247))
			(make-ctx 'not-implemented 'c84))
       (values (car newsig) newexpr)))))

;; SO - 2012-12-12 - experimenting 
;; (defun simplify-prod-divides (lhs rhs)
;;   (cond ((and (typep lhs 'rational-expr)
;; 	      (is-division? rhs)
;; 	      (cond ((typep (args1 rhs) 'rational-expr) ; Q * (Q / X)
;; 		     (make!-divides (make!-number-expr
;; 				     (* (number lhs) (number (args1 rhs))))
;; 				    (args2 rhs)))
;; 		    ((typep (args2 rhs) 'rational-expr) ; Q * (X / Q)
;; 		     (make!-times (make!-number-expr
;; 				   (/ (number lhs) (number (args2 rhs))))
;; 				  (args1 rhs))))))
;; 	((and (typep rhs 'rational-expr)
;; 	      (is-division? lhs)
;; 	      (cond ((typep (args1 lhs) 'rational-expr) ; (Q / X) * Q
;; 		     (make!-divides (make!-number-expr
;; 				     (* (number rhs) (number (args1 lhs))))
;; 				    (args2 lhs)))
;; 		    ((typep (args2 lhs) 'rational-expr) ; (X / Q) * Q
;; 		     (make!-times (make!-number-expr
;; 				   (/ (number rhs) (number (args2 lhs))))
;; 				  (args1 lhs))))))))


(defun assert-if-division (expr newargs sig)
  (assert *use-rationals*)
  (let* ((hashvalue (gethash expr *assert-if-arith-hash*))
	 (prod (or hashvalue
		   (let* ((nargs (argument-list newargs))
			  (op (operator expr))
			  (lhs (car nargs))
			  (rhs (cadr nargs))
			  ;;(type (compatible-type (type lhs) (type rhs)))
			  )
		     (if (typep rhs 'rational-expr)
			 (if (typep lhs 'rational-expr)
			     (car (simplify-or-copy-app expr op newargs))
			     ;; (if (or (is-division? lhs)
			     ;; 	     (is-multiplication? lhs)
			     ;; 	     (is-addition? lhs)
			     ;; 	     (is-subtraction? lhs))
			     ;; 	 (merge-division lhs rhs type)
			     ;; 	 expr)
			     expr)
			 expr)))))
;    (when hashvalue (format t "~%arith"))
    (unless hashvalue
      (setf (gethash expr *assert-if-arith-hash*) prod)
      (unless (eq expr prod)
	(setf (gethash prod *assert-if-arith-hash*) prod)))
    (if (tc-eq prod expr)
	(multiple-value-bind
	 (newsig newexpr)
	 (do-auto-rewrite expr (cons sig (make-trace 'not-implemented 'p248))
			  (make-ctx 'not-implemented 'c85))
	 (values (car newsig) newexpr))
      (multiple-value-bind
       (newsig newexpr)
       (do-auto-rewrite prod (cons '? (make-trace 'not-implemented 'p249))
			(make-ctx 'not-implemented 'c86))
       (values (car newsig) newexpr)))))

(defun merge-division (l r type)
  (if (or (is-addition? l)
	  (is-subtraction? l))
      (let ((list (loop for x in (addends l)
			collect
			(merge-division x r type))))
	(make-sum list type))
      (make-div l r)))

(defun make-div (l r)
  (cond ((and (rational-expr? l)
	      (rational-expr? r)
	      (not (zerop (number r))))
	 (make!-number-expr (/ (number l) (number r))))
	(t (make!-divides l r))))

;(defmethod compare-expr ((L number-expr) (R number-expr))
;  (if (< (number L)(number R)) '<
;      (if (eql (number L)(number R)) '=
;	  '>)))
;
;(defmethod compare-expr ((L name) (R name)))
;
;
;(defmethod compare-expr ((L list)(R list))
;  (if (null L)
;      (if (null R) '=  '<)
;      (if (null R) '>
;	  (let ((x (compare-expr (car L)(car R))))
;	    (if (eq x '=)
;		(compare-expr (cdr L)(cdr R))
;		x)))))
;
;(defmethod compare-expr ((L tuple-expr) (R tuple-expr))
;  (compare-expr (exprs L)(exprs R)))
;
;(defmethod compare-expr ((L record-expr)(R record-expr))
;  (compare-expr (assignments L)(assignments R)))
;
;(defmethod compare-expr ((L update-expr)(R update-expr))
;  (let ((x (compare-expr (expression L)(expression R))))
;    (if (eq x '=)
;	(compare-expr (assignments L)(assignments R))
;	x)))
;
;
;(defmethod compare-expr ((L binding-expr)(R binding-expr))
;  (let ((x (compare-binding-op L R)))
;    (if (eq x '=)
;	(let ((y (compare-expr (bindings L)(bindings R))))
;	  (if (eq y '=)
;	      (compare-expr (expression L)(expression R))
;	      y))
;	x)))
			    
	
(defun cancel-terms (lhs-terms rhs-terms)
  (cancel-terms* lhs-terms rhs-terms nil 'X))

(defun cancel-terms* (lhs* rhs* lhs-accum sig)
  (if (null lhs*)
      (values sig (nreverse lhs-accum) rhs*)
      (let ((rhs-match
	     (find (car lhs*) rhs*
		   :test #'tc-eq)) ;#'(lambda (x y)
				   ;(true-p (assert-test (make-equality x y))))
	    )
	(if rhs-match
	    (cancel-terms* (cdr lhs*)
			   (remove rhs-match rhs*
				   :count 1);;NSH(2.21.97) 
			   lhs-accum '?)
	    (cancel-terms* (cdr lhs*)
			   rhs*
			   (cons (car lhs*) lhs-accum)
			   sig)))))
      
(defun assert-numeric-equality (expr sig ctx)
  ;;NSH(12.1.94): assumes that equality has been simplified and
  ;;process has been unsuccessfully
  ;;applied to the given equality. 
  (let* ((lhs (args1 expr))
	 (rhs (args2 expr))
	 (lhs-addends (addends (args1 expr)))
	 (rhs-addends (addends (args2 expr))))
    (if (and (singleton? lhs-addends)
	     (singleton? rhs-addends))
	(do-auto-rewrite expr sig (make-ctx 'not-implemented 'c87))
      (multiple-value-bind
       (newsig new-lhs-addends new-rhs-addends)
       (cancel-terms lhs-addends rhs-addends)
       (if (eq newsig '?)
	   (if (and (null new-lhs-addends)
		    (null new-rhs-addends))
	       (values (cons '? (make-trace 'not-implemented 'p179)) *true*)
	     (let ((newval (make!-equation
				 (make-sum new-lhs-addends
					   (compatible-type (type lhs)
							    *integer*))
				 (make-sum new-rhs-addends
					   (compatible-type (type rhs)
							    *integer*)))))
	       (do-auto-rewrite newval
				(cons '?
				      (apply-trace
				       (cdr sig)
				       (list 
					(make-trace 'deep-trusted-rule
						    (list ctx 'rational newval expr)
						    (list (make-trace 'proof-hole))))))
				(make-ctx 'not-implemented 'c88))))
	 (do-auto-rewrite expr sig (make-ctx 'not-implemented 'c89)))))))

(defun assert-disequality (expr newargs sig ctx)
  (let* ((nargs (if (tuple-expr? newargs)
		    (exprs newargs)
		  (make!-projections newargs)))
	 (equality (make!-equation (car nargs) (cadr nargs)))
	 (trace (cdr sig)))
    (multiple-value-bind
     (sig newequality);;FG is this shadowing intended for the do-auto-rewrite case?
     (assert-equality equality newargs
		      (cons (car sig)
			    (if (and (tuple-expr? newargs)
				     (application? expr)
				     (tc-eq (argument expr) newargs));;FG if
				(apply-trace
				 (cdr sig)
				 (list (make-trace 'rewrite-rule
						   (list ctx (compute-negation equality) expr)
						   (list (make-trace 'proof-hole)))))
			      (make-trace 'not-implemented 'p176)))
		      (make-ctx 'not-implemented 'c64))
     (if (eq (car sig) '?)
	 (let* ((neg-res (negate-with-proofs newequality))
		(disequality (car neg-res)))
	   (if (application? disequality)
	       (assert-if-application*-i
		disequality
		(operator disequality)
		newequality
		(cons '?
		      (apply-trace
		       (cdr sig)
		       (list (make-trace
			      'deep-inference-rule
			      (list ctx
				    (car neg-res)
				    (compute-negation newequality))
			      (list (make-trace 'proof-hole)
				    (apply-trace
				     (car (cdr neg-res))
				     (list (make-trace
					    'axiom-rule
					    (list (car neg-res)))))
				    (apply-trace
				     (cdr (cdr neg-res))
				     (list (make-trace
					    'axiom-rule
					    (list
					     (compute-negation newequality))))))))))
		(make-ctx 'not-implemented 'c57))
	     (values (cons '? (make-trace 'not-implemented 'p91))
		     (nth-value 1 (assert-if-i disequality (make-ctx 'not-implemented 'c32))))))
       (do-auto-rewrite expr (cons (car sig) trace) ctx)))))

;;finds non-false recog in recs1 and recs2 and invokes compare-recognizers*
(defun compare-recognizers (recs1 recs2)
  (let ((found-rec1 (find-non-false-recognizer recs1))
	(found-rec2 (find-non-false-recognizer recs2)))
    (and (consp found-rec1)(consp found-rec2)
	(if (tc-eq (car found-rec1)(car found-rec2))
	    (and (null (accessors (constructor (car found-rec1))))
		 *true*)
	    *false*))))


(defun assert-equality (expr newargs sig ctx)
  (let ((nargs (argument-list newargs)))
    (cond ((tc-eq (car nargs)(cadr nargs))
	   (values
	    (cons '?
		  (apply-trace
		   (cdr sig)
		   (list
		    (make-trace 'deep-inference-rule
				(list ctx *true* expr)
				(list (make-trace 'proof-hole)
				      (make-trace 'refl-rule (list (car nargs)))
				      (make-trace 'true-rule))))))
	    *true*))
	  ;;NSH(10.21.94): separated out since this shouldn't be
					;invoked from assert-if-inside.
	  ((tc-eq (find-supertype (type (car nargs)))
		  *number*)
	   (assert-numeric-equality expr sig ctx))
	  ((and (typep (car nargs) 'tuple-expr)
		(typep (cadr nargs) 'tuple-expr))
	   (multiple-value-bind (newsig newval)
	       (assert-tuple-equality expr)
	       (values (cons newsig
			     (make-trace 'not-implemented 'p138))
		       newval)))
	  ((and (typep (car nargs) 'record-expr)
		(typep (cadr nargs) 'record-expr))
	   (multiple-value-bind (newsig newval)
	       (assert-record-equality expr)
	       (values (cons newsig
			     (make-trace 'not-implemented 'p139))
		       newval)))
	  (t (let ((p1 (adt-subtype? (type (args1 expr))))
		   (p2 (adt-subtype? (type (args2 expr)))))
	       (if (and p1 p2)
		   (if (not (eq (id p1) (id p2)));;NSH(12.1.95)
		       (values (cons '?
				     (make-trace 'not-implemented 'p140))
			       *false*)
		     (multiple-value-bind
		      (newsig newval)
		      (do-auto-rewrite expr (cons (car sig) (make-trace 'not-implemented 'p254))
				       (make-ctx 'not-implemented 'c91))
			   (values (cons (car newsig)
					 (make-trace 'not-implemented 'p141))
				   newval)))
		   (if (and (injection-application? (args1 expr))
			    (injection-application? (args2 expr)))
		       (if (not (eq (id (args1 expr)) (id (args2 expr))))
			   (values (cons '?
					 (make-trace 'not-implemented 'p142))
				   *false*)
			 (multiple-value-bind
			  (newsig newval)
			  (do-auto-rewrite expr (cons (car sig) (make-trace 'not-implemented 'p255))
					   (make-ctx 'not-implemented 'c92))
			       (values (cons (car newsig)
					     (make-trace 'not-implemented 'p143))
				       newval)))
		       (let* ((pred (or p1 p2))
			      (term (if p1 (args2 expr) (args1 expr)))
			      (result (if pred
					  (check-rest-recognizers
					   pred
					   (check-all-recognizers term))
					  (compare-recognizers
					   (check-all-recognizers (args1 expr))
					   (check-all-recognizers (args2 expr))))))
			 ;;(NSH:12-20-09) rearranged the order of COND
			 (cond ((false-p result)
				(values (cons '?
					      (make-trace 'not-implemented 'p144))
					*false*))
			       ((and (not pred) (true-p result))
				(values (cons '?
					      (make-trace 'not-implemented 'p145))
					*true*))
			       ((null pred)
				(do-auto-rewrite expr sig (make-ctx 'not-implemented 'c93)))
			       ((and (eq result 'restfalse)
				     (null (accessors (constructor pred))))
				(values (cons '?
					      (make-trace 'not-implemented 'p147))
					*true*))
			       (t
				(multiple-value-bind
				 (newsig newval)
				 (do-auto-rewrite expr
						  (cons (car sig) (make-trace 'not-implemented 'p257))
						  (make-ctx 'not-implemented 'c94))
				    (values (cons (car newsig)
						  (make-trace 'not-implemented 'p148))
					    newval))))))))))))

(defmethod assert-if-application* (expr newop newargs sig)
  (declare (ignore expr newop newargs sig))
  (assert nil))

(defmethod assert-if-application*-i (expr newop (newargs branch) sig ctx)
  (if (negation? expr)
      (multiple-value-bind
       (newsig newval)
       (do-auto-rewrite expr (cons (car sig) (make-trace 'not-implemented 'p258))
			(make-ctx 'not-implemented 'c95))
       (values (cons (car newsig)
		     (make-trace 'not-implemented 'p65))
	       newval))
    (let ((*assert-typepreds-off* t));;NSH(9-10-10)
      (multiple-value-bind
       (thensig thenval)
       (assert-if-application*-i
	(make!-application newop (then-part newargs))
	newop (then-part newargs)
	(cons '? (make-trace 'proof-hole))
	(apply-ctx
	 ctx
	 (list
	  (make-ctx
	   'application
	   (list (make-ctx 'expr (operator newargs))
		 (make-ctx 'tuple
			   (list
			    (make-ctx 'expr (condition newargs))
			    (make-ctx 'expr-hole
				      (type (make!-application newop (then-part newargs))))
			    (make-ctx 'expr (make!-application newop (else-part newargs))))))))))
       (multiple-value-bind
	(elsesig elseval)
	(assert-if-application*-i
	 (make!-application newop (else-part newargs))
	 newop (else-part newargs)
	 (cons '? (make-trace 'proof-hole))
	 (apply-ctx
	 ctx
	 (list
	  (make-ctx
	   'application
	   (list (make-ctx 'expr (operator newargs))
		 (make-ctx 'tuple
			   (list
			    (make-ctx 'expr (condition newargs))
			    (make-ctx 'expr thenval)
			    (make-ctx 'expr-hole
				      (type (make!-application newop (else-part newargs)))))))))))
	(values-assert-if
	 (cons '?
	       (apply-trace
		(cdr sig)
		(list
		 (make-trace 'deep-trusted-rule
			     (list ctx
				   'ifthenelse4
				   (compute-if (condition newargs)
					       (make!-application newop (then-part newargs))
					       (make!-application newop (else-part newargs)))
				   expr)
			     (list (apply-trace (cdr thensig)
						(list (cdr elsesig))))))))
	 (make!-if-expr (condition newargs) thenval elseval)
	 expr))))))

(defmethod assert-if-application*-i (expr (newop branch) newargs sig ctx)
  (declare (ignore ctx sig))
  (let ((*assert-typepreds-off* t));;NSH(9-10-10)
    (let ((thenval (nth-value 1
		   (assert-if-application*-i
		    (make!-application (then-part newop) newargs)
		    (then-part newop) newargs
		    (cons '? (make-trace 'not-implemented 'p173))
		    (make-ctx 'not-implemented 'c60))))
	(elseval (nth-value 1
		   (assert-if-application*-i
		    (make!-application (else-part newop) newargs)
		    (else-part newop) newargs
		    (cons '? (make-trace 'not-implemented 'p174))
		    (make-ctx 'not-implemented 'c61)))))
      (multiple-value-bind (newsig newval)
	  (values-assert-if '?
			    (make!-if-expr (condition newop) thenval elseval)
			    expr)
	  (values (cons newsig
			  (make-trace 'not-implemented 'p102))
		    newval)))))

(defmethod assert-if-application*-i (expr (newop lambda-expr) newargs sig ctx)
  (declare (ignore ctx sig))
  (let ((val (nth-value 1
	       (assert-if-i (substit (expression newop) ;; FG caution with substit
			    (pairlis-args (bindings newop)
					  (argument-list newargs)))
			     (make-ctx 'not-implemented 'c33)))))
    (multiple-value-bind (newsig newval)
	(values-assert-if '? val expr)
	(values (cons newsig
		      (make-trace 'not-implemented 'p103))
		newval))))

(defmethod assert-if-application*-i ((expr let-expr) newop newargs sig ctx)
  (declare (ignore ctx newop newargs))
  (if *let-reduce?*
      (call-next-method)
    (multiple-value-bind
     (newsig newval)
     (do-auto-rewrite expr (cons (car sig) (make-trace 'not-implemented 'p259))
		      (make-ctx 'not-implemented 'c96))
	(values (cons (car newsig)
		      (make-trace 'not-implemented 'p104))
		newval))))

(defmethod assert-if-application*-i ((expr negation) newop  newargs sig ctx)
  (declare (ignore newop))
  (if (tc-eq newargs *true*)
      (values
       (cons '?
	     (apply-trace
	      (cdr sig)
	      (list (make-trace
		     'deep-inference-rule
		     (list ctx *false* expr)
		     (list (make-trace 'proof-hole)
			   (make-trace 'not-false-rule)
			   (make-trace 'not-not-rule
				       (list *true*)
				       (list (make-trace 'true-rule))))))))
       *false*)
    (if (tc-eq newargs *false*)
	(values
	 (cons '?
	       (apply-trace
		(cdr sig)
		(list (make-trace
			    'deep-inference-rule
			    (list ctx *true* expr)
			    (list (make-trace 'proof-hole)
				  (make-trace 'not-false-rule)
				  (make-trace 'true-rule))))))
	 *true*)
      (if (negation? newargs)
	  (values (cons '?
			(make-trace 'not-implemented 'p107))
		  (args1 newargs))
	 (do-auto-rewrite expr sig (make-ctx 'not-implemented 'c97))))))

(defmethod assert-if-application*-i ((expr implication) newop  newargs sig ctx)
  (declare (ignore newop))
  (let ((nargs (argument-list newargs)))
	   (cond ((tc-eq (car nargs) *false*)
		  (values
		   (cons '?
			 (apply-trace
			  (cdr sig)
			  (list
			   (make-trace
			    'deep-inference-rule
			    (list ctx *true* expr)
			    (list (make-trace 'proof-hole)
				  (make-trace 'implication-rule
					      nargs
					      (list (make-trace 'not-false-rule)))
				  (make-trace 'true-rule))))))
		   *true*))
		 ((tc-eq (cadr nargs) *true*)
		  (values
		   (cons '?
			 (apply-trace
			  (cdr sig)
			  (list
			   (make-trace
			    'deep-inference-rule
			    (list ctx *true* expr)
			    (list (make-trace 'proof-hole)
				  (make-trace 'implication-rule
					      nargs
					      (list (make-trace 'true-rule)))
				  (make-trace 'true-rule))))))
		   *true*))
		 ((tc-eq (car nargs) *true*)
		  (values
		   (cons '?
			 (apply-trace
			  (cdr sig)
			  (list
			   (make-trace
			    'deep-inference-rule
			    (list ctx (cadr nargs) expr)
			    (list (make-trace 'proof-hole)
				  (make-trace 'implication-rule
					      nargs
					      (list (make-trace 'axiom-rule (list (cadr nargs)))))
				  (make-trace 'not-implication-rule
					      nargs
					      (list (make-trace 'axiom-rule (list (cadr nargs)))
						    (make-trace 'true-rule))))))))
		   (cadr nargs)))
		 ((tc-eq (cadr nargs) *false*)
		  (let ((neg-res (make!-negation-with-proofs (car nargs))))
		    (values
		     (cons '?
			   (apply-trace
			    (cdr sig)
			    (list (make-trace
				   'deep-trusted-rule
				   (list ctx
					 'implicationsimp
					 (compute-negation (car nargs))
					 expr)
				   (list (make-trace
					  'deep-inference-rule
					  (list ctx
						(car neg-res)
						(compute-negation (car nargs)))
					  (list (make-trace 'proof-hole)
						(apply-trace
						 (car (cdr neg-res))
						 (list (make-trace
							'axiom-rule
							(list (car neg-res)))))
						(apply-trace
						 (cdr (cdr neg-res))
						 (list (make-trace
							'axiom-rule
							(list
							 (compute-negation (car nargs)))))))))))))
		     (car neg-res))))
		 (t
		  (do-auto-rewrite expr sig (make-ctx 'not-implemented 'c98))))))

(defmethod assert-if-application*-i ((expr conjunction) newop  newargs sig ctx)
  (declare (ignore newop))
  (let ((nargs (argument-list newargs)))
    (cond ((tc-eq (car nargs) *true*)
	   (values
	    (cons '?
		  (apply-trace
		   (cdr sig)
		   (list
		    (make-trace
		     'deep-inference-rule
		     (list ctx (cadr nargs) expr)
		     (list (make-trace 'proof-hole)
			   (make-trace 'and-rule
				       nargs
				       (list (make-trace 'true-rule)
					     (make-trace 'axiom-rule (list (cadr nargs)))))
			   (make-trace 'not-and-rule
				       nargs
				       (list (make-trace 'axiom-rule (list (cadr nargs)))))
			   )))))
	    (cadr nargs)))
	  ((or (tc-eq (car nargs) *false*)
	       (tc-eq (cadr nargs) *false*))
	   (values (cons '?
			 (apply-trace
			  (cdr sig)
			  (list
			   (make-trace
			    'deep-inference-rule
			    (list ctx *false* expr)
			    (list (make-trace 'proof-hole)
				  (make-trace 'not-false-rule)
				  (make-trace 'not-and-rule
					      (list (car nargs) (cadr nargs))
					      (list (make-trace 'not-false-rule))))))))
		   *false*))
	  ((tc-eq (cadr nargs) *true*)
	   (values
	    (cons '?
		  (apply-trace
		   (cdr sig)
		   (list
		    (make-trace
		     'deep-inference-rule
		     (list ctx (car nargs) expr)
		     (list (make-trace 'proof-hole)
			   (make-trace 'and-rule
				       nargs
				       (list (make-trace 'axiom-rule (list (car nargs)))
					     (make-trace 'true-rule)))
			   (make-trace 'not-and-rule
				       nargs
				       (list (make-trace 'axiom-rule (list (car nargs))))))))))
	    (car nargs)))
	  (t
	   (do-auto-rewrite expr sig (make-ctx 'not-implemented 'c99))))))

(defmethod assert-if-application*-i ((expr disjunction) newop  newargs sig ctx)
  (declare (ignore newop))
  (let ((nargs (argument-list newargs)))
    (cond ((or (tc-eq (car nargs) *true*)
	       (tc-eq (cadr nargs) *true*))
	   (values (cons '?
			 (apply-trace
			  (cdr sig)
			  (list
			   (make-trace
			    'deep-inference-rule
			    (list ctx *true* expr)
			    (list (make-trace 'proof-hole)
				  (make-trace 'or-rule
					      (list (car nargs) (cadr nargs))
					      (list (make-trace 'true-rule)))
				  (make-trace 'true-rule))))))
		   *true*))
	  ((tc-eq (car nargs) *false*)
	   (values
	    (cons '?
		  (apply-trace
		   (cdr sig)
		   (list
		    (make-trace
		     'deep-inference-rule
		     (list ctx (cadr nargs) expr)
		     (list (make-trace 'proof-hole)
			   (make-trace 'or-rule
				       (list (car nargs) (cadr nargs))
				       (list (make-trace 'axiom-rule (list (cadr nargs)))))
			   (make-trace 'not-or-rule
				       (list (car nargs) (cadr nargs))
				       (list (make-trace 'not-false-rule)
					     (make-trace 'axiom-rule (list (cadr nargs))))))))))
	    (cadr nargs)))
	  ((tc-eq (cadr nargs) *false*)
	   (values
	    (cons '?
		  (apply-trace
		   (cdr sig)
		   (list
		    (make-trace
		     'deep-inference-rule
		     (list ctx (car nargs) expr)
		     (list (make-trace 'proof-hole)
			   (make-trace 'or-rule
				       (list (car nargs) (cadr nargs))
				       (list (make-trace 'axiom-rule (list (car nargs)))))
			   (make-trace 'not-or-rule
				       (list (car nargs) (cadr nargs))
				       (list (make-trace 'axiom-rule (list (car nargs)))
					     (make-trace 'not-false-rule))))))))
	    (car nargs)))
	  (t
	   (do-auto-rewrite expr sig (make-ctx 'not-implemented 'c100))))))

(defmethod assert-if-application*-i ((expr iff-or-boolean-equation)
				   newop  newargs sig ctx)
  (declare (ignore newop))  
  (let* ((nargs (argument-list newargs))
		(left (car nargs))
		(right (cadr nargs)))
	   (cond ((tc-eq left *true*)
		  (values
		   (cons '?
			 (let ((trace
				(make-trace
				 'deep-inference-rule
				 (list ctx right (compute-iff left right))
				 (list (make-trace 'proof-hole)
				       (make-trace
					'iff-rule
					(list left right)
					(list (make-trace
					       'implication-rule
					       (list left right)
					       (list (make-trace 'axiom-rule (list right))))
					      (make-trace
					       'implication-rule
					       (list right left)
					       (list (make-trace 'true-rule)))))
				       (make-trace
					'not-iff-rule
					(list left right)
					(list (make-trace
					       'not-implication-rule
					       (list left right)
					       (list (make-trace 'axiom-rule (list right))
						     (make-trace 'true-rule)))))))))
			   (if (iff? expr)
			       (apply-trace (cdr sig) (list trace))
			     (make-trace 'not-implemented 'p121))))
		   right))
		 ((tc-eq right *true*)
		  (let ((trace
			 (make-trace
			  'deep-inference-rule
			  (list ctx left (compute-iff left right))
			  (list (make-trace 'proof-hole)
				(make-trace
				 'iff-rule
				 (list left right)
				 (list (make-trace
					'implication-rule
					(list left right)
					(list (make-trace 'true-rule)))
				       (make-trace
					'implication-rule
					(list right left)
					(list (make-trace 'axiom-rule (list left))))))
				(make-trace
				 'not-iff-rule
				 (list left right)
				 (list (make-trace
					'not-implication-rule
					(list right left)
					(list (make-trace 'axiom-rule (list left))
					      (make-trace 'true-rule)))))))))
		    (values
		     (cons '?
			   (if (iff? expr)
			       (apply-trace
				(cdr sig)
				(list trace))
			     (apply-trace
				(cdr sig)
				(list (make-trace
				       'deep-inference-rule
				       (list ctx
					     (compute-iff left right)
					     expr)
				       (list trace
					     (make-trace
					      'extprop-rule
					      (list left right)
					      (list (make-trace
						     'axiom-rule
						     (list (compute-iff left right)))))
					     (make-trace
					      'leibniz-rule
					      (list (make-ctx
						     'application
						     (list (make-ctx 'expr (operator
									    (compute-iff left right)))
							   (make-ctx
							    'tuple
							    (list
							     (make-ctx 'expr left)
							     (make-ctx 'expr-hole (type right))))))
						    left
						    right)
					      (list (make-trace
						     'iff-rule
						     (list left left)
						     (list (make-trace
							    'implication-rule
							    (list left left)
							    (list (make-trace
								   'axiom-rule
								   (list left))))
							   (make-trace
							    'implication-rule
							    (list left left)
							    (list (make-trace
								   'axiom-rule
								   (list left))))))
						    (make-trace 'axiom-rule
								(list expr))))))))))
		     left)))
		 ((tc-eq left *false*) ;;NSH(1.20.96) added
		  (let* ((neg-res (negate-with-proofs right))
			 (trace
			  (make-trace
			   'deep-inference-rule
			   (list ctx (compute-negation right) (compute-iff left right))
			   (list (make-trace
				  'deep-inference-rule
				  (list ctx (car neg-res) (compute-negation right))
				  (list (make-trace 'proof-hole)
					(apply-trace
					 (car (cdr neg-res))
					 (list (make-trace
						'axiom-rule
						(list (car neg-res)))))
					(apply-trace
					 (cdr (cdr neg-res))
					 (list (make-trace
						'axiom-rule
						(list (compute-negation right)))))))
				 (make-trace
				  'iff-rule
				  (list left right)
				  (list (make-trace
					 'implication-rule
					 (list left right)
					 (list (make-trace 'not-false-rule)))
					(make-trace
					 'implication-rule
					 (list right left)
					 (list (make-trace
						'axiom-rule
						(list (compute-negation right)))))))
				 (make-trace
				  'not-iff-rule
				  (list left right)
				  (list (make-trace
					 'not-implication-rule
					 (list right left)
					 (list (make-trace 'not-false-rule)
					       (make-trace 'axiom-rule
							   (list right))))))))))
		    (values
		     (cons '?
			   (if (iff? expr)
			       (apply-trace
				(cdr sig)
				(list trace))
			     (apply-trace
				(cdr sig)
				(list (make-trace
				       'deep-inference-rule
				       (list ctx
					     (compute-iff left right)
					     expr)
				       (list trace
					     (make-trace
					      'extprop-rule
					      (list left right)
					      (list (make-trace
						     'axiom-rule
						     (list (compute-iff left right)))))
					     (make-trace
					      'leibniz-rule
					      (list (make-ctx
						     'application
						     (list (make-ctx 'expr (operator
									    (compute-iff left right)))
							   (make-ctx
							    'tuple
							    (list
							     (make-ctx 'expr left)
							     (make-ctx 'expr-hole (type right))))))
						    left
						    right)
					      (list (make-trace
						     'iff-rule
						     (list left left)
						     (list (make-trace
							    'implication-rule
							    (list left left)
							    (list (make-trace
								   'axiom-rule
								   (list left))))
							   (make-trace
							    'implication-rule
							    (list left left)
							    (list (make-trace
								   'axiom-rule
								   (list left))))))
						    (make-trace 'axiom-rule
								(list expr))))))))))
		     (car neg-res))))
		 ((tc-eq right *false*)
		  (let* ((neg-res (negate-with-proofs left))
			 (trace
			  (make-trace
			   'deep-inference-rule
			   (list ctx (compute-negation left) (compute-iff left right))
			   (list (make-trace
				  'deep-inference-rule
				  (list ctx (car neg-res) (compute-negation left))
				  (list (make-trace 'proof-hole)
					(apply-trace
					 (car (cdr neg-res))
					 (list (make-trace
						'axiom-rule
						(list (car neg-res)))))
					(apply-trace
					 (cdr (cdr neg-res))
					 (list (make-trace
						'axiom-rule
						(list (compute-negation left)))))))
				 (make-trace
				  'iff-rule
				  (list left right)
				  (list (make-trace
					 'implication-rule
					 (list left right)
					 (list (make-trace
						'axiom-rule
						(list (compute-negation left)))))
					(make-trace
					 'implication-rule
					 (list right left)
					 (list (make-trace 'not-false-rule)))))
				 (make-trace
				  'not-iff-rule
				  (list left right)
				  (list (make-trace
					 'not-implication-rule
					 (list left right)
					 (list (make-trace 'not-false-rule)
					       (make-trace 'axiom-rule
							   (list left))))))))))
		    (values
		     (cons '?
			   (if (iff? expr)
			       (apply-trace
				(cdr sig)
				(list trace))
			     (apply-trace
				(cdr sig)
				(list (make-trace
				       'deep-inference-rule
				       (list ctx
					     (compute-iff left right)
					     expr)
				       (list trace
					     (make-trace
					      'extprop-rule
					      (list left right)
					      (list (make-trace
						     'axiom-rule
						     (list (compute-iff left right)))))
					     (make-trace
					      'leibniz-rule
					      (list (make-ctx
						     'application
						     (list (make-ctx 'expr (operator
									    (compute-iff left right)))
							   (make-ctx
							    'tuple
							    (list
							     (make-ctx 'expr left)
							     (make-ctx 'expr-hole (type right))))))
						    left
						    right)
					      (list (make-trace
						     'iff-rule
						     (list left left)
						     (list (make-trace
							    'implication-rule
							    (list left left)
							    (list (make-trace
								   'axiom-rule
								   (list left))))
							   (make-trace
							    'implication-rule
							    (list left left)
							    (list (make-trace
								   'axiom-rule
								   (list left))))))
						    (make-trace 'axiom-rule
								(list expr))))))))))
		     (car neg-res))))
		 ((tc-eq (car nargs)(cadr nargs))
		  (values
		   (cons '?
			 (if (iff? expr)
			     (apply-trace
			      (cdr sig)
			      (list (make-trace
				     'deep-inference-rule
				     (list ctx *true* (compute-iff left right))
				     (list (make-trace 'proof-hole)
					   (make-trace
					    'iff-rule
					    (list left right)
					    (list (make-trace
						   'implication-rule
						   (list left right)
						   (list (make-trace 'axiom-rule (list left))))
						  (make-trace
						   'implication-rule
						   (list right left)
						   (list (make-trace 'axiom-rule (list left))))))
					   (make-trace 'true-rule)))))
			   (make-trace 'not-implemented 'p122)))
		   *true*))
		 (t
		  (do-auto-rewrite expr sig (make-ctx 'not-implemented 'c101))))))

(defmethod assert-if-application*-i ((expr equation) newop newargs sig ctx)
  (declare (ignore newop))
  (assert-equality expr newargs sig ctx))

(defmethod assert-if-application*-i ((expr disequation) newop newargs sig ctx)
  (declare (ignore newop))
  (assert-disequality expr newargs sig ctx))

(defmethod assert-if-application*-i (expr newop newargs sig ctx)
  (cond ((or (is-addition? expr) (is-subtraction? expr))
	 (multiple-value-bind (newsig newval)
	     (assert-if-addition expr newargs (car sig))
	     (values (cons newsig
			   (apply-trace
			    (cdr sig)
			    (list 
			     (make-trace 'deep-trusted-rule
					 (list ctx 'rational newval expr)
					 (list (make-trace 'proof-hole))))))
		     newval)))
	((is-multiplication? expr)
	 (multiple-value-bind (newsig newval)
	     (assert-if-multiplication expr newargs (car sig))
	     (values (cons newsig
			   (apply-trace
			    (cdr sig)
			    (list 
			     (make-trace 'deep-trusted-rule
					 (list ctx 'rational newval expr)
					 (list (make-trace 'proof-hole))))))
		     newval)))
	((and *use-rationals*
	       (is-division? expr))
	 (multiple-value-bind (newsig newval)
	     (assert-if-division expr newargs (car sig))
	     (values (cons newsig
			   (apply-trace
			    (cdr sig)
			    (list 
			     (make-trace 'deep-trusted-rule
					 (list ctx 'rational newval expr)
					 (list (make-trace 'proof-hole))))))
		     newval)))
	((and (typep newop 'name-expr)
	      (accessor? newop)
	      (typep newargs 'application)
	      (typep (operator newargs) 'name-expr)
	      (member (declaration (operator newargs)) (constructor newop)
		      :test #'same-id)) ;;NSH(9.29.00) was tc-eq-ops
	                        ;;which is too strong.
	 (multiple-value-bind (newsig newval)
	     (values-assert-if
	      '?
	      (let ((accessors (accessors (operator newargs))))
		(if (cdr accessors)
		    (let ((args (arguments newargs))
			  (pos (position newop accessors :test #'same-id)))
		      ;;was tc-eq-ops (see above)
		      (if (cdr args)
			  (nth pos (arguments newargs))
			(make!-projection-application (1+ pos) (car args))))
		  (argument newargs)))
	      expr)
	     (values (cons newsig
			   (make-trace 'not-implemented 'p132))
		     newval)))
	((function-update-redex? expr)
	 (let ((result
		(simplify-function-update-redex expr)))
	   (if (tc-eq result expr)
	       (multiple-value-bind
		(newsig newval)
		(do-auto-rewrite expr (cons (car sig) (make-trace 'not-implemented 'p265))
				 (make-ctx 'not-implemented 'c102))
		   (values (cons (car newsig)
				 (make-trace 'not-implemented 'p133))
			   newval))
	     (values (cons '?
			   (make-trace 'not-implemented 'p134))
		     result))))
	((accessor-update-redex? expr)
	 (let ((result
		(simplify-accessor-update-redex expr)))
	   (if (tc-eq result expr)
	       (multiple-value-bind
		(newsig newval)
		(do-auto-rewrite expr (cons (car sig) (make-trace 'not-implemented 'p266))
				 (make-ctx 'not-implemented 'c103))
		   (values (cons (car newsig)
				 (make-trace 'not-implemented 'p135))
			   newval))
	     (values (cons '?
			   (make-trace 'not-implemented 'p126))
		     result))))
	(t (do-auto-rewrite expr sig ctx))))

(defun simplify-accessor-update-redex (expr)
  (let* ((op (operator expr))
	 (arg (argument expr))
	 (updates
	  (loop for assn in (assignments arg)
		when (eq (id op) (id (caar (arguments assn))))
		collect assn))
	 (expr-of-arg (expression arg)))
    (if updates
	(if (every #'(lambda (x) (cdr (arguments x)))
		   updates) ;;;a curried update::
	                             ;;;a(exp WITH [((a)(i)):= e])
	    (let ((newexpr;;NSH(9.15.94): otherwise TCCs
		   ;;are generated when domain is subtype.
		   ;;(let ((*generate-tccs* 'none)))
		   (make!-update-expr
		    (make-accessor-update-reduced-application
		     op expr-of-arg)
		    (mapcar #'(lambda (x)
				(lcopy x 'arguments
				       (cdr (arguments x))))
		      updates))))
	      newexpr)
	    (nth-value 1 (make-update-expr-from-updates updates)))
	(make-accessor-update-reduced-application op expr-of-arg))))
  
(defun assert-if-application (expr newop newargs sig ctx)
  (cond ((eq *assert-flag* 'rewrite)
	 (multiple-value-bind
	  (newsig newval)
	  (do-auto-rewrite expr (cons (car sig) (make-trace 'not-implemented 'p268))
			   (make-ctx 'not-implemented 'c105))
	     (values (cons (car newsig)
			   (make-trace 'not-implemented 'p99))
		     newval)))
	(t (assert-if-application*-i expr newop newargs sig ctx))))

;	 (multiple-value-bind (nsig nval)
;	       (assert-if-application* expr newop newargs sig)
;	     (multiple-value-bind (osig oval)
;		 (old-assert-if-application expr newop newargs sig)
;	       (if (and (eq nsig osig)
;			(tc-eq nval oval))
;		   (values nsig nval)
;		   (break "assert-if-app-mismatch")))))))

(defmethod assert-if-i ((expr projection-application) ctx)
  (declare (ignore ctx))
  (with-slots (index argument) expr
    (multiple-value-bind (sig newarg)
	(assert-if-i argument (make-ctx 'not-implemented 'c34))
      (multiple-value-bind (newsig newexpr)
	  (reduce-proj-application (car sig) newarg index expr)
	;;NSH(11.22.94)
	(if (and (not (connective-occurs? newexpr))
		 ;;*boolean-context*
		 (tc-eq (find-supertype (type newexpr))
			*boolean*))
		(let ((result (assert-test newexpr)));;NSH(11.18.94)
		  (if (false-p result)
		      (multiple-value-bind
		       (sig newexpr)
		       (values-assert-if '? *false* newexpr)
		       (values (cons sig (make-trace 'not-implemented 'p207)) newexpr))
		    (if (true-p result)
			(multiple-value-bind
			 (sig newexpr)
			 (values-assert-if '? *true* newexpr)
			 (values (cons sig (make-trace 'not-implemented 'p208)) newexpr))
		      (multiple-value-bind
		       (sig newexpr)
		       (do-auto-rewrite newexpr
					(cons (car sig) (make-trace 'not-implemented 'p269))
					(make-ctx 'not-implemented 'c106))
		       (values (cons (car sig) (make-trace 'not-implemented 'p209)) newexpr)))))
	  (values (cons newsig (make-trace 'not-implemented 'p210)) newexpr))))))

(defun reduce-proj-application (sig newarg index &optional expr)
  ;;expr is only given at the top-level call.
  (cond ((typep newarg 'tuple-expr)
	 (values
	  '? (nth (1- index) (exprs newarg))))
	((typep newarg 'update-expr)
	 (tuple-update-reduce index newarg))
	((branch? newarg)
	 (let* ((thenval (nth-value 1
			   (reduce-proj-application
			    '? (then-part newarg) index)))
		(elseval (nth-value 1
			   (reduce-proj-application
			    '? (else-part newarg) index)))
		(new-expr (make!-if-expr (condition newarg) thenval elseval)))
	   (if expr
	       (values-assert-if '? new-expr expr)
	       (values '? new-expr))))
	(t (let ((new-expr (if expr 
			       (lcopy expr 'argument newarg)
			       (make!-projection-application index newarg))))
	     (multiple-value-bind
	      (newsig newexpr)
	      (do-auto-rewrite new-expr (cons sig (make-trace 'not-implemented 'p270))
			       (make-ctx 'not-implemented 'c107))
	      (values (car newsig) newexpr))))))

(defun tuple-update-reduce (index arg)
  (let ((updates (loop for assn in (assignments arg)
		 when (eql index (number (caar (arguments assn))))
		 collect assn))
	(expr-of-arg (expression arg)));(break)
    (if updates
	(if (every #'(lambda (x) (cdr (arguments x)))
		     updates) ;;;a curried update::
	                             ;;;PROJ_n(exp WITH [(n)(i):= e])
	    (let ((newexpr (make!-update-expr
			    (make-tuple-update-reduced-projection
			     index expr-of-arg)
			    (mapcar #'(lambda (x)
				    (lcopy x 'arguments
					   (cdr (arguments x))))
			      updates)
;			    (list (lcopy update 'arguments
;					 (cdr (arguments update)))
			    ;;(type (make!-projection-application index arg))
			    )))
	      (multiple-value-bind
	       (newsig newexpr)
	       (do-auto-rewrite
		newexpr
		(cons '? (make-trace 'not-implemented 'p271)) (make-ctx 'not-implemented 'c108))
	       (values (car newsig) newexpr)));;return a(exp) WITH [(i) := e] simplified.
	    (make-update-expr-from-updates updates))
	(multiple-value-bind
	 (newsig newexpr)
	 (do-auto-rewrite (make-tuple-update-reduced-projection
			   index expr-of-arg)
			  (cons '? (make-trace 'not-implemented 'p272))
			  (make-ctx 'not-implemented 'c109))
	 (values (car newsig) newexpr)))))

(defun make-tuple-update-reduced-projection (index expr)
  (let ((new-application (make!-projection-application index expr)))
    (if (typep expr 'update-expr)
	(nth-value 1 (tuple-update-reduce index expr))
	new-application)))

(defmethod assert-if-i ((expr injection-application) ctx)
  (declare (ignore ctx))
  (with-slots (index argument) expr
    (multiple-value-bind (sig newarg)
	(assert-if-i argument (make-ctx 'not-implemented 'c35))
      (if (and (extraction-application? newarg)
	       (= (index newarg) index))
	  (values (cons '? (make-trace 'not-implemented 'p211)) (argument newarg))
	(let ((newexpr (lcopy expr 'argument newarg)))
	  (values (cons (car sig) (make-trace 'not-implemented 'p212)) newexpr))))))

(defmethod assert-if-i ((expr injection?-application) ctx)
  (declare (ignore ctx))
  (with-slots (index argument) expr
    (multiple-value-bind (sig newarg)
	(assert-if-i argument (make-ctx 'not-implemented 'c36))
      (let* ((newexpr (lcopy expr 'argument newarg))
	     (result (check-other-injection?s newexpr)))
	(if (false-p result)
	    (multiple-value-bind
	     (sig newexpr)
	     (values-assert-if '? *false* expr)
	     (values (cons sig (make-trace 'not-implemented 'p213)) newexpr))
	  (if (true-p result)
	      (multiple-value-bind
	       (sig newexpr)
	       (values-assert-if '? *true* expr)
	       (values (cons sig (make-trace 'not-implemented 'p214)) newexpr))
	    (values (cons (car sig) (make-trace 'not-implemented 'p215)) newexpr)))))))

(defmethod assert-if-i ((expr extraction-application) ctx)
  (declare (ignore ctx))
  (with-slots (index argument) expr
    (multiple-value-bind (sig newarg)
	(assert-if-i argument (make-ctx 'not-implemented 'c37))
      (if (and (injection-application? newarg)
	       (= (index newarg) index))
	  (values (cons '? (make-trace 'not-implemented 'p216)) (argument newarg))
	  (let ((newexpr (lcopy expr 'argument newarg)))
	    (values (cons (car sig) (make-trace 'not-implemented 'p217)) newexpr))))))

;;NSH(9.14.94): updated assert-if(projection/field-application) to
;;distribute through if-then-else. 
(defmethod assert-if-i ((expr field-application) ctx)
  (declare (ignore ctx))
  (with-slots (id argument) expr
    (multiple-value-bind (sig newarg)
	(assert-if-i argument (make-ctx 'not-implemented 'c38))
      (multiple-value-bind
	  (newsig newexpr)
	  (reduce-field-application (car sig) newarg id expr)
	(cond
	 ((and (not (connective-occurs? newexpr))
	       ;;*boolean-context*
	       (tc-eq (find-supertype (type newexpr)) *boolean*))
	  (let ((result (assert-test newexpr)));;NSH(11.18.94)
	    (if (false-p result)
		(multiple-value-bind
		 (sig newexpr)
		 (values-assert-if '? *false* newexpr)
		 (values (cons sig (make-trace 'not-implemented 'p218)) newexpr))
	      (if (true-p result)
		  (multiple-value-bind
		   (sig newexpr)
		   (values-assert-if '? *true* newexpr)
		   (values (cons sig (make-trace 'not-implemented 'p219)) newexpr))
		(multiple-value-bind
		 (sig newexpr)
		 (do-auto-rewrite newexpr
				  (cons newsig (make-trace 'not-implemented 'p273))
				  (make-ctx 'not-implemented 'c110))
		 (values (cons (car sig) (make-trace 'not-implemented 'p220)) newexpr))))))
	 (t (values (cons newsig (make-trace 'not-implemented 'p221)) newexpr)))))))

(defun reduce-field-application (sig newarg id &optional expr)
  (let ((newexpr (if expr
		     (lcopy expr 'argument newarg)
		     (make!-field-application id newarg))))
    (cond ((record-redex? newexpr)
	   (values-assert-if
	    '?
	    (expression
	     (find id (assignments newarg)
		   :test #'(lambda (x y)
			     (eq x (id (caar (arguments y)))))))
	    newexpr))
	  ((record-update-redex? newexpr)
	   (record-update-reduce newexpr id newarg))
	  ((branch? newarg)
	   (let* ((thenval (nth-value 1 (reduce-field-application
					 '? (then-part newarg) id)))
		  (elseval (nth-value 1 (reduce-field-application
					 '? (else-part newarg) id)))
		  (newexpr (make!-if-expr (condition newarg) thenval elseval)))
	     (if expr
		 (values-assert-if '? newexpr expr)
		 (values '? newexpr))))
	  (t (multiple-value-bind
	      (newsig newexpr)
	      (do-auto-rewrite newexpr (cons sig (make-trace 'not-implemented 'p274))
			       (make-ctx 'not-implemented 'c111))
	      (values (car newsig) newexpr))))))

(defun assert-if-arg (expr sign)
  ;;called from assert-if(application)
  ;;expr is the original expr
  (let* ((ctx* (make-ctx 'application (list (make-ctx 'expr (operator expr))
					    (make-ctx 'expr-hole (type (argument expr))))))
	 (ctx
	 (if sign
	     ctx*;;positif
	   (make-ctx 'negation (list ctx*)))));;negatif
    (let ((arg (argument expr)))
      (cond ((or (implication? expr)
		 (conjunction? expr)
		 (disjunction? expr))
	     (let* ((arg1 (args1 expr))
		    (arg2 (args2 expr)))
	       (multiple-value-bind
		   (sig1 new-arg1)
		   (assert-if-i arg1
				(apply-ctx
				 ctx
				 (list (make-ctx
					'tuple
					(list (make-ctx 'expr-hole (type arg1))
					      (make-ctx 'expr arg2))))))
		 (multiple-value-bind
		     (sig2 new-arg2)
		     (let ((*assert-typepreds-off* t))
		       (assert-if-i arg2
				    (apply-ctx
				     ctx
				     (list (make-ctx
					    'tuple
					    (list (make-ctx 'expr new-arg1)
						  (make-ctx 'expr-hole (type arg2))))))))
		     (multiple-value-bind
		       (sigargs newargs)
		       (if (memq '? (list (car sig1) (car sig2)))
			   (do-auto-rewrite ;; utiliser sign
			    (lcopy arg
				   'exprs (list new-arg1 new-arg2))
			    (cons '?
				  (apply-trace (cdr sig1) (list (cdr sig2))))
			    (make-ctx 'not-implemented 'c112))
			 (do-auto-rewrite arg (cons 'X (make-trace 'proof-hole))
					  (make-ctx 'not-implemented 'c113))) ;; utiliser sign
		     (values sigargs newargs))))))
	    (t
	     (assert-if-i (argument expr) ctx))))))

(defmethod assert-if-i ((ex application) ctx) ; (break "assert-if-ap")
  (with-slots (operator argument) ex
	      (multiple-value-bind
	       (sigop newop)
	       (if (and (lambda? operator)
			(not (eq *assert-flag* 'rewrite)))
		   (values (cons 'X (make-trace 'not-implemented 'p293)) operator)
		 (assert-if-i operator (make-ctx 'not-implemented 'c42)))
	       (multiple-value-bind
		(sigargs newargs)
		(assert-if-i argument
			     (apply-ctx ctx
					(list (make-ctx 'application
							(list (make-ctx 'expr newop)
							      (make-ctx 'expr-hole (type argument)))))))
		(let* ((sig (if (eq (car sigop) '?) '? (car sigargs)))
		       (op (if (eq (car sigop) '?) newop operator))
		       (arg (if (eq (car sigargs) '?) newargs argument))
		       (expr ;;(simplify-or-copy-app ex op arg)
			(lcopy ex 'operator op 'argument arg))
		       (expr* (compute-application op arg))
		       (trace
			(if (tc-eq expr expr*)
			    (apply-trace
			     (cdr sigop) ;; to be merged with sig?
			     (list (cdr sigargs)))
			  (apply-trace
			   (cdr sigop)
			   (list (apply-trace
				  (cdr sigargs)
				  (list (make-trace 'deep-trusted-rule
						    (list ctx 'rational expr expr*)
						    (list (make-trace 'proof-hole)))))))))
		       (result
			(when (and (tc-eq (find-supertype (type expr)) *boolean*)
				   (not (eq *top-assert-flag* 'rewrite))
				   (not (negation? expr))
				   (not (connective-occurs? expr)) ;;NSH(11.27.02)
				   ) ;;this would be wasted work
			  (assert-test expr))
			))
		  ;; (format t "~%expr1: ~a" (compute-application op arg))
		  ;; (format t "~%expr2: ~a" (lcopy ex 'operator op 'argument arg))
		  ;; (format t "~%tc-eq?: ~a" (tc-eq (compute-application op arg)
		  ;; 				    (lcopy ex 'operator op 'argument arg)))
		  (cond ((true-p result)
			 ;; (format t "~%~a~%" expr)
			 ;; (show *dp-state*)
			 (values
			  (cons '?
				(apply-trace
				 trace
				 (list
				  (make-trace
				   'deep-decision-procedure
				   (list ctx *true* expr)
				   (list (make-trace 'proof-hole))))))
				 *true*))
			((false-p result)
			 (values
			  (cons '?
				(apply-trace
				 trace
				 (list
				  (make-trace
				   'deep-decision-procedure
				   (list ctx *false* expr)
				   (list (make-trace 'proof-hole))))))
				 *false*))
			((and (is-predicate? newop)
			      (adt? (find-supertype (type newargs)))
			      (typep newop 'name-expr)
			      (recognizer? newop))
			 (let ((result (check-other-recognizers
					newop newargs)))
			   (if (false-p result)
			       (multiple-value-bind
				(sig newexpr)
				(values-assert-if '? *false* expr)
				(values (cons sig (make-trace 'not-implemented 'p224)) newexpr))
			     (if (true-p result)
				 (multiple-value-bind
				  (sig newexpr)
				  (values-assert-if '? *true* expr)
				  (values (cons sig (make-trace 'not-implemented 'p225)) newexpr))
			       (multiple-value-bind
				(sig newexpr)
				(do-auto-rewrite expr (cons sig trace) (make-ctx 'not-implemented 'c114))
				(values (cons (car sig) (make-trace 'not-implemented 'p226)) newexpr))))))
			((and (is-predicate? newop)
			      (member expr (type-constraints newargs t)
				      :test #'tc-eq)) ;;(break)
			 ;; (assert (and 'assert3 nil));; FG to be modified later
			 (values-assert-if
			  (cons '?
				(make-trace 'not-implemented 'p3)
				;; (apply-trace
				;;  trace
				;;  (list
				;;   (make-trace
				;;    'deep-decision-procedure
				;;    (list ctx *true* expr)
				;;    (list (make-trace 'proof-hole)))

				;; (make-trace
				  ;;  'deep-inference-rule
				  ;;  (list ctx *true* expr)
				  ;;  (list (make-trace 'proof-hole)
				  ;; 	 (make-trace
				  ;; 	  'typepred-rule
				  ;; 	  (list (list (compute-negation expr)))
				  ;; 	  (list (make-trace 'axiom-rule (list expr))))
				  ;; 	 (make-trace 'true-rule)))
				  )
			  *true*
			  expr))
			;;NSH(9.10.93) The case above is kept here so that assert-if-inside doesn't
			;;remove something brought in by typepred.
			((and (equation? expr) ;;moved here from
			      ;;assert-if-application so that
			      ;;assert-if-inside does not
			      ;;self-simplify antecedent
			      ;;equalities.
			      (tc-eq (find-supertype (type (car (exprs newargs))))
				     *number*)
			      (not (connective-occurs? expr)))
			 (assert-numeric-equality expr (cons sig trace) ctx))
			(t
			 (assert-if-application expr newop newargs (cons sig trace) ctx))))))))

;;FG reference is (app op arg), not expr
(defmethod simplify-or-copy-app (expr (op name-expr) arg
				      &optional (type (type expr)))
  (or (and *use-rationals*
	   (simplify-ground-arith op arg);;FG this can be nil
	   (cons (simplify-ground-arith op arg) (make-trace 'not-implemented 'p73)))
      (cons (lcopy expr 'operator op 'argument arg 'type type) (make-trace 'proof-hole))))

;;FG reference is (app op arg), not expr
(defmethod simplify-or-copy-app (expr op arg &optional (type (type expr)))
  (cons (lcopy expr 'operator op 'argument arg 'type type) (make-trace 'proof-hole)))

(defun ground-arith-simplifiable? (op arg)
  (and *use-rationals*
       (name-expr? op)
       (memq (id op) '(+ - * /))
       (resolution op)
       (eq (id (module-instance op)) '|number_fields|)
       (if (tuple-expr? arg)
	   (every #'rational-expr? (exprs arg))
	   (rational-expr? arg))
       (or (not (eq (id op) '/))
	   (not (zerop (number (cadr (exprs arg))))))))

(defun simplify-ground-arith (op arg)
  (when (ground-arith-simplifiable? op arg)
    (let ((num (apply (id op) (if (tuple-expr? arg)
				  (mapcar #'number (exprs arg))
				  (list (number arg))))))
      (make!-number-expr num))))

(defun do-auto-rewrite (expr sig ctx)
  (let* ((op* (operator* expr)) ;; op* ((f a) b) is f, not (f a)
	 ;;;these are all the rewritable op*s.
	 (hashname (auto-rewrite-hashname op*))
	 (decl (if (name-expr? hashname)
		   (declaration hashname)
		   hashname)))  ;;(break "in-do-auto-rewrite")
    (if (and (not (memq *assert-flag*
			'(record simplify)));;do only if flag is rewrite/assert
	     decl
	     (gethash decl *auto-rewrites-ops*))
	(if *hash-rewrites?*
	    (do-auto-rewrite-memo expr op* decl sig ctx)
	   (do-auto-rewrite-non-memo expr op* decl sig ctx))
      (values sig expr))))


(defun do-auto-rewrite-memo (expr op* decl sig ctx)
  (let ((hash-res (gethash expr *rewrite-hash*)))
    (if hash-res
	(do-auto-rewrite-memo* expr op* decl sig hash-res ctx)
	(let ((top-hash-res (when *top-rewrite-hash*
			      (gethash expr *top-rewrite-hash*))))
	  (if top-hash-res
	      (do-auto-rewrite-memo* expr op* decl sig top-hash-res ctx)
	    (do-auto-rewrite-non-memo-then-hash expr op* decl sig ctx))))))


(defun do-auto-rewrite-memo* (expr op* decl sig hash-res ctx)
  (assert (= (length hash-res) 5))
  (let* ((hashed-result (nth 0 hash-res))
	 (hashed-dp-state (nth 1 hash-res))
	 (hashed-rewrites (nth 2 hash-res))
	 (hashed-rewrites! (nth 3 hash-res))
	 (hashed-macros (nth 4 hash-res))) ;;(break "memo")
	(progn
	  (incf *rewrite-hits*)
	  (if (and (not (dpi-state-changed? hashed-dp-state *dp-state*))
		   ;;if context unchanged since hashing
		   (eq *auto-rewrites-names* hashed-rewrites)
		   (eq *auto-rewrites!-names* hashed-rewrites!)
		   (eq *macro-names* hashed-macros))
	      (if (eq hashed-result 'X) ; Previous rewrites did not alter expr.
		  (values sig expr);;FG cdr sig
		(values (cons '?
			      (apply-trace (cdr sig)
					   (list
					    (make-trace 'deep-trusted-rule
							(list ctx 'hashed hashed-result expr)
							(list (make-trace 'proof-hole))))))
			hashed-result))
	      (multiple-value-bind (newsig newexpr)
		  (progn (remhash expr *rewrite-hash*)
			 (if (eq hashed-result 'X);then rewrite, else assert rhs.
			     (do-auto-rewrite-non-memo
			      expr op* decl
			      (cons 'X (make-trace 'proof-hole)) ctx)
			   (multiple-value-bind
			    (newsig newexpr)
			    (lazy-assert-if-i hashed-result ctx)
			    (values (cons (car newsig)
					  (make-trace 'not-implemented 'p16));;FG NO cdr sig
				    newexpr))))
		(cond ((and (eq hashed-result 'X)
			    (eq (car newsig) 'X))
		       (set-rewrite-hash expr 'X)
		       (values sig expr))
		      ((eq (car newsig) 'X)
		       (set-rewrite-hash expr hashed-result)
		       (values (cons '?
				     (apply-trace (cdr sig)
						  (list
						   (make-trace 'deep-trusted-rule
							       (list ctx 'hashed hashed-result expr)
							       (list (make-trace 'proof-hole))))))
			       hashed-result))
		      (t (set-rewrite-hash expr newexpr)
			 (values (cons '?
				       (apply-trace (cdr sig)
						    (list (cdr newsig))))
				 newexpr))))))))

(defun do-auto-rewrite-non-memo-then-hash (expr op* decl sig ctx)
  (if (or (null *top-rewrite-hash*)
	  (eq *top-rewrite-hash* *rewrite-hash*)
	  (freevars expr));;NSH(4.2.95):means there are free
      ;;occurrences of bound variables in expr and these should
      ;;not be hashed at the top level.  
      (do-auto-rewrite-non-memo-then-hash* expr op* decl sig ctx)
    (multiple-value-bind
     (topsig topexpr)
     (nprotecting-cong-state
      ((*dp-state* *top-dp-state*))
      (let ((*rewrite-hash* *top-rewrite-hash*))
	(do-auto-rewrite-non-memo-then-hash* expr op* decl sig ctx)))
     (if (eq (car topsig) 'X)
	 (do-auto-rewrite-non-memo-then-hash* expr op* decl sig ctx)
       (multiple-value-bind
	(newsig newexpr)
	(lazy-assert-if-i topexpr ctx)
	(cond ((eq (car newsig) topexpr)
	       (set-rewrite-hash expr topexpr)
	       (values (cons '? (make-trace 'not-implemented 'p295)) topexpr));;FG cdr sig)
	      (t (set-rewrite-hash expr newexpr)
		 (values (cons '?
			       (apply-trace (cdr topsig)
					    (list (cdr newsig))))
			 newexpr))))))));;FG cdr sig)

(defun set-rewrite-hash (expr result)
  (let ((hashed-dp-state (dpi-copy-state *dp-state*)))
    (setf (gethash expr *rewrite-hash*)
	  (list result
		hashed-dp-state
		*auto-rewrites-names*
		*auto-rewrites!-names*
		*macro-names*))))

(defun do-auto-rewrite-non-memo-then-hash* (expr op* decl sig ctx)
  (multiple-value-bind (newsig newexpr)
	  (do-auto-rewrite-non-memo expr op* decl (cons 'X (make-trace 'proof-hole)) ctx)
	(incf *rewrite-misses*)
	(cond ((eq (car newsig) 'X)
	       (set-rewrite-hash expr 'X)
	       (values sig expr))
	    (t (set-rewrite-hash expr newexpr)
	       (values (cons (car newsig)
			     (apply-trace (cdr sig)
					  (list (cdr newsig))))
		       newexpr)))))



(defun do-auto-rewrite-non-memo (expr op* decl sig ctx)
  (auto-rewrite* expr
		 sig
		 (gethash  decl    ;;;get the rewrite rules for decl.
			   *auto-rewrites*)
		 ctx
		 op*))


(defun flag-assert-if (expr ctx &optional flag)
  (let ((*assert-flag* flag))
    (assert-if-i expr ctx)))

(defun is-res-rewrite (res)
  (find res *all-rewrites-names* :test #'tc-eq))

(defun is-res-macro (res)
  (memq res *macro-names*))

(defun is-res-auto-rewrite-non! (res)
  (memq res *auto-rewrites-names*))

(defun is-res-auto-rewrite! (res)
  (memq res *auto-rewrites!-names*))

(defun is-res-auto-rewrite (res)
    (or (is-res-auto-rewrite-non! res)
	(is-res-auto-rewrite! res)
	(is-res-macro res)))

(defun generic? (res)
  (and (resolution? res)
       (null (actuals (module-instance res)))))

	      
(defun op*-depth (expr)
  (if (application? expr)(1+ (op*-depth (operator expr))) 0))

(defmethod id ((res resolution))
  (id (declaration res)))

(defun auto-rewrite* (expr oldsig hashentry ctx &optional op*)
  ;;hashentry is a list of rewrite rules for op*
  (if (null hashentry)
      (values (cons (car oldsig) (make-trace 'not-implemented 'p298)) expr)
      (let* ((hashentry1 (car hashentry)) ;;get first rewrite rule
	     (res (res hashentry1)) ;; get resolution for rewrite rule.
	     (res-decl (unless (consp res) (declaration res)))
	     ;;to handle antecedent rewrites.
	     (mod-inst (when res-decl (module-instance res)))
	     (modsubst
	      (if (and res-decl
		       (typep res-decl 'formula-decl))
		  (let* ((current-mod? (eq (module res-decl)
					   (current-theory)))
			 (actuals (unless current-mod? (actuals mod-inst)))
			 (formals (unless current-mod?
				    (formals-sans-usings
				     (module res-decl)))))
		    (if (or (null formals) actuals)
			t
			(mapcar #'(lambda (x) (list x))
			  formals)))
		  t))
	     (lhs-hashentry (lhs hashentry1)))
	(cond ((and (eq expr op*)
		    (is-res-macro res)
		    (name-expr? op*)
		    (if (generic? res)
			(tc-eq (declaration op*)(declaration res))
			(tc-eq (resolution op*) res)))
	       (let* ((defns (create-formulas (resolution op*)))
		      (rhs (args2 (car (last defns)))))
		 (format-rewrite-msg (id (declaration res)) expr rhs)
		 (push-references-list (module-instance res) *dependent-decls*)
		 (pushnew (declaration res) *dependent-decls*)
		 (values (cons '? (make-trace 'not-implemented 'p299)) rhs)))
	      ((not (eql (op*-depth expr)
			 (op*-depth lhs-hashentry)))
	       (auto-rewrite* expr oldsig (cdr hashentry) ctx op*))
	      (t (let* ((def-or-lemma? (if (is-res-auto-rewrite res)
					   (if (typep res-decl 'def-decl)
					       'def-decl
					       (if (typep res-decl 'const-decl)
						   'const-decl
						   'formula-decl))
					   nil))
			(defn
			  (when (and (constant? op*)
				     (memq def-or-lemma? '(const-decl def-decl))
				     (if (generic? res)
					 (tc-eq (declaration op*) res-decl)
					 (tc-eq (resolution op*) res)))
			    (let ((defns (create-formulas (resolution op*))))
			      (car defns))))
			(defbody (when defn (if (forall-expr? defn)
						(expression defn)
						defn)))
			(lhs (if defbody (args1 defbody)
				 (if (eq def-or-lemma? 'formula-decl)
				     (lhs hashentry1)
				     nil)))
			(rhs (if defbody (args2 defbody)
				 (if (eq def-or-lemma? 'formula-decl)
				     (rhs hashentry1)
				     nil)))
			(if-flag (if defbody
				     (or (def-decl? res-decl)
					 (is-res-auto-rewrite-non! res))
				   (is-res-auto-rewrite-non! res)))
			(rewrite-rule-flag;; FG record trace as a rewrite rule or not
			 (not (or (eq def-or-lemma? 'formula-decl)
				  (and (eq def-or-lemma? 'def-decl)
				       defn
				       (measure (declaration (resolution op*))))))))
		   (multiple-value-bind (usubst modsubst)
		       (if defn
			   (values
			    (loop for vars in (arguments* lhs)
				  as args in (arguments* expr)
				  nconc (pairlis-args
					 (mapcar #'declaration vars)
					 args))
			    t)
			   (if lhs
			       (let ((*modsubst* modsubst) ;;no tccs in match
				     (*generate-tccs* 'none)
				     (*no-match-assert-test* t))
				 (values (match lhs expr nil nil)
					 *modsubst*))
			       'fail))
		     (let* ((psubst (if (eq usubst 'fail)
					usubst
					(sort-alist usubst)))
			    (modsubst (unless (or (eq psubst 'fail)
						  (eq modsubst t))
					(if (every #'cdr modsubst)
					    (copy mod-inst
					      'actuals
					      (mapcar
						  #'(lambda (x)
						      (mk-actual (cdr x)))
						modsubst))
					    'fail)))
			    (subst (if (or (eq psubst 'fail)
					   (null modsubst)
					   (eq modsubst 'fail))
				       psubst
				       (subst-mod-params-substlist
					psubst modsubst (module res-decl))))
			    (nsubst (when (consp subst)
				      (mapcan #'(lambda (p1 p2)
						  (unless (eq (car p1) (car p2))
						    (list (cons (car p1) (car p2)))))
					psubst subst)))
			    (hyp (substit (hyp hashentry1) nsubst)) ;; FG caution with substit
			    (hyp (unless (or (null hyp)
					     (eq subst 'fail)
					     (eq modsubst 'fail))
				   (if (null modsubst)
				       hyp
				       (subst-mod-params hyp modsubst))))
			    ;; defn may have been simplidfed, e.g. p = true
			    ;; simplifies (in substit) to p.  There is a
			    ;; flag for controlling this, but then hashing
			    ;; must be made aware of the flag settings.
			    ;; Easier just to return *true*.
			    (rhs (or (substit rhs nsubst) *true*)) ;; FG caution with substit
			    (rhs (unless (or (eq subst 'fail)
					      (eq modsubst 'fail))
				    (if (null modsubst)
					rhs
					(subst-mod-params rhs modsubst)))))
		       (cond ((or (eq subst 'fail)(eq modsubst 'fail))
			      (if lhs ;;then match must've failed.
				  (track-rewrite-format
				   res expr
				   "LHS ~a does not match."
				   lhs))
			      (auto-rewrite* expr oldsig
					     (cdr hashentry) ctx op*))
			     (t 
			      ;; (when ;;FG check
			      ;; 	  (and rewrite-rule-flag
			      ;; 	       (not (tc-eq (compute-normalize
			      ;; 			    (compute-substit rhs subst))
			      ;; 			   (compute-normalize expr))))
			      ;; 	(show (declaration (res hashentry1)))
			      ;; 	(assert nil))
			      (if defbody
				  (multiple-value-bind (sigrhs newrhs)
				      (cond ((is-res-auto-rewrite! res)
					     (inc-rewrite-depth res)
;					     (format t "~%test: ~a~%" rhs)
					     (let ((result (substit-with-proofs
							    rhs
							    subst
							    ctx)))
					       (multiple-value-bind
						   (sig newexpr)
						   (flag-assert-if
						    (car result) ctx) ;; FG caution with substit
						   (values (cons (car sig)
								 (make-trace
								  'rewrite-rule2
								  (list ctx
									(compute-substit rhs subst)
									expr
									rewrite-rule-flag)
								  (list (apply-trace
									 (cdr result)
									 (list (cdr sig))))))
							 newexpr))))
					    (t
					     (multiple-value-bind
						   (sig newexpr)
						   (top-lazy-assert-if-with-subst
						    rhs subst ctx
						    if-flag
						    res)
						 (values (cons (car sig)
							       (make-trace
								  'rewrite-rule2
								  (list ctx
									(compute-substit rhs subst)
									expr
									rewrite-rule-flag)
								  (list (cdr sig))))
							 newexpr))))
				    (decf *auto-rewrite-depth*)	;;NSH(5.26.95)
				    (cond ((and if-flag (eq (car sigrhs) 'X))
			 ;;;then ignore current rewrite.
					   (track-rewrite-format
					    res expr
					    "RHS did not simplify.")
					   (auto-rewrite* expr oldsig
							  (cdr hashentry) ctx op*))
					  (t (format-rewrite-msg
					      (if (consp res)
						  (car res)
						  (id res-decl))
					      expr newrhs)
					     (when (not (consp res))
					       (push-references-list
						(module-instance res)
						*dependent-decls*)
					       (pushnew res-decl
							*dependent-decls*))
					     ;;Records too many dependencies
					     ;;but this is conservative.
					     (values
					      (cons
					       '?
					       (apply-trace
					       	(cdr oldsig)
					       	(list
						 (cdr sigrhs)
						 )))
					      newrhs))))
				  (multiple-value-bind (subst tccforms)
				      (let* ((*tccforms* nil)
					     (*keep-unbound* *bound-variables*)
					     (tsubst (tc-alist subst nil 'top)))
					(values tsubst *tccforms*))
				    (when (modname? modsubst) ;;NSH(2.8.97)
				      ;;ensure generation of assumption TCCS
				      ;;for generic rewrites.
				      (typecheck modsubst :tccs 'all))
				    (let ((newhyp
					   (nth-value 1
					     (when (hyp hashentry1)
					       (inc-rewrite-depth res)
					       ;;hit it with full assert.
					       (flag-assert-if  
						(substit hyp subst)
						(make-ctx
						 'not-implemented 'c5)))))) ;; FG caution with substit
				      (when hyp
					(decf *auto-rewrite-depth*))
				      (cond
				       ((or (null hyp)
					    (tc-eq newhyp *true*))
					(let ((newtccs
					       (nth-value 1
						 (progn 
						   (inc-rewrite-depth res)
						   (flag-assert-if
						    (mapcar #'tccinfo-formula
							    tccforms)
						    (make-ctx 'not-implemented 'c44))))))
					  (decf *auto-rewrite-depth*)
					  (cond ((every #'true-p newtccs)
						 (multiple-value-bind
						     (sigrhs newrhs)
						     (top-lazy-assert-if-with-subst
						      rhs
						      subst
						      ctx
						      if-flag
						      res)
						   (decf *auto-rewrite-depth*)
						   (cond ((and if-flag (eq (car sigrhs) 'X))
							  (track-rewrite-format
							   res expr
							   "RHS did not simplify."
							   )
							  (auto-rewrite* expr oldsig
									 (cdr hashentry)
									 ctx op*))
							 (t (format-rewrite-msg
							     (if (consp res)
								 (car res)
								 (id res-decl))
							     expr newrhs)
							    (when (not (consp res))
							      (push-references-list
							       (module-instance res)
							       *dependent-decls*)
							      (pushnew res-decl
								       *dependent-decls*
								       ))
							    (values
							     (cons
							      '?
							      (apply-trace
							       (cdr oldsig)
							       (list 
								(make-trace
								 'rewrite-rule2
								 (list ctx
								       (compute-substit rhs subst)
								       expr
								       rewrite-rule-flag)
								 (list (cdr sigrhs))))))
							     newrhs)))))
						(t
						 (track-rewrite-format
						  res expr
						  "TCC(s)~{~a, ~} remain."
						  (loop for x in newtccs
							when (not (tc-eq x *true*))
							collect x))
						 (auto-rewrite* expr oldsig
								(cdr hashentry) ctx op*)))))
				       (t (track-rewrite-format
					   res expr
					   "Hypothesis ~a did not simplify."
					   newhyp)
					  (auto-rewrite* expr oldsig
							 (cdr hashentry) ctx op*))))))))))))))))

;;NSH(5.18.95)
(defun gensort (list order &optional accum);;generic sorter, CLISP sort sucks!!
  (cond ((null list) accum)
	(t (let* ((greatest (select-greatest list order))
		  (rest (remove greatest list)))
	     (gensort rest order (cons greatest accum))))))

(defun select-greatest (list order)
  (cond ((null list) nil)  ;;this should never happen if input is nonempty
	((member (car list)(cdr list)
		 :test order)
	 (select-greatest (cdr list) order))
	(t (car list))))
	     
(defun sort-alist (alist)
  (gensort alist
	#'(lambda (x y)
	    (member (declaration (car x))
		    (freevars (car y))
		    :test #'(lambda (u v)
			      (eq u (declaration v)))))))

;; FG :  supposed to ouptut a simplification of (substit expr subst)
(defun top-lazy-assert-if-with-subst (expr subst ctx if-flag res)
  (let ((*assert-flag* nil))
    (inc-rewrite-depth res)
    (lazy-assert-if-with-subst-i expr subst ctx if-flag)))

(defun case-or-branch? (expr)
  (or (branch? expr)(cases? expr)))

(defmethod lazy-assert-if-with-subst (expr subst &optional if-flag)
  (declare (ignore expr subst if-flag))
  (assert nil))

(defmethod lazy-assert-if-with-subst-i ((expr branch) subst ctx &optional if-flag)
  (let* ((expr* (compute-substit expr subst))
	 (ctxtest (apply-ctx
		   ctx
		   (list
		    (make-ctx 'application
			      (list (make-ctx 'expr (operator expr*))
				    (make-ctx 'tuple
					      (list
					       (make-ctx 'expr-hole *boolean*)
					       (make-ctx 'expr
							 (cadr (exprs (argument expr*))))
					       (make-ctx 'expr
							 (caddr (exprs (argument expr*)))))))))))
	 (subres (substit-with-proofs (condition expr) subst ctxtest))
	 (subexpr (car subres))
	 (restest (assert-if-simplify subexpr ctxtest)) ;; FG as above, will have to use expr* in ctx
	 (newtest (car restest))) ;;(break "lazy")
    ;;check if assert-if-simplify is needed.  Why another assert-test
    ;;below.
    (if (check-for-connectives? newtest)
	(if if-flag
	    (values (cons 'X (make-trace 'not-implemented 'p21)) expr);;expr is irrelevant
	    (let ((newexpr (substit expr subst))) ;; FG caution with substit
	      (values (cons '? (make-trace 'not-implemented 'p30))
		      (cond ((eq newtest subexpr)
			     newexpr)
			    ((branch? newexpr)
			     (lcopy newexpr
			       'argument
			       (lcopy (argument newexpr)
				 'exprs (cons newtest
					      (cdr (arguments newexpr))))))
			    (t newexpr)))))
	(let ((result newtest));;instead of (assert-test newtest)
	  (cond ((tc-eq result *true*)
		 (multiple-value-bind
		  (sigthen newthen)
		  (lazy-assert-if-with-subst-i (then-part expr) subst ctx)
		  (values-assert-if
		   (cons '?
			 (apply-trace
			  (cdr subres)
			  (list (apply-trace
				 (cdr restest)
				 (list (make-trace 'deep-trusted-rule
						   (list ctx
							 'ifthenelse5
							 (then-part expr*)
							 (lcopy expr*
								'argument
								(lcopy (argument expr*)
								       'exprs (cons newtest
										    (cdr (arguments
											  expr*))))))
						   (list (cdr sigthen))))))))
		   newthen expr)))
		((tc-eq result *false*)
		 (multiple-value-bind
		  (sigelse newelse)
		  (lazy-assert-if-with-subst-i (else-part expr) subst ctx)
		  (values-assert-if
		   (cons '?
			 (apply-trace
			  (cdr subres)
			  (list (apply-trace
				 (cdr restest)
				 (list (make-trace 'deep-trusted-rule
						   (list ctx
							 'ifthenelse6
							 (else-part expr*)
							 (lcopy expr*
								'argument
								(lcopy (argument expr*)
								       'exprs (cons newtest
										    (cdr (arguments
											  expr*))))))
						   (list (cdr sigelse))))))))
		   newelse expr)))
		(if-flag (values (cons 'X (make-trace 'not-implemented 'p167)) expr))
		(t (values (cons '? (make-trace 'not-implemented 'p169))
			   (let ((newexpr (substit expr subst))) ;; FG caution with substit
				(cond ((eq newtest subexpr)
				       newexpr)
				      ((branch? newexpr)
				       (lcopy newexpr
					 'argument
					 (lcopy (argument newexpr)
					   'exprs (cons newtest
							(cdr (arguments
							      newexpr))))))
				      (t newexpr))))))))))

(defmethod lazy-assert-if (expr)
  (declare (ignore expr))
  (assert nil))

(defmethod lazy-assert-if-i ((expr branch) ctx)
  (declare (ignore ctx))
  (let ((newtest (car (assert-if-simplify (condition expr) (make-ctx 'not-implemented 'c62)))))
    ;;check if assert-if-simplify is needed.  Why another assert-test
    ;;below.  
    (if (check-for-connectives? newtest)
	(values (cons 'X (make-trace 'proof-hole)) expr)
	(let ((result newtest));;instead of (assert-test newtest)
	  (cond ((tc-eq result *true*)
		 (let ((newthen (nth-value 1
					   (lazy-assert-if-i (then-part expr)
							   (make-ctx 'not-implemented 'c40)))))
		   (values-assert-if (cons '? (make-trace 'not-implemented 'p54))
				     newthen expr)))
		((tc-eq result *false*)
		 (let ((newelse (nth-value 1
					   (lazy-assert-if-i (else-part expr)
							   (make-ctx 'not-implemented 'c41)))))
		   (values-assert-if  (cons '? (make-trace 'not-implemented '60))
				      newelse expr)))
		(t (values (cons 'X (make-trace 'proof-hole)) expr)))))))

(defun sig-assert-if (expr sig)
  (multiple-value-bind (newsig newexpr)
      (assert-if-i expr (make-ctx 'not-implemented 'c45))
    (if (eq (car newsig) 'X) (values sig expr)(values (car newsig) newexpr))))

(defun sig-lazy-assert-if (expr sig)
  (multiple-value-bind (newsig newexpr)
      (lazy-assert-if-i expr (make-ctx 'not-implemented 'c39))
    (if (eq (car newsig) 'X) (values sig expr)(values (car newsig) newexpr))))

(defun sig-lazy-assert-if-with-subst (expr sig subst)
  (multiple-value-bind (newsig newexpr)
      (lazy-assert-if-with-subst-i expr subst (make-ctx 'not-implemented 'c25))
      (if (eq (car newsig) 'X)
	  (values sig newexpr)
	(values (cons (car newsig) (make-trace 'not-implemented 'p183)) newexpr))))

(defmethod lazy-assert-if-with-subst-i ((expr cases-expr) subst ctx &optional if-flag)
  (declare (ignore ctx))
  (with-slots (expression selections else-part) expr
    (let ((expression (substit expression subst))) ;; FG caution with substit
      (multiple-value-bind (sigexpr newexpr)
	  (assert-if-i expression (make-ctx 'not-implemented 'c46)) ;;(10.8.96):was cond-assert-if
	(let* ((expression (if (eq (car sigexpr) '?) newexpr expression))
	       (all-result (check-all-recognizers expression))
	       (select (loop for sel in selections
			     thereis
			     (let ((check
				    (check-some-recognizer
				     (recognizer (constructor sel))
				     all-result)))
			       (when (true-p check) sel)))))
	  (cond ((null select)
		 (if (and else-part
			  (loop for sel in selections
				always (false-p
					(check-some-recognizer
					 (recognizer (constructor sel))
					 all-result))))
		     (sig-lazy-assert-if-with-subst
		      else-part (cons '? (make-trace 'not-implemented 'p184)) subst)
		     (if  if-flag ;;NSH(2.27.97)
			  ;;was lcopying even on if-flag.
			  (values (cons 'X (make-trace 'not-implemented 'p228)) expr)
			  (if (eq (car sigexpr) '?)
			      (values (cons '? (make-trace 'not-implemented 'p256))
				      (lcopy expr 'expression expression
					     'selections
					     (substit selections subst) ;; FG caution with substit
					     'else-part
					     (substit else-part subst))) ;; FG caution with substit 
			    (values (cons '? (make-trace 'not-implemented 'p260))
				    (substit expr subst)))))) ;; FG caution with substit
		((and (name-expr? expression)(constructor? expression))
		 (sig-lazy-assert-if-with-subst
		  (expression select)
		  (cons '? (make-trace 'not-implemented 'p262))
		  subst))
		((and (application? expression)
		      (constructor? (operator expression)))
		 (sig-lazy-assert-if-with-subst
		  (expression select)
		  (cons '? (make-trace 'not-implemented 'p275))
		  (nconc (pvs-pairlis (args select)
				      (arguments expression))
			 subst)))
		(t (sig-lazy-assert-if-with-subst
		    (expression select)
		    (cons '? (make-trace 'not-implemented 'p276))
		    (get-subst-accessors-in-selection-with-subst
		     expression
		     select subst)))))))))

(defmethod lazy-assert-if-with-subst-i ((expr unpack-expr) subst ctx &optional if-flag)
  (declare (ignore ctx))
  (with-slots (expression selections else-part)
      expr
    (let ((expression (substit expression subst))) ;; FG caution with substit
      (multiple-value-bind (sigexpr newexpr)
	  (assert-if-i expression (make-ctx 'not-implemented 'c47));;(10.8.96):was cond-assert-if
	(let* ((expression (if (eq (car sigexpr) '?) newexpr expression))
	       (all-result (check-all-recognizers expression))
	       (select (loop for sel in selections
			     thereis
			     (let ((check
				    (check-some-recognizer
				     (recognizer (constructor sel))
				     all-result)))
			       (when (true-p check) sel)))))
	  (cond ((null select)
		 (if (and else-part
			  (loop for sel in selections
				always (false-p
					(check-some-recognizer
					 (recognizer (constructor sel))
					 all-result))))
		     (sig-lazy-assert-if-with-subst
		      else-part (cons '? (make-trace 'not-implemented 'p288))  subst)
		     (if  if-flag;;NSH(2.27.97)
			  ;;was lcopying even on if-flag.
			  (values (cons 'X (make-trace 'not-implemented 'p296)) expr)
			  (if (eq (car sigexpr) '?)
			      (values (cons '? (make-trace 'not-implemented 'p297))
				      (lcopy expr 'expression expression
					     'selections
					     (substit selections subst) ;; FG caution with substit
					     'else-part
					     (substit else-part subst))) ;; FG caution with substit 
			    (values (cons '? (make-trace 'not-implemented 'p310))
				    (substit expr subst)))))) ;; FG caution with substit
		((and (name-expr? expression)(constructor? expression))
		 (sig-lazy-assert-if-with-subst
		  (expression select)  (cons '? (make-trace 'not-implemented 'p311)) subst))
		((and (application? expression)
		      (constructor? (operator expression)))
		 (sig-lazy-assert-if-with-subst
		  (expression select)
		  (cons '? (make-trace 'not-implemented 'p324))
		  (nconc (pvs-pairlis (args select)
				      (arguments expression))
			 subst)))
		(t (sig-lazy-assert-if-with-subst
		    (expression select)
		    (cons '? (make-trace 'not-implemented 'p331))
		    (get-subst-accessors-in-selection-with-subst
		     expression
		     select subst)))))))))

(defun get-subst-accessors-in-selection-with-subst (expr sel subst)
  (if (cotupletype? (find-supertype (type expr)))
      (let* ((accs (accessors (constructor sel)))
	     (vars (args sel)))
	(nconc (pairlis vars
			(mapcar #'(lambda (acc)
				    (if (injection-application? expr)
					(argument expr)
					(make!-extraction-application
					 (index acc) expr)))
			  accs))
	       subst))
      (let* ((stype (find-supertype (type expr)))
	     (thinst (module-instance stype))
	     (decl (declaration stype))
	     (theory (module decl))
	     (accs (substit (subst-mod-params (accessors (constructor sel)) ;; FG caution with substit
					      thinst theory decl)
		     subst))
	     (vars (args sel)))
	(nconc (pairlis vars
			(mapcar #'(lambda (acc) (make!-application acc expr))
			  accs))
	       subst))))

(defmethod lazy-assert-if-i ((expr cases-expr) ctx)
  (declare (ignore ctx))
  (with-slots (expression selections else-part)
      expr
    (multiple-value-bind (sigexpr newexpr)
	(cond-assert-if expression (make-ctx 'not-implemented 'c56))
      (let* ((expression (if (eq (car sigexpr) '?) newexpr expression))
	     (all-result (check-all-recognizers expression))
	     (select (loop for sel in selections
			   thereis
			   (let ((check
				  (check-some-recognizer
				   (recognizer (constructor sel))
				   all-result)))
			     (when (true-p check) sel)))))
	(cond ((null select)
	       (if else-part
		   (if (loop for sel in selections
			     always (false-p (check-some-recognizer
					      (recognizer (constructor sel))
					      all-result)))
		       (multiple-value-bind
			(newsig newexpr)
			(sig-lazy-assert-if else-part '?)
			(values (cons newsig (make-trace 'not-implemented 'p61))
				newexpr))
		       (values (cons 'X (make-trace 'not-implemented 'p66)) expr))
		   (values (cons 'X (make-trace 'not-implemented 'p72)) expr)))
	      ((and (name-expr? expression)(constructor? expression))
	       (multiple-value-bind
		(newsig newexpr)
		(sig-lazy-assert-if (expression select) '?)
		(values (cons newsig (make-trace 'not-implemented 'p90))
			newexpr)))
	      ((and (application? expression)(constructor? (operator expression)))
	       (multiple-value-bind
		(newsig newexpr)
		(sig-lazy-assert-if (substit (expression select) ;; FG caution with substit
					     (pvs-pairlis (args select)
							  (arguments expression))) '?)
		(values (cons newsig (make-trace 'not-implemented 'p110))
			newexpr)))
	      (t
	       (multiple-value-bind
		(newsig newexpr)
		(sig-lazy-assert-if (subst-accessors-in-selection expression
								  select) '?)
		(values (cons newsig (make-trace 'not-implemented 'p112))
			newexpr))))))))

(defmethod lazy-assert-if-with-subst-i ((expr application) subst ctx &optional if-flag)
  (with-slots ((op operator) (arg argument))
      expr
  (if (and *let-reduce?*
	   (lambda? op))  ;;Don't bother simplifying within a lambda op.
      (multiple-value-bind
       (sigexpr newexpr)
       (lazy-assert-if-with-subst-i
	(expression (operator expr))
	(append (pairlis-args (bindings op)
			      (substit (argument-list arg) subst)) ;; FG caution with substit
		subst)
	ctx
	if-flag)
       (values (cons (car sigexpr) (make-trace 'not-implemented 'p332)) newexpr))
    (call-next-method))))

(defmethod lazy-assert-if-with-subst-i ((expr expr) subst ctx &optional if-flag)
  (declare (ignore if-flag))
  (let ((ressubst (substit-with-proofs expr subst ctx)))
    (multiple-value-bind
     (sig result)
     (assert-if-i (car ressubst) ctx)
     (values-assert-if (cons '?
			     (apply-trace (cdr ressubst) (list (cdr sig))))
		       result result))))

(defmethod lazy-assert-if-i ((expr expr) ctx)
  (declare (ignore ctx))
   (assert-if-i expr (make-ctx 'not-implemented 'c49)))
		       
    

(defun adt-subtype? (type);;returns recognizer.
  (and (typep type 'subtype)
       (adt? (find-supertype type))
       (find-if #'recognizer? (type-predicates type))))

(defun assert-record-equality (expr)
  (let* ((labels (loop for x in (assignments (args1 expr))
		       collect  (caar (arguments x))))
	 (equalities
	  (loop for x in labels
		collect (make!-equation
			 (expression
			  (find x (assignments (args1 expr))
				:test #'(lambda (y z)
					  (same-id y (caar (arguments z))))))
			 (expression
			  (find x (assignments (args2 expr))
				:test #'(lambda (y z)
					  (same-id y (caar (arguments z)))))))))
	 (conjunction (make!-conjunction* equalities)))
    (multiple-value-bind (sig newexpr)
	(assert-if-i conjunction (make-ctx 'not-implemented 'c50))
      (if (eq (car sig) '?) (values '? newexpr)(values '? conjunction)))))
						   
				       

(defun assert-tuple-equality (expr)
  ;;NSH(10/91)This code will have to be revisited if we bring in
  ;;structural subtyping.
  (let ((conjunction
	 (make!-conjunction* (assert-tuple-equality* (exprs (args1 expr))
						     (exprs (args2 expr))))))
    (multiple-value-bind  (sig newexpr)
	(assert-if-i conjunction (make-ctx 'not-implemented 'c51))
      (if (eq (car sig) '?) (values '? newexpr) (values '? conjunction)))))

(defun assert-tuple-equality* (lhs* rhs*)
  (cond ((null lhs*) *true*)
	((null (cdr lhs*)) (list (make!-equation (car lhs*)(car rhs*))))
	(t  (cons (make!-equation (car lhs*)(car rhs*))
		  (assert-tuple-equality* (cdr lhs*)(cdr rhs*))))))

(defmethod assert-if-i ((expr list) ctx)
  (cond ((null expr) (values (cons 'X (make-trace 'proof-hole)) nil))
	(t
	 ;; (format t "~%intest : ~a" (car expr))
	 ;; (when (expr-ctx? (apply-ctx ctx
	 ;; 			       (cons (make-ctx 'expr-hole (type (car expr)))
	 ;; 				     (mapcar #'(lambda (ex)
	 ;; 						 (make-ctx 'expr ex))
	 ;; 					     (cdr expr)))))
	 ;;   (format t "~%inctx : ~a" (expr (apply-ctx ctx
	 ;; 			       (cons (make-ctx 'expr-hole (type (car expr)))
	 ;; 				     (mapcar #'(lambda (ex)
	 ;; 						 (make-ctx 'expr ex))
	 ;; 					     (cdr expr)))))))
	 (multiple-value-bind (sig1 newcar)
	       (assert-if-i (car expr)
			    (if (not (expr? (car expr)))
				(make-ctx 'not-implemented 'assignment)
			      (apply-ctx ctx
					 (cons (make-ctx 'expr-hole (type (car expr)))
					       (mapcar #'(lambda (ex)
							   (make-ctx 'expr ex))
						       (cdr expr))))))
	     (multiple-value-bind (sig2 newcdr)
		  (assert-if-i (cdr expr)
			       (apply-ctx ctx
					  (cons (make-ctx 'expr newcar)
						(mapcar #'(lambda (ex)
							    (make-ctx 'expr-hole (type ex)))
						     (cdr expr)))))
		  (if (and (eq (car sig1) 'X)(eq (car sig2) 'X))
		      (values (cons 'X (make-trace 'proof-hole)) expr)
		    (values (cons '?
				  (apply-trace (cdr sig1)
					       (list (cdr sig2))))
			    (cons newcar newcdr))))))))

(defmethod assert-if-i ((expr binding-expr) ctx);;(break "assert-if-binding")
  (with-slots (bindings expression) expr
    (let* ((*subtype-hash* (when *subtype-hash* (copy *subtype-hash*)))
	   (*assert-typepreds-off* t)
	   (*bound-variables* (append bindings
				      *bound-variables*))
	   (*local-typealist* *local-typealist*);;shadowing
	   (typepreds (loop for x in bindings
			    nconc
			    (let ((y (make-variable-expr x))
				  (*keep-unbound* *bound-variables*))
			      ;; NSH(12.30.93)not sure if *keep-unbound*
			      ;; needs to be set.
			      (collect-type-constraints* y))))
	   );;(break "binding")
      (multiple-value-bind
       (sig newexpr)
       (cond-assert-if expression
		       (apply-ctx ctx
				  (list (cond
					 ((forall-expr? expr)
					  (make-ctx
					   'forall
					   (list
					    (make-ctx
					     'typepreds
					     (list (make-ctx 'expr-hole (type expression)))
					     (list typepreds)))
					   (list bindings)))
					 ((lambda-expr? expr)
					  (make-ctx
					   'lambda
					   (list (make-ctx 'expr-hole (type expression)))
					   (list bindings)))
					 (t
					  (make-ctx
					   'exists
					   (list (make-ctx 'expr-hole (type expression)))
					   (list bindings))))))
		       typepreds)
       (assert-if-quant-i expr sig newexpr ctx)))))

(defmethod assert-if-quant (expr sig newbody)
  (declare (ignore expr sig newbody))
  (assert nil))

;;FG sig proves expr from (lcopy expr 'expression newbody) 
(defmethod assert-if-quant-i ((expr exists-expr) sig newbody ctx)
  (declare (ignore ctx))
  (if (tc-eq newbody *false*)
      (values (cons '? (make-trace 'not-implemented 'p70)) *false*)
    (if (tc-eq newbody *true*)
	(let ((check (and *top-proofstate*
			  (not (existence-tcc? (declaration
						*top-proofstate*)))
			  (loop for bd in (bindings expr)
				always (nonempty? (type bd))))))
	  (if check
	      (values
	       ;; (assert (and 'assert4 nil));; FG to be modified later
	       (cons '?
		     (make-trace 'not-implemented 'p4)
		     ;; (apply-trace
		     ;; 	   (cdr sig)
		     ;; 	   (list
		     ;; 	    (make-trace
		     ;; 	     'deep-inference-rule
		     ;; 	     (list ctx *true* (lcopy expr 'expression newbody))
		     ;; 	     (list (make-trace 'proof-hole)
		     ;; 	    	   (make-trace
		     ;; 		    'typepred-rule
		     ;; 		    (list (list (compute-negation (lcopy expr 'expression newbody))))
		     ;; 		    (list (make-trace 'axiom-rule
		     ;; 				      (list (lcopy expr 'expression newbody)))))
		     ;; 	    	   (make-trace 'true-rule)))))
		     )
	       *true*)
	    (multiple-value-bind
	     (newsig newexpr)
	     (do-auto-rewrite (lcopy expr 'expression newbody)
			      (cons (car sig) (make-trace 'not-implemented 'p278))
			      (make-ctx 'not-implemented 'c115))
	     (values (cons (car newsig) (make-trace 'not-implemented 'p291)) newexpr))))
      (if *quant-simp?*
	  (multiple-value-bind
	   (newsig newexpr)
	   (assert-if-exists expr (car sig) newbody)
	   (values (cons newsig (make-trace 'not-implemented 'p302)) newexpr))
	(do-auto-rewrite (lcopy expr 'expression newbody) sig (make-ctx 'not-implemented 'c116))))))

(defun collect-subst-equalities (conjuncts bindings)
  (if (consp conjuncts)
      (let ((atom (car conjuncts))
	    (rest (collect-subst-equalities (cdr conjuncts)
					    bindings)))
	(if (equality? atom)
	    (let* ((args1 (args1 atom))
		   (args2 (args2 atom)))
	      (let ((bvar1 (and (variable? args1)
				(member args1 bindings
					:test #'same-declaration))))
		(if bvar1
		    (cons (cons (car bvar1) args2)
			  rest)
		    (let ((bvar2 (and (variable? args2)
				      (member args2 bindings
					      :test #'same-declaration))))
		      (if bvar2
			  (cons (cons (car bvar2) args1)
				rest)
			  rest)))))
		  rest))
	    nil))

(defun order-subst-equalities (substs accum)
  (let ((first (loop for pair in substs
		     thereis
		     (let ((var (car pair))
			   (term (cdr pair)))
		       (and (not (assoc (declaration var) accum
					:key #'declaration))
			    (loop for x in (freevars term)
				  always
				  (null (assoc (declaration x)
					       substs
					       :key #'declaration)))
			    pair)))))
    (if first
	(order-subst-equalities (delete first substs)
				(cons first accum))
	accum)))

							  
(defun replace-list (substs expr)
  (if substs
      (let ((newexpr (replace-expr (caar substs)(cdar substs)
				   expr)))
	(replace-list (cdr substs) newexpr))
      expr))

(defun keepsubsts (substs bindings accum)
  (let* ((keeps (loop for xy in substs
		     when (member (car xy)
				  bindings
				  :test #'same-declaration)
		     collect xy))
	(rest (set-difference substs keeps)))
    (if keeps
	(keepsubsts rest bindings (append keeps accum))
	accum)))

(defun keep-bindings (substs new-bindings freevars-new-bindings)
  (let* ((keeps (loop for pair in substs
		     when (member (declaration (car pair))
				  freevars-new-bindings
				  :key #'declaration)
		     collect pair))
	 (rest-substs (set-difference substs keeps))
	 (more-new-bindings (loop for (x . nil) in keeps
				  collect (declaration x))))
    (if keeps
	(keep-bindings rest-substs (append more-new-bindings new-bindings)
		       (append (freevars more-new-bindings)
			       freevars-new-bindings))
	new-bindings)))

(defun nonempty-bindings? (bindings)
  (loop for bd in bindings always (nonempty? (type bd))))

(defun self-apply-substitution (substs new-bindings)
  (if (consp substs)
      (let ((var (caar substs))
	    (term (cdar substs))
	    (rest-subst (self-apply-substitution (cdr substs)
						 new-bindings)))
	(if (member (declaration var) new-bindings)
	    rest-subst
	    (cons (cons var (substit term rest-subst)) ;; FG caution with substit
		  rest-subst)))
      nil))

(defun assert-if-exists (expr sig newbody)
  (let* ((conjuncts (car (and+ newbody)))
	 (bindings (bindings expr))
	 (substs (collect-subst-equalities conjuncts bindings)))
    (if substs
	(let* ((substs (order-subst-equalities substs nil))
	       (varsubsts (loop for (x . nil) in substs
				collect (declaration x)))
	       (new-bindings (loop for x in bindings
				   when (not (member x varsubsts))
				   collect x))
	       (new-bindings (keep-bindings substs new-bindings
					    (freevars new-bindings)))
	       (substs (self-apply-substitution substs new-bindings)))
	  (if substs
	      (let* ((*bound-variables* (append bindings *bound-variables*))
		     (*keep-unbound* *bound-variables*)
		     (newbody (substit newbody substs)) ;; FG caution with substit
		     (*tccforms* nil)
		     (dummy (tc-alist substs nil 'top))
		     (conjunctions (make!-conjunction*
				    (mapcar #'tccinfo-formula *tccforms*)))
		     (newbody (make!-conjunction conjunctions newbody))
		     (new-expr (if new-bindings
				   (if (tc-eq newbody *false*)
				       *false*
				       (if (and (tc-eq newbody *true*)
						(nonempty-bindings? new-bindings))
					   *true*
					   (make!-exists-expr new-bindings newbody)))
				 newbody)))
		(declare (ignore dummy))
		(multiple-value-bind
		 (newsig newexpr)
		 (do-auto-rewrite new-expr (cons '? (make-trace 'not-implemented 'p280))
				  (make-ctx 'not-implemented 'c117))
		 (values (car newsig) newexpr)))
	    (multiple-value-bind
	     (newsig newexpr)
	     (do-auto-rewrite (lcopy expr 'expression newbody)
			      (cons sig (make-trace 'not-implemented 'p281))
			      (make-ctx 'not-implemented 'c118))
	     (values (car newsig) newexpr))))
      (multiple-value-bind
       (newsig newexpr)
       (do-auto-rewrite (lcopy expr 'expression newbody)
			(cons sig (make-trace 'not-implemented 'p282))
			(make-ctx 'not-implemented 'c119))
       (values (car newsig) newexpr)))))

;;FG sig proves expr from (lcopy expr 'expression newbody) 
(defmethod assert-if-quant-i ((expr forall-expr) sig newbody ctx)
  (if (tc-eq newbody *true*)
      (values
       (cons '?
	     (apply-trace
	      (cdr sig)
	      (list
	       (make-trace
		'deep-inference-rule
		(list ctx *true* (lcopy expr 'expression newbody))
		(list (make-trace 'proof-hole)
		      (make-trace 'forall-rule
				  (list newbody
					(mapcar
					 #'(lambda (bind)
					     (cons bind
						   (makeskoconst
						    (pc-parse
						     (new-sko-symbol
						      'pvs_with_proofs_id
						      *current-context*)
						     'expr)
						    (type bind)
						    *current-context*)))
					 (bindings expr)))
				  (list (make-trace 'true-rule)))
		      (make-trace 'true-rule)
		      ))))) *true*)
      (if (tc-eq newbody *false*)
	  (let ((check (loop for bd in (bindings expr)
			     always (nonempty? (type bd)))))
	    (if check
		(values (cons '? (make-trace 'not-implemented 'p306)) *false*)
	      (multiple-value-bind
	       (newsig newexpr)
	       (do-auto-rewrite (lcopy expr 'expression newbody)
				(cons (car sig) (make-trace 'not-implemented 'p283))
				(make-ctx 'not-implemented 'c120))
	       (values (cons (car newsig) (make-trace 'not-implemented 'p307)) newexpr))))
	(if *quant-simp?*
	    (multiple-value-bind
	     (newsig newexpr)
	     (assert-if-forall expr (car sig) newbody)
	     (values (cons newsig (make-trace 'not-implemented 'p308)) newexpr))
	  (do-auto-rewrite (lcopy expr 'expression newbody) sig (make-ctx 'not-implemented 'c121))))))

(defun assert-if-forall (expr sig newbody)
  (let* ((disjuncts (simplify-disjunct newbody nil))
	 (bindings (bindings expr))
	 (ndisjuncts (loop for x in disjuncts ;collect args of negations
			   when (negation? x)
			   collect (argument x)))
	 (substs (collect-subst-equalities ndisjuncts bindings)))
    (if substs
	(let* ((osubsts (order-subst-equalities substs nil))
	       (varsubsts (loop for (x . nil) in osubsts
				collect (declaration x)))
	       (new-bindings (loop for x in bindings
				   when (not (member x varsubsts))
				   collect x))
	       (new-bindings (keep-bindings osubsts new-bindings
					    (freevars new-bindings)))
	       (substs (self-apply-substitution osubsts new-bindings)))
	  (if substs
	      (let* ((*bound-variables* (append bindings *bound-variables*))
		     (*keep-unbound* *bound-variables*)
		     (newbody (substit newbody substs)) ;; FG caution with substit
		     (*tccforms* nil)
		     (dummy (tc-alist substs nil 'top))
		     (conjunctions (make!-conjunction*
				    (mapcar #'tccinfo-formula
				      *tccforms*)))
		     (newbody (make!-implication conjunctions newbody))
		     (new-expr (if new-bindings
				   (if (tc-eq newbody *true*)
				       *true*
				       (if (and (tc-eq newbody *false*)
						(nonempty-bindings? new-bindings))
					   *false*
					   (make!-forall-expr new-bindings newbody)))
				   newbody)))
		(declare (ignore dummy))
		(assert (subsetp (freevars new-expr) (freevars expr)
				 :test #'same-declaration))
		(multiple-value-bind
		 (newsig newexpr)
		 (do-auto-rewrite new-expr (cons '? (make-trace 'not-implemented 'p285))
				  (make-ctx 'not-implemented 'c122))
		 (values (car newsig) newexpr)))
	    (multiple-value-bind
	     (newsig newexpr)
	     (do-auto-rewrite (lcopy expr 'expression newbody)
			      (cons sig (make-trace 'not-implemented 'p286))
			      (make-ctx 'not-implemented 'c123))
	     (values (car newsig) newexpr))))
      (multiple-value-bind
       (newsig newexpr)
       (do-auto-rewrite (lcopy expr 'expression newbody)
			(cons sig (make-trace 'not-implemented 'p287))
			(make-ctx 'not-implemented 'c124))
       (values (car newsig) newexpr)))))

(defmethod assert-if-quant-i ((expr t) sig newbody ctx)
  (declare (ignore ctx))
  (do-auto-rewrite (lcopy expr 'expression newbody) sig (make-ctx 'not-implemented 'c1)))

(defmethod assert-if-i ((expr expr) ctx)
  (declare (ignore ctx))
  (values (cons 'X (make-trace 'proof-hole)) expr))


;;JMR's 4/19/01 bug suggests that assert-test should collect and
;;assert inner typepreds before the main assert.

(defun collect-subexpr-typepreds (expr)
  (collect-subexpr-typepreds* expr))

(defmethod collect-subexpr-typepreds* :around ((expr expr))
  (let ((constraints (type-constraints expr)))
    (dolist (constraint constraints)
	  (pushnew constraint *assert-typepreds* :test #'tc-eq))
    (call-next-method)))

(defmethod collect-subexpr-typepreds* ((expr application))
  (with-slots (operator argument) expr
      (and (collect-subexpr-typepreds* operator)
	   (collect-subexpr-typepreds* argument))))

(defmethod collect-subexpr-typepreds* ((expr branch))
  ;don't go into then/else.
  (collect-subexpr-typepreds* (condition expr)))

(defmethod collect-subexpr-typepreds* ((expr cases-expr))
  (with-slots (expression) expr
    (collect-subexpr-typepreds* expression)))

(defmethod collect-subexpr-typepreds* ((expr t))
  t) ;;ignoring bound variable contexts.

(defmethod collect-subexpr-typepreds*((expr list))
  (or (null expr)
      (and (collect-subexpr-typepreds* (car expr))
	   (collect-subexpr-typepreds* (cdr  expr)))))

(defmethod collect-subexpr-typepreds* ((expr tuple-expr))
  (with-slots (exprs) expr
    (collect-subexpr-typepreds* exprs)))

(defmethod collect-subexpr-typepreds* ((expr record-expr))
  (with-slots (assignments) expr
    (collect-subexpr-typepreds* assignments)))

(defmethod collect-subexpr-typepreds* ((expr assignment))
  (with-slots (expression) expr
    (collect-subexpr-typepreds* expression)))

(defmethod collect-subexpr-typepreds* ((expr field-application))
  (with-slots (argument) expr
    (collect-subexpr-typepreds* argument)))

(defmethod collect-subexpr-typepreds* ((expr projection-application))
  (with-slots (argument) expr
    (collect-subexpr-typepreds* argument)))

(defmethod collect-subexpr-typepreds* ((expr injection-application))
  (with-slots (argument) expr
    (collect-subexpr-typepreds* argument)))

(defmethod collect-subexpr-typepreds* ((expr injection?-application))
  (with-slots (argument) expr
    (collect-subexpr-typepreds* argument)))

(defmethod collect-subexpr-typepreds* ((expr extraction-application))
  (with-slots (argument) expr
    (collect-subexpr-typepreds* argument)))


;;tests the value of a formula in the current dec. procedure alist.
(defun assert-test (fmla)
  (unless (check-for-connectives? fmla)
    (let ((*sequent-typealist* nil))
      (nprotecting-cong-state ;;changed from LET on alists
       ((*dp-state* *dp-state*))
       (if (eq *pseudo-normalizing* 'include-typepreds?)
	   (let ((*assert-typepreds* *assert-typepreds*))
	     (collect-subexpr-typepreds fmla)
	     (unless (assq (caar primtypealist) typealist)
	       (setq typealist (append typealist primtypealist)))
	     (assert-typepreds *assert-typepreds*)
	     (call-process fmla *dp-state*))
	   (call-process fmla *dp-state*))))))

(defun assert-test0 (fmla)
  (unless (check-for-connectives? fmla)
    (let ((*sequent-typealist* nil))
      (nprotecting-cong-state
       ((*dp-state* *init-dp-state*))
       (call-process fmla *dp-state*)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;auto-rewriting
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun auto-rewrite (names-form ps &optional force?)
  (declare (ignore ps))
  (let ((names (parse-auto-rewrite-names-input names-form)))
    (loop for nm in names
	  do (let ((force? (or force?
			       (typecase nm
				 (cons (error "Bad rewrite name"))
				 (macro-rewrite '!!)
				 (eager-rewrite t)
				 (t nil))))
		   (res-alist (collect-auto-rewrite-res nm)))
	       (when res-alist
		 (loop for (res . fmla) in res-alist
		       do (if (integerp res)
			      (auto-rewrite-antecedent
			       res fmla force?)
			      (auto-rewrite-res
			       res force? *current-context*))))))))

(defun parse-auto-rewrite-names-input (names-form)
  (let ((bangs-allowed? (not (some #'consp names-form))))
    (mapcan #'(lambda (nf)
		(if (consp nf)
		    (parse-auto-rewrite-names-input! nf)
		    (list (parse-rewrite-name nf bangs-allowed?))))
      names-form)))

(defun parse-auto-rewrite-names-input! (names-form)
  (mapcan #'(lambda (nf)
	      (if (consp nf)
		  (parse-auto-rewrite-names-input!! nf)
		  (list (parse-rewrite-name nf nil '!))))
    names-form))

(defun parse-auto-rewrite-names-input!! (names-form)
  (mapcar #'(lambda (nf)
	      (if (consp nf)
		  (error-format-if "~%Only two levels of nesting allowed")
		  (parse-rewrite-name nf nil '!!)))
    names-form))

(defun parse-rewrite-name (form bangs-allowed? &optional bangs)
  (unless (or (stringp form)
	      (symbolp form)
	      (integerp form)
	      (rewrite-name? form))
    (error-format-if "~%Illegal rewrite name: ~a" form))
  (let* ((rewrite (pc-parse form 'rewrite-name-or-fnum))
	 (rewrite-name
	  (typecase rewrite
	    (lazy-rewrite-name
	     (case bangs
	       (! (change-class rewrite 'eager-rewrite-name))
	       (!! (change-class rewrite 'macro-rewrite-name))
	       (t rewrite)))
	    (lazy-fnum-rewrite
	     (case bangs
	       (! (change-class rewrite 'eager-fnum-rewrite))
	       (!! (change-class rewrite 'macro-fnum-rewrite))
	       (t rewrite)))
	    (t
	     (unless bangs-allowed?
	       (error-format-if
		"~%Do not mix parens and !'s in rewrite names"))
	     rewrite))))
    (unless (or (fnum-rewrite? rewrite-name)
		(resolutions rewrite-name))
      (typecheck rewrite-name))
    rewrite-name))

(defun prefix? (x y) ;both strings
  (let ((lx (length x))
	(ly (length y)))
    (and (<= lx ly)
	 (equal x (subseq y 0 lx)))))

(defun auto-rewrite-antecedent (num fmla always?)
  (let* ((string (format nil "~a_~a" (label *top-proofstate*)
				 (abs num)))
	 (occurrences
	  (loop for res in *auto-rewrites-names*
		when (and (consp res)
			  (prefix? string (string (car res))))
		collect (symbol-index (string (car res)))))
	 (occurrences!
	  (loop for res in *auto-rewrites!-names*
		when (and (consp res)
			  (prefix? string (string (car res))))
		collect (symbol-index (string (car res)))))
	 (all-occurrences (append occurrences occurrences!))
	 (new-index (if all-occurrences
			(1+ (apply #'max all-occurrences))
			1))
	 (name (intern (format nil "~a$~a" string new-index))))
    (install-rewrite-res (list name fmla) name fmla always?)))


(defmethod collect-auto-rewrite-res ((fnumrw fnum-rewrite))
  (let ((num (fnum fnumrw)))
    (if (minusp num)
	(let* ((fmlas (mapcar #'formula
			(select-seq (s-forms (current-goal *ps*))
				    (list num))))
	       (fmla (when fmlas (args1 (car fmlas)))))
	  (when fmla (list (cons num fmla))))
	(progn
	  (error-format-if
	   "~%Consequent formula numbered ~a cannot be used for rewriting."
	   num)
	  nil))))
		       
(defmethod collect-auto-rewrite-res ((name rewrite-name))
  (collect-auto-rewrite-res* (resolutions name)))

(defun collect-auto-rewrite-res* (reses &optional res-alist)
  (if (null reses)
      (nreverse res-alist)
      (let* ((res (car reses))
	     (fmla (select-from-fmlas (create-formulas res))))
	(collect-auto-rewrite-res*
	 (cdr reses)
	 (if (or (not (formula-decl? (declaration res)))
		 (check-auto-rewrite res fmla))
	     (append (collect-auto-rewrite-resolutions res fmla)
		     res-alist)
	     res-alist)))))

(defun collect-auto-rewrite-resolutions (res fmla)
  (let* ((thinst (module-instance res))
	 (th (module (declaration res)))
	 (lres (if (and (library-datatype-or-theory? th)
			(null (library thinst)))
		   (copy res
		     'module-instance
		     (copy thinst
		       'library (libref-to-libid (lib-ref th))))
		   res)))
    (if (or (actuals thinst)
	    (null (formals-sans-usings th))
	    (eq th (current-theory)))
	(list (cons lres fmla))
	;; Create name instances based on the importing instances.
	(let ((instances (get-importings th)))
	  (mapcar #'(lambda (inst)
		       (if (actuals inst)
			   (cons (copy lres 'module-instance inst)
				 (subst-mod-params fmla inst th))
			   (cons lres fmla)))
	    instances)))))

(defun check-auto-rewrite (res fmla)
  (let* ((mod-inst (module-instance res))
	 (theory (module (declaration res)))
	 (current-mod? (eq theory (current-theory)))
	 (actuals (unless current-mod?
		    (actuals mod-inst)))
	 (formals (unless current-mod?
		    (formals-sans-usings theory))))
    (multiple-value-bind
	(lhs rhs hyp)
	(split-rewrite fmla)
      (let* ((lhs-freevars (freevars lhs))
	     (rhs-freevars (freevars rhs))
	     (hyp-freevars (freevars hyp))
	     (op* (operator* lhs))
	     (hashname (auto-rewrite-hashname op*)))
	(cond
	 ((null hashname)
	  (error-format-if "~%Can't rewrite using ~a:  LHS key ~a is bad."
		     (id (declaration res)) op*)
	  nil)
	 ((not (subsetp rhs-freevars lhs-freevars
			:test #'tc-eq))
	  (error-format-if "~%RHS free variables in ~a must be contained in the LHS f
ree variables in: ~a" rhs lhs)
	  nil)
	 ((not (subsetp hyp-freevars lhs-freevars
			:test #'tc-eq))
	  (error-format-if "~%Hypothesis free variables in ~a must be contained in th
e LHS free variables in ~a" hyp lhs)
	  nil)
	 ((and formals (null actuals)
	       (not (subsetp (free-params lhs) formals)))
	  (error-format-if "~%Theory~a is generic; No actuals given;~%~
          Free parameters in the LHS of rewrite must contain all theory formals."
		     mod-inst)
	  nil)
	 (t))))))
		 
  
(defun select-from-fmlas (fmlas)
  (cond ((null fmlas) nil)
	(t (car fmlas))))
;above defn selects most curried form instead of
;f(x) form of a function definition for auto-rewriting.
;	((null (cdr fmlas))
;	 (car fmlas))
;
;	((null (cddr fmlas))
;	 (car fmlas))
;	(t (select-from-fmlas (cdr fmlas)))

(defmethod auto-rewrite-hashname ((expr name-expr))
  (if (variable? expr)
      (call-next-method)
      expr))

(defmethod auto-rewrite-hashname ((expr record-expr))
  'recordcons)

(defmethod auto-rewrite-hashname ((expr tuple-expr))
  'tuplecons)

(defmethod auto-rewrite-hashname ((expr update-expr))
  'update)

(defmethod auto-rewrite-hashname ((expr projection-expr))
  (id expr))

(defmethod auto-rewrite-hashname ((expr injection-expr))
  (id expr))

(defmethod auto-rewrite-hashname ((expr injection?-expr))
  (id expr))

(defmethod auto-rewrite-hashname ((expr extraction-expr))
  (id expr))

(defmethod auto-rewrite-hashname ((expr projection-application))
  (id expr))

(defmethod auto-rewrite-hashname ((expr injection-application))
  (id expr))

(defmethod auto-rewrite-hashname ((expr injection?-application))
  (id expr))

(defmethod auto-rewrite-hashname ((expr extraction-application))
  (id expr))

(defmethod auto-rewrite-hashname ((expr field-application))
  (id expr))  ;;NSH(9.15.95): in progress.

(defmethod auto-rewrite-hashname ((expr lambda-expr))
  'lambda)

(defmethod auto-rewrite-hashname ((expr forall-expr))
  'forall)

(defmethod auto-rewrite-hashname ((expr exists-expr))
  'exists)

(defmethod auto-rewrite-hashname ((expr cases-expr))
  'cases)

(defmethod auto-rewrite-hashname ((expr expr))
  nil)


(defun auto-rewrite-res (res always? context)
  (cond ((member res *auto-rewrites-off* :test #'tc-eq)
;	 (setf *auto-rewrites-off*
;	       (delete res *auto-rewrites-off* :test #'tc-eq))
	 nil)
	(t (let* ((fmlas (create-formulas res context))
		  (thefmla (select-from-fmlas fmlas))
		  (name (id (declaration res))))
	     (when thefmla
	       (install-rewrite-res res name thefmla always?))))))

(defun install-rewrite-res (res name fmla always?)	       
  (multiple-value-bind (lhs rhs hyp)
      (split-rewrite fmla)
    (let* ((res (or (is-res-rewrite res) res))
	   (lhs-freevars (freevars lhs))
	   (rhs-freevars (freevars rhs))
	   (hyp-freevars (freevars hyp))
	   (op* (operator* lhs))
	   (hashname (auto-rewrite-hashname op*))
	   (decl (if (typep hashname 'name-expr)
		     (declaration hashname)
		     hashname))) ;;(break "install-rewrite-res")
      (cond
       ((null hashname)
	(error-format-if "~%Can't rewrite using ~a:  LHS key ~a is bad" name op*))
       ((not (subsetp rhs-freevars lhs-freevars
		      :test #'tc-eq))
	(error-format-if "~%Can't rewrite using ~a: non-LHS freevars in RHS." name ))
       ((not (subsetp hyp-freevars lhs-freevars
		      :test #'tc-eq))
	(error-format-if "~%Can't rewrite using ~a: non-LHS freevars in hypotheses." name))
       ((and (resolution? res)
	     (fixpoint-decl? (declaration res)))
	(error-format-if "~%Can't rewrite using ~a: (co)inductive definition cannot be used." name))
       (t
	(unless (or (consp res) ;;(6.16.95)avoids antecedent rewrites
		    (not (fully-instantiated? res)))
	  (typecheck (module-instance res) :tccs 'all))
	;;NSH(6.14.95): above typecheck needed to generate
	;;assuming TCCS.  
	(pushnew
	 (make-instance 'rewrite
	   :lhs lhs
	   :rhs rhs
	   :hyp hyp
	   :res res)
	 (gethash decl
		  *auto-rewrites*)
	 :test #'(lambda (x y)(tc-eq (res x)(res y))))
	(pushnew res *all-rewrites-names*) ;;don't need tc-eq
	;;				(*auto-rewrites*)
	(cond ((and (eq always? '!!) ;;NSH(5.8.98) inserted macro case
		    (not (and (resolution? res)	;;NSH(12.1.95)
			      (def-decl? (declaration res)))))
	       (pushnew res *macro-names*)
	       ;;:test #'tc-eq
	       (setq *auto-rewrites-names*
		     (remove res *auto-rewrites-names*))
	       (setq *auto-rewrites!-names*
		     (remove res *auto-rewrites!-names*))
	       ;;:test #'tc-eq
	       (format-if "~%Installing macro(!!) ~a~@[ ~a~]"
			  (if (resolution? res)
			      (resolution-string res)
			      name)
			  (and (resolution? res)
			       (not (fully-instantiated? res))
			       "(all instances)")))
	      ((and always? ;;NSH(10.7.95) decl -> (declaration res)
		    (not (and (resolution? res)	;;NSH(12.1.95)
			      (def-decl? (declaration res)))))
	       (pushnew res *auto-rewrites!-names*)
	       ;;:test #'tc-eq
	       (setq *auto-rewrites-names*
		     (remove res *auto-rewrites-names*))
	       (setq *macro-names*
		     (remove res *macro-names*))
	       ;;:test #'tc-eq
	       (format-if "~%Installing rewrite rule(!) ~a~@[ ~a~]"
			  (if (resolution? res)
			      (resolution-string res)
			      name)
			  (and (resolution? res)
			       (not (fully-instantiated? res))
			       "(all instances)")))
	      (t (pushnew res *auto-rewrites-names*)
		 ;;:test #'tc-eq
		 (setq *auto-rewrites!-names*
		       (remove res *auto-rewrites!-names*))
		 (setq *macro-names*
		       (remove res *macro-names*))
		 ;;:test #'tc-eq
		 (format-if "~%Installing rewrite rule ~a~@[ ~a~]"
			    (if (resolution? res)
			      (resolution-string res)
			      name)
			    (and (resolution? res)
			       (not (fully-instantiated? res))
			       "(all instances)"))))
	(setf (gethash (rewrite-declaration hashname) *auto-rewrites-ops*) t)
	;;(format-if "~%Installing rewrite rule ~a" name)
	)))))




(defun auto-rewrite-step (names &optional force?)
  #'(lambda (ps)
      (let* ((*auto-rewrites-names* *auto-rewrites-names*)
	     (*auto-rewrites!-names* *auto-rewrites!-names*)
	     (*macro-names*  *macro-names*)
	     (*auto-rewrites* (copy *auto-rewrites*)))
	(auto-rewrite names ps force?)
	(if (and (eq *auto-rewrites-names*
		     (auto-rewrites-names (current-auto-rewrites ps)))
		 (eq *auto-rewrites!-names*
		     (auto-rewrites!-names (current-auto-rewrites ps)))
		 (eq *macro-names*
		     (macro-names (current-auto-rewrites ps))))
	    (values (cons 'X (make-trace 'empty 'np22)) nil nil)
	  (values (cons '? (make-trace 'proof-hole))
		  (list (cons (current-goal ps)
			      (list 'current-auto-rewrites
				    (mk-auto-rewrites-info
				     *auto-rewrites-names*
				     *auto-rewrites!-names*
				     *macro-names*
				     *all-rewrites-names*
				     *auto-rewrites*
				     (current-auto-rewrites ps))))))))))

      
      
      

;      (cond ((consp names)
;	     (loop for name in names do
;		   (auto-rewrite name (context *current-theory*))))
;	    (t (auto-rewrite names (context *current-theory*))))
;      (values '? (list (current-goal ps)))

(defmethod arithop-decl? ((x name-expr))
  (and (memq (id x)
	     '(+ - * / < <= > >=))
       (memq (id (module x))
	     '(|numbers| |number_fields| |reals| |rationals|
	       |integers| |naturalnumbers|))))

(defmethod arithop-decl? ((x const-decl))
  (and (memq (id x)
	     '(+ - * / < <= > >=))
       (memq (id (module x))
	     '(|numbers| |number_fields| |reals| |rationals|
	       |integers| |naturalnumbers|))))

(defmethod arithop-decl? ((x t))
  nil)

;;NSH(7.25.94): Sam's improved collect-explicit-names.  The earlier one
;;was inefficient in exploring paths repeatedly.
;;NSH(12.14.94): collect-explicit-names not used anymore.
;(defun collect-explicit-names (decl ps explicit)
;  (let ((decls (collect-referenced-decls decl ps explicit)))
;    (mapcar #'(lambda (d)
;		(mk-name-expr (id d) nil (id (module d))))
;	    decls)))

;;NSH(3.28.95): exclude-theories must be a list of theories.
(defun collect-referenced-decls (decl ps explicit exclude-theories
				      &optional exclude-names)
  (let ((decls nil)
	(all-decls nil))
    (labels ((collect (decl)
	       (unless (memq decl all-decls)
		 (push decl all-decls)
		 (when (and (not (memq decl decls))
			    (not (arithop-decl? decl))
			    (not (memq (module decl) exclude-theories))
			    (not (member decl exclude-names
					 :key #'resolutions
					 :test #'some-declaration-matches?)))
		   (when (and (or (and (const-decl? decl)
				       (not (def-decl? decl)));;NSH(4.3.95)
				  (and (not explicit)
				       (def-decl? decl)))
			      (definition decl))
		     (push decl decls))
		   (dolist (d (refers-to decl))
		     (collect d))))))
      (collect decl)
      (loop for x in (proof-dependent-decls ps) do (collect x))
      decls)))

(defun some-declaration-matches? (decl reses)
  (member decl reses :key #'declaration))


;;NSH(12.21.93) moved auto-rewrite-defs, auto-rewrite-explicit to strategies.lisp.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;auto-rewriting for theory
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;NSH(12.7.94): Changing install rewrites so that theories are given
;;in one list with keywords attached to each theory name.


;(defun install-rewrites (names theories theory-definitions
;			       exclude-names always? no-tccs?)
;  #'(lambda (ps)
;      (let* ((*auto-rewrites-names* *auto-rewrites-names*)
;	     (*auto-rewrites!-names* *auto-rewrites!-names*)
;	     (names (if (listp names) names (list names)))
;	     (exclude-names
;	      (mapcar #'(lambda (x) (pc-parse x 'name))
;		      (if (listp exclude-names)
;			  exclude-names
;			  (list exclude-names))))
;	     (exclude-resolutions
;	      (loop for name in exclude-names
;		    nconc (nconc (resolve name 'formula nil)
;				 (resolve name 'expr nil))))
;	     (theories (if (listp theories) theories
;			   (list theories)))
;	     (theory-definitions (if (listp theory-definitions)
;				     theory-definitions
;				     (list theory-definitions))))
;	(loop for theory in theories do
;	      (auto-rewrite-theory theory nil exclude-resolutions
;				   always? (not no-tccs?) ps))
;	(loop for theory in theory-definitions do
;	      (auto-rewrite-theory theory T exclude-resolutions
;				   always? (not no-tccs?) ps))
;	(auto-rewrite names ps always?) ;;NSH(11.22.94) changed order.
;	(let ((new-rewrites-info
;	       (mk-auto-rewrites-info
;				      *auto-rewrites-names*
;				      *auto-rewrites!-names*
;				      (current-auto-rewrites ps))))
;	  (cond ((eq new-rewrites-info
;		     (current-auto-rewrites ps))
;		 (format-if "~%No new rewrites installed.")
;		 (values 'X nil nil))
;		(t 
;		 (values '? (list (cons (current-goal ps)
;					(list 'current-auto-rewrites
;					      new-rewrites-info))))))))))


(defun auto-rewrite-theory (name &optional defs-only? exclude-resolutions
				 always? tccs? ps)
      (auto-rewrite-theory* name defs-only? exclude-resolutions
			    always? tccs? ps))

(defun check-theory-names (names modules &optional defs-only?)
  (cond ((null modules) t)
	((null (car modules))
	 (error-format-if "~%Could not find theory ~a" (car names))
	 nil)
	((and (eq (id (car modules))(id *current-theory*))
	      (actuals (car names))) ;;NSH(9.21.94)
	 (error-format-if "~%Current theory ~a should not have actuals."
		    (id (car modules)))
	 nil)
	((and (null defs-only?)
	      (not (or (eq (id (car modules))(id *current-theory*))
		       (null (formals-sans-usings (car modules)))
		       (actuals (car names)))))
	 (error-format-if
	  "~%~a is not a fully instantiated theory." (car names))
	 nil)
	(t t)))
	       
	       

(defun auto-rewrite-theory* (name defs-only? exclude-resolutions
				  always? tccs? ps)
  (let* (;(*auto-rewrites-names* *auto-rewrites-names* )
	 ;(*auto-rewrites!-names* *auto-rewrites!-names* )
	 (names (list name)) ;;historical, names->name in args.
	 ;;(*generate-tccs* 'all)
	 (names (loop for name in names
		      collect (typecheck
			       (pc-parse name 'modname)
			       :tccs 'all
			       :context *current-context*)))
	 ;;(*generate-tccs* nil)
	 (modules (loop for name in names
			collect (get-theory name)))
	(check (check-theory-names names modules defs-only?)))
    (cond ((null names) (values 'X nil))
	  ((not check) (values 'X nil))
	  (t (loop for name in names
		   as module in modules
		   do (auto-rewrite-theory-name name module
						defs-only?
						exclude-resolutions
						always? tccs? ps))
;	     (values '? (list
;			 (cons (current-goal ps)
;			       (list 'current-auto-rewrites
;				     (mk-auto-rewrites-info
;				      *auto-rewrites-names*
;				      *auto-rewrites!-names*
;				      (current-auto-rewrites ps))))))
	     ))))

(defun auto-rewrite-theory-name (name module defs-only?
				      exclude-resolutions
				      always? tccs? ps)
  (declare (ignore ps))
  (let* ((assuming-decls (when module (assuming module)))
	 (theory-decls (when module (theory module)))
	 (all-decls (append assuming-decls theory-decls))
	 (fdecls (loop for decl in all-decls
		       when
		       (and (if defs-only?
				(typep decl '(or const-decl def-decl))
				(and (typep decl
					    '(or formula-decl const-decl
						 def-decl))
				     (or tccs? (not (tcc? decl)))))
			    (not (member decl
					 exclude-resolutions
					 :test
					 #'(lambda (x y)
					     (let* ((modinst
						     (module-instance y))
						    (actuals (actuals modinst)))
					       (and (eq x (declaration y))
						    (eq (id modinst)
							(id module))
						    (or (null actuals)
							(tc-eq actuals
							       (actuals module)))))))))
		       collect decl))
	 (fdecls
	  (if (eq (id module)(id *current-theory*))
	      (ldiff fdecls
		     (memq (declaration *top-proofstate*)
			   fdecls))
	      fdecls)))
    (format-if "~%Installing rewrites from theory ~a" name)
    (loop for decl in fdecls
	  do (auto-rewrite-res
	      (make-resolution decl name)
	      always? 
	      *current-context*)))
  (format-if "~%Installed rewrites from theory ~a" name))


	       
(defun get-antec-name (name all-names &optional (max 0))
  (if (consp all-names)
      (let ((aname (when (consp (car all-names))
		     (string (caar all-names)))))
	(if (and aname
		 (prefix? name aname)
		 (> (symbol-index aname) max))
	    (get-antec-name name (cdr all-names)
			    (symbol-index aname))
	    (get-antec-name name (cdr all-names) max))) 
      (unless (zerop max)
	(intern (format nil "~a$~a" name max)))))    


(defun stop-rewrite-step (names)
  #'(lambda (ps)
      (if (null names)
	  (cond ((or *auto-rewrites-names* *auto-rewrites!-names*
		     *macro-names*)
		 (format-if "~%Disabling all current auto-rewrites.")
		 (values '?
			 (list (cons (current-goal ps)
				     (list 'current-auto-rewrites
					   (mk-auto-rewrites-info
					    nil  nil nil
					    *all-rewrites-names*
					    *auto-rewrites*
					    (current-auto-rewrites ps))
					   'rewrite-hash (clrhash
							  *rewrite-hash*))))))
		(t (format-if "~%No current auto-rewrites.")
		   (values 'X nil nil)))
	  (let* ((names (if (consp names) names (list names)))
		 (context *current-context*)
		 (old-auto-rewrites-names *auto-rewrites-names*)
		 (old-auto-rewrites!-names *auto-rewrites!-names*)
		 (old-macro-names *macro-names*)
		 (antecedent-names
		  (let* ((all-names (append *auto-rewrites-names*
					    *auto-rewrites!-names*
					    *macro-names*))
			 (numbered-antecedents
			  (loop for name in names
				when (integerp name)
				collect
				(get-antec-name
				 (format nil "~a_~a"
				   (label *top-proofstate*)
				   (abs name))
				 all-names)))
			 (named-antecedents
			  (loop for name in names
				when (member name
					     all-names
					     :test
					     #'(lambda (x y)
						 (when (consp y)
						   (same-id x (car y)))))
				collect name)))
		    (append numbered-antecedents named-antecedents)))
		 (names (remove-if #'integerp names))
		 (names (set-difference names antecedent-names
					     :test #'eq))
		 (parsenames (loop for name in names
				   collect (pc-parse name 'name)))
		 (fmla-resolutions
		  (loop for name in parsenames
			append (resolve name
				       'formula
				       nil context)))
		 (const-resolutions
		  (loop for name in parsenames
			append (resolve name 'expr nil context)))
		 (constant-resolutions
		  (loop for res in  const-resolutions
			when (and (typep (declaration res) 'const-decl)
				  (definition (declaration res)))
			collect res))
		 (resolutions (append fmla-resolutions constant-resolutions)))
	    (loop for name in antecedent-names
		  do (progn
		       (setq *auto-rewrites-names*
			     (remove name *auto-rewrites-names*
				     :test #'(lambda (x y)	
				       (when (consp y)
						 (same-id x (car y))))))
		       (setq *auto-rewrites!-names*
			     (remove name *auto-rewrites!-names*
				     :test #'(lambda (x y)
					       (when (consp y)
						 (same-id x (car y))))))
		       (setq *macro-names*
			     (remove name *macro-names*
				     :test #'(lambda (x y)
					       (when (consp y)
						 (same-id x (car y))))))
		       nil))
	    (loop for res in resolutions do
		  (if (or (member res *auto-rewrites-names* :test #'tc-eq)
			  (member res *auto-rewrites!-names* :test #'tc-eq)
			  (member res *macro-names* :test #'tc-eq))
		      (stop-rewrite-res res)
		      (error-format-if "~%~a.~a is not an auto-rewrite"
				       (module-instance res)
				       (id (declaration res)))))
	    (if (and (eq *auto-rewrites-names* old-auto-rewrites-names)
		     (eq *auto-rewrites!-names* old-auto-rewrites!-names)
		     (eq *macro-names* old-macro-names))
		(values 'X nil nil)
		(values '? (list (cons (current-goal ps)
				       (list 'current-auto-rewrites
					     (mk-auto-rewrites-info
					      *auto-rewrites-names*
					      *auto-rewrites!-names*
					      *macro-names*
					      *all-rewrites-names*
					      *auto-rewrites*
					      (current-auto-rewrites ps))
					     'rewrite-hash
					     (clrhash *rewrite-hash*))))))))))

(defun stop-rewrite-res (res)
  (cond ((member res *auto-rewrites-names* :test #'tc-eq)
	 (setq *auto-rewrites-names*
	       (remove res *auto-rewrites-names* :test #'tc-eq))
	 (format-if "~%Turned off ~a.~a"
		    (module-instance res) (id (declaration res)))
;;	 (pushnew res *auto-rewrites-off* :test #'tc-eq)
	 nil)
	((member res *auto-rewrites!-names* :test #'tc-eq)
	 (setq *auto-rewrites!-names*
	       (remove res *auto-rewrites!-names* :test #'tc-eq))
	 (format-if "~%Turned off ~a.~a"
		    (module-instance res) (id (declaration res)))
;;	 (pushnew res *auto-rewrites-off* :test #'tc-eq)
	 nil)
	((member res *macro-names* :test #'tc-eq)
	 (setq *macro-names*
	       (remove res *macro-names* :test #'tc-eq))
	 nil)
	(t nil)))



;;NSH(1.4.95): The stop-rewrite-theory code is no longer used.
	    

(defun stop-rewrite-theory (names)
  #'(lambda (ps)
      (let ((*auto-rewrites-names* *auto-rewrites-names*)
	    (*auto-rewrites!-names* *auto-rewrites!-names*))
	(stop-rewrite-theory-names names ps))))

(defun stop-rewrite-theory-names (names ps)
  (cond ((null names)(values 'X nil))
	(t (let* ((name (car names))
		  (name (typecheck (pc-parse name 'modname)
			      :context *current-context*))
		  (module (get-theory name))
		  (carval (stop-rewrite-theory-name name module ps))
		  (cdrval (stop-rewrite-theory-names (cdr names) ps)))
	     (if (or (eq carval '?)(eq cdrval '?))
		 (values '? (list (cons (current-goal ps)
					(list 'current-auto-rewrites
					      (mk-auto-rewrites-info
					       *auto-rewrites-names*
					       *auto-rewrites!-names*
					       *macro-names*
					       *all-rewrites-names*
					       *auto-rewrites*
					       (current-auto-rewrites ps))
					      'rewrite-hash
					      (clrhash *rewrite-hash*)))))
		 (values 'X nil))))))
	 
(defun stop-rewrite-theory-name (name module ps)
  (cond (module
	 (cond ((or (eq (id module)(id *current-theory*))
		    (null (formals-sans-usings module))(actuals name))
		(let ((assuming-resolves
		       (loop for decl in (assuming module)
			     when (typep decl '(or formula-decl
						const-decl def-decl))
			     collect (make-resolution decl name)))
		      (theory-resolves
		       (loop for decl in (theory module)
			     when (typep decl '(or formula-decl
						const-decl def-decl))
			     collect (make-resolution decl name))))
		  (loop for res in assuming-resolves
			do (stop-rewrite-res res))
		  (loop for res in theory-resolves
			do (stop-rewrite-res res))
		  (values '? (list (current-goal ps)))))
	       (t (error-format-if "~%~a is not a fully instantiated theory." name)
		  (values 'X nil))))
	((error-format-if "~%Could not find theory ~a" name)
	 (values 'X nil))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;(1/20/93): The issue here is to define simpler versions of assert,
;;specifically
;;1. record/note: just note the assertable statements.
;;2. simplify: do arithmetic and boolean simplification but no note.
;;3. auto-expand: which expands definitions using decision procs, I can
;;probably get expand to do this automatically.
;;The main new code that is needed is an arithmetic simplifier.
;;The transformations are to put arithmetic terms into sum of products
;;normal form so that each product looks like 2*x*x*y and the sum looks
;;like A + B + 4.

(defun collect-auto-rewrites ()
  (when (macro-names *ps*)
    (format t "The following definitions are always macro-expanded.~2%")
    (loop for res in (macro-names *ps*)
	  do (if (consp res)
		 (format t "~a: ~a~2%" (car res)
			 (unpindent (cadr res)
				    (+ (length (string (car res))) 2)
				    :string t))
		 (let* ((name (make-instance 'name
			       :id (id (declaration res))
			       :actuals (actuals (module-instance res))))
		       (name-string (unparse name :string t)))
		   (format t "~a: ~:[ ~;~%    ~]~a~2%"
		     name-string
		     (> (length name-string) 15)
		     (unpindent (car (create-formulas res))
				(if (> (length name-string) 15)
				    4
				    (+ (length name-string) 2))
				:string t)
		     )))))
  (format t "~2%The remaining rewrites of function definitions only occur 
when an expression matches the most curried form of the LHS of the
definition. ~2%")
  (when (auto-rewrites!-names *ps*)
    (format t "The following rewrite rules apply unconditionally
in reverse chronological order: ~3%")
    (loop for res in (auto-rewrites!-names *ps*)
	  do (if (consp res)
		 (format t "~a: ~a~2%" (car res)
			 (unpindent (cadr res)
				    (+ (length (string (car res))) 2)
				    :string t))
		 (let* ((name (make-instance 'name
			       :id (id (declaration res))
			       :actuals (actuals (module-instance res))))
		       (name-string (unparse name :string t)))
		   (format t "~a: ~:[ ~;~%    ~]~a~2%"
		     name-string
		     (> (length name-string) 15)
		     (unpindent (car (create-formulas res))
				(if (> (length name-string) 15)
				    4
				    (+ (length name-string) 2))
				:string t)
		     ))))
    (format t "~3%"))
  (when (auto-rewrites-names *ps*)
    (format t "The following rewrite rules apply only if any top-level
IF-THEN-ELSE or CASE in the RHS simplifies.  The rules in reverse
chronological order are:~3%") 
    (let ((names (auto-rewrites-names *ps*)))
      (loop for res in names do
	    (if (consp res)
		(format t "~a: ~a~2%" (car res)
			(unpindent (cadr res)
				   (+ (length (string (car res))) 2)
				   :string t))
		(let* ((name (make-instance 'name
			       :id (id (declaration res))
			       :actuals (actuals (module-instance res))))
		       (name-string (unparse name :string t)))
		  (format t "~a: ~:[ ~;~%    ~]~a~2%"
		     name-string
		     (> (length name-string) 15)
		     (unpindent (car (create-formulas res))
				(if (> (length name-string) 15)
				    4
				    (+ (length name-string) 2))
				:string t)
		     )))))))

(defun show-auto-rewrites ()
  (if (and *in-checker* *ps*)
      (let ((*disable-gc-printout* t))
	(pvs-buffer "*Auto-Rewrites*"
	  (with-output-to-string (*standard-output*)
	    (collect-auto-rewrites))
	  t t))
      (pvs-message "No current proof")))
