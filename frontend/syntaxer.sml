(* syntaxer.sml -*-Coding: us-ascii-unix;-*- *)
(* Copyright (C) 2018-2021 RIKEN R-CCS *)

(* Simple transformations. *)

structure syntaxer :
sig

val expand_equations_for_connects : unit -> 'a list

end = struct

open plain ast common message

val instance_tree = classtree.instance_tree
val traverse_tree = classtree.traverse_tree
val store_to_instance_tree = classtree.store_to_instance_tree

val expression_is_literal = expression.expression_is_literal
val find_iterator_range = expression.find_iterator_range

val fold_constants = folder.fold_constants
val explicitize_range = folder.explicitize_range
val expression_to_string = dumper.expression_to_string

val bind_in_scoped_expression = binder.bind_in_scoped_expression

val walk_in_class = walker.walk_in_class
val walk_in_expression = walker.walk_in_expression
val walk_in_equation = walker.walk_in_equation
val walk_in_statement = walker.walk_in_statement

fun trace n (s : string) = if n <= 3 then (print (s ^"\n")) else ()

(* Removes record constructors that take class instances (casting). *)

(* ================================================================ *)

(* Tests if the cardinality function appears in an expression. *)

fun contains_cardinality (w, contains0) = (
    case w of
	NIL => contains0
      | Colon => contains0
      | Otherwise => contains0
      | Scoped _ => raise Match
      | Vref _ => contains0
      | Opr _ => contains0
      | App (f, xx) => (
	(f = Vref (SOME PKG, [(Id "cardinality", [])]))
	orelse (foldl contains_cardinality contains0 (f :: xx)))
      | ITE cc => (
	(foldl contains_cardinality contains0
	       (List.concat (map (fn (x, y) => [x, y]) cc))))
      | Der _ => contains0
      | Pure _ => contains0
      | Closure (n, xx) => (foldl contains_cardinality contains0 xx)
      | L_Number _ => contains0
      | L_Bool _ => contains0
      | L_Enum _ => contains0
      | L_String _ => contains0
      | Array_Triple (x, y, NONE) => (
	(foldl contains_cardinality contains0 [x, y]))
      | Array_Triple (x, y, SOME z) => (
	(foldl contains_cardinality contains0 [x, y, z]))
      | Array_Constructor xx => (
	(foldl contains_cardinality contains0 xx))
      | Array_Comprehension (x, ii) => (
	(contains_cardinality (x, false))
	orelse (foldl contains_cardinality contains0 (map #2 ii)))
      | Array_Concatenation ee => (
	(foldl (fn (xx, acc) => (foldl contains_cardinality acc xx))
	       contains0 ee))
      | Tuple xx => (
	(foldl contains_cardinality contains0 xx))
      | Reduction_Argument (x, ii) => (
	(contains_cardinality (x, false))
	orelse (foldl contains_cardinality contains0 (map #2 ii)))
      | Named_Argument (n, x) => (
	(contains_cardinality (x, contains0)))
      | Pseudo_Split (x, v) => (
	(contains_cardinality (x, contains0)))
      | Component_Ref (x, v) => (
	(contains_cardinality (x, contains0)))
      | Instances _ => contains0
      | Iref _ => contains0
      | Lref _ => contains0
      | Cref _ => contains0
      | Array_fill (x, y) => (
	(foldl contains_cardinality contains0 [x, y]))
      | Array_diagonal x => (
	(contains_cardinality (x, contains0))))

(* Tests if a connector reference (connect equations or the
   cardinality function) appears in an equation. *)

fun contains_connectors (q0, contains0) = (
    let
	fun contains_connectors_x_qq ((x, qq), contains) = (
	    (contains_cardinality (x, false)
	     orelse (foldl contains_connectors contains qq)))

	fun contains_connectors_n_qq ((_, qq), contains) = (
	    (foldl contains_connectors contains qq))
    in
	case q0 of
	    Eq_Eq ((x, y), (_ ,_)) => (
	    (foldl contains_cardinality contains0 [x, y]))
	  | Eq_Connect _ => true
	  | Eq_If (cc, (_, _)) => (
	    (foldl contains_connectors_x_qq contains0 cc))
	  | Eq_When (cc, (_, _)) => (
	    if (foldl contains_connectors_n_qq false cc) then
		raise error_when_contains_connectors
	    else
		(foldl contains_connectors_x_qq contains0 cc))
	  | Eq_App ((f, xx), (_, _)) => (
	    (foldl contains_cardinality contains0 (f :: xx)))
	  | Eq_For ((_, qq), (_, _)) => (
	    (foldl contains_connectors contains0 qq))
    end)

(* Replaces iterator references.  Folding constants with an
   environment replaces iterators. *)

fun replace_iterators kp env q0 = (
    let
	fun mapl f (x0, x1) = (f x0, x1)
	val efix = (mapl (fold_constants kp false env))
	val qfix = (fn (q, a) => (q, a))
	val (q1, _) = (walk_in_equation qfix efix (q0, ()))
    in
	q1
    end)

(* Simplifies equations by choosing a branch of if-equations and
   unrolling for-equations, when they contain connect equations.  Note
   that it checks containment of a connect multiple times. *)

fun expand_equations kp env q0 = (
    let
	fun branch env0 cc0 : equation_t list = (
	    case cc0 of
		[] => []
	      | (w0, qq0) :: cc1 => (
		let
		    val w1 = (fold_constants kp false env0 w0)
		in
		    if (not (expression_is_literal w1)) then
			raise error_conditional_containing_connect
		    else
			case w1 of
			    Otherwise => (
			    (map (expand_equations kp env) qq0))
			  | L_Number _ => raise error_non_boolean
			  | L_Bool false => (branch env cc1)
			  | L_Bool true => (
			    (map (expand_equations kp env) qq0))
			  | L_Enum _ => raise error_non_boolean
			  | L_String _ => raise error_non_boolean
			  | Array_Triple _ => raise error_non_boolean
			  | Array_Constructor _ => raise error_non_boolean
			  | Array_Concatenation _ => raise error_non_boolean
			  | Named_Argument _ => raise error_non_boolean
			  | _ => raise Match
		end))

	fun unroll qq0 env0 rr0 : equation_t list = (
	    case rr0 of
		[] => (
		(map (replace_iterators kp env0) qq0))
	      | (v, Colon) :: rr1 => (
		case (find_iterator_range (Iref v) qq0) of
		    NONE => raise error_unknown_iterator_range
		  | SOME n => (
		    let
			val vv = (map z_literal (z_seq 1 1 n))
		    in
			(map (fn x =>
				 Eq_If ([(Otherwise,
					  (unroll qq0 ((v, x) :: env0) rr1))],
					(Annotation [], Comment [])))
			     vv)
		    end))
	      | (v, w0) :: rr1 => (
		let
		    val w1 = (fold_constants kp false env0 w0)
		    val vv = (explicitize_range w1)
		in
		    (map (fn x =>
			     Eq_If ([(Otherwise,
				      (unroll qq0 ((v, x) :: env0) rr1))],
				    (Annotation [], Comment [])))
			 vv)
		end))
    in
	if (not (contains_connectors (q0, false))) then
	    q0
	else
	    case q0 of
		Eq_Eq _ => q0
	      | Eq_Connect _ => q0
	      | Eq_If (cc0, (aa, ww)) => (
		let
		    val qq1 = (branch env cc0)
		in
		    Eq_If ([(Otherwise, qq1)], (aa, ww))
		end)
	      | Eq_When _ => q0
	      | Eq_App _ => q0
	      | Eq_For ((rr0, qq0), (aa, ww)) => (
		let
		    val qq1 = (unroll qq0 env rr0)
		in
		    Eq_If ([(Otherwise, qq1)], (aa, ww))
		end)
    end)

fun expand_equations_in_instance (k0, acc0) = (
    if (class_is_outer_alias k0) then
	acc0
    else if (class_is_enumerator k0) then
	acc0
    else if (class_is_package k0) then
	acc0
    else
	let
	    val _ = if (not (class_is_primitive k0)) then () else raise Match
	in
	    let
		val subj = (subject_of_class k0)
		val qfix = (fn (q, _) => ((expand_equations k0 [] q), []))
		val sfix = (fn (s, a) => (s, a))
		val walker = {vamp_q = qfix, vamp_s = sfix}
		val (k1, acc1) = (walk_in_class walker (k0, acc0))
		val _ = (store_to_instance_tree subj k1)
	    in
		acc1
	    end
	end)

(* Expands if-equations and for-equations containing connect equations
   or the cardinality function.  Those equations consist of
   translation-time constants (it is always affirmative for "for" and
   when those contain connect equations for "if"). *)

fun expand_equations_for_connects () = (
    (traverse_tree expand_equations_in_instance (instance_tree, [])))

(* ================================================================ *)

end
