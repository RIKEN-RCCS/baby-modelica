(* connector.sml -*-Coding: us-ascii-unix;-*- *)
(* Copyright (C) 2018-2020 RIKEN R-CCS *)

(* CONNECTOR HANDLING. *)

structure connector
(*
: sig
xcollect
end
*)
= struct

open ast plain
open small1

fun tr_conn (s : string) = if true then (print (s ^"\n")) else ()
fun tr_conn_vvv (s : string) = if false then (print (s ^"\n")) else ()

val instance_tree = classtree.instance_tree
val traverse_tree = classtree.traverse_tree

val expression_is_literal = expression.expression_is_literal
val find_iterator_range = expression.find_iterator_range

val fold_constants = folder.fold_constants
val explicitize_range = folder.explicitize_range

val walk_in_class = walker.walk_in_class
val walk_in_expression = walker.walk_in_expression
val walk_in_equation = walker.walk_in_equation
val walk_in_statement = walker.walk_in_statement

(* ================================================================ *)

(* Tests a connector equation appears in an equation. *)

fun contains_connects (q0, contains0) = (
    let
	fun contains_connects_x_qq ((x, qq), contains) = (
	    (foldl contains_connects contains qq))
    in
	case q0 of
	    Eq_Eq _ => contains0
	  | Eq_Connect _ => true
	  | Eq_If (cc, _, _) => (foldl contains_connects_x_qq contains0 cc)
	  | Eq_When (cc, _, _) => contains0
	  | Eq_App _ => contains0
	  | Eq_For ((_, qq), _, _) => (
	    (foldl contains_connects contains0 qq))
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
				    Annotation [], Comment []))
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
				    Annotation [], Comment []))
			 vv)
		end))
    in
	if (not (contains_connects (q0, false))) then
	    q0
	else
	    case q0 of
		Eq_Eq _ => q0
	      | Eq_Connect _ => q0
	      | Eq_If (cc0, aa, ww) => (
		let
		    val qq1 = (branch env cc0)
		in
		    Eq_If ([(Otherwise, qq1)], aa, ww)
		end)
	      | Eq_When _ => q0
	      | Eq_App _ => q0
	      | Eq_For ((rr0, qq0), aa, ww) => (
		let
		    val qq1 = (unroll qq0 env rr0)
		in
		    Eq_If ([(Otherwise, qq1)], aa, ww)
		end)
    end)

fun expand_equations_in_instance (k0, acc0) = (
    if (class_is_alias k0) then
	acc0
    else if (class_is_enumerator_definition k0) then
	acc0
    else if (class_is_package k0) then
	acc0
    else
	let
	    val _ = if (not (class_is_primitive k0)) then () else raise Match
	in
	    let
		val qfix = (fn (q, _) => ((expand_equations k0 [] q), []))
		val sfix = (fn (s, a) => (s, a))
		val walker = {q_vamp = qfix, s_vamp = sfix}
		val (k1, acc1) = (walk_in_class walker (k0, acc0))
	    in
		acc1
	    end
	end)

fun expand_equations_for_connects () = (
    (traverse_tree expand_equations_in_instance (instance_tree, [])))

(* ================================================================ *)

fun drop_subscripts rr = (
    (map (fn (id, _) => id) rr))

(* Tests if a reference is a component.  It ignores subscripts but it
   is precise. *)

fun reference_is_component subj w = (
    case w of
	Vref (_, []) => raise Match
      | Vref (NONE, _) => raise Match
      | Vref (SOME ns0, rr0) => (
	let
	    val rr1 = (drop_subscripts rr0)
	    val (prefix, _) = (split_last rr1)
	    val Subj (ns1, cc0) = subj
	    val cc1 = (drop_subscripts cc0)
	in
	    (ns0 = ns1) andalso (cc1 = prefix)
	end)
      | _ => raise Match)

fun collect_connects_in_equation kp (q0, acc0) = (
    let
	val subj = (subject_of_class kp)
    in
	case q0 of
	    Eq_Eq _ => (q0, acc0)
	  | Eq_Connect ((x, y), aa, ww) => (
	    let
		val cx = (reference_is_component subj x)
		val cy = (reference_is_component subj y)
	    in
		(q0, ([(x, cx), (y, cy)] :: acc0))
	    end)
	  | Eq_If _ => (q0, acc0)
	  | Eq_When _ => (q0, acc0)
	  | Eq_App _ => (q0, acc0)
	  | Eq_For _ => (q0, acc0)
    end)

fun collect_connects_in_instance (k0, acc0) = (
    if (class_is_alias k0) then
	acc0
    else if (class_is_enumerator_definition k0) then
	acc0
    else if (class_is_package k0) then
	acc0
    else
	let
	    val _ = if (not (class_is_primitive k0)) then () else raise Match
	in
	    let
		val efix = (fn (e, a) => (e, a))
		val qfix = (collect_connects_in_equation k0)
		val qwalk = (walk_in_equation qfix efix)
		val sfix = (fn (s, a) => (s, a))
		val walker = {q_vamp = qwalk, s_vamp = sfix}
		val (k1, acc1) = (walk_in_class walker (k0, acc0))
	    in
		acc1
	    end
	end)

fun collect_connects () = (
    (traverse_tree collect_connects_in_instance (instance_tree, [])))

(* ================================================================ *)

fun xcollect () = (
    let
	val _ = (expand_equations_for_connects ())
	val cc0 = (collect_connects ())
	val cc1 = (make_unions (op =) cc0)
    in
	cc1
    end)

end
