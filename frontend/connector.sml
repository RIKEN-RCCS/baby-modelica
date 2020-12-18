(* connector.sml -*-Coding: us-ascii-unix;-*- *)
(* Copyright (C) 2018-2020 RIKEN R-CCS *)

(* CONNECTOR HANDLING.  It removes the uses of "connect",
   "Connections", "inStream()", "actualStream()", and
   "cardinality()". *)

structure connector :
sig
    type expression_t
    type subject_t
    val xconnect :
	unit -> ((ast.expression_t * bool) * (ast.expression_t * bool)
		 * subject_t) list
end = struct

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

val bind_in_scoped_expression = binder.bind_in_scoped_expression

val walk_in_class = walker.walk_in_class
val walk_in_expression = walker.walk_in_expression
val walk_in_equation = walker.walk_in_equation
val walk_in_statement = walker.walk_in_statement

val expand_equations_for_connects = syntaxer.expand_equations_for_connects

(* ================================================================ *)

(* Operators in Connections package (equation operators).
   Connect+false is for a connect equation (weak edge), Connect+true
   is for Connections.branch() (hard edge).  Root+true is for
   Connections.root(), Root+false is Connections.potentialRoot(). *)

datatype edge_marker_t = Edge of bool
datatype root_marker_t = Root of bool

(* ================================================================ *)

fun simplify_subscript kp w0 = (
    let
	val buildphase = false
	val w1 = (bind_in_scoped_expression buildphase kp w0)
    in
	(fold_constants kp buildphase [] w1)
    end)

(* ================================================================ *)

(* Tests if a reference is a component of a class specified by a
   subject (true when a reference is a class itself).  It ignores
   subscripts but it is precise. *)

fun reference_is_component__ subj w = (
    case w of
	Vref (_, []) => raise Match
      | Vref (NONE, _) => raise Match
      | Vref (SOME ns0, rr0) => (
	let
	    val rr1 = (drop_subscripts rr0)
	    val Subj (ns1, cc0) = subj
	    val cc1 = (drop_subscripts cc0)
	in
	    (ns0 = ns1) andalso (list_prefix (op =) cc1 rr1)
	end)
      | _ => raise Match)

(* Tests if a referenced component is a connector declared in the
   class (it checks the first part of the name declared in the class
   is a connector). *)

fun reference_is_connector_component subj w = (
    case w of
	Vref (_, []) => raise Match
      | Vref (NONE, _) => raise Match
      | Vref (SOME ns0, rr0) => (
	let
	    val Subj (ns1, cc0) = subj
	    val cc1 = (drop_subscripts cc0)
	    val rr1 = (drop_subscripts rr0)
	in
	    if (not ((ns0 = ns1) andalso (list_prefix (op =) cc1 rr1))) then
		false
	    else
		case (List.drop (rr0, (length cc0))) of
		    [] => false
		  | (id, ss) :: _ => (
		    let
			val component = (compose_subject subj id [])
			val k = surely (fetch_from_instance_tree component)
		    in
			(class_is_connector false k)
		    end)
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
		val outsidex = (reference_is_connector_component subj x)
		val outsidey = (reference_is_connector_component subj y)
	    in
		(q0, (((x, outsidex), (y, outsidey), subj) :: acc0))
	    end)
	  | Eq_If _ => (q0, acc0)
	  | Eq_When _ => (q0, acc0)
	  | Eq_App _ => (q0, acc0)
	  | Eq_For _ => (q0, acc0)
    end)

fun collect_connects_in_instance (k0, acc0) = (
    if (class_is_outer_alias k0) then
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
		val swalk = (fn (s, a) => (s, a))
		val walker = {vamp_q = qwalk, vamp_s = swalk}
		val (k1, acc1) = (walk_in_class walker (k0, acc0))
	    in
		acc1
	    end
	end)

fun collect_connects () = (
    (traverse_tree collect_connects_in_instance (instance_tree, [])))

(* ================================================================ *)

(* Finds an expandable connector in the reference path.  An undefined
   name is not an error. *)

fun find_expandable_loop kp rr0 = (
    case rr0 of
	[] => NONE
      | (id, ss0) :: rr1 => (
	let
	    val ss1 = (map (simplify_subscript kp) ss0)
	    val index = (map literal_to_int ss1)
	    val subj = (subject_of_class kp)
	    val subsubj = (compose_subject subj id index)
	in
	    case (fetch_from_instance_tree subsubj) of
		NONE => NONE
	      | SOME kx => (
		if (class_is_connector true kx) then
		    SOME subsubj
		else
		    case kx of
		        Def_Mock_Array _ => NONE
		      | _ => (find_expandable_loop kx rr1))
	end))

(*
fun find_expandable kp w = (
    case w of
	Vref (_, []) => raise Match
      | Vref (NONE, rr as (id, ss_) :: _) => (
	let
	    val _ = if (not (reference_is_global w)) then ()
		    else raise error_connector_in_package
	    val subj = (subject_of_class kp)
	    val subsubj = (compose_subject subj id [])
	in
	    case (fetch_from_instance_tree subsubj) of
		NONE => raise (error_name_not_found id kp)
	      | SOME kx => (
		if (class_is_connector true kx) then
		else
		    find_expandable_loop


		end)
	end)
      | Vref (SOME _, _) => raise Match
      | _ => raise Match)
*)

(* ================================================================ *)

fun connect_connects () = (
    let
	val _ = (expand_equations_for_connects ())
	val cc0 = (collect_connects ())
	(*val cc1 = (make_unions (op =) cc0)*)
    in
	cc0
    end)

(* ================================================================ *)

fun xconnect () = (connect_connects ())

end
