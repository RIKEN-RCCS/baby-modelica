(* function.sml -*-Coding: us-ascii-unix;-*- *)
(* Copyright (C) 2018-2021 RIKEN R-CCS *)

(* A NAME RESOVLER IN FUNCTIONS. *)

structure function :
sig
    type class_definition_t
    type definition_body_t
    type expression_t
    type subject_t
    type ctx_t

    val resolve_function_components : definition_body_t -> unit
end = struct

open ast
open plain
open small1

type ctx_t = {k : definition_body_t}
type binder_t = expression_t -> expression_t

val class_tree = classtree.class_tree
val instance_tree = classtree.instance_tree
val fetch_class_by_scope = classtree.fetch_class_by_scope
val store_to_instance_tree = classtree.store_to_instance_tree
val assert_stored_in_instance_tree = classtree.assert_stored_in_instance_tree
val unwrap_array_of_instances = classtree.unwrap_array_of_instances
val subject_to_instance_tree_path = classtree.subject_to_instance_tree_path
val component_is_outer_alias = classtree.component_is_outer_alias
val component_is_expandable = classtree.component_is_expandable
val dereference_outer_alias = classtree.dereference_outer_alias
val insert_outer_alias = classtree.insert_outer_alias
val access_node = classtree.access_node
val find_in_components = classtree.find_in_components

val find_element = finder.find_element
val list_elements = finder.list_elements

val assemble_instance = blender.assemble_instance
val assemble_package = blender.assemble_package

val commute_modifier_over_subscript = refiner.commute_modifier_over_subscript

val walk_in_expression = walker.walk_in_expression

val fold_constants = folder.fold_constants

val obtain_array_dimension = operator.obtain_array_dimension

val bind_in_scoped_expression = binder.bind_in_scoped_expression

fun tr_build (s : string) = if true then (print (s ^"\n")) else ()
fun tr_build_vvv (s : string) = if false then (print (s ^"\n")) else ()

fun strip_dimension k0 = (
    case k0 of
	Def_Body _ => ([], [], k0)
      | Def_Der _ => raise Match
      | Def_Refine (x0, v, ts0, q0, (ss0, mm0), cc0, aa0, ww0) => (
	let
	    val k1 = Def_Refine (x0, v, ts0, q0, ([], []), cc0, aa0, ww0)
	in
	    ([], [], k1)
	end)
      | _ => raise Match)

(* Resolves references in the input/output variables of a function.
   It is similar to instantiate_components but differs.  It rewrites
   component declarations in a class.  It leaves array dimensions of a
   component because they are non-constants. *)

fun resolve_function_components kp = (
    let
	fun instantiate binding = (
	    case binding of
		Naming (_, _, _, _, (z, r, EL_Class _, h)) => raise Match
	      | Naming (id, subj, inner, _, (z, r, EL_State dx, h)) => (
		case (fetch_from_instance_tree subj) of
		    SOME kx => ()
		  | NONE => (
		    let
			val Defvar (_, q, k0, c0, aa, ww) = dx
			val _ = if (isSome c0) then () else raise Match
			val (ss, mm, k1) = (strip_dimension k0)
			val k2 = Def_Refine (k1, NONE, copy_type, q,
					     ([], []), NIL, aa, ww)
			(*val (dim, array) = (instantiate_class (subj, k2))*)
		    in
			()
		    end)))
    in
	if (class_is_outer_alias kp) then
	    ()
	else if (class_is_simple_type kp) then
	    ()
	else if (not (kind_is_function kp)) then
	    ()
	else
	    let
		val _ = (assert_cooked_at_least E3 kp)
		val bindings = (list_elements true kp)
		val (_, states) =
		      (List.partition binding_is_class bindings)
	    in
		(app instantiate states)
	    end
    end)

end
