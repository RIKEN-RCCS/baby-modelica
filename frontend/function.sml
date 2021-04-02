(* function.sml -*-Coding: us-ascii-unix;-*- *)
(* Copyright (C) 2018-2021 RIKEN R-CCS *)

(* A NAME RESOVLER IN FUNCTIONS. *)

structure function :
sig
    type definition_body_t

    val resolve_function_components : definition_body_t -> unit
end = struct

open ast
open plain
open small1

val fetch_from_instance_tree = classtree.fetch_from_instance_tree
val store_to_instance_tree = classtree.store_to_instance_tree

val find_element = finder.find_element
val list_elements = finder.list_elements

val assemble_instance = blender.assemble_instance
val assemble_package = blender.assemble_package

val merge_modifiers = refiner.merge_modifiers
val commute_modifier_over_subscript = refiner.commute_modifier_over_subscript

val walk_in_expression = walker.walk_in_expression

val fold_constants = folder.fold_constants

val obtain_array_dimension = operator.obtain_array_dimension

val bind_in_scoped_expression = binder.bind_in_scoped_expression

fun tr_build (s : string) = if true then (print (s ^"\n")) else ()
fun tr_build_vvv (s : string) = if false then (print (s ^"\n")) else ()

fun strip_dimension k0 = (
    case k0 of
	Def_Body _ => (k0, [], [])
      | Def_Der _ => raise Match
      | Def_Refine (kx, v, ts, q, (ss, mm), cc, aa, ww) => (
	let
	    val k1 = Def_Refine (kx, v, ts, q, ([], []), cc, aa, ww)
	in
	    (k1, ss, mm)
	end)
      | Def_Scoped _ => (k0, [], [])
      | _ => raise Match)

(* Resolves references in the input/output variables of a function.
   It is similar to instantiate_components but differs.  It leaves
   array dimensions of a component because they are non-constants. *)

fun resolve_function_components kp = (
    let
	fun resolve binding = (
	    case binding of
		Naming (_, _, _, _, (z, r, EL_Class _, h)) => raise Match
	      | Naming (id, subj, inner, _, (z, r, EL_State dx, h)) => (
		let
		    val Defvar (_, q, k0, cc, aa, ww) = dx
		    val _ = if (not (isSome (fetch_from_instance_tree subj)))
			    then () else raise Match
		    val _ = if (not (isSome inner)) then () else raise Match
		    val _ = if (not (isSome cc)) then () else raise Match
		    val (k1, ss1, mm1) = (strip_dimension k0)
		    val k3 = (assemble_instance (subj, k1))
		    val (k4, ss0, mm0) = (strip_dimension k3)
		    val ctx = k0
		    val ssx = (merge_subscripts ss0 ss1)
		    val mmx = (merge_modifiers ctx mm1 mm0)
		    val k5 = Def_Argument (k4, (ssx, mmx), aa, ww)
		    val _ = (store_to_instance_tree subj k5)
		in
		    ()
		end))

	val kx = (body_of_argument kp)
    in
	if (class_is_simple_type kx) then
	    ()
	else if (not (kind_is_function kx)) then
	    ()
	else
	    let
		val _ = if (not (class_is_outer_alias kx)) then ()
			else raise Match
		val _ = (assert_cooked_at_least E3 kp)
		val bindings = (list_elements true kp)
		val (_, states) =
		      (List.partition binding_is_class bindings)
	    in
		(app resolve states)
	    end
    end)

end
