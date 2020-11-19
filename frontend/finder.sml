(* finder.sml -*-Coding: us-ascii-unix;-*- *)
(* Copyright (C) 2018-2020 RIKEN R-CCS *)

(* COMPONENT NAME LOOKUP. *)

structure finder :
sig
    type name_t
    type id_t
    type subject_t
    type definition_body_t
    type cook_step_t
    type cooker_t
    type binding_t

    val find_class :
	cooker_t -> (subject_t * definition_body_t) -> name_t
	-> (subject_t * definition_body_t) option
    val list_elements :
	cooker_t -> bool -> definition_body_t -> binding_t list
    val find_name_initial_part :
	cooker_t -> cook_step_t -> (subject_t * definition_body_t) -> id_t
	-> binding_t option
end = struct

open ast
open plain
open small0

type cooker_t = common.cooker_t

val class_bindings = classtree.class_bindings
val dummy_inners = classtree.dummy_inners
val fetch_from_instance_tree = classtree.fetch_from_instance_tree
val list_base_classes = classtree.list_base_classes
val assert_enclosings_are_cooked = classtree.assert_enclosings_are_cooked
val main_class = classtree.main_class
val assemble_package_if_fresh = classtree.assemble_package_if_fresh

val lookup_class_in_root = loader.lookup_class_in_root
val fetch_enclosing_class = loader.fetch_enclosing_class

(* Prints a trace message. *)

fun tr_find (s : string) = if true then (print (s ^"\n")) else ()
fun tr_find_vvv (s : string) = if false then (print (s ^"\n")) else ()

(* ================================================================ *)

(* Errs if a binding has an inner or outer. *)

fun check_without_inner_or_outer (Binding (v, _, _, (z, r, cv, h))) = (
    let
	val {Inner, Outer, ...} = r
    in
	if ((Inner, Outer) = (false, false)) then ()
	else raise (error_inner_outer_in_package v)
    end)

fun clear_inner {Final=f, Replaceable=p, Inner=i, Outer=j} = (
    {Final=f, Replaceable=p, Inner=false, Outer=j} : element_prefixes_t)

fun find_predefined_variable v = (
    case (List.find (fn d => (declaration_id d = v)) predefined_variables) of
	NONE => NONE
      | SOME d => SOME (EL_State d))

(* ================================================================ *)

fun make_dummy_inner (cv0 : named_element_t) subj = (
    let
	val _ = (warn_no_inner cv0)
	val v = (name_of_naming cv0)
	val subject = (compose_subject subj v [])
	val s = (subject_to_string subject)
	val r = {Final=false, Replaceable=false,
		 Inner=true, Outer=false}
	val dummy = Binding (v, subject, false, (Public, r, cv0, NONE))
    in
	case (HashTable.find dummy_inners s) of
	    NONE => (
	    let
		val _ = (HashTable.insert dummy_inners (s, dummy))
	    in
		dummy
	    end)
	  | SOME (b as Binding (v, _, _, (_, _, cv1, _))) => (
	    if (not (classes_are_compatible cv0 cv1)) then
		raise (error_incompatible_outers cv0 cv1)
	    else
		b)
    end)

(* Gathers variable/class names in a class including its imported and
   base classes.  It incorporates the inner/outer relation.  It
   gathers the list in classes after modifications and thus is fixed.
   It can be called with non-main (base) classes.  Note that the
   entries of non-constant variables and outer classes are skipped
   when it is processed as a package. *)

fun list_elements (cooker : cooker_t) exclude_imported kp = (
    let
	(*val _ = tr_find (";; list_elements ("^ (class_print_name kp) ^")")*)

	fun filter bb = (
	    if (not exclude_imported) then
		bb
	    else
		(List.filter (not o binding_is_imported) bb))

	val _ = if (class_is_body kp) then () else raise Match
	val _ = if (step_is_at_least E3 kp) then () else raise Match

	val subj = (subject_of_class kp)
	val tag = (innate_tag kp)
	val key = ((subject_to_string subj)
		   ^"@"^ (tag_to_string tag))
    in
	case ((HashTable.find class_bindings key)) of
	    SOME bb => (filter bb)
	  | NONE => (
	    let
		val bb = (gather_names_in_class cooker (subj, kp))
		val _ = (HashTable.insert class_bindings (key, bb))
	    in
		(filter bb)
	    end)
    end)

(* Gathers variable/class names in the class for list_elements.  See
   comments of list_elements.  Note that the outer case handles the
   inner-outer case as well. *)

and gather_names_in_class (cooker : cooker_t) (subjkp, kp) : binding_t list = (
    let
	val package = (class_is_package kp)

	fun mark_imported (Binding (v, j, _, e)) = (Binding (v, j, true, e))

	fun list_names (subjkp, kp) e = (
	    case e of
		Import_Clause _ => raise Match
	      | Extends_Clause _ => raise Match
	      | Element_Class (z, r, d, h) => (
		let
		    val Defclass ((v, g), k) = d
		    val subsubj = (compose_subject subjkp v [])
		in
		    if (not package) then
			if (#Outer r) then
			    [(look_for_inner cooker (EL_Class d) subjkp)]
			else
			    [Binding (v, subsubj, false,
				      (z, r, EL_Class d, h))]
		    else
			if (#Outer r) then
			    []
			else
			    [Binding (v, subsubj, false,
				      (z, r, EL_Class d, h))]
		end)
	      | Element_State (z, r, d, h) => (
		let
		    val Defvar (v, _, _, _, _, _) = d
		    val subsubj = (compose_subject subjkp v [])
		in
		    if (not package) then
			if (#Outer r) then
			    [(look_for_inner cooker (EL_State d) subjkp)]
			else
			    [Binding (v, subsubj, false,
				      (z, r, EL_State d, h))]
		    else
			if (declaration_is_constant d) then
			    [Binding (v, subsubj, false,
				      (z, r, EL_State d, h))]
			else
			    []
		end)
	      | Redefine_Class _ => []
	      | Redeclare_State _ => []
	      | Element_Enumerators _ => raise Match
	      | Element_Equations _ => []
	      | Element_Algorithms _ => []
	      | Element_External _ => []
	      | Element_Annotation _ => []
	      | Element_Import (z, tag, idxid, a, w) => (
		let
		    val _ = tr_find (";; gather_names_in_class import ("^
				     (tag_to_string tag) ^")")

		    val subj = (tag_to_subject tag)
		    val x0 = surely (fetch_from_instance_tree subj)
		    val (enclosing, _) = (subject_prefix subj)
		    val x1 = (assemble_package_if_fresh cooker E3 (subj, x0))
		    val _ = (assert_match_subject subj x1)
		    val nn0 = (gather_in_body_elements
				   (list_names (subj, x1)) x1)
		    val nn1 = (List.filter binding_is_public nn0)
		    val nn2 = (map mark_imported nn1)
		    val _ = (app check_without_inner_or_outer nn1)
		in
		    case idxid of
			NONE => nn2
		      | SOME (id0, id1) => (
			case (find_in_bindings id0 nn2) of
			    NONE => raise (error_no_import_name id0)
			  | SOME (Binding (_, j, i, e)) =>
			    [Binding (id1, j, i, e)])
		end)
	      | Element_Base (z, ci, a) => []
	      | Base_List _ => []
	      | Base_Classes _ => [])

	fun list_names_in_class k = (
	    (gather_in_body_elements (list_names (subjkp, kp)) k))

	val bases = (list_base_classes kp)
	val classes = [kp] @ bases
	val vv0 = (List.concat (map list_names_in_class classes))
	val vv1 = (drop_duplicate_declarations E3 vv0)
    in
	vv1
    end)

(* Returns a matching inner for a class name or a variable cv from the
   subj class.  It returns a dummy naming when no inner is found. *)

and look_for_inner (cooker : cooker_t) cv (subj : subject_t) = (
    let
	val Subj (ns, _) = subj
	val _ = if (ns = VAR) then () else raise Match
	val (prefix, _) = (subject_prefix subj)
	val nm = (look_for_inner_loop cooker cv prefix)
	val Binding (v, subsubj, i, (z, r, d, h)) = nm

	val _ = tr_find (";; Match inner-outer ("^
			 (subject_print_string subsubj) ^" for "^
			 (subject_print_string (compose_subject subj v [])
			  ^")"))
    in
	nm
    end)

and look_for_inner_loop (cooker : cooker_t) cv (prefix0 : subject_t) = (
    let
	fun search cooker cv subj = (
	    case subj of
		Subj (PKG, _) => raise Match
	      | Subj (VAR, []) => NONE
	      | _ => (
		case (look_for_inner_in_class cooker cv subj) of
		    SOME nm => SOME nm
		  | NONE => (
		    let
			val (prefix1, _) = (subject_prefix subj)
		    in
			(search cooker cv prefix1)
		    end)))
    in
	case (search cooker cv prefix0) of
	    SOME nm => nm
	  | NONE => (make_dummy_inner cv prefix0)
    end)

and look_for_inner_in_class (cooker : cooker_t) cv0 subj = (
    let
	fun inner v (Binding (x, _, _, (z, {Inner, ...}, cv1, r))) = (
	    ((v = x) andalso (z = Public) andalso (Inner = true)))

	val _ = tr_find (";; look_for_inner ("^
			 (id_to_string (name_of_naming cv0))
			 ^" in "^ (subject_print_string subj) ^")")

	val v = (name_of_naming cv0)
	val k = surely (fetch_from_instance_tree subj)
	val _ = if (class_is_instance k) then () else raise Match
	val _ = (assert_match_subject subj k)
	val bindings = (list_elements cooker true k)
    in
	case (List.find (inner v) bindings) of
	    NONE => NONE
	  | SOME (nm as Binding (v1, subj1, i, e as (z, r, cv1, h))) => (
	    if (not (classes_are_compatible cv0 cv1)) then
		raise (error_incompatible_outers cv0 cv1)
	    else
		SOME nm)
    end)

(* ================================================================ *)

(* Looks for a name (variable/class) in a class in the instance_tree.
   A search continues in the enclosing class if nothing is found.  It
   assumes the enclosing classes are already in E3 or greater.  It
   does not resolve reference elements of a variable, because the
   components may not be cooked yet.  A pair (subj,class) is a class
   and an optional instance.  Only class names and constants are
   searched for, when a class is not associated to an instance. *)

fun find_name_initial_part (cooker : cooker_t) step (subjkp_, kp) (id as Id s) = (
    let
	val _ = if (class_is_body kp) then () else raise Match
    in
	if (body_is_root kp) then
	    case (find_predefined_variable id) of
		SOME dd => (
		let
		    val e = (global_element dd)
		    val subj1 = (predefined_reference id)
		in
		    SOME (Binding (id, subj1, false, e))
		end)
	      | NONE => (
		case (lookup_class_in_root id) of
		    NONE => NONE
		  | SOME (subjx, kx) => (
		    let
			val tag = surely (subject_to_tag subjx)
			val dd = (EL_Class (tag_as_displaced_class tag))
			val e = (global_element dd)
				    (*val subjx = (class_reference_in_root v)*)
		    in
			SOME (Binding (id, subjx, false, e))
		    end))
	else
	    let
		val _ = if (step_is_at_least E3 kp) then () else raise Match
		val _ = (assert_match_subject subjkp_ kp)
		(*val _ = (assert_enclosings_are_cooked kp)*)
		val bindings = (list_elements cooker false kp)
	    in
		case (find_in_bindings id bindings) of
		    SOME (n as Binding (_, _, _, (z, r, EL_Class d, h))) => (
		    SOME n)
		  | SOME (n as Binding (_, _, _, (z, r, EL_State d, h))) => (
		    SOME n)
		  | NONE => (
		    let
			val k1 = (fetch_enclosing_class kp)

			(*AHO*)
			(*val pkg = (tag_of_enclosing_class kp)*)
			(*val subj1 = (tag_to_subject pkg)*)
			(*val subj1 = (subject_of_class k1)*)
			(*val enclosing = (enclosing_of_body k1)*)
			(*val k2 = (cooker E3 (subj1, k1))*)

			val _ = (assert_cooked_at_least E3 k1)
			val k2 = k1
			val subj1 = (subject_of_class k2)
		    in
			(find_name_initial_part cooker step (subj1, k2) id)
		    end)
	    end
    end)

(* ================================================================ *)

fun find_class_loop (cooker : cooker_t) kp enclosing0 (subj0, k0) nn0 = (
    case nn0 of
	[] => SOME (enclosing0, k0)
      | (s :: tt) => (
	let
	    (*val _ = tr_find (";; AHO find_class_loop 0")*)
	    (*val Defclass ((_, _), x0) = d0*)
	    val k2 = (assemble_package_if_fresh cooker E3 (subj0, k0))
	    val _ = (assert_match_subject subj0 k2)
	    val id = (Id s)
	    val bindings = (list_elements cooker true k2)
	in
	    case (find_in_bindings id bindings) of
		NONE => raise (error_class_name_not_found (Name nn0) kp)
	      | SOME (Binding (_, subsubj, _, (z, r, EL_Class d, h))) => (
		let
		    val Defclass ((_, _), x0) = d
		    val enclosing1 = subj0
		in
		    (find_class_loop cooker kp enclosing1 (subsubj, x0) tt)
		end)
	      | SOME (Binding (v, _, _, (z, r, EL_State d, h))) => (
		raise (error_state_found_for_class (Name nn0) kp))
	end))

(* Looks for a class name in a class.  It processes intermediate
   classes as packages, but it does not process the one returned. *)

fun find_class (cooker : cooker_t) (subj_, kp) nn = (
    let
	val _ = if (step_is_at_least E3 kp) then () else raise Match
	val _ = (assert_match_subject subj_ kp)
	(*val kp = surely (fetch_from_instance_tree scope)*)
	(*val extending = false*)
	(*val step = if extending then E2 else E3*)
	val subj = (subject_of_class kp)
    in
	case nn of
	    Name [] => raise Match
	  | Name (s :: t) => (
	    case (find_name_initial_part cooker E3 (subj, kp) (Id s)) of
		NONE => NONE
	      | SOME (Binding (v, subsubj, _, (z, r, EL_Class d, h))) => (
		let
		    val Defclass ((_, _), x0) = d
		    val (enclosing, _) = (subject_prefix subsubj)
		in
		    (find_class_loop cooker kp enclosing (subsubj, x0) t)
		end)
	      | SOME (Binding (v, _, _, (z, r, EL_State d, h))) => (
		raise (error_state_found_for_class nn kp)))
    end)

end
