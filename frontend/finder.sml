(* finder.sml -*-Coding: us-ascii-unix;-*- *)
(* Copyright (C) 2018-2021 RIKEN R-CCS *)

(* COMPONENT NAME LOOKUP. *)

structure finder :
sig
    type name_t
    type id_t
    type subject_t
    type definition_body_t
    type cook_step_t
    type cooker_t
    type naming_t

    val find_class :
	cooker_t -> (subject_t * definition_body_t) -> name_t
	-> definition_body_t option
    val list_elements :
	cooker_t -> bool -> definition_body_t -> naming_t list

    val find_element :
	cooker_t -> bool -> definition_body_t -> id_t -> naming_t option
    val find_name_initial_part :
	cooker_t -> definition_body_t -> id_t -> naming_t option
    val list_component_names : definition_body_t -> id_t list
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

val lookup_class_in_package_root = loader.lookup_class_in_package_root
val fetch_enclosing_class = loader.fetch_enclosing_class

(* Prints a trace message. *)

fun tr_find (s : string) = if true then (print (s ^"\n")) else ()
fun tr_find_vvv (s : string) = if false then (print (s ^"\n")) else ()

(* ================================================================ *)

(* Errs if a binding has an inner or outer. *)

fun check_without_inner_or_outer (Naming (v, _, _, _, (z, r, cv, h))) = (
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

fun import_name_to_string tag idxid = (
    case idxid of
	NONE => (tag_to_string tag)
      | SOME (id, _) => ((tag_to_string tag) ^"."^ (id_to_string id)))

(* ================================================================ *)

fun make_dummy_inner (cv0 : element_sum_t) subj = (
    let
	val _ = (warn_no_inner cv0)
	val id = (name_of_element_union cv0)
	val subject = (compose_subject subj id [])
	val s = (subject_to_string subject)
    in
	case (HashTable.find dummy_inners s) of
	    NONE => (
	    let
		val r = {Final=false, Replaceable=false,
			 Inner=true, Outer=false}
		val dummy = Naming (id, subject, NONE, false,
				    (Public, r, cv0, NONE))
		val _ = (HashTable.insert dummy_inners (s, dummy))
	    in
		subject
	    end)
	  | SOME (Naming (_, _, _, _, (_, _, cv1, _))) => (
	    if (not (classes_are_compatible cv0 cv1)) then
		raise (error_incompatible_outers cv0 cv1)
	    else
		subject)
    end)

(* Gathers variable/class names in a class including its imported and
   base classes.  It incorporates the inner/outer relation.  It can be
   called with both main and base classes.  A returned list is
   complete for a class at step=E3 or greater.  Yet, it may be called
   with a class at step=E2 before applying modifiers, but then the
   list of names is only usable.  It caches the list for a class
   step=E3 or greater.  Note that the entries of non-constant
   variables and outer classes are skipped when it is processed as a
   package.  It is an error to call this with the package-root. *)

fun list_elements (cooker : cooker_t) exclude_imported kp = (
    let
	(*val _ = tr_find (";; list_elements ("^ (class_print_name kp) ^")")*)

	fun filter bb = (
	    if (not exclude_imported) then
		bb
	    else
		(List.filter (not o binding_is_imported) bb))

	val _ = if (class_is_body kp) then () else raise Match
	val _ = if (step_is_at_least E2 kp) then () else raise Match

	val caching = (step_is_at_least E3 kp)
	val subj = (subject_of_class kp)
	val tag = (innate_tag kp)
	val key = ((subject_to_string subj) ^"@"^ (tag_to_string tag))
    in
	if (not caching) then
	    let
		val bb = (gather_names_in_class cooker kp)
	    in
		(filter bb)
	    end
	else
	    case (HashTable.find class_bindings key) of
		SOME bb => (filter bb)
	      | NONE => (
		let
		    val bb = (gather_names_in_class cooker kp)
		    val _ = (HashTable.insert class_bindings (key, bb))
		in
		    (filter bb)
		end)
    end)

(* Gathers variable/class names in a class for list_elements.  See
   comments of list_elements.  Note that the outer case handles the
   inner-outer case as well. *)

and gather_names_in_class (cooker : cooker_t) kp : naming_t list = (
    let
	val _ = if (not (class_is_root kp)) then () else raise Match

	val package = (class_is_package kp)
	val function = (kind_is_function kp)

	fun mark_imported (Naming (v, j, i, _, e)) = Naming (v, j, i, true, e)

	fun list_names kp e = (
	    case e of
		Import_Clause _ => raise Match
	      | Extends_Clause _ => raise Match
	      | Element_Class (z, r, d, h) => (
		let
		    val Defclass ((v, g), k) = d
		    val subjkp = (subject_of_class kp)
		    val subj = (compose_subject subjkp v [])
		in
		    if (not package) then
			if (#Outer r) then
			    let
				val inner = (look_for_inner
						 cooker (EL_Class d) subjkp)
			    in
				[Naming (v, subj, SOME inner, false,
					 (z, r, EL_Class d, h))]
			    end
			else
			    [Naming (v, subj, NONE, false,
				     (z, r, EL_Class d, h))]
		    else
			if (#Outer r) then
			    []
			else
			    [Naming (v, subj, NONE, false,
				     (z, r, EL_Class d, h))]
		end)
	      | Element_State (z, r, d, h) => (
		let
		    val Defvar (v, _, _, _, _, _) = d
		    val subjkp = (subject_of_class kp)
		    val subj = (compose_subject subjkp v [])
		in
		    if (not package) then
			if (#Outer r) then
			    let
				val inner = (look_for_inner
						 cooker (EL_State d) subjkp)
			    in
				[Naming (v, subj, SOME inner, false,
					 (z, r, EL_State d, h))]
			    end
			else
			    [Naming (v, subj, NONE, false,
				     (z, r, EL_State d, h))]
		    else if (not function) then
			if (declaration_is_constant d) then
			    [Naming (v, subj, NONE, false,
				     (z, r, EL_State d, h))]
			else
			    []
		    else
			[Naming (v, subj, NONE, false,
				 (z, r, EL_State d, h))]
		end)
	      | Redefine_Class _ => []
	      | Redeclare_State _ => []
	      | Element_Enumerators _ => []
	      | Element_Equations _ => []
	      | Element_Algorithms _ => []
	      | Element_External _ => []
	      | Element_Annotation _ => []
	      | Element_Import (z, tag, idxid, a, w) => (
		let
		    val _ = tr_find (";; gather_names_in_class import ("^
				     (import_name_to_string tag idxid) ^")")

		    val subj = (tag_to_subject tag)
		    val x0 = surely (fetch_from_instance_tree subj)
		    val (enclosing, _) = (subject_prefix subj)
		    val x1 = (assemble_package_if_fresh cooker E3 (subj, x0))
		    val _ = (assert_match_subject subj x1)
		    val nn0 = (gather_in_body_elements
				   (list_names x1) x1)
		    val nn1 = (List.filter binding_is_public nn0)
		    val nn2 = (map mark_imported nn1)
		    val _ = (app check_without_inner_or_outer nn1)
		in
		    case idxid of
			NONE => nn2
		      | SOME (id0, id1) => (
			case (find_in_bindings id0 nn2) of
			    NONE => raise (error_no_import_name id0)
			  | SOME (Naming (_, j, n, i, e)) =>
			    [Naming (id1, j, n, i, e)])
		end)
	      | Element_Base (z, ci, a) => []
	      | Base_List _ => []
	      | Base_Classes _ => [])

	fun list_names_in_class k = (
	    (gather_in_body_elements (list_names kp) k))

	val bases = (list_base_classes kp)
	val classes = [kp] @ bases
	val vv0 = (List.concat (map list_names_in_class classes))
	val vv1 = (drop_duplicate_declarations E3 vv0)
    in
	vv1
    end)

(* Returns a matching inner for a class or variable name cv from the
   class pointed by a subject.  It returns a dummy one when no inner
   is found. *)

and look_for_inner (cooker : cooker_t) cv (subj : subject_t) = (
    let
	val id = (name_of_element_union cv)
	val Subj (ns, _) = subj
	val _ = if (ns = VAR) then () else raise Match
	val (prefix, _) = (subject_prefix subj)
	val inner = (look_for_inner_loop cooker cv prefix)
	val newsubj = (compose_subject subj id [])
	(*val Naming (id, subsubj, inner, i, e) = binding0*)
	(*val _ = if (inner = NONE) then () else raise Match*)
	(*val binding1 = Naming (id, newsubj, SOME subsubj, i, e)*)

	val _ = tr_find (";; Match inner-outer ("^
			 (subject_print_string inner) ^" for "^
			 (subject_print_string newsubj) ^")")
    in
	inner
    end)

and look_for_inner_loop (cooker : cooker_t) cv (prefix0 : subject_t) = (
    let
	fun search cooker cv subj0 = (
	    case subj0 of
		Subj (PKG, _) => raise Match
	      | Subj (VAR, _) => (
		case (look_for_inner_in_class cooker cv subj0) of
		    SOME subj1 => SOME subj1
		  | NONE => (
		    case subj0 of
		        Subj (VAR, []) => NONE
		      | Subj (VAR, _) => (
			let
			    val (prefix1, _) = (subject_prefix subj0)
			in
			    (search cooker cv prefix1)
			end)
		      | Subj (PKG, _) => raise Match)))
    in
	case (search cooker cv prefix0) of
	    SOME inner => inner
	  | NONE => (make_dummy_inner cv prefix0)
    end)

and look_for_inner_in_class (cooker : cooker_t) cv0 subj0 = (
    let
	fun inner id (Naming (x, _, _, _, (z, {Inner, ...}, d, r))) = (
	    ((x = id) andalso (z = Public) andalso (Inner = true)))

	val _ = tr_find (";; look_for_inner ("^
			 (id_to_string (name_of_element_union cv0))
			 ^" in "^ (subject_print_string subj0) ^")")

	val id = (name_of_element_union cv0)
	val kp = surely (fetch_from_instance_tree subj0)
	val _ = if (class_is_instance kp) then () else raise Match
	val _ = (assert_match_subject subj0 kp)
	val bindings = (list_elements cooker true kp)
    in
	case (List.find (inner id) bindings) of
	    NONE => NONE
	  | SOME (Naming (_, subj1, _, _, (z, r, cv1, h))) => (
	    if (not (classes_are_compatible cv0 cv1)) then
		raise (error_incompatible_outers cv0 cv1)
	    else
		SOME subj1)
    end)

(* ================================================================ *)

(* Lists names of components in the class. *)

fun list_component_names kp = (
    let
	val _ = if ((cook_step kp) = E2) then () else raise Match

	fun name (Naming (id, _, _, _, (z, r, d, h))) = (
	    case d of
		EL_Class _ => raise Match
	      | EL_State (Defvar (_, q, k, c, a, w)) => id)

	fun faulting_cooker _ (_, _) = raise Match
	val bindings = (list_elements faulting_cooker false kp)
	val (classes, states) = (List.partition binding_is_class bindings)
	val cc = (map name states)
    in
	cc
    end)

(* ================================================================ *)

(* Looks for a name (variable/class) in a class.  Only classes and
   constants are searched for when a class is a package.  It returns a
   variable/class as it is declared/defined (that is, it is not
   cooked). *)

fun find_element (cooker : cooker_t) exclude_imported kp id = (
    let
	val _ = if (class_is_body kp) then () else raise Match
	val _ = if (step_is_at_least E3 kp) then () else raise Match
    in
	if (body_is_package_root kp) then
	    case (find_predefined_variable id) of
		SOME dd => (
		let
		    val e = (usual_element dd)
		    val subj1 = (predefined_reference id)
		in
		    SOME (Naming (id, subj1, NONE, false, e))
		end)
	      | NONE => (
		case (lookup_class_in_package_root id) of
		    NONE => NONE
		  | SOME (subjx, kx) => (
		    let
			val tag = surely (subject_to_tag subjx)
			val dd = (EL_Class (tag_as_displaced_class tag))
			val e = (usual_element dd)
		    in
			SOME (Naming (id, subjx, NONE, false, e))
		    end))
	else
	    let
		(*AHOAHOAHO*) fun faulting_cooker _ (_, _) = raise Match
		val bindings = (list_elements cooker exclude_imported kp)
	    in
		case (find_in_bindings id bindings) of
		    SOME binding => SOME binding
		  | NONE => NONE
	    end
    end)

(* ================================================================ *)

(* Looks for a name (variable/class) in a class.  A search continues
   in the enclosing classes if nothing is found in a given class.  It
   assumes the enclosing classes are already in step=E3 or greater.
   See find_element. *)

fun find_name_initial_part (cooker : cooker_t) kp (id as Id s) = (
    let
	val _ = if (class_is_body kp) then () else raise Match
    in
	case (find_element cooker false kp id) of
	    SOME binding => SOME binding
	  | NONE => (
	    if (body_is_package_root kp) then
		NONE
	    else
		let
		    val k1 = (fetch_enclosing_class kp)
		    val _ = (assert_cooked_at_least E3 k1)
		    val subj1_ = (subject_of_class k1)
		    fun faulting_cooker _ (_, _) = raise Match
		in
		    (find_name_initial_part faulting_cooker k1 id)
		end)
    end)

(* ================================================================ *)

(* Returns a name taking account of an inner-outer matching. *)

fun true_subject (Naming (_, subj, inner, _, e)) = (
    case inner of
	NONE => subj
      | SOME subjx => subjx)

fun find_class_loop (cooker : cooker_t) kp enclosing0_ (subjk0, k0) nn0 = (
    case nn0 of
	[] => SOME k0
      | (s :: tt) => (
	let
	    val k2 = (assemble_package_if_fresh cooker E3 (subjk0, k0))
	    val _ = (assert_match_subject subjk0 k2)
	    val id = (Id s)
	    (*AHOAHOAHO*) fun faulting_cooker _ (_, _) = raise Match
	in
	    case (find_element cooker true k2 id) of
		NONE => raise (error_class_name_not_found (Name nn0) kp)
	      | SOME (name as Naming (_, _, _, _, (z, r, EL_Class dx, h))) => (
		let
		    val subjx0 = (true_subject name)
		    val Defclass ((_, _), x0) = dx
		    val enclosing1_ = subjk0
		in
		    (find_class_loop cooker kp enclosing1_ (subjx0, x0) tt)
		end)
	      | SOME (Naming (_, _, _, _, (z, r, EL_State d, h))) => (
		raise (error_state_found_for_class (Name nn0) kp))
	end))

(* Looks for a class name in a class.  It processes intermediate
   classes as packages, but it does not process the one returned. *)

fun find_class (cooker : cooker_t) (subjkp_, kp) nn = (
    let
	val _ = if (step_is_at_least E3 kp) then () else raise Match
	val _ = (assert_match_subject subjkp_ kp)
	(*val kp = surely (fetch_from_instance_tree scope)*)
	(*val extending = false*)
	(*val step = if extending then E2 else E3*)
	val subj = (subject_of_class kp)
    in
	case nn of
	    Name [] => raise Match
	  | Name (s :: t) => (
	    case (find_name_initial_part cooker kp (Id s)) of
		NONE => NONE
	      | SOME (name as Naming (_, _, _, _, (z, r, EL_Class dx, h))) => (
		let
		    val subjx0 = (true_subject name)
		    val Defclass (_, x0) = dx
		    val (enclosing, _) = (subject_prefix subjx0)
		in
		    (find_class_loop cooker kp enclosing (subjx0, x0) t)
		end)
	      | SOME (Naming (_, _, _, _, (z, r, EL_State dx, h))) => (
		raise (error_state_found_for_class nn kp)))
    end)

end
