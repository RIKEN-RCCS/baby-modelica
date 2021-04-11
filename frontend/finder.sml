(* finder.sml -*-Coding: us-ascii-unix;-*- *)
(* Copyright (C) 2018-2021 RIKEN R-CCS *)

(* COMPONENT NAME LOOKUP. *)

structure finder :
sig
    type name_t
    type id_t
    type subject_t
    type definition_body_t
    type cooker_t
    type naming_t

    val find_class :
	cooker_t -> definition_body_t -> name_t -> definition_body_t option

    val list_elements :
	bool -> definition_body_t -> naming_t list
    val find_element :
	bool -> definition_body_t -> id_t -> naming_t option
    val find_name_initial_part :
	definition_body_t -> id_t -> naming_t option
    val list_component_names : definition_body_t -> id_t list
end = struct

open plain ast common message small0

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

fun trace n (s : string) = if n <= 3 then (print (s ^"\n")) else ()

(* ================================================================ *)

(* Errs if a naming has an inner or outer. *)

fun check_no_inner_or_outer (Naming (v, _, _, _, ne)) = (
    let
	val r = (element_prefixes_of_naming_element ne)
	val {Inner, Outer, ...} = r
    in
	if ((Inner, Outer) = (false, false)) then ()
	else raise (error_inner_outer_in_package v)
    end)

fun clear_inner {Final=f, Replaceable=p, Inner=i, Outer=j} = (
    {Final=f, Replaceable=p, Inner=false, Outer=j} : element_prefixes_t)

fun find_predefined_variable v = (
    let
	fun id_of_declaration (Defvar (v, _)) = v
    in
	(List.find (fn d => (id_of_declaration d = v)) predefined_variables)
    end)

fun import_name_to_string tag idxid = (
    case idxid of
	NONE => (tag_to_string tag)
      | SOME (id, _) => ((tag_to_string tag) ^"."^ (id_to_string id)))

(*AHO*) (* CLASS SIMILARITY IS NOT IMPLEMENTED. *)

(* Drops duplicate declarations.  It does not matter about variable
   declarations at step=E3. *)

fun drop_duplicate_declarations step (bindings : naming_t list) = (
    let
	fun eq (Naming (v0, _, _, _, _), Naming (v1, _, _, _, _)) = (
	    (v0 = v1))

	fun unify (b0 as Naming (_, _, _, _, e0), b1 as Naming (_, _, _, _, e1)) = (
	    case (e0, e1) of
		(EL_Class (_, _, d0, _), EL_Class (_, _, d1, _)) => (
		let
		    val Defclass ((v0, g0), k0) = d0
		    val Defclass ((v1, g1), k1) = d1
		in
		    if ((tag_of_definition d0) = (tag_of_definition d1)) then
			b0
		    else
			(*raise (error_duplicate_declarations (b0, b1))*)
			b0
		end)
	      | (EL_State (_, q0, d0, _), EL_State (_, q1, d1, _)) => (
		let
		    val Defvar (v0, k0) = d0
		    val Defvar (v1, k1) = d1
		in
		    if (step = E3) then
			b0
		    else
			(*raise (error_duplicate_declarations (b0, b1))*)
			b0
		end)
	      | _ => raise (error_duplicate_declarations (b0, b1)))

	fun unify_by_pairs ([]) = raise Match
	  | unify_by_pairs (b :: bb) = (foldl unify b bb)

	val bb0 = (list_groups eq bindings)
	val bb1 = (map unify_by_pairs bb0)
    in
	bb1
    end)

(* ================================================================ *)

fun mark_inner ne0 = (
    let
	fun mark_in_element_prefixes r = (
	    let
		val {Final=f, Replaceable=p, Inner=i, Outer=u} = r
	    in
		{Final=f, Replaceable=p, Inner=true, Outer=u}
	    end)
    in
	case ne0 of
	    EL_Class (z, r0, d, h) => (
	    EL_Class (z, (mark_in_element_prefixes r0), d, h))
	  | EL_State (z, r0, d, h) => (
	    EL_State (z, (mark_in_element_prefixes r0), d, h))
    end)

fun make_dummy_inner (cv0 : naming_element_t) subj = (
    let
	val _ = (warn_no_inner cv0)
	val id = (name_of_naming_element cv0)
	val subject = (compose_subject subj id [])
	val s = (subject_to_string subject)
    in
	case (HashTable.find dummy_inners s) of
	    NONE => (
	    let
		(*
		val r = {Final=false, Replaceable=false,
			 Inner=true, Outer=false}
		val cvx = (Public, r, cv0, NONE)
		*)
		val ne1 = (mark_inner cv0)
		val inner = Naming (id, subject, NONE, false, ne1)
		val _ = (HashTable.insert dummy_inners (s, inner))
	    in
		subject
	    end)
	  | SOME (Naming (_, _, _, _, cv1)) => (
	    if (not (classes_are_compatible cv0 cv1)) then
		raise (error_incompatible_outers cv0 cv1)
	    else
		subject)
    end)

(* Gathers class/variable names in a class including its imported and
   base classes.  It incorporates the inner/outer relation.  It can be
   called with both main and base classes.  A returned list is
   complete for a class at step=E3 or greater.  It caches the list for
   a class step=E3 or greater.  Note that the entries of non-constant
   variables and outer classes are skipped when it is processed as a
   package.  It is an error to call this with the package-root. *)

fun list_elements exclude_imported kp = (
    let
	(*val _ = trace 3 (";; list_elements ("^ (class_print_name kp) ^")")*)
	val _ = if (class_is_body kp) then () else raise Match
	val _ = if (step_is_at_least E3 kp) then () else raise Match

	fun filter bb = (
	    if (not exclude_imported) then
		bb
	    else
		(List.filter (not o binding_is_imported) bb))

	(*val caching = (step_is_at_least E3 kp)*)
	val subj = (subject_of_class kp)
	val tag = (innate_tag kp)
	val key = ((subject_to_string subj) ^"@"^ (tag_to_string tag))
    in
	case (HashTable.find class_bindings key) of
	    SOME bb => (filter bb)
	  | NONE => (
	    let
		val bb0 = (gather_names_in_class kp)
		val bb1 = (drop_duplicate_declarations E3 bb0)
		val _ = (HashTable.insert class_bindings (key, bb1))
	    in
		(filter bb1)
	    end)
    end)

(* Gathers class/variable names in a class.  See the comments of
   list_elements.  The returned list may have duplicates, and the
   caller should unified them.  Note that the outer case handles the
   inner-outer case as well.  It is called with a class at step=E2 via
   list_component_names, or step=E3 via list_elements.  A class at
   step=E2 is before applying modifiers, and then, the list of names
   is only usable. *)

and gather_names_in_class kp : naming_t list = (
    let
	fun faulting_cooker _ (_, _) = raise Match
	val cooker : cooker_t = faulting_cooker
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
		    val ne = EL_Class (z, r, d, h)
		    val Defclass ((v, g), k) = d
		    val subjkp = (subject_of_class kp)
		    val subj = (compose_subject subjkp v [])
		in
		    if (not package) then
			if (#Outer r) then
			    let
				val inner = (look_for_inner
						 cooker ne subjkp)
			    in
				[Naming (v, subj, SOME inner, false, ne)]
			    end
			else
			    [Naming (v, subj, NONE, false, ne)]
		    else
			if (#Outer r) then
			    []
			else
			    [Naming (v, subj, NONE, false, ne)]
		end)
	      | Element_State (z, r, d, h) => (
		let
		    val ne = EL_State (z, r, d, h)
		    val Defvar (v, _) = d
		    val subjkp = (subject_of_class kp)
		    val subj = (compose_subject subjkp v [])
		in
		    if (not package) then
			if (#Outer r) then
			    let
				val inner = (look_for_inner
						 cooker ne subjkp)
			    in
				[Naming (v, subj, SOME inner, false, ne)]
			    end
			else
			    [Naming (v, subj, NONE, false, ne)]
		    else if (not function) then
			if (declaration_is_constant d) then
			    [Naming (v, subj, NONE, false, ne)]
			else
			    []
		    else
			[Naming (v, subj, NONE, false, ne)]
		end)
	      | Redefine_Class _ => []
	      | Redeclare_State _ => []
	      | Element_Enumerators _ => []
	      | Element_Equations _ => []
	      | Element_Algorithms _ => []
	      | Element_External _ => []
	      | Element_Annotation _ => []
	      | Element_Import (z, tag, idxid, (aa, ww)) => (
		let
		    val _ = trace 5 (";; gather_names_in_class import ("^
				     (import_name_to_string tag idxid) ^")")

		    val subj = (tag_to_subject tag)
		    val x0 = surely (fetch_from_instance_tree subj)
		    (*
		    val (enclosing, _) = (subject_prefix subj)
		    val x1 = (assemble_package_if_fresh cooker E3 (subj, x0))
		    val _ = (assert_match_subject subj x1)
		    *)
		    val x1 = x0
		    val nn0 = (gather_in_body_elements
				   (list_names x1) x1)
		    val nn1 = (List.filter binding_is_public nn0)
		    val nn2 = (map mark_imported nn1)
		    val _ = (app check_no_inner_or_outer nn1)
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
    in
	vv0
    end)

(* Returns a matching inner for a class or variable name cv from the
   class pointed by a subject.  It returns a dummy one when no inner
   is found. *)

and look_for_inner (cooker : cooker_t) cv (subj : subject_t) = (
    let
	val id = (name_of_naming_element cv)
	val Subj (ns, _) = subj
	val _ = if (ns = VAR) then () else raise Match
	val (prefix, _) = (subject_prefix subj)
	val inner = (look_for_inner_loop cooker cv prefix)
	val newsubj = (compose_subject subj id [])
	(*val Naming (id, subsubj, inner, i, e) = binding0*)
	(*val _ = if (inner = NONE) then () else raise Match*)
	(*val binding1 = Naming (id, newsubj, SOME subsubj, i, e)*)

	val _ = trace 3 (";; Match inner-outer ("^
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
	fun inner id (Naming (x, _, _, _, ne)) = (
	    case ne of
		EL_Class (z, {Inner=i, ...}, _, _) => (
		((x = id) andalso (z = Public) andalso (i = true)))
	      | EL_State (z, {Inner=i, ...}, _, _) => (
		((x = id) andalso (z = Public) andalso (i = true))))

	val _ = trace 3 (";; look_for_inner ("^
			 (id_to_string (name_of_naming_element cv0))
			 ^" in "^ (subject_print_string subj0) ^")")

	val id = (name_of_naming_element cv0)
	val kp = surely (fetch_from_instance_tree subj0)
	val _ = if (class_is_instance kp) then () else raise Match
	val _ = (assert_match_subject subj0 kp)
	val _ = (assert_cooked_at_least E3 kp)
	val bindings = (list_elements true kp)
    in
	case (List.find (inner id) bindings) of
	    NONE => NONE
	  | SOME (Naming (_, subj1, _, _, cv1)) => (
	    if (not (classes_are_compatible cv0 cv1)) then
		raise (error_incompatible_outers cv0 cv1)
	    else
		SOME subj1)
    end)

(* ================================================================ *)

(* Lists names of components in the class.  This is called with a
   class at step=E2 during building. *)

fun list_component_names kp = (
    let
	val _ = if ((cook_step kp) = E2) then () else raise Match

	val _ = trace 5 (";; list_component_names ("^
			 (class_print_name kp) ^")...")

	fun name (Naming (id, _, _, _, ne)) = (
	    case ne of
		EL_Class _ => raise Match
	      | EL_State _ => id)

	(*val bindings = (list_elements false kp)*)
	val bindings = (gather_names_in_class kp)
	val (_, states) = (List.partition binding_is_class bindings)
	val cc0 = (map name states)
	val cc1 = (list_uniquify (op =) cc0)

	val _ = trace 5 (";; list_component_names ("^
			 (class_print_name kp) ^")... done")
    in
	cc1
    end)

(* ================================================================ *)

(* Looks for a name (class/variable) in a class.  Only classes and
   constants are searched for when a class is a package.  It returns a
   class/variable as it is defined/declared (that is, it is not
   cooked). *)

fun find_element exclude_imported kp id = (
    let
	val _ = if (class_is_body kp) then () else raise Match
	val _ = if (step_is_at_least E3 kp) then () else raise Match
    in
	if (body_is_package_root kp) then
	    case (find_predefined_variable id) of
		SOME dd => (
		let
		    val ne = (usual_state_element dd)
		    val subj1 = (predefined_reference id)
		in
		    SOME (Naming (id, subj1, NONE, false, ne))
		end)
	      | NONE => (
		case (lookup_class_in_package_root id) of
		    NONE => NONE
		  | SOME (subjx, kx) => (
		    let
			val tag = surely (subject_to_tag subjx)
			val dd = (tag_as_displaced_class tag)
			val ne = (usual_class_element dd)
		    in
			SOME (Naming (id, subjx, NONE, false, ne))
		    end))
	else
	    let
		val bindings = (list_elements exclude_imported kp)
	    in
		case (find_in_bindings id bindings) of
		    SOME binding => SOME binding
		  | NONE => NONE
	    end
    end)

(* ================================================================ *)

(* Looks for a name (class/variable) in a class.  A search continues
   in the enclosing classes if nothing is found in a given class.  It
   assumes the enclosing classes are already in step=E3 or greater.
   See find_element. *)

fun find_name_initial_part kp (id as Id s) = (
    let
	val _ = if (class_is_body kp) then () else raise Match
    in
	case (find_element false kp id) of
	    SOME binding => SOME binding
	  | NONE => (
	    if (body_is_package_root kp) then
		NONE
	    else
		let
		    val k1 = (fetch_enclosing_class kp)
		    val _ = (assert_cooked_at_least E3 k1)
		    val subj1_ = (subject_of_class k1)
		in
		    (find_name_initial_part k1 id)
		end)
    end)

(* ================================================================ *)

(* Returns a name taking account of an inner-outer matching. *)

fun true_subject (Naming (_, subj, inner, _, e)) = (
    case inner of
	NONE => subj
      | SOME subjx => subjx)

fun find_class_loop (cooker : cooker_t) kp (subjk0, k0) nn0 = (
    case nn0 of
	[] => SOME k0
      | (s :: tt) => (
	let
	    val k2 = (assemble_package_if_fresh cooker E3 (subjk0, k0))
	    val _ = (assert_match_subject subjk0 k2)
	    val id = (Id s)
	in
	    case (find_element true k2 id) of
		NONE => raise (error_class_name_not_found (Name nn0) kp)
	      | SOME (name as Naming (_, _, _, _, EL_Class (z, r, dx, h))) => (
		let
		    val subjx0 = (true_subject name)
		    val Defclass ((_, _), x0) = dx
		in
		    (find_class_loop cooker kp (subjx0, x0) tt)
		end)
	      | SOME (Naming (_, _, _, _, EL_State (z, r, dx, h))) => (
		raise (error_state_found_for_class (Name nn0) kp))
	end))

(* Looks for a class name in a class.  It processes intermediate
   classes as packages, but it does not process the one returned. *)

fun find_class (cooker : cooker_t) kp nn = (
    let
	val _ = if (step_is_at_least E3 kp) then () else raise Match
	val subj = (subject_of_class kp)
    in
	case nn of
	    Name [] => raise Match
	  | Name (s :: tt) => (
	    case (find_name_initial_part kp (Id s)) of
		NONE => NONE
	      | SOME (name as Naming (_, _, _, _, EL_Class (z, r, dx, h))) => (
		let
		    val subjx0 = (true_subject name)
		    val Defclass (_, x0) = dx
		in
		    (find_class_loop cooker kp (subjx0, x0) tt)
		end)
	      | SOME (Naming (_, _, _, _, EL_State (z, r, dx, h))) => (
		raise (error_state_found_for_class nn kp)))
    end)

end
