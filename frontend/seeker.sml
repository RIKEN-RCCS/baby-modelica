(* seeker.sml -*-Coding: us-ascii-unix;-*- *)
(* Copyright (C) 2018-2021 RIKEN R-CCS *)

(* LOOKUP FOR IMPORT/EXTENDS-CLAUSES.  It searches in classes that are
   half-syntaxed (step=E0-E2), while other routines are used for
   syntaxed ones.  It handles classes as packages.  Finding a class
   returns a naming of it. *)

structure seeker :
sig
    type id_t
    type name_t
    type subject_t
    type definition_body_t
    type cooker_t

    val find_import_class :
	cooker_t -> definition_body_t -> name_t -> (subject_t * id_t) option
    val find_base_class :
	cooker_t -> definition_body_t -> name_t -> (subject_t * id_t) option
end = struct

open ast
open plain
open small0

type cooker_t = common.cooker_t

val fetch_from_instance_tree = classtree.fetch_from_instance_tree
val ensure_in_instance_tree = classtree.ensure_in_instance_tree
val assemble_package_if_fresh = classtree.assemble_package_if_fresh
val assert_stored_in_instance_tree = classtree.assert_stored_in_instance_tree

val lookup_class_in_package_root = loader.lookup_class_in_package_root
val fetch_enclosing_class = loader.fetch_enclosing_class

val find_element = finder.find_element

datatype seek_mode_t = Seek_Export | Seek_Base
type seek_context_t = {Scope : scope_t, Name : name_t, Mode : seek_mode_t}

(* Prints a trace message. *)

fun tr_seek (s : string) = if true then (print (s ^"\n")) else ()
fun tr_seek_vvv (s : string) = if false then (print (s ^"\n")) else ()

(* ================================================================ *)

(* Finds a class element for which (f e) returns SOME. *)

fun find_in_elements f (k : definition_body_t) = (
    (list_find_some f (body_elements k)))

(* Finds all elements in a class for which (f e) returns SOME. *)

fun find_all_in_elements f (k : definition_body_t) = (
    (gather_some f (body_elements k)))

(* Lists classes of direct importing candidates.  Note that a search
   for importing is not transitive.  It returns a pair (class,id),
   because an imported name can be substituted. *)

fun list_import_candidate_classes (cooker : cooker_t) kp id = (
    let
	val _ = if (step_is_at_least E2 kp) then () else raise Match

	fun candidate id e = (
	    case e of
		Import_Clause _ => raise Match
	      | Extends_Clause _ => NONE
	      | Element_Class _ => NONE
	      | Element_State _ => NONE
	      | Redefine_Class _ => NONE
	      | Redeclare_State _ => NONE
	      | Element_Enumerators _ => raise Match
	      | Element_Equations _ => NONE
	      | Element_Algorithms _ => NONE
	      | Element_External _ => NONE
	      | Element_Annotation _ => NONE
	      | Element_Import (z, tag, SOME (v0, v1), a, w) => (
		if (id <> v1) then
		    NONE
		else
		    let
			val subjx = (tag_to_subject tag)
			val x0 = surely (fetch_from_instance_tree subjx)
		    in
			SOME (x0, v0)
		    end)
	      | Element_Import (z, tag, NONE, a, w) => (
		let
		    val subjx = (tag_to_subject tag)
		    val x0 = surely (fetch_from_instance_tree subjx)
		in
		    SOME (x0, id)
		end)
	      | Element_Base _ => NONE
	      | Base_List _ => NONE
	      | Base_Classes _ => NONE)
    in
	(find_all_in_elements (candidate id) kp)
    end)

(* Finds a class definition in the class.  A Lookup ends here. *)

fun lookup_in_declared (cooker : cooker_t) ctx fullaccess kp id = (
    let
	val _ = tr_seek_vvv (";; - lookup_in_declared ("^
			     (id_to_string id) ^" in "^
			     (class_print_name kp) ^")")

	fun lookup id e = (
	    case e of
		Import_Clause _ => NONE
	      | Extends_Clause _ => NONE
	      | Element_Class (z, r, d, h_) => (
		let
		    val Defclass ((x, g), k0) = d
		in
		    if (x <> id) then
			NONE
		    else if (not (fullaccess orelse z = Public)) then
			NONE
		    else if ((#Mode ctx) = Seek_Base
			     andalso (#Replaceable r)) then
			raise (error_replaceable_base ctx)
		    else if (#Outer r) then
			raise (error_outer_package ctx)
		    else
			let
			    val subj = (subject_of_class kp)
			    val subsubj = (compose_subject subj x [])
			in
			    case k0 of
				Def_Body _ => raise Match
			      | Def_Der _ => SOME (subsubj, k0)
			      | Def_Primitive _ => raise Match
			      | Def_Outer_Alias _ => raise Match
			      | Def_Argument _ => raise Match
			      | Def_Named _ => raise Match
			      | Def_Scoped _ => SOME (subsubj, k0)
			      | Def_Refine _ => SOME (subsubj, k0)
			      | Def_Extending _ => raise Match
			      | Def_Replaced _ => SOME (subsubj, k0)
			      | Def_Displaced _ => SOME (subsubj, k0)
			      | Def_In_File => raise Match
			      | Def_Mock_Array _ => raise Match
			end
		end)
	      | Element_State _ => NONE
	      | Redefine_Class _ => NONE
	      | Redeclare_State _ => NONE
	      | Element_Enumerators _ => raise Match
	      | Element_Equations _ => NONE
	      | Element_Algorithms _ => NONE
	      | Element_External _ => NONE
	      | Element_Annotation _ => NONE
	      | Element_Import _ => NONE
	      | Element_Base _ => NONE
	      | Base_List _ => NONE
	      | Base_Classes _ => NONE)

	val _ = if (class_is_body kp) then () else raise Match
	val enclosing = (subject_of_class kp)
    in
	if (body_is_package_root kp) then
	    case (lookup_class_in_package_root id) of
		NONE => NONE
	      | SOME (subj, kx) => SOME (subj, kx)
	else
	    case (find_in_elements (lookup id) kp) of
		NONE => NONE
	      | SOME (subj, kx) => SOME (subj, kx)
    end)

fun lookup_in_main_and_bases (cooker : cooker_t) ctx kp id = (
    let
	val _ = tr_seek_vvv (";; - lookup_in_main_and_bases ("^
			     (id_to_string id) ^" in "^
			     (class_print_name kp) ^")")

	val _ = if (id <> (Id "")) then () else raise Match
	val _ = if (class_is_body kp) then () else raise Match
	val enclosing = (subject_of_class kp)
	val (openscope, fullaccess) = (false, false)
    in
	if (body_is_package_root kp) then
	    case (lookup_in_declared cooker ctx fullaccess kp id) of
		SOME (subj, kx) => SOME (enclosing, (subj, kx))
	      | NONE => raise (error_name_not_found id kp)
	else if (step_is_at_least E3 kp) then
	    let
	    in
		case (find_element true kp id) of
		    NONE => raise (error_name_not_found id kp)
		  | SOME (Naming (_, subj, _, _, (z, r, EL_Class dx, h))) => (
		    let
			val Defclass (_, k0) = dx
		    in
			SOME (enclosing, (subj, k0))
		    end)
		  | SOME (Naming (_, subj, _, _, (z, r, EL_State dx, h))) => (
		    raise (error_name_is_state id kp))
	    end
	else
	    case (lookup_in_declared cooker ctx fullaccess kp id) of
		SOME (subj, kx) => SOME (enclosing, (subj, kx))
	      | NONE => (
		case (lookup_in_bases_dummy cooker ctx kp id) of
		    SOME _ => raise Match
		  | NONE => raise (error_name_not_found id kp))
    end)

(* Warns skipping a search in bases.  Another routine is used after a
   class is syntaxed.  A SEARCH IN THE BASES NEVER HAPPENS FOR THE
   "HeatingSystem" EXAMPLE. *)

and lookup_in_bases_dummy (cooker : cooker_t) ctx kp id = (
    if (step_is_at_least E3 kp) then
	raise Match
    else
	let
	    val _ = (warn_skip_lookup_in_bases ())
	in
	    NONE
	end)

(* Looks for a composite name for an element.  It continues a lookup
   for the remaining parts, after starting a lookup for the initial
   part.  It tries to fetch a class first, to check existence of an
   already syntaxed one.  The lookup is for both public/protected
   accesses, because it is for bases. *)

fun lookup_composite_loop (cooker : cooker_t) ctx enclosing0 (subj0, k0) nn = (
    case nn of
	[] => (
	let
	    val (_, (id, _)) = (subject_prefix subj0)
	in
	    SOME (enclosing0, id)
	end)
      | (p :: tt) => (
	let
	    val _ = if (p <> "") then () else raise Match
	    val k1 = (getOpt ((fetch_from_instance_tree subj0), k0))
	    val k2 = (assemble_package_if_fresh cooker E2 (subj0, k1))
	in
	    case (lookup_in_main_and_bases cooker ctx k2 (Id p)) of
		NONE => raise error_already_issued
	      | SOME (enclosing1, (subj1, kx)) => (
		(lookup_composite_loop cooker ctx enclosing1 (subj1, kx) tt))
	end))

(* Looks for a class of an import-clause.  It takes a class at
   step=E1.  It returns a pair of a defining class and a name.  It
   looks for the first part of a name, and then continues.  A context
   is the class a lookup starts, which is used for diagnostics
   messages. *)

fun find_import_class (cooker : cooker_t) kp name = (
    let
	val _ = tr_seek_vvv (";; find_import_class ("^
			     (name_to_string name)
			     ^" in "^ (body_name_at_step kp) ^")")

	fun drop_explicit_dot (Name nn) = (
	    case nn of
		[] => raise Match
	      | ("" :: tt) => (Name tt)
	      | _ => (Name nn))

	val _ = if (class_is_body kp) then () else raise Match
	val _ = if (step_is_at_least E0 kp) then () else raise Match
	val (subj, tag) = (naming_of_class kp)
	val scope = (subj, tag)
	val ctx = {Scope=scope, Name=name, Mode=Seek_Export}
	val (Name nn) = (drop_explicit_dot name)
	val _ = if (not (null nn)) then () else raise Match
	val rootsubj = the_package_root_subject
	val root = the_package_root
	val enclosing = rootsubj
    in
	(lookup_composite_loop cooker ctx enclosing (rootsubj, root) nn)
    end)

(* Looks for a class name in the imported names. *)

fun lookup_in_imported (cooker : cooker_t) ctx kp id = (
    let
	val _ = tr_seek_vvv (";; - lookup_in_imported ("^
			     (id_to_string id) ^" in "^
			     (body_name_at_step kp) ^")")
	val _ = if (class_is_body kp) then () else raise Match

	val candidates = (list_import_candidate_classes cooker kp id)
    in
	(list_find_some
	     (fn (kx, v) => (lookup_in_main_and_bases cooker ctx kx v))
	     candidates)
    end)

(* Looks for the first part of a name of an extends-clause. *)

fun lookup_for_bases (cooker : cooker_t) ctx kp id = (
    let
	val _ = tr_seek_vvv (";; - lookup_for_bases ("^
			     (id_to_string id) ^" in "^
			     (class_print_name kp) ^")")

	val _ = if (class_is_body kp) then () else raise Match
	val _ = if (id <> (Id "")) then () else raise Match
	val _ = if (step_is_at_least E2 kp) then () else raise Match

	val enclosing = (subject_of_class kp)
	val openscope = true
	val fullaccess = false
    in
	case (lookup_in_declared cooker ctx fullaccess kp id) of
	    SOME (subjx, kx) => SOME (enclosing, (subjx, kx))
	  | NONE => (
	    if (body_is_package_root kp) then
		raise (error_name_not_found id kp)
	    else if (not openscope) then
		raise (error_name_not_found id kp)
	    else
		case (lookup_in_imported cooker ctx kp id) of
		    SOME (enclosing, (subjx, kx)) => SOME (enclosing, (subjx, kx))
		  | NONE =>
		    let
			val _ = if (openscope) then () else raise Match
			val x0 = (fetch_enclosing_class kp)

			(*AHO*)
			(*val pkg = (tag_of_enclosing_class kp)*)
			(*val subj = (tag_to_subject pkg)*)
			(*val x1 = (assemble_package_if_fresh cooker E2 (subj, x0)*)

			val _ = (assert_cooked_at_least E2 x0)
			val x1 = x0
		    in
			(lookup_for_bases cooker ctx x1 id)
		    end)
    end)

(* Looks for a class of an extends-clause.  It returns a pair of an
   enclosing class and a name.  It takes a class at step=E2.  It looks
   for the first part of a name of an extends-clause, then continues.
   It calls a cooker to resolve some names in the class definition. *)

fun find_base_class (cooker : cooker_t) kp name = (
    let
	val _ = tr_seek_vvv (";; find_base_class ("^ (name_to_string name)
			     ^" in "^ (body_name_at_step kp) ^")")

	val _ = if (class_is_body kp) then () else raise Match
	val _ = if (step_is_at_least E2 kp) then () else raise Match

	val scope = (naming_of_class kp)
	val ctx = {Scope=scope, Name=name, Mode=Seek_Base}
    in
	case name of
	    Name [] => raise Match
	  | Name ("" :: tt) => (
	    let
		val _ = if (not (null tt)) then () else raise Match
		val root = (the_package_root_subject, the_package_root)
		val enclosing = the_package_root_subject
	    in
		(lookup_composite_loop cooker ctx enclosing root tt)
	    end)
	  | Name (p :: tt) => (
	    case (lookup_for_bases cooker ctx kp (Id p)) of
		NONE => raise error_already_issued
	      | SOME (enclosing, (subj, kx)) => (
		(lookup_composite_loop cooker ctx enclosing (subj, kx) tt)))
    end)

end
