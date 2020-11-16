(* syntaxer.sml -*-Coding: us-ascii-unix;-*- *)
(* Copyright (C) 2018-2020 RIKEN R-CCS *)

(* CLASS BUILDER.  Syntaxing resolves base classes and applies
   modifiers. *)

structure cooker :
sig
    type subject_t
    type cook_step_t
    type definition_body_t
    type modifier_t

    val assemble_package :
	cook_step_t -> (subject_t * definition_body_t) -> definition_body_t
    val assemble_instance :
	(subject_t * definition_body_t) -> definition_body_t
end = struct

open plain
open ast
open small0

val instance_tree = classtree.instance_tree
val fetch_from_loaded_classes = classtree.fetch_from_loaded_classes
val fetch_from_instance_tree = classtree.fetch_from_instance_tree
val store_to_instance_tree = classtree.store_to_instance_tree
val fetch_class_by_scope = classtree.fetch_class_by_scope
val list_base_names = classtree.list_base_names
val extract_base_classes = classtree.extract_base_classes
val extract_base_elements = classtree.extract_base_elements
val ensure_in_instance_tree = classtree.ensure_in_instance_tree
val assert_stored_in_instance_tree = classtree.assert_stored_in_instance_tree
val assert_package_constraints = classtree.assert_package_constraints
val assert_enclosings_are_cooked = classtree.assert_enclosings_are_cooked

val simplify_simple_type = simpletype.simplify_simple_type
val insert_attributes_to_enumeration = simpletype.insert_attributes_to_enumeration
val unify_value_and_initializer = simpletype.unify_value_and_initializer
val register_enumerators_for_enumeration = simpletype.register_enumerators_for_enumeration

val fetch_displaced_class = loader.fetch_displaced_class

val find_class = finder.find_class
val list_elements = finder.list_elements

val find_import_class = seeker.find_import_class
val find_base_class = seeker.find_base_class

val associate_modifiers = refiner.associate_modifiers
val rectify_modified_class = refiner.rectify_modified_class
val merge_modifiers = refiner.merge_modifiers
val merge_annotations = refiner.merge_annotations
val merge_type_prefixes = refiner.merge_type_prefixes
val merge_component_prefixes = refiner.merge_component_prefixes
val make_modified_class = refiner.make_modified_class

(* Prints a trace message. *)

fun tr_cook (s : string) = if true then (print (s ^"\n")) else ()
fun tr_cook_vvv (s : string) = if false then (print (s ^"\n")) else ()

(* ================================================================ *)

(*AHO*)

fun reset_visibility z k0 = k0

(*AHO*)

fun make_base_list subj bases = (
    (map (fn (tag, k) => (subj, tag)) bases))

(* Fetches a definition from a defining class.  It shortcuts a search,
   when fetching a lexically visible class.  It can shortcut when a
   class is in the lexical hierarchy because it cannot be modified.
   Actually, this shortcutting is sometimes necessary to avoid a
   potential cycle. *)

fun fetch_element_class cooker (enclosing, id) : definition_body_t = (
    let
	val subj = (compose_subject enclosing id [])
	val tagopt = (subject_to_tag subj)
    in
	case (Option.join (Option.map fetch_from_loaded_classes tagopt)) of
	    SOME d => (
	    let
		val Defclass (_, k0) = d
		val k2 = (assign_enclosing k0 enclosing)
	    in
		k2
	    end)
	  | NONE => (
	    let
		val kp = surely (fetch_from_instance_tree enclosing)
		val _ = if (step_is_at_least E3 kp) then () else raise Match
		(*val (id, pkg) = (tag_prefix tag)*)
		val bindings = (list_elements cooker false kp)
	    in
		case (find_in_bindings id bindings) of
		    NONE => raise (error_name_not_found id kp)
		  | SOME (Binding (_, subsubj, _, (z, r, EL_Class d, h))) => (
		    let
			val Defclass (_, k0) = d
		    in
			k0
		    end)
		  | SOME (Binding (_, _, _, (z, r, EL_State d, h))) => (
		    raise (error_name_is_state id kp))
	    end)
    end)

fun store_to_instance_tree_if c subj k = (
    if c then
	ignore (store_to_instance_tree subj k)
    else
	())

fun test_expression_is_scoped x0 = (
    case x0 of
	NIL => true
      | Colon => true
      | Otherwise => true
      | Scoped _ => true
      | Pseudo_Split (x1, _) => (test_expression_is_scoped x1)
      | Component_Ref (x1, v) => (test_expression_is_scoped x1)
      | _ => false)

(* Checks an item is scoped.  The check is only at the top-level. *)

fun assert_modifiers_are_scoped mm = (
    let
	fun test_modifier_is_scoped m = (
	    case m of
		Mod_Redefine (r_, d, h) => (
		let
		    val c0 = (test_rename_is_scoped d)
		    val c1 = (Option.map test_constraint_is_scoped h)
		in
		    (c0 andalso (c1 = NONE orelse (valOf c1)))
		end)
	      | Mod_Elemental_Redefine (z_, r_, d, h) => (
		let
		    val c0 = (test_rename_is_scoped d)
		    val c1 = (Option.map test_constraint_is_scoped h)
		in
		    (c0 andalso (c1 = NONE orelse (valOf c1)))
		end)
	      | Mod_Redeclare (r_, d, h) => (
		let
		    val c0 = (test_redeclare_is_scoped d)
		    val c1 = (Option.map test_constraint_is_scoped h)
		in
		    (c0 andalso (c1 = NONE orelse (valOf c1)))
		end)
	      | Mod_Elemental_Redeclare (z_, r_, d, h) => (
		let
		    val c0 = (test_redeclare_is_scoped d)
		    val c1 = (Option.map test_constraint_is_scoped h)
		in
		    (c0 andalso (c1 = NONE orelse (valOf c1)))
		end)
	      | Mod_Entry (ef, v, mmx, w) => (
		(List.all test_modifier_is_scoped mmx))
	      | Mod_Value e => (
		(test_expression_is_scoped e)))

	and test_rename_is_scoped (Defclass ((v, g), k)) = (
	    (test_body_is_scoped k))

	and test_body_is_scoped k = (
	    case k of
		Def_Body _ => raise Match
	      | Def_Der _ => raise Match
	      | Def_Primitive _ => raise Match
	      | Def_Name _ => raise Match
	      | Def_Scoped _ => true
	      | Def_Refine (kx, v, ts, q, (ssx, mmx), aa, ww) => (
		let
		    val c0 = (List.all test_expression_is_scoped ssx)
		    val c1 = (List.all test_modifier_is_scoped mmx)
		    val c2 = (test_body_is_scoped kx)
		in
		    (c0 andalso c1 andalso c2)
		end)
	      | Def_Extending _ => raise Match
	      | Def_Replaced _ => raise Match
	      | Def_Displaced _ => raise Match
	      | Def_In_File => raise Match
	      | Def_Mock_Array _ => raise Match)

	and test_redeclare_is_scoped (Defvar (v, q, d, c, a, w)) = (
	    let
		val _ = if (c = NONE) then ()
			else raise error_condition_in_modifiers
		val c0 = (test_body_is_scoped d)
	    in
		c0
	    end)

	and test_constraint_is_scoped (kx, mmx, a, w) = (
	    let
		val c0 = (test_body_is_scoped kx)
		val c1 = (List.all test_modifier_is_scoped mmx)
	    in
		(c0 andalso c1)
	    end)
    in
	if (List.all test_modifier_is_scoped mm) then () else raise Match
    end)

fun assert_expressions_are_scoped ee = (
    let
    in
	if (List.all test_expression_is_scoped ee) then () else raise Match
    end)

fun assert_no_base_list ee = (
    let
	fun check e = (
	    case e of
		Base_List _ => raise Match
	      | Base_Classes _ => raise Match
	      | _ => ())
    in
	(app check ee)
    end)

(* Test if a modified class is (essentially) different. *)

fun modifiers_have_redeclarations mm = (
    (List.exists test_modifier_is_redeclaration mm))

and test_modifier_is_redeclaration m = (
    case m of
	Mod_Redefine _ => true
      | Mod_Elemental_Redefine _ => true
      | Mod_Redeclare _ => true
      | Mod_Elemental_Redeclare _ => true
      | Mod_Entry (ef, v, mmx, ww) => (modifiers_have_redeclarations mmx)
      | Mod_Value e => false)

(* ================================================================ *)

(* Records a defining class in a class body element. *)

fun record_defining_class (subj, k0) = (
    let
	fun record_defining_class_in_element subj e = (
	    case e of
		Import_Clause _ => e
	      | Extends_Clause _ => e
	      | Element_Class (z, r, d0, h) => (
		let
		    val Defclass ((id, g), k0) = d0
		    val subsubj = (compose_subject subj id [])
		    val k1 = (record_defining_class_in_class (subsubj, k0))
		    val d1 = Defclass ((id, g), k1)
		in
		    Element_Class (z, r, d1, h)
		end)
	      | Element_State _ => e
	      | Redefine_Class (z, r, d0, h) => (
		let
		    val Defclass ((id, g), k0) = d0
		    val subsubj = (compose_subject subj id [])
		    val k1 = (record_defining_class_in_class (subsubj, k0))
		    val d1 = Defclass ((id, g), k1)
		in
		    Redefine_Class (z, r, d1, h)
		end)
	      | Redeclare_State _ => e
	      | Element_Enumerators _ => e
	      | Element_Equations _ => e
	      | Element_Algorithms _ => e
	      | Element_External _ => e
	      | Element_Annotation _ => e
	      | Element_Import _ => raise Match
	      | Element_Base _ => raise Match
	      | Base_List _ => e
	      | Base_Classes _ => e)

	and record_defining_class_in_class (subsubj, k0) = (
	    case k0 of
		Def_Body _ => raise Match
	      | Def_Der _ => k0
	      | Def_Primitive _ => raise Match
	      | Def_Name _ => k0
	      | Def_Scoped _ => k0
	      | Def_Refine (x0, v, ts, q, (ss, mm), aa, ww) => (
		let
		    val x1 = (record_defining_class_in_class (subsubj, x0))
		in
		    Def_Refine (x1, v, ts, q, (ss, mm), aa, ww)
		end)
	      | Def_Extending (true, _, _) => raise Match
	      | Def_Extending (false, (kb, mm), x0) => (
		let
		    val x1 = (record_defining_class_in_class (subsubj, x0))
		in
		    Def_Extending (false, (kb, mm), x1)
		end)
	      | Def_Replaced (x0, ko) => (
		let
		    val x1 = (record_defining_class_in_class (subsubj, x0))
		in
		    Def_Replaced (x1, ko)
		end)
	      | Def_Displaced (tag, enc_) => (
		let
		    val _ = if (enc_ = bad_subject) then () else raise Match
		    val (enclosing, _) = (subject_prefix subsubj)
		in
		    (assign_enclosing k0 enclosing)
		end)
	      | Def_In_File => raise Match
	      | Def_Mock_Array _ => raise Match)

	val ee0 = (body_elements k0)
	val ee1 = (map (record_defining_class_in_element subj) ee0)
	val k1 = (replace_body_elements k0 ee1)
    in
	k1
    end)

fun closure_expression (scope : scope_t) x = (
    case x of
	NIL => x
      | Colon => x
      | Otherwise => x
      | Scoped _ => x
      | _ => (
	Scoped (x, scope)))

fun closure_modifier (scope : scope_t) m = (
    case m of
	Mod_Redefine (r, d0, h0) => (
	let
	    val d1 = (closure_definition scope d0)
	    val h1 = ((Option.map (closure_constraint scope)) h0)
	in
	    Mod_Redefine (r, d1, h1)
	end)
      | Mod_Elemental_Redefine (z, r, d0, h0) => (
	let
	    val d1 = (closure_definition scope d0)
	    val h1 = ((Option.map (closure_constraint scope)) h0)
	in
	    Mod_Elemental_Redefine (z, r, d1, h1)
	end)
      | Mod_Redeclare (r, d0, h0) => (
	let
	    val d1 = (closure_declaration true scope d0)
	    val h1 = ((Option.map (closure_constraint scope)) h0)
	in
	    Mod_Redeclare (r, d1, h1)
	end)
      | Mod_Elemental_Redeclare (z, r, d0, h0) => (
	let
	    val d1 = (closure_declaration false scope d0)
	    val h1 = ((Option.map (closure_constraint scope)) h0)
	in
	    Mod_Elemental_Redeclare (z, r, d1, h1)
	end)
      | Mod_Entry (ef, v, mm, w) => (
	Mod_Entry (ef, v, (map (closure_modifier scope) mm), w))
      | Mod_Value x => (
	Mod_Value (closure_expression scope x)))

and closure_definition (scope : scope_t) (kp as Defclass ((v, g), k0)) = (
    let
	val k1 = (closure_class scope k0)
    in
	Defclass ((v, g), k1)
    end)

and closure_declaration modifier (scope : scope_t) (Defvar (v, q, k0, c0, a0, w)) = (
    let
	val _ = if (not modifier orelse c0 = NONE)
		then () else raise error_condition_in_modifiers
	val k1 = (closure_class scope k0)
	val c1 = (Option.map (closure_expression scope) c0)
	val a1 = (closure_annotation scope a0)
    in
	Defvar (v, q, k1, c1, a1, w)
    end)

and closure_constraint (scope : scope_t) (k0, mm0, a0, w) = (
    let
	val k1 = (closure_class scope k0)
	val mm1 = (map (closure_modifier scope) mm0)
	val a1 = (closure_annotation scope a0)
    in
	(k1, mm1, a1, w)
    end)

(* Attaches a scope to a class definition.  It also assigns an
   enclosing class to extends-redeclarations.  IT SKIPS ATTACHING
   SCOPES TO EXTENDS-REDECLARATIONS BECAUSE THEY HAVE SPECIAL SCOPING
   RULES. *)

and closure_class (scope : scope_t) k0 = (
    case k0 of
	Def_Body (mk, j, cs, nm, ee, aa, ww) => (
	let
	    val _ = if (j = bad_subject) then () else raise Match
	    val (subj, tag) = scope
	    (*val k1 = (assign_enclosing k0 subj)*)
	    val k1 = k0
	in
	    k1
	end)
      | Def_Der _ => k0
      | Def_Primitive _ => raise Match
      | Def_Name n => Def_Scoped (n, scope)
      | Def_Scoped _ => raise Match
      | Def_Refine (x0, v, ts, q, (ss0, mm0), aa, ww) => (
	let
	    val x1 = (closure_class scope x0)
	    val ss1 = (map (closure_expression scope) ss0)
	    val mm1 = (map (closure_modifier scope) mm0)
	    val k1 = Def_Refine (x1, v, ts, q, (ss1, mm1), aa, ww)
	in
	    k1
	end)
      | Def_Extending (true, (n0, mm0), x0) => raise Match
      | Def_Extending (false, (n0, mm0), x0) => (
	let
	    val n1 = (closure_class scope n0)
	    (*val m1 = (map (closure_modifier NONE) m0)*)
	    val x1 = (closure_class scope x0)
	in
	    Def_Extending (false, (n1, mm0), x1)
	end)
      | Def_Replaced _ => raise Match
      | Def_Displaced _ => (
	let
	    val (subj, tag) = scope
	    (*val k1 = (assign_enclosing k0 subj)*)
	    val k1 = k0
	in
	    k1
	end)
      | Def_In_File => raise Match
      | Def_Mock_Array _ => raise Match)

and closure_annotation (scope : scope_t) (Annotation m) = (
    Annotation (map (closure_modifier scope) m))

(* Attaches an explicit environment (a scope) to expressions and class
   names.  It permits to move modifiers and subscripts inside another
   class.  It sets the step=E1.  It does not process the equations nor
   the statements.  It does not process the nested class definitions,
   neither.  The scope is an associated package/instance of the class,
   and indicates an enclosing class for modifiers and subscripts *)

fun attach_scope (subj, k0) = (
    let
	val scope = (subj, (tag_of_body k0))

	fun attach e = (
	    case e of
		Import_Clause _ => e
	      | Extends_Clause (z, (n, mm0), a) => (
		let
		    val mm1 = (map (closure_modifier scope) mm0)
		in
		    Extends_Clause (z, (n, mm1), a)
		end)
	      | Element_Class (z, r, d0, h) => (
		let
		    val d1 = (closure_definition scope d0)
		in
		    Element_Class (z, r, d1, h)
		end)
	      | Element_State (z, r, d0, h) => (
		let
		    val d1 = (closure_declaration false scope d0)
		in
		    Element_State (z, r, d1, h)
		end)
	      | Redefine_Class (z, r, d0, h) => (
		let
		    val d1 = (closure_definition scope d0)
		in
		    Redefine_Class (z, r, d1, h)
		end)
	      | Redeclare_State (z, r, d0, h) => (
		let
		    val d1 = (closure_declaration false scope d0)
		in
		    Redeclare_State (z, r, d1, h)
		end)
	      | Element_Enumerators _ => e
	      | Element_Equations _ => e
	      | Element_Algorithms _ => e
	      | Element_External _ => e
	      | Element_Annotation _ => e
	      | Element_Import _ => raise Match
	      | Element_Base _ => raise Match
	      | Base_List _ => e
	      | Base_Classes _ => e)

	val _ = tr_cook_vvv (";; attach_scope ("^
			     (subject_tag_to_string scope) ^")")
	val ee0 = (body_elements k0)
	val ee1 = (map attach ee0)
	val k1 = (replace_body_elements k0 ee1)
    in
	k1
    end)

fun prepare_for_modification main pkg (subj, k0) = (
    let
	val scope = (subj, (tag_of_body k0))

	fun marker (m, main) = (
	    if (m = ENUM) then
		ENUM
	    else if (main) then
		MAIN
	    else
		BASE)

	val _ = tr_cook_vvv (";; prepare_for_modification ("^
			     (subject_tag_to_string scope) ^")")
	val _ = if ((cook_step k0) = E0) then () else raise Match
    in
	case k0 of
	    Def_Body ((u, f_, b_), j_, cs, (c, n, x), ee, aa, ww) => (
	    let
		val _ = if (f_ = PKG) then () else raise Match
		val _ = if (b_ = ENUM orelse b_ = MAIN) then ()
			else raise Match
		val _ = if (j_ = bad_subject) then () else raise Match
		val _ = if ((f_ = PKG) orelse (x <> bad_subject)) then ()
			else raise Match
		val mark = (marker (b_, main))
		val k1 = Def_Body ((u, pkg, mark), subj, cs,
				   (c, n, x), ee, aa, ww)
		val k2 = (attach_scope (subj, k1))
		val k3 = (record_defining_class (subj, k2))
		val k4 = (set_cook_step E1 k3)
	    in
		k4
	    end)
	  | Def_Der _ => raise Match
	  | Def_Primitive _ => raise Match
	  | Def_Name _ => raise Match
	  | Def_Scoped _ => raise Match
	  | Def_Refine _ => raise Match
	  | Def_Extending _ => raise Match
	  | Def_Replaced _ => raise Match
	  | Def_Displaced _ => raise Match
	  | Def_In_File => raise Match
	  | Def_Mock_Array _ => raise Match
    end)

(* ================================================================ *)

(* A defined name of a class.  Its state transitions as Vacant =>
   Candidate => Decisive. *)

datatype name_candidate_t
    = Decisive_Name of subject_t
    | Candidate_Name of subject_t
    | Vacant_Name

fun choose_candidate_name n0 n1 = (
    case (n0, n1) of
	(Decisive_Name subj, _) => n0
      | (_, NONE) => n0
      | (_, SOME subj) => Candidate_Name subj)

fun coerce_decisive_name n = (
    case n of
	Decisive_Name subj => n
      | Candidate_Name subj => Decisive_Name subj
      | Vacant_Name => Vacant_Name)

fun take_decisive_name n = (
    case n of
	Decisive_Name subj => subj
      | Candidate_Name subj => subj
      | Vacant_Name => raise Match)

fun take_optional_name n = (
    case n of
	Decisive_Name subj => SOME subj
      | Candidate_Name subj => SOME subj
      | Vacant_Name => NONE)

(* Unifies class names.  It replaces a package part of a name by its
   identity name. *)

fun identify_class_name subj = (
    let
	val (supsubj, (id, ss)) = (subject_prefix subj)
	val x0 = surely (fetch_from_instance_tree supsubj)
	val identity = (identity_name_of_body x0)
    in
	(compose_subject identity id ss)
    end)

(* Processes a class as a package (non-instance).  It is frequently
   used as a callback "cooker" during lookups, and it is called via
   assemble_package_if_fresh.  It is called with wantedstep with E0
   for a class searched in for an imported class, E2 for a class
   searched in for a base class, and E3 for usual processing.  It
   ensures a class is stored in the instance_tree. *)

fun assemble_package wantedstep (subj, k0) = (
    let
	val _ = if ((step_compare wantedstep (op >=) E1)
		    andalso (step_compare wantedstep (op <=) E3)) then ()
		else raise Match
	val _ = if ((not (class_is_body k0)) orelse (class_is_main k0))
		then () else raise Match

	val k2 = (getOpt ((fetch_from_instance_tree subj), k0))
    in
	if (class_is_root_body k2) then
	    k2
	else if (body_is_unmodifiable k2) then
	    (ensure_in_instance_tree (subj, k2))
	else if (step_is_at_least wantedstep k2) then
	    let
		val _ = (assert_stored_in_instance_tree (subj, k2))
	    in
		k2
	    end
	else
	    case (cook_step k2) of
		E0 => (
		let
		    (*val (enclosing, _) = (subject_prefix subj)*)
		    (*val k3 = (assign_enclosing k2 enclosing)*)
		    val k4 = (cook_class_binary PKG (subj, k2))
		in
		    k4
		end)
	      | E1 => (
		let
		    val _ = (warn_cycle_in_lookup ())
		    val _ = (assert_stored_in_instance_tree (subj, k2))
		in
		    k2
		end)
	      | E2 => (
		let
		    val _ = (warn_cycle_in_lookup ())
		    val _ = (assert_stored_in_instance_tree (subj, k2))
		in
		    k2
		end)
	      | E3 => raise Match
	      | E4 => raise Match
	      | E5 => raise Match
    end)

(* Processes a class as an instance.  A class is wrapped by a
   Def_Refine to pass component-prefixes to the instance. *)

and assemble_instance (subj, k0) = (
    let
	val _ = if ((cook_step k0) = E0) then () else raise Match
    in
	(cook_class_binary VAR (subj, k0))
    end)

(* Processes a class for either a package or an instance.  A subject
   refers to a package or a variable. *)

and cook_class_binary pkg (subj, k0) = (
    let
	val _ = tr_cook_vvv (";; cook_class_binary : ("^
			     (subject_body_to_string (subj, k0))
			     ^")...")

	val siblings = []
	val k1 = (cook_class_refining true pkg (subj, k0) siblings)
	val k2 = (cook_class_body true pkg (subj, k1) siblings)

	val _ = tr_cook_vvv (";; cook_class_binary : ("^
			     (subject_body_to_string (subj, k0))
			     ^")... done")
    in
	k2
    end)

and cook_class_refining main pkg (subj, k0) siblings = (
    let
	val noname = Vacant_Name
	val noprefixes = (Implied, no_class_prefixes, no_component_prefixes)
	val aa = Annotation []
	val k1 = (collect_refining
		      main pkg (subj, k0)
		      (noname, noprefixes, [], aa) siblings)
    in
	k1
    end)

(* Gathers modifiers of the class until a definition body is found.
   It is called with empty modifiers at the start.  Note the ordering
   of merging modifiers, because the passed modifiers are more recent
   and appended to the tail. *)

and collect_refining main pkg (subj, k0) (name1, (t1, p1, q1), mm1, aa1) siblings = (
    case k0 of
	Def_Body (mk, j, (t0, p0, q0), nm0, ee, aa0, ww0) => (
	let
	    val _ = tr_cook_vvv (";; collect_refining"^
				 (if main then ":main" else ":base") ^" ("^
				 (subject_body_to_string (subj, k0)) ^")")

	    val _ = if (not (class_is_root_body k0)) then () else raise Match
	    val _ = if (not (body_is_unmodifiable k0)) then () else raise Match

	    val ctx = k0
	    val (tx, px) = (merge_type_prefixes (t0, p0) (t1, p1))
	    val qx = (merge_component_prefixes q0 q1)
	    val aax = (merge_annotations ctx aa0 aa1)
	    val (tag, name_, enclosing) = nm0
	    val _ = if (name_ = bad_subject) then () else raise Match
	    val (id, g) = (tag_prefix tag)
	    val name0 = (compose_subject enclosing id [])
	    val namec = (choose_candidate_name name1 (SOME name0))
	    val namex = (take_decisive_name namec)
	    val identity = (identify_class_name namex)
	    val nmx = (tag, identity, enclosing)
	    val k1 = Def_Body (mk, j, (tx, px, qx), nmx, ee, aax, ww0)
	    val k3 = (make_modified_class k1 mm1 (Annotation []) (Comment []))
	in
	    k3
	end)
      | Def_Der _ => (
	let
	    val _ = if (null mm1) then ()
		    else if (modifier_is_value mm1) then raise Match
		    else raise (error_modifiers_to_der mm1)
	in
	    (ensure_in_instance_tree (subj, k0))
	end)
      | Def_Primitive _ => raise Match
      | Def_Name _ => raise Match
      | Def_Scoped (name, scope) => (
	let
	    val cooker = assemble_package
	    val (subj1, k1) = (fetch_class_by_scope scope)
	    val _ = (assert_match_subject subj1 k1)
	in
	    case (find_class cooker (subj1, k1) name) of
		NONE => raise (error_class_not_found name k1)
	      | SOME (enclosing_, x0) => (
		let
		    val _ = tr_cook_vvv (";; collect_refining find ("^
					 (class_print_name x0)
					 ^") in ("^
					 (subject_body_to_string (subj1, k1))
					 ^")")
		in
		    (collect_refining
			 main pkg (subj, x0)
			 (name1, (t1, p1, q1), mm1, aa1) siblings)
		end)
	end)
      | Def_Refine (k1, name0, ts0, q0, (ss0, mm0), aa0, ww0) => (
	let
	    val _ = tr_cook_vvv (";; collect_refining (refine "^
				(class_print_name k0) ^")")
	    val _ = (assert_modifiers_are_scoped mm0)
	    val _ = (assert_expressions_are_scoped ss0)
	    val ctx = k0
	    val mmx = (merge_modifiers ctx mm0 mm1)
	    val aax = (merge_annotations ctx aa0 aa1)
	    val (tx, px) = (merge_type_prefixes ts0 (t1, p1))
	    val qx = (merge_component_prefixes q0 q1)
	    val namec = (choose_candidate_name name1 name0)
	    val namex = if (modifiers_have_redeclarations mm0)
			then (coerce_decisive_name namec) else namec
	    val nameopt = (take_optional_name namex)
	in
	    if (not (null ss0)) then
		Def_Refine (k1, nameopt, (tx, px), qx, (ss0, mmx), aax, ww0)
	    else
		(collect_refining
		     main pkg (subj, k1)
		     (namex, (tx, px, qx), mmx, aax) siblings)
	end)
      | Def_Extending (true, (x0, mm0), body0) => (
	let
	    val body1 = (fetch_displaced_class E0 body0)
	    val scope = (subj, (tag_of_body body1))
	    val mm0x = (map (closure_modifier scope) mm0)
	    val x1 = (fetch_displaced_class E0 x0)
	    val x2 = (make_modified_class x1 mm0x (Annotation []) (Comment []))
	    val x3 = (cook_class_refining false pkg (subj, x2) siblings)
	    val x4 = (cook_class_body false pkg (subj, x3) siblings)
	    val _ = (enclosing_of_body body1)
	    val k3 = (insert_base_of_extends_redeclaration subj x4 body1)
	in
	    (collect_refining
		 main pkg (subj, k3)
		 (name1, (t1, p1, q1), mm1, aa1) siblings)
	end)
      | Def_Extending (false, _, _) => raise Match
      | Def_Replaced (x0, _) => (
	(collect_refining
	     main pkg (subj, x0)
	     (name1, (t1, p1, q1), mm1, aa1) siblings))
      | Def_Displaced _ => (
	let
	    val x1 = (fetch_displaced_class E0 k0)
	in
	    (collect_refining
		 main pkg (subj, x1)
		 (name1, (t1, p1, q1), mm1, aa1) siblings)
	end)
      | Def_In_File => raise Match
      | Def_Mock_Array _ => raise Match)

(* Calls cook_class_with_modifiers when a class is scalar, or returns
   a class as it is.  It only accepts a Def_Refine form that is
   created by make_modified_class. *)

and cook_class_body main pkg (subj, k0) siblings = (
    case k0 of
	Def_Body _ => (
	let
	    val noclass = (Implied, no_class_prefixes)
	    val q = no_component_prefixes
	    val aa = Annotation []
	in
	    (cook_class_with_modifiers
		 main pkg (subj, k0) [] aa siblings)
	end)
      | Def_Der _ => (
	let
	    val noclass = (Implied, no_class_prefixes)
	    val q = no_component_prefixes
	    val aa = Annotation []
	in
	    (cook_class_with_modifiers
		 main pkg (subj, k0) [] aa siblings)
	end)
      | Def_Primitive _ => raise Match
      | Def_Name _ => raise Match
      | Def_Scoped _ => raise Match
      | Def_Refine (k1, v, ts, q, (ss, mm), aa, ww) => (
	if (not (null ss)) then
	    k0
	else
	    let
		val _ = if (ts = copy_type) then () else raise Match
		val _ = if (q = no_component_prefixes) then () else raise Match
		val _ = if (null ss) then () else raise Match
	    in
		(cook_class_with_modifiers
		     main pkg (subj, k1) mm aa siblings)
	    end)
      | Def_Extending _ => raise Match
      | Def_Replaced _ => raise Match
      | Def_Displaced _ => raise Match
      | Def_In_File => raise Match
      | Def_Mock_Array _ => raise Match)

(* Transforms a class at the loaded-state (step=E0) be ready for
   finding class/variable names (step=E3), by applying modifiers after
   resolving the classes of importing and extending (it accepts a
   class at step=E3 or higher).  The class is given a name by a
   subject.  A class is processed as a main/base specified by
   main=true/false, and as a package/instance specified by pkg=PKG/VAR
   (there are only small differences in processing).  Note that an
   array dimension is empty, because it is processed at instantiation
   for instances, or arrays are illegal for packages.  (*AHO*)
   (Subscripts will be removed from here).  It reveals an intemediate
   state (step=E1,E2) of a package so that name resolution started by
   other classes can look in this class.  A list siblings0 holds a
   chain of an extends-relation to check a cycle in the base class
   hierarchy.  The passed modifiers are scoped in the environment. *)

and cook_class_with_modifiers main pkg (subj, k0) mm a siblings0 = (
    let
	val _ = if (class_is_body k0) then () else raise Match
	val _ = (assert_modifiers_are_scoped mm)
	val _ = (enclosing_of_body k0)

	val (t, p) = copy_type
	val q = no_component_prefixes

	val tag0 = (tag_of_body k0)
	val siblings1 = (tag0 :: siblings0)
	val _ = if (tag0 <> bad_tag) then () else raise Match
	val _ = if (not (List.exists (fn i => (i = tag0)) siblings0)) then ()
		else raise (error_cycle_in_extends_relation siblings1)
	val _ = if ((cook_step k0) <> E2) then ()
		else raise (error_cycle_in_lookup_dependency siblings1)
	val _ = if (step_is_less E3 k0) then () else raise Match

	val packagemain = (main andalso (pkg = PKG))

	val _ = tr_cook_vvv (";; cook_body:"^
			     (if main then "main" else "base")
			     ^" ("^
			     (subject_body_to_string (subj, k0))
			     ^" modifiers="^ (modifier_list_to_string mm)
			     ^")...")

	val k1 = (prepare_for_modification main pkg (subj, k0))
	val _ = (store_to_instance_tree_if packagemain subj k1)
	val k2 = (cook_imports k1)
	val k3 = (insert_attributes_to_enumeration k2)
	val _ = (store_to_instance_tree_if packagemain subj k3)
	val k4 = (gather_bases main pkg k3 siblings1)
	val k5 = (associate_modifiers k4 mm)
	val k8 = (rectify_modified_class (k5, q) (t, p) a)
	val k9 = (simplify_simple_type k8)
	val _ = (store_to_instance_tree_if packagemain subj k9)
	val _ = (register_enumerators_for_enumeration k9)

	(*AHOAHO*)
	(*
	val _ = if (not (kind_is_record k0)) then ()
		else raise Match
	*)

	val _ = tr_cook_vvv (";; cook_body:"^
			     (if main then "main" else "base")
			     ^" ("^
			     (subject_body_to_string (subj, k0))
			     ^")... done")
	val _ = tr_cook_vvv (";; ... bases("^ (class_print_name k9) ^")={"^
			     ((String.concatWith " ")
				  (map tag_to_string (list_base_names k9)))
			     ^"}")
    in
	k9
    end)

(* Assembles classes of import-clauses.  It takes a class at
   step=E1 and moves it to step=E2.  Note that Base_List and
   Base_Classes may appear in elements due to early processing of an
   extends-redeclaration which adds a base class. *)

and cook_imports (kp : definition_body_t) = (
    let
	val cooker = assemble_package

	fun ensure_fetch cooker subj = (
	    case (fetch_from_instance_tree subj) of
		SOME _ => ()
	      | NONE => (
		let
		    val (enclosing, (id, _)) = (subject_prefix subj)
		    val x0 = (fetch_element_class cooker (enclosing, id))
		    val _ = (store_to_instance_tree subj x0)
		in
		    ()
		end))

	fun resolve e = (
	    case e of
		Import_Clause (z, cn, idxid, a, w) => (
		case (find_import_class cooker kp cn) of
		    NONE => raise (error_class_name_not_found cn kp)
		  | SOME (enclosing, id) => (
		    let
			val subj = (compose_subject enclosing id [])
			val tag = surely (subject_to_tag subj)
			val _ = (ensure_fetch cooker subj)
		    in
			[Element_Import (z, tag, idxid, a, w)]
		    end))
	      | Extends_Clause _ => [e]
	      | Element_Class _ => [e]
	      | Element_State _ => [e]
	      | Redefine_Class _ => [e]
	      | Redeclare_State _ => [e]
	      | Element_Enumerators _ => raise Match
	      | Element_Equations _ => [e]
	      | Element_Algorithms _ => [e]
	      | Element_External _ => [e]
	      | Element_Annotation _ => [e]
	      | Element_Import _ => raise Match
	      | Element_Base _ => raise Match
	      | Base_List _ => [e]
	      | Base_Classes _ => [e])

	val _ = if (class_is_body kp) then () else raise Match
	val _ = if ((cook_step kp) = E1) then () else raise Match
    in
	if (body_is_root kp) then
	    kp
	else if (class_is_enum kp) then
	    kp
	else
	    (set_cook_step E2 (subst_body_element resolve kp))
    end)

(* Assembles a class of an extends-clause.  It takes a class at
   step=E2. *)

and cook_base pkg kp siblings (e, acc) = (
    let
	val _ = if ((cook_step kp) = E2) then () else raise Match
	val cooker = assemble_package
    in
	case e of
	    Import_Clause _ => raise Match
	  | Extends_Clause (z, (name, mm), aa0) => (
	    case (find_base_class cooker kp name) of
		NONE => raise (error_class_name_not_found name kp)
	      | SOME (enclosing, id) => (
		let
		    (*val _ = if (null ss) then () else raise Match*)
		    val _ = (assert_modifiers_are_scoped mm)
		    (*val _ = (assert_expressions_are_scoped ss)*)

		    val subj = (subject_of_class kp)
		    val k0 = (fetch_element_class cooker (enclosing, id))
		    val k1 = (make_modified_class k0 mm aa0 (Comment []))
		    val k2 = (cook_class_refining
				  false pkg (subj, k1) siblings)
		    val k3 = (cook_class_body
				  false pkg (subj, k2) siblings)
		    val k4 = (reset_visibility z k3)
		    val tag = (innate_tag k4)
		    val scope = (subj, tag)
		    val (bases0, k5) = (extract_base_classes false k4)
		    val _ = (app ((assert_match_subject subj) o #2) bases0)
		    val bases2 = (bases0 @ [(tag, k5)])
		in
		    (* Annotations are duplicated. *)
		    (Element_Base (z, scope, aa0), (acc @ bases2))
		end))
	  | Element_Class _ => (e, acc)
	  | Element_State _ => (e, acc)
	  | Redefine_Class _ => (e, acc)
	  | Redeclare_State _ => (e, acc)
	  | Element_Enumerators _ => (e, acc)
	  | Element_Equations _ => (e, acc)
	  | Element_Algorithms _ => (e, acc)
	  | Element_External _ => (e, acc)
	  | Element_Annotation _ => (e, acc)
	  | Element_Import _ => (e, acc)
	  | Element_Base _ => raise Match
	  | Base_List _ => raise Match
	  | Base_Classes _ => raise Match
    end)

(* Resolves extends-clauses.  It is called for both main and base
   classses.  It (in cook_base) replaces the elements of
   Extends_Clause by Element_Base and Base_Classes. *)

and gather_bases main pkg kp siblings = (
    let
	val _ = if (class_is_body kp) then () else raise Match
	val _ = if (not (body_is_root kp)) then () else raise Match
	val _ = if (step_is_less E3 kp) then () else raise Match

	val cooker = assemble_package
	fun eq ((tag0, k0), (tag1, k1)) = (classes_are_similar k0 k1)

	val subj = (subject_of_class kp)
	val (extendsredeclare, list0_, k1) = (extract_base_elements kp)
	val ee0 = (body_elements k1)
	val (ee1, bases0) = (map_along
				 (cook_base pkg kp siblings)
				 (ee0, []))
	val bases1 = (remove_duplicates eq (extendsredeclare @ bases0))
	val baselist = (make_base_list subj bases1)
	val _ = (assert_no_base_list ee1)
	val ee2 = ee1 @ [Base_List baselist] @ [Base_Classes bases1]
	val k3 = (replace_body_elements k1 ee2)
	val k4 = (set_cook_step E3 k3)

	val _ = tr_cook_vvv (";; gather_bases ("^ (class_print_name kp)
			     ^") bases={"^
			     ((String.concatWith " ")
				  (map tag_to_string (list_base_names k4)))
			     ^"}")
    in
	k4
    end)

(* Adds a base class to a class definition of an
   extends-redeclaration. *)

and insert_base_of_extends_redeclaration subj x0 k0 = (
    let
	val _ = if (step_is_at_least E3 x0) then () else raise Match
	val _ = if (class_is_body k0) then () else raise Match
	val _ = if ((cook_step k0) = E0) then () else raise Match

	val truename = (innate_tag x0)
	val (bases0, x1) = (extract_base_classes false x0)
	val bases1 = (bases0 @ [(truename, x1)])
	val baselist = (make_base_list subj [(truename, x1)])
	val ee0 = (body_elements k0)
	val _ = (assert_no_base_list ee0)
	val ee1 = ee0 @ [Base_List baselist] @ [Base_Classes bases1]
	val ee2 = (ee0 @ ee1)
	val k1 = (replace_body_elements k0 ee2)
    in
	k1
    end)

(* Makes sure every package to be syntaxed in the path, where a path
   is a suffix of a class-tag.  The flag retrying is true for the
   second call. *)

and secure_package_path__ (retrying : bool) path0 node0 = (
    case path0 of
	[] => node0
      | (n :: path1) => (
	let
	    val (subj, x0, components0) = node0
	    val kp = (! x0)
	    val components = (! components0)

	    val _ = (assert_package_constraints node0)
	    val _ = if (step_is_at_least E3 kp) then () else raise Match
	    val _ = if (class_is_package kp) then () else raise Match
	    val id = Id n
	in
	    case (List.find (fn (Slot (x, _, _, _)) => (x = id)) components) of
		SOME (Slot (v_, dim, nodes, dummy)) => (
		let
		    val _ = if (null dim) then () else raise Match
		    val _ = if ((length nodes) = 1) then () else raise Match
		    val node1 = (hd nodes)
		    val (subsubj, x1, _) = node1
		    val k0 = (! x1)
		    val k1 = (assemble_package E3 (subsubj, k0))
		in
		    (secure_package_path__ false path1 node1)
		end)
	      | NONE => (
		let
		    val _ = if (not retrying) then () else raise Match
		    val cooker = assemble_package
		    val bindings = (list_elements cooker false kp)
		in
		    case (find_in_bindings id bindings) of
			NONE => raise (error_name_not_found id kp)
		      | SOME (Binding (v, subsubj, _, (z, r, EL_Class d, h))) => (
			let
			    val Defclass (_, k0) = d
			    val kx = (assemble_package E3 (subsubj, k0))
			in
			    (secure_package_path__ true path0 node0)
			end)
		      | SOME (Binding (v, _, _, (z, r, EL_State d, h))) => (
			raise (error_name_is_state v kp))
		end)
	end))

end
