(* small0.sml -*-Coding: us-ascii-unix;-*- *)
(* Copyright (C) 2018-2021 RIKEN R-CCS *)

(* SMALL FUNCTIONS FOR ELABORATION (first half). *)

structure small0 = struct

open plain
open ast
open message

type cooker_t = common.cooker_t

(* Prints a trace message. *)

fun tr_tree (s : string) = if true then (print (s ^"\n")) else ()
fun tr_tree_vvv (s : string) = if false then (print (s ^"\n")) else ()

(* ================================================================ *)

fun make_file_path basepath (Name ss) =
    (foldl (fn (r, l) => (l ^ "/" ^ r)) basepath ss)

(* Check eq on Id.  It is to avoid "polyEqual" warning. *)

fun id_eq (Id s0 : id_t) (Id s1 : id_t) = (s0 = s1)

fun id_as_name (Id p) = (Name [p])

(* Returns a class-tag for a qualified name. *)

fun qualified_name_as_tag name = (
    case name of
	Name [] => raise Match
      | Name [""] => Ctag []
      | Name ("" :: nn) => Ctag nn
      | Name _ => raise Match)

(* Returns a class-tag (which is full-qualified) for a unqualified
   name.  For example, a qualified name of "Modelica" is
   ".Modelica". *)

fun make_name_qualified (Name nn) = (
    (qualified_name_as_tag (Name ("" :: nn))))

fun check_name_is_qualified name = (
    case name of
	Name ("" :: t) => true
      | Name _ => false)

fun tag_as_name tag = (
    case tag of
	Ctag [""] => raise Match
      | Ctag [] => raise Match
      | Ctag nn => Name ("" :: nn))

fun declaration_id (Defvar (v, _)) = v

fun same_class k0 k1 = (
    (tag_of_definition k0) = (tag_of_definition k1))

fun definition_body (Defclass ((v, g), b)) = b

(* Returns a TAG from which a class is modified. *)

fun innate_tag k = (
    case k of
	Def_Body (mk, cs, (j, n, tag, x), cc, ee, aa, ww) => tag
      | Def_Der (tag, cs, n, vv, aa, ww) => tag
      | Def_Primitive _ => raise Match
      | Def_Outer_Alias _ => raise Match
      | Def_Argument _ => raise Match
      | Def_Named _ => raise Match
      | Def_Scoped _ => raise Match
      | Def_Refine (kx, v, ts, q, (ss, mm), cc, aa, ww) => (innate_tag kx)
      | Def_Extending (_, x, kx) => (innate_tag kx)
      | Def_Replaced (kx, _) => (innate_tag kx)
      | Def_Displaced (tag, _) => tag
      | Def_In_File => raise Match
      | Def_Mock_Array _ => raise Match)

fun body_elements (k : definition_body_t) = (
    case k of
	Def_Body (mk, cs, nm, cc, ee, aa, ww) => ee
      | Def_Der _ => raise Match
      | Def_Primitive _ => raise Match
      | Def_Outer_Alias _ => raise Match
      | Def_Argument _ => raise Match
      | Def_Named _ => raise Match
      | Def_Scoped _ => raise Match
      | Def_Refine _ => raise Match
      | Def_Extending _ => raise Match
      | Def_Replaced _ => raise Match
      | Def_Displaced _ => raise Match
      | Def_In_File => raise Match
      | Def_Mock_Array _ => raise Match)

(* Returns a list of the class body elements. *)

fun class_elements (Defclass ((v, g), k)) = (body_elements k)

fun replace_body_elements (k : definition_body_t) ee = (
    case k of
	Def_Body (mk, cs, nm, cc, ee_, aa, ww) => (
	Def_Body (mk, cs, nm, cc, ee, aa, ww))
      | Def_Der _ => raise Match
      | Def_Primitive _ => raise Match
      | Def_Outer_Alias _ => raise Match
      | Def_Argument _ => raise Match
      | Def_Named _ => raise Match
      | Def_Scoped _ => raise Match
      | Def_Refine _ => raise Match
      | Def_Extending _ => raise Match
      | Def_Replaced _ => raise Match
      | Def_Displaced _ => raise Match
      | Def_In_File => raise Match
      | Def_Mock_Array _ => raise Match)

fun assert_match_subject_name id subj = (
    let
	val (prefix, (v, ss)) = (subject_prefix subj)
	val _ = if (v = id) then () else raise Match
    in
	()
    end)

(* Checks a variable declaration has no subscripts by nature. *)

fun assert_no_subscript_to_subject subj = (
    let
	val (prefix, (v, ss)) = (subject_prefix subj)
	val _ = if (null ss) then () else raise Match
    in
	()
    end)

fun assert_match_subject subj k = (
    if (subj = (subject_of_class k)) then () else raise Match)

fun drop_last_subscript_of_subject subj = (
    if (subj = the_model_subject) then
	subj
    else if (subj = the_package_root_subject) then
	subj
    else
	let
	    val (prefix, (v, ss)) = (subject_prefix subj)
	in
	    (compose_subject prefix v [])
	end)

fun subject_equal_sans_subscript subj0 subj1 = (
    ((drop_last_subscript_of_subject subj0)
     = (drop_last_subscript_of_subject subj1)))

(* Checks the subjects ignoring the subscripts of an instance k. *)

fun assert_match_subject_sans_subscript subj0 k = (
    let
	val subj1 = (subject_of_class k)
	val subj2 = (drop_last_subscript_of_subject subj1)
    in
	if (subj0 = subj2) then () else raise Match
    end)

(* ================================================================ *)

(* Tests if the subjects are in the inner-outer relation -- true if
   subj1 is the prefix of subj0.  (IT IGNORES SUBSCRIPTS). *)

fun subject_is_prefix__ (subj0, subj1) = (
    let
	fun prefix (cc0, cc1) = (
	    case (cc0, cc1) of
		(_, []) => true
	      | ([], _) => false
	      | ((v0, _) :: tt0, (v1, _) :: tt1) =>
		if (v0 <> v1) then
		    false
		else
		    (prefix (tt0, tt1)))
    in
	case (subj0, subj1) of
	    (Subj (ns0, cc0), Subj (ns1, cc1)) => (
	    (ns0 = ns1) andalso (prefix (cc0, cc1)))
    end)

fun subject_is_inner_outer__ (subj0, subj1) = (
    case (subj0, subj1) of
	(Subj (ns0, cc0), Subj (ns1, cc1)) => (
	let
	    val (tt0, s0) = (split_last cc0)
	    val (tt1, s1) = (split_last cc1)
	in
	    if (s0 = s1) then
		(subject_is_prefix__ (Subj (ns0, tt0), Subj (ns1, tt1)))
	    else
		false
	end))

(* Tests the prefix relation with the same name part.  It is true for
   "model.tank.system" and "model.system". *)

fun subject_is_inner_outer (subj0, subj1) = (
    let
	val (prefix0, (id0, ss0)) = (subject_prefix subj0)
	val (prefix1, (id1, ss1)) = (subject_prefix subj1)
    in
	if ((id0, ss0) = (id1, ss1)) then
	    (subject_is_prefix prefix0 prefix1)
	else
	    false
    end)

fun outer_but_not_inner (q : element_prefixes_t) = (
    (#Outer q) andalso (not (#Inner q)))

(* ================================================================ *)

(* Returns a new class with replacing body elements. *)

fun replace_class_elements (Defclass ((v, g), k)) ee = (
    Defclass ((v, g), (replace_body_elements k ee)))

(* ??? *)

(* Gathers what (f e) returns for each class element. *)

fun gather_in_elements f (d as Defclass ((v, g), k)) = (
    (foldl (fn (e, acc) => (acc @ (f e))) [] (class_elements d)))

fun gather_in_body_elements f (k : definition_body_t) = (
    (foldl (fn (e, acc) => (acc @ (f e))) [] (body_elements k)))

(* Substitutes elements e0 by e1,... (by appending) if f e0 returns
   [e1,...]. *)

fun subst_element f (d as Defclass _) = (
    (replace_class_elements d (gather_in_elements f d)))

(* Substitutes elements e0 by e1,... if f (e0,a0) returns
   ([e1,...],a1).  f is called along with passing around an argument
   a0. *)

fun subst_element_along f (k0, a0) = (
    let
	val (ee3, a3) =
	      (foldl
		   (fn (e1, (ee1, a1)) =>
		       let val (ee2, a2) = (f (e1, a1)) in (ee1 @ ee2, a2) end)
		   ([], a0)
		   (class_elements k0))
    in
	((replace_class_elements k0 ee3), a3)
    end)

fun subst_body_element f (k : definition_body_t) = (
    (replace_body_elements k (gather_in_body_elements f k)))

fun app_in_element__ f (d as Defclass ((v, g), k)) = (
    (app f (class_elements d)))

(* Tests if modifiers is empty or a single value. *)

fun modifier_is_value nn = (
    case nn of
	[] => true
      | [m] => (
	case m of
	    Mod_Redefine _ => false
	  | Mod_Elemental_Redefine _ => false
	  | Mod_Redeclare _ => false
	  | Mod_Elemental_Redeclare _ => false
	  | Mod_Entry _ => false
	  | Mod_Value _ => true)
      | _ => false)

(* ================================================================ *)

(*AHO*)

(* Tests if classes are the same.  It is used to drop duplicates in a
   list of base classes. *)

fun classes_are_similar x y = (
    case (x, y) of
	(Def_Body _, Def_Body _) => (innate_tag x) = (innate_tag y)
      | (Def_Der _, Def_Der _) => x = y
      | (Def_Named _, _) => raise Match
      | (_, Def_Named _) => raise Match
      | (Def_Scoped _, _) => raise Match
      | (_, Def_Scoped _) => raise Match
      | (Def_Refine _, Def_Refine _) => (innate_tag x) = (innate_tag y)
      | (Def_Extending _, Def_Extending _) => (innate_tag x) = (innate_tag y)
      | (Def_Replaced _, _) => raise Match
      | (_, Def_Replaced _) => raise Match
      | (Def_Displaced _, Def_Displaced _) => (innate_tag x) = (innate_tag y)
      | (Def_In_File, _) => raise Match
      | (_, Def_In_File) => raise Match
      | (_, _) => false)

(*AHO*)

(* Tests if classes are compatible for outer ci0 to inner ci1.  (They
   are compatible if ci0 extends ci1). *)

fun classes_are_compatible cv0 cv1 = (
    let
	(*val same = ((nominal_is_class cv0) = (nominal_is_class cv1))*)
	(*val ci0 = (class_of_nominal cv0)*)
	(*val ci1 = (class_of_nominal cv1)*)
	val _ = (warn_no_compatibility_test ())
    in
	true
    end)

fun binding_is_public (Naming (_, _, _, _, (z, r, dx, h))) = (z = Public)

fun binding_is_imported (Naming (_, _, _, i, (z, r, dx, h))) = i

fun binding_is_class (Naming (_, _, _, _, (z, r, dx, h))) = (
    case dx of
	EL_Class _ => true
      | EL_State _ => false)

(* ================================================================ *)

(* Returns true for a constant or a parameter.  It is used to list
   constants in a package.  Note that the variability is precise for a
   package after modifier applications, so it is not necessary to
   check the class definition (k) when it is not processed yet. *)

fun declaration_is_constant (Defvar (v, k)) = (
    case k of
	Def_Body _ => raise Match
      | Def_Der _ => false
      | Def_Primitive _ => false
      | Def_Outer_Alias _ => raise Match
      | Def_Argument _ => raise Match
      | Def_Named _ => raise Match
      | Def_Scoped _ => raise Match
      | Def_Refine (kx, v, ts, (fs, vc, io), (ss, mm), cc, aa, ww) => (
	(vc = Constant orelse vc = Parameter))
      | Def_Extending _ => raise Match
      | Def_Replaced _ => raise Match
      | Def_Displaced _ => raise Match
      | Def_In_File => raise Match
      | Def_Mock_Array _ => raise Match)

(* Tests if the class is proper for variable declaration form. *)

fun body_is_declaration_form k = (
    case k of
	Def_Body _ => raise Match
      | Def_Der _ => false
      | Def_Primitive _ => true
      | Def_Outer_Alias _ => raise Match
      | Def_Argument _ => raise Match
      | Def_Named _ => true
      | Def_Scoped _ => true
      | Def_Refine (kx, v, ts, q, (ss, mm), cc, aa, ww) => (
	(body_is_declaration_form kx))
      | Def_Extending _ => false
      | Def_Replaced _ => false
      | Def_Displaced _ => false
      | Def_In_File => raise Match
      | Def_Mock_Array _ => raise Match)

(* ================================================================ *)

(*AHO*)

(* CLASS SIMILARITY IS NOT IMPLEMENTED. *)

(* It does not matter about variable declarations at step=E3. *)

fun drop_duplicate_declarations step (bindings : naming_t list) = (
    let
	fun eq (Naming (v0, _, _, _, _), Naming (v1, _, _, _, _)) = (
	    (v0 = v1))

	fun unify (b0, b1) = (
	    case (b0, b1) of
		(Naming (v0, _, _, _, e0), Naming (v1, _, _, _, e1)) => (
		case (e0, e1) of
		    ((_, _, EL_Class d0, _), (_, _, EL_Class d1, _)) => (
		    if ((tag_of_definition d0) = (tag_of_definition d1)) then
			b0
		    else
			(*raise (error_duplicate_declarations (b0, b1))*)
			b0)
		  | ((_, q0, EL_State d0, _), (_, q1, EL_State d1, _)) => (
		    if (step = E3) then
			b0
		    else
			(*raise (error_duplicate_declarations (b0, b1))*)
			b0)
		  | _ => raise (error_duplicate_declarations (b0, b1))))

	fun unify_by_pairs ([]) = raise Match
	  | unify_by_pairs (b :: bb) = (foldl unify b bb)

	val bb0 = (list_groups eq bindings)
	val bb1 = (map unify_by_pairs bb0)
    in
	bb1
    end)

(* Tests approximately if a class is modifiable.  The cooker skips
   modifier applications if it is not.  It returns true only when it
   is certain.  Returning false is OK that continues applying
   modifications. *)

fun body_is_unmodifiable k = (
    case k of
	Def_Body _ => false
      | Def_Der _ => true
      | Def_Primitive _ => raise Match
      | Def_Outer_Alias _ => raise Match
      | Def_Argument _ => raise Match
      | Def_Named _ => raise Match
      | Def_Scoped _ => false
      | Def_Refine _ => false
      | Def_Extending _ => false
      | Def_Replaced (kx, _) => (body_is_unmodifiable kx)
      | Def_Displaced _ => false
      | Def_In_File => raise Match
      | Def_Mock_Array _ => raise Match)

(* Tests if a definition is an extends-redeclaration. *)

fun body_is_extending k = (
    case k of
	Def_Body _ => false
      | Def_Der _ => false
      | Def_Primitive _ => raise Match
      | Def_Outer_Alias _ => raise Match
      | Def_Argument _ => raise Match
      | Def_Named _ => false
      | Def_Scoped _ => false
      | Def_Refine _ => false
      | Def_Extending _ => true
      | Def_Replaced _ => false
      | Def_Displaced _ => false
      | Def_In_File => raise Match
      | Def_Mock_Array _ => raise Match)

fun find_in_bindings id bindings = (
    (List.find (fn Naming (x, _, _, _, _) => x = id) bindings))

fun assert_cook_step step k = (
    if ((cook_step k) = step) then () else raise Match)

fun assert_cooked_at_least step k = (
    if (step_is_at_least step k) then () else raise Match)

(* ================================================================ *)

fun extract_bases_in_main_class (k0 : definition_body_t) = (
    let
	fun base_classes e = (
	    case e of
		Import_Clause _ => false
	      | Extends_Clause _ => false
	      | Element_Class _ => false
	      | Element_State _ => false
	      | Redefine_Class _ => false
	      | Redeclare_State _ => false
	      | Element_Enumerators _ => false
	      | Element_Equations _ => false
	      | Element_Algorithms _ => false
	      | Element_External _ => false
	      | Element_Annotation _ => false
	      | Element_Import _ => false
	      | Element_Base _ => false
	      | Base_List _ => false
	      | Base_Classes _ => true)

	fun content e = (
	    case e of
		Base_Classes u => u
	      | _ => raise Match)

	val (bb, ee) = (List.partition base_classes (body_elements k0))
	val bases = (List.concat (map content bb))
	val k1 = (replace_body_elements k0 ee)
    in
	if (null bb) then
	    (NONE, k1)
	else
	    (SOME bases, k1)
    end)

end
