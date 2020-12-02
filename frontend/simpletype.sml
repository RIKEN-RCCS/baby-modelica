(* simpletype.sml -*-Coding: us-ascii-unix;-*- *)
(* Copyright (C) 2018-2020 RIKEN R-CCS *)

(* FIXING ELEMENTS OF THE SIMPLE TYPES. *)

structure simpletype :
sig
    type id_t
    type subject_t
    type definition_body_t
    type modifier_t
    type enum_list_t
    type expression_t
    type primitive_type_t

    val unify_value_and_initializer :
	definition_body_t -> modifier_t list -> modifier_t list
    val simplify_simple_type :
	definition_body_t -> definition_body_t
    val insert_attributes_to_enumeration :
	definition_body_t -> definition_body_t
    val take_enumarator_element :
	definition_body_t -> enum_list_t option
    val register_enumerators_for_enumeration :
	definition_body_t -> unit

    val simple_type_attribute :
	definition_body_t -> id_t -> expression_t
    val type_of_simple_type :
	definition_body_t -> ast.primitive_type_t
end = struct

open ast
open plain
open small0

val store_to_instance_tree = classtree.store_to_instance_tree
val assert_stored_in_instance_tree = classtree.assert_stored_in_instance_tree

fun tr_bind_vvv (s : string) = if true then (print (s ^"\n")) else ()

(* ================================================================ *)

fun take_enumarator_element kp = (
    let
	fun enumerators e = (
	    case e of
		Import_Clause _ => raise Match
	      | Extends_Clause _ => raise Match
	      | Element_Class _ => NONE
	      | Element_State _ => NONE
	      | Redefine_Class _ => NONE
	      | Redeclare_State _ => NONE
	      | Element_Enumerators vvx => SOME vvx
	      | Element_Equations _ => NONE
	      | Element_Algorithms _ => NONE
	      | Element_External _ => NONE
	      | Element_Annotation _ => NONE
	      | Element_Import _ => NONE
	      | Element_Base _ => NONE
	      | Base_List _ => NONE
	      | Base_Classes _ => raise Match)
    in
	case kp of
	    Def_Body _ => (
	    let
		val _ = if (class_is_enum kp) then () else raise Match
		val ee = (body_elements kp)
	    in
		(surely (list_find_some enumerators ee))
	    end)
	  | _ => raise Match
    end)

(* Unifies initializer forms "x(value=v)" and "x=v" to the first form,
   which have the same meaning to simple-types.  It selects a
   "x(value=v)" form, because it can have each/final. *)

fun unify_value_and_initializer kp mm0 = (
    let
	fun select (m, (v, acc)) = (
	    case m of
		Mod_Redefine _ => (v, acc @ [m])
	      | Mod_Elemental_Redefine _ => (v, acc @ [m])
	      | Mod_Redeclare _ => (v, acc @ [m])
	      | Mod_Elemental_Redeclare _ => (v, acc @ [m])
	      | Mod_Entry (ef, (Name ["value"]), mx, w) => (
		case mx of
		    [] => raise Match
		  | [Mod_Value x] => (
		    if (v = NONE) then
			(SOME m, acc)
		    else
			raise error_both_value_and_initializer)
		  | _ => (
		    (*(v, acc @ [m])*)
		    raise error_modifier_to_attribute))
	      | Mod_Entry (ef, n, mx, w) => (
		(v, acc @ [m]))
	      | Mod_Value x => (
		if (v = NONE) then
		    let
			val ef = {Each=false, Final=false}
			val mx = Mod_Entry (ef, Name ["value"],
					    [Mod_Value x], Comment [])
		    in
			(SOME mx, acc)
		    end
		else
		    raise error_both_value_and_initializer))

	val (v, mm1) = (foldl select (NONE, []) mm0)
    in
	((if (isSome v) then [valOf v] else []) @ mm1)
    end)

(* ================================================================ *)

(* Makes enumerators for a given enumeration and makes them visible in
   the instance_tree.  Each enumerator has its value in the
   initializer slot.  It is called at processing a definition of an
   enumeration.  It stores the enumeration prior to the enumerators to
   make a hierarchy. *)

fun register_enumerators_for_enumeration kp = (
    let
	val _ = (assert_class_is_body kp)

	fun make_enumerator k subj value = (
	    case k of
		Def_Body (mk, j, cs, (tag, n, x), ee, aa, ww) => (
		Def_Primitive (P_Enum tag, value))
	      | _ => raise Match)

	fun enumerate kp tag (v, a, w) = (
	    let
		val subj = (subject_of_class kp)
		val subsubj = (compose_subject subj v [])
		val value = L_Enum (tag, v)
		val k1 = (make_enumerator kp subsubj value)
		(*val k2 = (set_cook_step E5 k1)*)
		val k2 = k1
		val _ = (store_to_instance_tree subsubj k2)
	    in
		()
	    end)
    in
	if (not (class_is_enumeration_definition kp)) then
	    ()
	else
	    case kp of
		Def_Body (mk, j, cs, (tag, n, x), ee, aa, ww) => (
		let
		    val _ = if (class_is_package kp) then () else raise Match

		    val subj = (subject_of_class kp)
		    val _ = (assert_cook_step E3 kp)
		    val _ = (assert_stored_in_instance_tree (subj, kp))
		    val vvx = (take_enumarator_element kp)
		    val _ = case vvx of
				NONE => ()
			      | SOME vv => (app (enumerate kp tag) vv)
		in
		    ()
		end)
	      | _ => raise Match
    end)

(* ================================================================ *)

(* Makes a dummy type which is used to hold attributes in the
   simple-types. *)

fun make_primitive_type_by_name n = (
    let
	val ty = case n of
		     "Real" => P_Number R
		   | "Integer" => P_Number Z
		   | "Boolean" => P_Boolean
		   | "String" => P_String
		   | "StateSelect" => P_Enum (Ctag [n])
		   | _ => raise Match
    in
	Def_Primitive (ty, NIL)
    end)

(* Simplifies a simple-type (except enumerations) using primitive
   types.  Simple-types may have attribute definitions and an equation
   section of an assertion.  A attribute definition has a form
   Def_Scoped(n) or Def_Refine(Def_Scoped(n)), and it is converted to
   a dummy Def_Primitive type.  Attributes have no annotations
   initially. *)

fun simplify_simple_type (k0 : definition_body_t) = (
    let
	val _ = if (step_is_at_least E3 k0) then () else raise Match
	val _ = if ((cook_step k0) = E3) then () else raise Match
	val subj = (subject_of_class k0)

	fun just_value_modifier mm = (
	    case mm of
		[] => NIL
	      | [Mod_Value e] => e
	      | _ => raise error_bad_modifier_to_attribute)

	fun primitivize x0 = (
	    case x0 of
		Def_Body _ => raise Match
	      | Def_Der _ => raise Match
	      | Def_Primitive _ => raise Match
	      | Def_Name _ => raise Match
	      | Def_Scoped (Name n, (subjx, tag)) => (
		let
		    val _ = if (subj = subjx) then () else raise Match
		in
		    case n of
			[s] => (make_primitive_type_by_name s)
		      | _ => raise Match
		end)
	      | Def_Refine (x1, v, ts, q, (ss, mm), aa, ww) => (
		let
		    val _ = if (v = NONE) then () else raise Match
		    val _ = if (q = no_component_prefixes) then ()
			    else raise Match
		    val _ = if (null ss) then ()
			    else raise error_array_modifier_to_attribute
		    val x2 = (primitivize x1)
		    val value = (just_value_modifier mm)
		in
		    case x2 of
			Def_Primitive (ty, v_) => (
			Def_Primitive (ty, value))
		      | Def_Body _ => raise Match
		      | _ => raise Match
		end)
	      | Def_Extending _ => raise Match
	      | Def_Replaced _ => raise Match
	      | Def_Displaced _ => raise Match
	      | Def_In_File => raise Match
	      | Def_Mock_Array _ => raise Match)

	fun set_fixed k value = (
	    case k of
		Def_Primitive (P_Boolean, ov) => (
		let
		    val _ = if (ov = NIL orelse ov = value) then ()
			    else (warn_ignore_fixed ())
		in
		    Def_Primitive (P_Boolean, value)
		end)
	      | _ => raise Match)

	fun resolve variability e = (
	    case e of
		Import_Clause _ => raise Match
	      | Extends_Clause _ => raise Match
	      | Element_Class _ => e
	      | Element_State (z, r, d0, h) => (
		let
		    val Defvar (v, q, x0, c, a, w) = d0
		    val _ = if (c = NONE) then () else raise Match
		    val x1 = (primitivize x0)
		    val fixed = L_Bool (variability = Parameter
					orelse variability = Constant)
		    val x2 = if (v = Id "fixed") then
				 (set_fixed x1 fixed)
			     else
				 x1
		    val d1 = Defvar (v, q, x2, c, a, w)
		in
		    Element_State (z, r, d1, h)
		end)
	      | Redefine_Class _ => e
	      | Redeclare_State _ => e
	      | Element_Enumerators _ => raise Match
	      | Element_Equations _ => e
	      | Element_Algorithms _ => e
	      | Element_External _ => e
	      | Element_Annotation _ => e
	      | Element_Import _ => raise Match
	      | Element_Base _ => raise Match
	      | Base_List x => if (null x) then e else raise Match
	      | Base_Classes x => if (null x) then e else raise Match)
    in
	case k0 of
	    Def_Body (mk, j, cs, (c, n, x), ee0, aa, ww) => (
	    (*
	    if (class_is_enumeration_definition k0) then
		k0
	    else
	    *)
	    if (not (class_is_simple_type k0)) then
		k0
	    else if (class_is_enum k0) then
		k0
	    else
		let
		    val (t, p, (l, variability, y)) = cs
		    val ee1 = (map (resolve variability) ee0)
		    val k1 = Def_Body (mk, j, cs, (c, n, x), ee1, aa, ww)
		in
		    k1
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

(* Takes bounds of an enumeration.  It returns NIL for ":" or an empty
   enumeration. *)

fun enumeration_bounds kp = (
    let
	val tag = (innate_tag kp)
    in
	case (take_enumarator_element kp) of
	    NONE => (NIL, NIL)
	  | SOME [] => (NIL, NIL)
	  | SOME vv => (
	    let
		val (v0, a0, w0) = (hd vv)
		val (vn, an, wn) = (List.last vv)
	    in
		(L_Enum (tag, v0), L_Enum (tag, vn))
	    end)
    end)

fun enumeration_attributes kp = (
    let
	val (min, max) = (enumeration_bounds kp)
	val tag = (innate_tag kp)

	fun this_type v = Def_Primitive (P_Enum tag, v)
	fun string_type v = Def_Primitive (P_String, L_String v)
	val boolean_type = Def_Primitive (P_Boolean, NIL)

	fun withvalue__ ty value = (
	    Def_Refine (ty, NONE, (Implied, no_class_prefixes),
			no_component_prefixes,
			([], [Mod_Value value]),
			Annotation [], Comment []))

	fun declare name variability ty = (
	    let
		val declaration
		    = Defvar (Id name, (Effort, variability, Modeless),
			      ty, NONE, Annotation [], Comment [])
	    in
		(Public, no_element_prefixes, declaration, NONE)
	    end)
    in
	[Element_State (declare "value" Discrete (this_type NIL)),
	 Element_State (declare "quantity" Parameter (string_type "")),
	 Element_State (declare "min" Parameter (this_type min)),
	 Element_State (declare "max" Parameter (this_type max)),
	 Element_State (declare "start" Parameter (this_type min)),
	 Element_State (declare "fixed" Parameter boolean_type)]
    end)

(* Add attributes to an enumeration.  Enumerations have attributes,
   and they are added here. *)

fun insert_attributes_to_enumeration k0 = (
    case k0 of
	Def_Body (mk, j, cs, (c, n, x), ee0, aa, ww) => (
	if (not (class_is_enum k0)) then
	    k0
	else
	    let
		val _ = if ((cook_step k0) = E1) then () else raise Match
		val attributes = (enumeration_attributes k0)
		val ee1 = ee0 @ attributes
		val k1 = Def_Body (mk, j, cs, (c, n, x), ee1, aa, ww)
		val k2 = (set_cook_step E2 k1)
	    in
		k2
	    end)
      | Def_Der _ => k0
      | Def_Primitive _ => raise Match
      | Def_Name _ => raise Match
      | Def_Scoped _ => raise Match
      | Def_Refine _ => raise Match
      | Def_Extending _ => raise Match
      | Def_Replaced _ => raise Match
      | Def_Displaced _ => raise Match
      | Def_In_File => raise Match
      | Def_Mock_Array _ => raise Match)

(* ================================================================ *)

(* It is an error to call with an undefined attribute. *)

fun simple_type_attribute kp (id : id_t) = (
    let
	fun check e = (
	    case e of
		Element_State (z, r, d, h) => (
		let
		    val Defvar (v, q, kx, c, a, w) = d
		in
		    if (v = id) then
			SOME kx
		    else
			NONE
		end)
	      | _ => NONE)

	val ee = (body_elements kp)
    in
	case (list_find_some check ee) of
	    NONE => raise Match
	  | SOME kx => (
	    case kx of
		Def_Primitive (name, v) => v
	      | _ => raise Match)
    end)

(* Returns a primitive-type as a name corresponding to a
   simple-type. *)

fun type_of_simple_type k = (
    case k of
	Def_Body (mk, j, cs, (tag, n, x), ee, a, w) => (
	if (class_is_enum k) then
	    P_Enum tag
	else
	    case tag of
		Ctag [""] => raise Match
	      | Ctag ["Real"] => P_Number R
	      | Ctag ["Integer"] => P_Number Z
	      | Ctag ["Boolean"] => P_Boolean
	      | Ctag ["String"] => P_String
	      | Ctag _ => raise Match)
      | Def_Der _ => raise Match
      | Def_Primitive _ => raise Match
      | Def_Name _ => raise Match
      | Def_Scoped _ => raise Match
      | Def_Refine _ => raise Match
      | Def_Extending _ => raise Match
      | Def_Replaced _ => raise Match
      | Def_Displaced _ => raise Match
      | Def_In_File => raise Match
      | Def_Mock_Array _ => raise Match)

end
