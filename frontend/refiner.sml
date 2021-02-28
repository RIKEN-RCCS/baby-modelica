(* refiner.sml -*-Coding: us-ascii-unix;-*- *)
(* Copyright (C) 2018-2021 RIKEN R-CCS *)

(* MODIFIER APPLICATION. *)

structure refiner : sig
    type subject_t
    type definition_body_t
    type modifier_t
    type component_prefixes_t
    type type_prefixes_t
    type instantiation_t
    type scope_t
    type annotation_t
    type comment_t

    val associate_modifiers :
	definition_body_t -> modifier_t list -> definition_body_t

    val rectify_modified_class :
	definition_body_t * component_prefixes_t
	-> type_prefixes_t -> annotation_t -> definition_body_t
    val make_modified_class :
	definition_body_t -> modifier_t list
	-> annotation_t -> comment_t -> definition_body_t

    val merge_modifiers :
	definition_body_t ->
	modifier_t list -> modifier_t list -> modifier_t list
    val merge_annotations :
	definition_body_t ->
	annotation_t -> annotation_t -> annotation_t
    val merge_type_prefixes :
	type_prefixes_t -> type_prefixes_t -> type_prefixes_t
    val merge_component_prefixes :
	component_prefixes_t -> component_prefixes_t -> component_prefixes_t

    val commute_modifier_over_subscript :
	int list -> modifier_t list -> modifier_t list
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
val assert_stored_in_instance_tree = classtree.assert_stored_in_instance_tree
val assert_package_constraints = classtree.assert_package_constraints
val assert_enclosings_are_cooked = classtree.assert_enclosings_are_cooked

val simplify_simple_type = simpletype.simplify_simple_type
val insert_attributes_to_enumeration = simpletype.insert_attributes_to_enumeration
val unify_value_and_initializer = simpletype.unify_value_and_initializer
val register_enumerators_for_enumeration = simpletype.register_enumerators_for_enumeration

val list_elements = finder.list_elements

(* Prints a trace message. *)

fun tr_cook (s : string) = if true then (print (s ^"\n")) else ()
fun tr_cook_vvv (s : string) = if false then (print (s ^"\n")) else ()

(* ================================================================ *)

(* This is a workaround of missing "each" in Fluid.Interfaces
   .PartialDistributedVolume in MSL-3.2.3. *)

fun pseudo_split_named_entry m = (
    if (false) then
	raise error_split_named_entry
    else
	let
	    val _ = warn_split_named_entry ()
	in
	    m
	end)

(* Splits an initializer-value from modifiers.  It returns a pair of a
   value and modifiers, where a value is NIL if there is no
   initializer. *)

fun split_initializer_value mm0 = (
    let
	fun value m = (
	    case m of
		Mod_Redefine _ => false
	      | Mod_Elemental_Redefine _ => false
	      | Mod_Redeclare _ => false
	      | Mod_Elemental_Redeclare _ => false
	      | Mod_Entry _ => false
	      | Mod_Value _ => true)

	val (v, mm1) = (List.partition value mm0)
    in
	case v of
	    [] => (NIL, mm1)
	  | [Mod_Value e] => (e, mm1)
	  | _ => raise Match
    end)

(* Tests two modifiers specify the same subject class. *)

fun similar_modifiers (m0, m1) = (
    case (m0, m1) of
	(Mod_Redefine (r0_, d0, h0_), Mod_Redefine (r1_, d1, h1_)) => (
	let
	    val Defclass ((v0, g0), b0) = d0
	    val Defclass ((v1, g1), b1) = d1
	    val _ = if (g0 = bad_tag) then () else raise Match
	    val _ = if (g1 = bad_tag) then () else raise Match
	in
	    (v0 = v1)
	end)
      | (Mod_Redeclare (r0_, d0, h0_), Mod_Redeclare (r1_, d1, h1_)) => (
	let
	    val Defvar (v0, q0, t0, c0, a0, w0) = d0
	    val Defvar (v1, q1, t1, c1, a1, w1) = d1
	in
	    (v0 = v1)
	end)
      | (Mod_Entry (ef0, n0, mm0, w0), Mod_Entry (ef1, n1, mm1, w1)) => (
	(n0 = n1))
      | (Mod_Value e0, Mod_Value e1) => true
      | _ => false)

fun print_removed_modifiers ctx all new = (
    let
	fun message mm = (
	    let
		val s = ((String.concatWith ",")
			     (map modifier_to_string mm))
		val _ = tr_cook (";; merge_modifiers: "^
				     "modifiers removed in "^
				     (class_print_name ctx) ^":"^ s)
	    in
		()
	    end)

	val removed = (list_diff all new)
	val _ = if (null removed) then () else (message removed)
    in
	()
    end)

(* Merges two sets of modifiers, keeping the later modifiers if two
   modifiers are on the same operand. *)

fun merge_modifiers ctx mm0 mm1 = (
    let
	val mmx = (list_uniquify similar_modifiers (mm0 @ mm1))
	(*val _ = (print_removed_modifiers ctx (mm0 @ mm1) mmx)*)
    in
	mmx
    end)

fun merge_annotations ctx (Annotation m0) (Annotation m1) = (
    let
	val _ = if ((null m0) orelse (null m1)) then ()
		else tr_cook (";; AHO ANNOTATION MERGED")
    in
	Annotation (merge_modifiers ctx m0 m1)
    end)

fun merge_comments ctx (Comment w0) (Comment w1) = Comment (w0 @ w1)

(* Moves modifiers over subscripts, such as "T~x[3](each~a=10)" to
   "T(a=10)[3]~x".  Or, "T~x[3](a=v)" to "T(a=v[i])~x[i]" for i in
   {1,2,3}.  It uses a pseudo split operation for an array indexing
   "v[i]". *)

fun commute_modifier_over_subscript index mm0 = (
    let
	val size = (length index)

	fun split m = (
	    case m of
		Mod_Redefine _ => raise error_each_is_needed
	      | Mod_Elemental_Redefine _ => raise Match
	      | Mod_Redeclare _ => raise error_each_is_needed
	      | Mod_Elemental_Redeclare _ => raise Match
	      | Mod_Entry _ => (
		(pseudo_split_named_entry m))
	      | Mod_Value x => (
		Mod_Value (Pseudo_Split (x, index))))

	fun commute m = (
	    case m of
		Mod_Redefine ({Each=e, Final=f, Replaceable=p}, d, h) => (
		if (e) then
		    Mod_Redefine ({Each=false, Final=f, Replaceable=p}, d, h)
		else
		    raise error_each_is_needed)
	      | Mod_Elemental_Redefine _ => raise Match
	      | Mod_Redeclare ({Each=e, Final=f, Replaceable=p}, d, h) => (
		if (e) then
		    Mod_Redeclare ({Each=false, Final=f, Replaceable=p}, d, h)
		else
		    raise error_each_is_needed)
	      | Mod_Elemental_Redeclare _ => raise Match
	      | Mod_Entry ({Each=e, Final=f}, n, mx0, w) => (
		if (e) then
		    Mod_Entry ({Each=false, Final=f}, n, mx0, w)
		else
		    let
			val mx1 = (map split mx0)
		    in
			Mod_Entry ({Each=e, Final=f}, n, mx1, w)
		    end)
	      | Mod_Value x => (
		Mod_Value (Pseudo_Split (x, index))))
    in
	case index of
	    [] => mm0
	  | _ => (map commute mm0)
    end)

(* Merges prefixes.  The second argument is specified later and has
   precedence.  (*AHO*) No checks of compatibility. *)

fun merge_type_prefixes (t0, p0) (t1, p1) = (
    let
	fun merge_class_kind t0 t1 = (
	    case (t0, t1) of
		(Bad_Kind, _) => raise Match
	      | (_, Bad_Kind) => raise Match
	      | (_, Implied) => t0
	      | (Implied, _) => t1
	      | _ => (
		let
		    val _ = warn_compatibility_not_checked ()
		in
		    t1
		end))

	fun merge_class_prefixes p0 p1 = (
	    let
		val {Final=f0, Encapsulated=e0, Partial=a0} = p0
		val {Final=f1, Encapsulated=e1, Partial=a1} = p1
	    in
		{Final = (f0 orelse f1),
		 Encapsulated = (e0 orelse e1),
		 Partial = (a0 orelse a1)}
	    end)

	(*val yx = (merge_modality y0 y1)*)
	val tx = (merge_class_kind t0 t1)
	val px = (merge_class_prefixes p0 p1)
    in
	(tx, px)
    end)

(* Merges input/output to component_prefixes.  It only merges when
   nothing is specified already.  Note that Effort, Continuous, and
   Modeless are used as unspecified. *)

fun merge_component_prefixes (a0, v0, y0) (a1, v1, y1) = (
    let
	fun merge_analogical a0 a1 = (
	    if (a1 = Effort) then
		a0
	    else
		case (a0, a1) of
		    (_, Effort) => a0
		  | (Effort, _) => a1
		  | (Flow, Flow) => Flow
		  | (Stream, Stream) => Stream
		  | _ => raise error_incompatible_analogical)

	fun merge_variability v0 v1 = (
	    if (v1 = Continuous) then
		v0
	    else if ((variability_order v1) <= (variability_order v0)) then
		v1
	    else
		raise error_incompatible_variability)

	fun merge_modality y0 y1 = (
	    if (y1 = Modeless) then
		y0
	    else
		case (y0, y1) of
		    (_, Modeless) => y0
		  | (Modeless, _) => y1
		  | (Input, Input) => Input
		  | (Output, Output) => Output
		  | _ => raise error_incompatible_mode)
    in
	((merge_analogical a0 a1),
	 (merge_variability v0 v1),
	 (merge_modality y0 y1))
    end)

(* ================================================================ *)

(* Makes a refining of a class with given modifiers.  It lowers the
   priority of the passed modifiers (by reversing the ordering), when
   the modifiers were ones attached to a replaced class. *)

fun make_refining_class_choose_order reverse k0 mm1 cc1 aa1 ww1 = (
    if ((null mm1) andalso (aa1 = Annotation [])
	andalso (ww1 = Comment [])) then
	k0
    else
	let
	    val kx = Def_Refine (k0, NONE, copy_type, no_component_prefixes,
				 ([], mm1), cc1, aa1, ww1)
	in
	    case k0 of
		Def_Body _ => kx
	      | Def_Der _ => raise (error_modifiers_to_der mm1)
	      | Def_Primitive _ => raise Match
	      | Def_Name _ => raise Match
	      | Def_Scoped _ => kx
	      | Def_Refine (x0, v, ts, q, (ss0, mm0), cc0, aa0, ww0) => (
		let
		    val _ = if (not (class_is_refining x0)) then ()
			    else raise Match
		    val ctx = k0
		    val mmx = if (reverse) then
				  (merge_modifiers ctx mm1 mm0)
			      else
				  (merge_modifiers ctx mm0 mm1)
		    val ccx = (choose_non_nil cc1 cc0)
		    val aax = (merge_annotations ctx aa0 aa1)
		    val wwx = (merge_comments ctx ww0 ww1)
		    val k1 = Def_Refine (x0, v, ts, q, (ss0, mmx), ccx, aax, wwx)
		in
		    k1
		end)
	      | Def_Extending _ => kx
	      | Def_Replaced (x0, kold) => (
		let
		    val x1 = (make_refining_class_choose_order
				  reverse x0 mm1 cc1 aa1 ww1)
		in
		    Def_Replaced (x1, kold)
		end)
	      | Def_Displaced _ => kx
	      | Def_In_File => raise Match
	      | Def_Mock_Array _ => raise Match
	end)

fun make_modified_class k0 mm1 aa1 ww1 = (
    (make_refining_class_choose_order false k0 mm1 NIL aa1 ww1))

fun make_modified_class_for_replacing k0 mm1 cc1 = (
    (make_refining_class_choose_order
	 true k0 mm1 cc1 (Annotation []) (Comment [])))

(* Checks if a class is proper to replace a replaceable. *)

fun assert_class_is_good_to_dispatch k = (
    case k of
	Def_Body _ => ()
      | Def_Der _ => ()
      | Def_Primitive _ => raise Match
      | Def_Name _ => raise Match
      | Def_Scoped _ => ()
      | Def_Refine _ => ()
      | Def_Extending _ => ()
      | Def_Replaced _ => ()
      | Def_Displaced _ => ()
      | Def_In_File => raise Match
      | Def_Mock_Array _ => raise Match)

fun assert_class_is_good_to_modify k = (
    case k of
	Def_Body _ => raise Match
      | Def_Der _ => ()
      | Def_Primitive _ => ()
      | Def_Name _ => raise Match
      | Def_Scoped _ => ()
      | Def_Refine _ => ()
      | Def_Extending _ => ()
      | Def_Replaced _ => ()
      | Def_Displaced _ => ()
      | Def_In_File => raise Match
      | Def_Mock_Array _ => raise Match)

(* Extracts redeclarations in a class and returns them as a list of
   modifiers. *)

fun extract_redeclares (subj, kp) = (
    let
	fun extract e = (
	    case e of
		Import_Clause _ => raise Match
	      | Extends_Clause _ => raise Match
	      | Element_Class _ => NONE
	      | Element_State _ => NONE
	      | Redefine_Class (z, r, d0, h) => (
		let
		    val Defclass ((v, g), k0) = d0
		    val _ = (assert_class_is_good_to_dispatch k0)
		in
		    SOME (Mod_Elemental_Redefine (z, r, d0, h))
		end)
	      | Redeclare_State (z, r, d, h) => (
		let
		    val Defvar (v, q, k, c, a, w) = d
		    val _ = (assert_class_is_good_to_dispatch k)
		in
		    SOME (Mod_Elemental_Redeclare (z, r, d, h))
		end)
	      | Element_Enumerators _ => raise Match
	      | Element_Equations _ => NONE
	      | Element_Algorithms _ => NONE
	      | Element_External _ => NONE
	      | Element_Annotation _ => NONE
	      | Element_Import _ => NONE
	      | Element_Base _ => NONE
	      | Base_List _ => NONE
	      | Base_Classes _ => NONE)
    in
	if (class_is_enum kp) then
	    ([], kp)
	else
	    let
		val ee = (body_elements kp)
		val redeclares = (gather_some extract ee)
	    in
		(redeclares, kp)
	    end
    end)

(* Tests if a definition is a Def_Refine node created from
   initializers.  The node has only effective fields of a definition
   and modifiers. *)

fun refining_is_initializers k0 = (
    case k0 of
	Def_Refine (k1, v, ts, q, (ss, mm), cc, Annotation aa, Comment ww) => (
	((ts = copy_type) andalso (q = no_component_prefixes)
	 andalso (cc = NIL) andalso (null aa) andalso (null ww)
	 andalso (not (class_is_refining k1))))
      | _ => raise Match)

(* Replaces a class k0 of a replaceable variable by a redeclaration
   k1.  Modifiers of a replaceable are merged.  A replaceable has
   modifiers when it is a Def_Refine, where the modifiers are assumed
   to be for the existing fields in both an old and a new
   definitions. *)

fun switch_class_for_redeclaration state ctx k0 k1 = (
    case k0 of
	Def_Body _ => k1
      | Def_Der _ => k1
      | Def_Primitive _ => raise Match
      | Def_Name _ => raise Match
      | Def_Scoped _ => k1
      | Def_Refine (kx, v, ts, q, (ss, mm), cc, aa, ww) => (
	let
	    val _ = print "(AHO) DROP PREFIXES\n"
	    val _ = if (null ss) then ()
		    else (warn_no_array_compatibility_test ())
	    val _ = if (null mm) then ()
		    else (warn_redeclaration_compatibility ())
	    val _ = if (not (class_is_refining kx)) then ()
		    else raise Match
	    val _ = if (not state) then ()
		    else if (refining_is_initializers k0) then ()
		    else raise Match
	    val _ = if (aa = Annotation []) then ()
		    else (warn_drop_annotations ())
	    val _ = if (ww = Comment []) then ()
		    else (warn_drop_comments ())
	    val x1 = (make_modified_class_for_replacing k1 mm cc)
	in
	    x1
	end)
      | Def_Extending (true, (n, mm), x_) => (
	let
	in
	    k1
	end)
      | Def_Extending (false, _, _) => raise Match
      | Def_Replaced (x0, _) => (
	(switch_class_for_redeclaration state ctx x0 k1))
      | Def_Displaced _ => k1
      | Def_In_File => raise Match
      | Def_Mock_Array _ => raise Match)

(* Replaces a replaceable (k0) by an extends-redeclaration (k1). *)

fun switch_class_by_extending_base k0 k1 = (
    let
	fun assert_name_matches k0 n = (
	    (*AHO*) (* No checks. *) ())
    in
	case k1 of
	    Def_Extending (true, _, _) => raise Match
	  | Def_Extending (false, (Def_Scoped (n, _), mm), body) => (
	    let
		val _ = (assert_name_matches k0 n)
	    in
		Def_Extending (true, (k0, mm), body)
	    end)
	  | _ => raise Match
    end)

(* Replaces a replaceable (k0) by a redefinition (k1). *)

fun switch_class_for_redefinition ctx k0 k1 = (
    if (not (body_is_extending k1)) then
	(switch_class_for_redeclaration false ctx k0 k1)
    else
	(switch_class_by_extending_base k0 k1))

fun attach_modifiers_to_body ctx k0 mm1 = (
    case k0 of
	Def_Body _ => raise Match
      | Def_Der _ => raise Match
      | Def_Primitive (p, v) => (
	case mm1 of
	    [m] => (
	    case m of
		Mod_Redefine _ => raise Match
	      | Mod_Elemental_Redefine _ => raise Match
	      | Mod_Redeclare _ => raise Match
	      | Mod_Elemental_Redeclare _ => raise Match
	      | Mod_Entry _ => raise Match
	      | Mod_Value e => (
		Def_Primitive (p, e)))
	  | _ => raise Match)
      | Def_Name _ => (
	Def_Refine (k0, NONE, copy_type, no_component_prefixes, ([], mm1),
		    NIL, Annotation [], Comment []))
      | Def_Scoped _ => (
	Def_Refine (k0, NONE, copy_type, no_component_prefixes, ([], mm1),
		    NIL, Annotation [], Comment []))
      | Def_Refine (kx, v, ts, q, (ss, mm0), cc, aa, ww) => (
	let
	    val mmx = (merge_modifiers ctx mm0 mm1)
	in
	    Def_Refine (kx, v, ts, q, (ss, mmx), cc, aa, ww)
	end)
      | Def_Extending _ => raise Match
      | Def_Replaced (x0, ko) => (
	let
	    val x1 = (attach_modifiers_to_body ctx x0 mm1)
	in
	    Def_Replaced (x1, ko)
	end)
      | Def_Displaced _ => raise Match
      | Def_In_File => raise Match
      | Def_Mock_Array _ => raise Match)

fun merge_element_prefixes q0 q1 = (
    let
	val {Final=f0, Replaceable=r0, Inner=i0, Outer=j0} = q0
	val {Final=f1, Replaceable=r1, Inner=i1, Outer=j1} = q1
	val _ = if (r0) then () else raise error_not_replaceable
	(*val _ = if (not f0) then () else raise error_replacing_final*)
	val _ = if (f0 = f1) then () else (warn_final_incompatible ())
    in
	if (i1 = false andalso j1 = false) then
	    {Final=f1, Replaceable=r1, Inner=i0, Outer=j0}
	else
	    {Final=f1, Replaceable=r1, Inner=i1, Outer=j1}
    end)

(* Redefines a class by a redeclarations in modifiers or in elements.
   The source (in-modifiers/in-elements) is indicated by source. *)

fun replace_class source ctx (z0, r0, d0, h0) (z1, r1, d1, h1) = (
    let
	val old0 = (z0, r0, EL_Class d0, h0)
	val Defclass ((v0, g0), k0) = d0
	val Defclass ((v1, g1), k1) = d1
	val _ = (assert_class_is_good_to_dispatch k1)

	val _ = tr_cook_vvv (";; - Replace class ("^
			     (name_of_definition d0) ^" by "^
			     (class_print_name k1) ^" in "^
			     (class_print_name ctx) ^")")

	val x1 = (switch_class_for_redefinition ctx k0 k1)
	val dx = Defclass ((v0, g0), Def_Replaced (x1, old0))
	val rx = (merge_element_prefixes r0 r1)
    in
	(z1, rx, dx, h1)
    end)

fun replace_class_by_modifiers ctx (z0, r0, d0, h0) (p1, d1, h1) = (
    let
	val z1 = z0
	val {Each=e, Final=f, Replaceable=r} = p1
	val r1 = {Final=f, Replaceable=r, Inner=false, Outer=false}
	(*AHO*) (*ENABLE LATER*)
	(*val _ = if (e = false) then () else raise Match*)
    in
	(replace_class In_Modifiers ctx (z0, r0, d0, h0) (z1, r1, d1, h1))
    end)

fun replace_class_by_elements ctx (z0, r0, d0, h0) (z1, r1, d1, h1) = (
    (replace_class In_Elements ctx (z0, r0, d0, h0) (z1, r1, d1, h1)))

(* Redeclares a state by a redeclarations in modifiers or in elements.
   The source (in-modifiers/in-elements) is indicated by source. *)

fun redeclare_state source ctx (z0, r0, d0, h0) (z1, r1, d1, h1) = (
    let
	val oldx = (z0, r0, EL_State d0, h0)
	val Defvar (v0, q0, k0, c0, aa0, ww0) = d0
	val Defvar (v1, q1, k1, c1, aa1, ww1) = d1
	val _ = (assert_class_is_good_to_dispatch k1)

	val _ = tr_cook_vvv (";; - Replace state ("^
			     (id_to_string v0) ^" by "^
			     (class_print_name k1) ^" in "^
			     (class_print_name ctx) ^")")

	val x1 = (switch_class_for_redeclaration true ctx k0 k1)
	val aax = (merge_annotations ctx aa0 aa1)
	val wwx = (merge_comments ctx ww0 ww1)
	val dx = Defvar (v0, q1, Def_Replaced (x1, oldx), c1, aax, wwx)
	val rx = (merge_element_prefixes r0 r1)
	val _ = raise Match
    in
	(z1, rx, dx, h1)
    end)

fun redeclare_state_by_modifiers ctx (z0, r0, d0, h0) (r1, d1, h1) = (
    let
	val z1 = z0
	val {Each=e, Final=f, Replaceable=r} = r1
	val q1 = {Final=f, Replaceable=r, Inner=false, Outer=false}
	val _ = if (e = false) then () else raise error_each_in_redeclare
    in
	(redeclare_state In_Modifiers ctx (z0, r0, d0, h0) (z1, q1, d1, h1))
    end)

fun redeclare_state_by_elements ctx (z0, r0, d0, h0) (z1, r1, d1, h1) = (
    (redeclare_state In_Elements ctx (z0, r0, d0, h0) (z1, r1, d1, h1)))

(* Lists names of components in the class. *)

fun list_components kp = (
    let
	val _ = if (step_is_at_least E3 kp) then () else raise Match

	fun name (Naming (id, _, _, _, (z, r, d, h))) = (
	    case d of
		EL_Class _ => raise Match
	      | EL_State (Defvar (_, q, k, c, a, w)) => [id])

	fun faulting_cooker wantedstep (subj, kx) = raise Match
	val bindings = (list_elements faulting_cooker false kp)
	val (classes, states) = (List.partition binding_is_class bindings)
	val cc = (List.concat (map name states))
    in
	cc
    end)

(* Associates an initializer value v to an instance k0.  It returns
   modifiers for each component of a class.  (It is for a declaration
   C~x=v for some variable x of a class k0). *)

fun associate_initializer kp e = (
    case e of
	NIL => []
      | _ => (
	let
	    val cc = (list_components kp)
	    val mm = (map (fn Id s =>
			      Mod_Entry (no_each_or_final, Name [s],
					 [Mod_Value (Component_Ref (e, Id s))],
					 Comment []))
			  cc)
	in
	    mm
	end))

(* Tries to associate a modifier to a class definition.  It creates a
   new class refining or attaches to an existing one.  Note that an
   application can be more than once for a class redefinition. *)

fun associate_to_definition ctx (z0, r0, d0, h0) m = (
    let
	val oldx = (z0, r0, d0, h0)
	val Defclass ((v0, g0), k0) = d0
	val _ = (assert_class_is_good_to_dispatch k0)
    in
	case m of
	    Mod_Redefine (r1, d1, h1) => (
	    let
		val Defclass ((v1, _), k1) = d1
	    in
		if (v0 <> v1) then
		    NONE
		else
		    let
			val ec = (replace_class_by_modifiers
				      ctx (z0, r0, d0, h0) (r1, d1, h1))
		    in
			SOME ec
		    end
	    end)

	  | Mod_Elemental_Redefine (z1, r1, d1, h1) => (
	    let
		val Defclass ((v1, _), k1) = d1
	    in
		if (v0 <> v1) then
		    NONE
		else
		    let
			val ec = (replace_class_by_elements
				      ctx (z0, r0, d0, h0) (z1, r1, d1, h1))
		    in
			SOME ec
		    end
	    end)

	  | Mod_Redeclare (p1, d1, h1) => (
	    let
		val Defvar (v1, _, _, _, _, _) = d1
	    in
		if (v0 <> v1) then
		    NONE
		else
		    raise (error_redeclare_to_class m)
	    end)

	  | Mod_Elemental_Redeclare (z1, r1, d1, h1) => (
	    let
		val Defvar (v1, _, _, _, _, _) = d1
	    in
		if (v0 <> v1) then
		    NONE
		else
		    raise (error_redeclare_to_class m)
	    end)

	  | Mod_Entry (ef, (Name nn), mm1, ww1) => (
	    case nn of
		[] => raise Match
	      | (p :: t) => (
		if (v0 <> (Id p)) then
		    NONE
		else
		    if (null t) then
			let
			    val aa0 = Annotation []
			    val kx = (make_modified_class k0 mm1 aa0 ww1)
			    val dx = Defclass ((v0, g0), kx)
			    val ec = (z0, r0, dx, h0)
			in
			    SOME ec
			end
		    else
			let
			    val aa0 = Annotation []
			    val ww0 = Comment []
			    val mmx = [Mod_Entry (ef, (Name t), mm1, ww0)]
			    val kx = (make_modified_class k0 mmx aa0 ww1)
			    val dx = Defclass ((v0, g0), kx)
			    val ec = (z0, r0, dx, h0)
			in
			    SOME ec
			end))

	  | Mod_Value _ => raise Match
    end)

(* Tries to associate a modifier to a variable declaration.  Note an
   application is at most once.  It merges a modifier to the modifiers
   attached to the original. *)

fun associate_to_declaration ctx (z0, r0, d0, h0) m = (
    let
	val oldx = (z0, r0, d0, h0)
	val Defvar (v0, q0, k0, c0, a0, w0) = d0
	val _ = (assert_class_is_good_to_modify k0)
	val _ = if (body_is_declaration_form k0) then () else raise Match
    in
	case m of
	    Mod_Redefine (p1, d1, h1) => (
	    let
		val Defclass ((v1, g1), k1) = d1
	    in
		if (v0 <> v1) then
		    NONE
		else
		    raise (error_redefine_to_state m)
	    end)

	  | Mod_Elemental_Redefine (z1, r1, d1, h1) => (
	    let
		val Defclass ((v1, g1), k1) = d1
	    in
		if (v0 <> v1) then
		    NONE
		else
		    raise (error_redefine_to_state m)
	    end)

	  | Mod_Redeclare (r1, d1, h1) => (
	    let
		val Defvar (v1, q1, k1, c1, a1, w1) = d1
		val _ = if (c1 = NONE) then () else raise Match
	    in
		if (v0 <> v1) then
		    NONE
		else
		    let
			val ec = (redeclare_state_by_modifiers
				      ctx (z0, r0, d0, h0) (r1, d1, h1))
		    in
			SOME ec
		    end
	    end)

	  | Mod_Elemental_Redeclare (z1, r1, d1, h1) => (
	    let
		val Defvar (v1, q1, k1, c1, a1, w1) = d1
	    in
		if (v0 <> v1) then
		    NONE
		else
		    let
			val ec = (redeclare_state_by_elements
				      ctx (z0, r0, d0, h0) (z1, r1, d1, h1))
		    in
			SOME ec
		    end
	    end)

	  | Mod_Entry (ef, (Name nn), mm1, w1) => (
	    case nn of
		[] => raise Match
	      | p :: tl => (
		if (v0 <> (Id p)) then
		    NONE
		else
		    if (null tl) then
			let
			    val k1 = (attach_modifiers_to_body ctx k0 mm1)
			    val ww = (merge_comments ctx w0 w1)
			    val dx = Defvar (v0, q0, k1, c0, a0, ww)
			    val ec = (z0, r0, dx, h0)
			in
			    SOME ec
			end
		    else
			let
			    val mmx = [Mod_Entry (ef, (Name tl), mm1, w1)]
			    val k1 = (attach_modifiers_to_body ctx k0 mmx)
			    val ww = (merge_comments ctx w0 w1)
			    val dx = Defvar (v0, q0, k1, c0, a0, ww)
			    val ec = (z0, r0, dx, h0)
			in
			    SOME ec
			end))

	  | Mod_Value _ => raise Match
    end)

fun dispatch_modifiers_to_class skipmain (subj, kp) mm0 = (
    let
	val _ = if (class_is_body kp) then () else raise Match
	val _ = if (step_is_at_least E3 kp) then () else raise Match

	fun dispatch m (e, used) = (
	    case e of
		Import_Clause _ => raise Match
	      | Extends_Clause _ => raise Match
	      | Element_Class (x0 as (z, r, d, h)) => (
		case (associate_to_definition kp x0 m) of
		    NONE => (e, used)
		  | SOME x1 => (Element_Class x1, true))
	      | Element_State (x0 as (z, r, d, h)) => (
		case (associate_to_declaration kp x0 m) of
		    NONE => (e, used)
		  | SOME x1 => (Element_State x1, true))
	      | Redefine_Class _ => (e, used)
	      | Redeclare_State _ => (e, used)
	      | Element_Enumerators _ => (e, used)
	      | Element_Equations _ => (e, used)
	      | Element_Algorithms _ => (e, used)
	      | Element_External _ => (e, used)
	      | Element_Annotation _ => (e, used)
	      | Element_Import _ => (e, used)
	      | Element_Base _ => (e, used)
	      | Base_List _ => (e, used)
	      | Base_Classes _ => (e, used))

	fun dispatch_to_body m ((tag, k0), used0) = (
	    let
		val ee0 = (body_elements k0)
		val (ee1, used1) = (map_along (dispatch m) (ee0, used0))
		val k1 = (replace_body_elements k0 ee1)
	    in
		((tag, k1), used1)
	    end)

	fun dispatch_to_class skipmain m k0 = (
	    let
		val tag = (innate_tag k0)
		val (bases0, k1) = (extract_base_classes false k0)
		val ((_, k2), used0) =
		      if (not skipmain) then
			  (dispatch_to_body m ((tag, k1), false))
		      else
			  ((tag, k1), false)
		val (bases1, used1) =
		      (map_along (dispatch_to_body m) (bases0, used0))
		val k3 = (replace_body_elements
			      k2 ((body_elements k2) @ [Base_Classes bases1]))
	    in
		(k3, used1)
	    end)

	val ctx = kp
	val mm1 = if (class_is_simple_type kp) then
		      (unify_value_and_initializer kp mm0)
		  else
		      mm0
	val (i, mm2) = (split_initializer_value mm1)
	val mm3 = (associate_initializer kp i)
	val mm4 = (merge_modifiers ctx mm2 mm3)
	val k1 = kp

	val (k2, mm5) = (foldl
			     (fn (m, (x0, residue)) =>
				 case (dispatch_to_class skipmain m x0) of
				     (x1, true) => (x1, residue)
				   | (x1, false) => (x1, (residue @ [m])))
			     (k1, []) mm4)
    in
	(k2, mm5)
    end)

(* Associates the given modifiers to class elements.  It works on a
   cooked class, because it is easier to work after gathering all the
   base classes.  It dispatches redeclarations in a definite order,
   first redeclarations in elements, then redeclarations in
   modifiers. *)

fun associate_modifiers k0 mm0 = (
    let
	val _ = tr_cook_vvv (";; associate_modifiers ("^ (class_print_name k0)
			     ^") modifiers="^ (modifier_list_to_string mm0))

	val _ = if ((cook_step k0) = E3) then () else raise Match
	val subj = (subject_of_class k0)
	val k1 = k0

	val (rr0, _) = (extract_redeclares (subj, k1))
	val (k3, rr1) = (dispatch_modifiers_to_class true (subj, k1) rr0)
	val _ = if (null rr1) then () else raise error_modifiers_remain

	val (k4, mm1) = (dispatch_modifiers_to_class false (subj, k3) mm0)
	val _ = if (null mm1) then () else raise error_modifiers_remain
    in
	k4
    end)

(* ================================================================ *)

(* Records a class name in a refining element for each element class.
   This makes easy to obtain a class name in syntaxing.  It should be
   called on a main class after collecting bases. *)

fun record_class_renaming k0 = (
    let
	fun renaming subsubj k = (
	    Def_Refine (k, SOME subsubj, copy_type, no_component_prefixes,
			([], []), NIL, Annotation [], Comment []))

	fun make_class_renaming subsubj k0 = (
	    case k0 of
		Def_Body _ => (*(renaming subsubj k0)*) raise Match
	      | Def_Der _ => (renaming subsubj k0)
	      | Def_Primitive _ => raise Match
	      | Def_Name _ => raise Match
	      | Def_Scoped _ => raise Match
	      | Def_Refine (x0, v_, ts, q, (ss, mm), cc, aa, ww) => (
		let
		    val _ = if (v_ = NONE) then () else raise Match
		in
		    Def_Refine (x0, SOME subsubj, ts, q, (ss, mm), cc, aa, ww)
		end)
	      | Def_Extending (true, _, _) => (renaming subsubj k0)
	      | Def_Extending (false, (kb, mm), x0) => k0
	      | Def_Replaced _ => (renaming subsubj k0)
	      | Def_Displaced _ => k0
	      | Def_In_File => raise Match
	      | Def_Mock_Array _ => raise Match)

	and record_class_renaming_in_element subj e = (
	    case e of
		Import_Clause _ => raise Match
	      | Extends_Clause _ => raise Match
	      | Element_Class (z, r, d0, h) => (
		let
		    val Defclass ((id, g), k0) = d0
		    val subsubj = (compose_subject subj id [])
		    val k1 = (make_class_renaming subsubj k0)
		    val d1 = Defclass ((id, g), k1)
		in
		    Element_Class (z, r, d1, h)
		end)
	      | Element_State _ => e
	      | Redefine_Class (z, r, d0, h) => (
		let
		    val Defclass ((id, g), k0) = d0
		    val subsubj = (compose_subject subj id [])
		    val k1 = (make_class_renaming subsubj k0)
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
	      | Element_Import _ => e
	      | Element_Base _ => e
	      | Base_List _ => e
	      | Base_Classes bb0 => (
		let
		    val bb1 = (map (fn (c, kx) =>
				       (c, (record_class_renaming kx)))
				   bb0)
		in
		    Base_Classes bb1
		end))

	val subj = (subject_of_class k0)
	val ee0 = (body_elements k0)
	val ee1 = (map (record_class_renaming_in_element subj) ee0)
	val k1 = (replace_body_elements k0 ee1)
    in
	k1
    end)

(* Makes final-touches to a modified class. *)

fun rectify_modified_class (k0, q1) (t1, p1) aa1 = (
    case k0 of
	Def_Body (mk, subj, (t0, p0, q0), nm, cc, ee, aa0, ww0) => (
	let
	    val ctx = k0
	    val (tx, px) = (merge_type_prefixes (t0, p0) (t1, p1))
	    val qx = (merge_component_prefixes q0 q1)
	    val aax = (merge_annotations ctx aa0 aa1)
	    val k1 = Def_Body (mk, subj, (tx, px, qx), nm, cc, ee, aax, ww0)
	    val k2 = if (class_is_main k0) then
			 (record_class_renaming k1)
		     else
			 k1
	in
	    k2
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
      | Def_Mock_Array _ => raise Match)

end
