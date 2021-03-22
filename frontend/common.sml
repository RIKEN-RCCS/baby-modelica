(* common.sml -*-Coding: us-ascii-unix;-*- *)
(* Copyright (C) 2018-2021 RIKEN R-CCS *)

(* SMALL COMMON ROUTINES. *)

structure common = struct

open plain
open ast

(* Prints a trace message. *)

fun tr_tree (s : string) = if true then (print (s ^"\n")) else ()
fun tr_tree_vvv (s : string) = if false then (print (s ^"\n")) else ()

(* ================================================================ *)

type cooker_t =
       cook_step_t -> (subject_t * definition_body_t) -> definition_body_t

(* component_slot_t is a component as a tuple of a name, a dimension,
   and an array of entries of the size.  An optional definition exists
   only when the array is empty for retaining the type information. *)

datatype component_slot_t
    = Slot of (id_t * int list * instance_node_t list
	       * definition_body_t option)

(* instance_node_t represents a node in the instance_tree.  It is a
   pair of a class definition and its elements/components associated
   by names.  Each node is a pair of references and updated by effect.
   Note that the instance_tree is modified at the leaves, because
   creation of instances is started at the root and develops towards
   its components. *)

withtype instance_node_t
	 = (subject_t * definition_body_t ref * component_slot_t list ref)

(* The model-root is unnamed. *)

val the_model_subject = Subj (VAR, [])

(* The package-root is the unnamed-enclosing-class, where the_root_tag
   and the_root_subject are synonymous. *)

val the_root_subject = Subj (PKG, [])
val the_root_tag = Ctag []
val root_class_print_name = "(*root*)"

val the_root_class = Def_Body ((E5, PKG, MAIN),
			       the_root_subject,
			       (Package, no_class_prefixes,
				no_component_prefixes),
			       (the_root_tag, the_root_subject,
				the_root_subject),
			       NIL,
			       [], Annotation [], Comment [])

val the_root_class_definition =
      Defclass ((Id root_class_print_name, bad_tag), the_root_class)

fun void_predefined_body x = (
    ((Id x, the_root_tag), Def_Displaced (bad_tag, bad_subject)))

(* predefined_types are classes in "predefined.mo".  It needs to keep
   correspondenece to the file.  See (4.8 Predefined Types and
   Classes). *)

val predefined_types = [
    Defclass (void_predefined_body "Real"),
    Defclass (void_predefined_body "Integer"),
    Defclass (void_predefined_body "Boolean"),
    Defclass (void_predefined_body "String"),
    Defclass (void_predefined_body "StateSelect"),
    Defclass (void_predefined_body "AssertionLevel"),
    Defclass (void_predefined_body "Clock"),
    (* Below are not defined in "redefined.mo" *)
    Defclass (void_predefined_body "ExternalObject"),
    Defclass (void_predefined_body "Connections")]

val the_real_class = Def_Displaced (Ctag ["Real"], the_root_subject)

val the_integer_class = Def_Displaced (Ctag ["Integer"], the_root_subject)

val predefined_variables = [
    Defvar (Id "time", (Effort, Continuous, Modeless),
	    the_real_class, NONE, Annotation [], Comment []),
    Defvar (Id "end", (Effort, Continuous, Modeless),
	    the_integer_class, NONE, Annotation [], Comment [])]

val predefined_function_names = [
    "abs",
    "sign",
    "sqrt",
    "div",
    "mod",
    "rem",
    "ceil",
    "floor",
    "integer",
    "sin",
    "cos",
    "tan",
    "asin",
    "acos",
    "atan",
    "atan2",
    "sinh",
    "cosh",
    "tanh",
    "exp",
    "log",
    "log10",
    "delay",
    "cardinality",
    "homotopy",
    "semiLinear",
    "inStream",
    "actualStream",
    "spatialDistribution",
    "getInstanceName",
    "homotopy",
    "initial",
    "terminal",
    "noEvent",
    "smooth",
    "sample",
    "pre",
    "edge",
    "change",
    "reinit",
    "assert",
    "terminate",
    "promote",
    "ndims",
    "size",
    "scalar",
    "vector",
    "matrix",
    "identity",
    "diagonal",
    "zeros",
    "ones",
    "fill",
    "linspace",
    "min",
    "max",
    "sum",
    "product",
    "transpose",
    "outerProduct",
    "symmetric",
    "cross",
    "skew",
    "cat",
    "previous",
    "hold",
    "subSample",
    "superSample",
    "shiftSample",
    "backSample",
    "noClock",
    "firstTick",
    "interval",
    "transition",
    "initialState",
    "activeState",
    "ticksInState",
    "timeInState"]

(* ================================================================ *)

val error_non_integer_value = Match
val error_non_constant_value = Match

(* Converts a literal constant to an int value. *)

fun literal_to_int w = (
    case w of
	L_Number (_, s) => (
	case (string_is_int s) of
	    NONE => raise error_non_integer_value
	  | SOME v => v)
      | _ => raise error_non_constant_value)

(* (Note that Real.fromString parses the prefix of s). *)

fun r_value s = (
    case (Real.fromString s) of
	SOME x => x
      | NONE => raise Match)

fun z_value s = (
    case (Int.fromString s) of
	SOME x => x
      | NONE => raise Match)

fun r_literal x = (
    L_Number (R, (Real.toString x)))

fun z_literal x = (
    L_Number (Z, (Int.toString x)))

fun literal_to_bool w = (
    case w of
	L_Bool b => b
      | _ => raise error_non_constant_value)

(* ================================================================ *)

fun id_to_string ((Id s) : id_t) : string = s

(* Returns a string for a qualified-name. *)

fun name_to_string (Name nn) : string = (
    case nn of
	[] => "(*empty*)"
      | [""] => (root_class_print_name)
      | ss => ((String.concatWith ".") ss))

fun tag_to_string (Ctag vv) = (name_to_string (Name ("" :: vv)))

fun tag_of_definition (Defclass ((v, g), b)) = (qualify_name (v, g))

fun class_name_id (Defclass ((v, g), b)) = v

fun name_of_definition (d as Defclass ((v, g), k)) = (
    (tag_to_string (tag_of_definition d)))

(* Prefixes subject parts by a dot for the package-root. *)

fun attach_dot_of_package_root ns cc = (
    if (ns = PKG) then
	(Id "", []) :: cc
    else
	cc)

(* Removes a dot prefix in the package reference parts. *)

fun drop_dot_of_package_root ns cc0 = (
    if (ns = PKG) then
	case cc0 of
	    (Id "", []) :: cc1 => cc1
	  | _ => raise Match
    else
	case cc0 of
	    (Id "", []) :: cc1 => raise Match
	  | _ => cc0)

fun subject_to_string (Subj (ns, cc0)) = (
    let
	val cc1 = (attach_dot_of_package_root ns cc0)
    in
	((String.concatWith ".")
	     (map (fn (v, ss) => (
		       case ss of
			   [] => (id_to_string v)
			 | _ => (
			   let
			       val ee = (String.concatWith
					     "," (map Int.toString ss))
			   in
			       ((id_to_string v) ^ "["^ ee ^"]")
			   end)))
		  cc1))
    end)

fun subject_print_string (Subj (ns, cc0)) = (
    let
	val cc1 = (attach_dot_of_package_root ns cc0)
    in
	((String.concatWith ".")
	     (map (fn (v, ss) => (
		       case ss of
			   [] => (id_to_string v)
			 | _ => ((id_to_string v) ^ "[]")))
		  cc1))
    end)

fun subject_as_reference (Subj (ns, cc0)) = (
    let
	fun mapr f (x0, x1) = (x0, (f x1))
    in
	Vref (SOME ns, (map (mapr (map z_literal)) cc0))
    end)

fun path_of_reference w = (
    case w of
	Vref (_, rr) => rr
      | _ => raise Match)

(* Checks if a class is in a processed form, which can appear in the
   instance_tree.  The other forms are syntactic.  Def_Primitive only
   appears in the instance_tree as an enumerator. *)

fun assert_proper_class (k : definition_body_t) = (
    case k of
	Def_Body _ => ()
      | Def_Der _ => ()
      | Def_Primitive _ => ()
      | Def_Outer_Alias _ => raise Match
      | Def_Name _ => raise Match
      | Def_Scoped _ => raise Match
      | Def_Refine _ => raise Match
      | Def_Extending _ => raise Match
      | Def_Replaced _ => raise Match
      | Def_Displaced _ => raise Match
      | Def_In_File => raise Match
      | Def_Mock_Array _ => raise Match)

(* ================================================================ *)

(* Returns the elaboration step.  It returns E0 for syntactic entries
   (Def_Replaced, etc).  Enumerators are represented by Def_Primitive
   and are stored in the instance_tree, thus, its step is E5. *)

fun cook_step (k : definition_body_t) = (
    case k of
	Def_Body ((u, f, b), j, cs, nm, cc, ee, aa, ww) => u
      | Def_Der _ => E5
      | Def_Primitive _ => E5 (*raise Match*)
      | Def_Outer_Alias _ => E5
      | Def_Name _ => E0
      | Def_Scoped _ => E0
      | Def_Refine _ => E0
      | Def_Extending _ => raise Match
      | Def_Replaced _ => E0
      | Def_Displaced _ => E0 (*raise Match*)
      | Def_In_File => raise Match
      | Def_Mock_Array _ => raise Match)

fun set_cook_step step (k : definition_body_t) = (
    case k of
	Def_Body ((u_, f, b), j, cs, nm, cc, ee, aa, ww) => (
	Def_Body ((step, f, b), j, cs, nm, cc, ee, aa, ww))
      | Def_Der _ => k
      | Def_Primitive _ => raise Match
      | Def_Outer_Alias _ => raise Match
      | Def_Name _ => k
      | Def_Scoped _ => raise Match
      | Def_Refine _ => k
      | Def_Extending _ => raise Match
      | Def_Replaced _ => raise Match
      | Def_Displaced _ => raise Match
      | Def_In_File => raise Match
      | Def_Mock_Array _ => raise Match)

fun cook_step_order step = (
    case step of
	E0 => 0
      | E1 => 1
      | E2 => 2
      | E3 => 3
      | E4 => 4
      | E5 => 5)

fun step_is_less step k = (
    (cook_step_order (cook_step k)) < (cook_step_order step))

fun step_is_at_least step k = (not (step_is_less step k))

fun step_compare s0 r s1 = (r ((cook_step_order s0), (cook_step_order s1)))

fun cook_step_to_string E0 = "E0"
  | cook_step_to_string E1 = "E1"
  | cook_step_to_string E2 = "E2"
  | cook_step_to_string E3 = "E3"
  | cook_step_to_string E4 = "E4"
  | cook_step_to_string E5 = "E5"

(* ================================================================ *)

(* True if definitions can be displaced. *)

fun definition_is_displaceable (Defclass ((v, g), k)) = (
    case k of
	Def_Body _ => true
      | Def_Der _ => false
      | Def_Primitive _ => raise Match
      | Def_Outer_Alias _ => raise Match
      | Def_Name _ => false
      | Def_Scoped _ => raise Match
      | Def_Refine _ => false
      | Def_Extending _ => false
      | Def_Replaced _ => false
      | Def_Displaced _ => raise Match
      | Def_In_File => raise Match
      | Def_Mock_Array _ => raise Match)

fun class_is_body k = (
    case k of
	Def_Body _ => true
      | Def_Der _ => false
      | Def_Primitive _ => raise Match
      | Def_Outer_Alias _ => raise Match
      | Def_Name _ => false
      | Def_Scoped _ => false
      | Def_Refine _ => false
      | Def_Extending _ => false
      | Def_Replaced _ => false
      | Def_Displaced _ => false
      | Def_In_File => raise Match
      | Def_Mock_Array _ => raise Match)

fun class_is_refining k0 = (
    case k0 of
	Def_Body _ => false
      | Def_Der _ => false
      | Def_Primitive _ => false
      | Def_Outer_Alias _ => raise Match
      | Def_Name _ => false
      | Def_Scoped _ => false
      | Def_Refine _ => true
      | Def_Extending _ => raise Match
      | Def_Replaced (k1, _) => (class_is_refining k1)
      | Def_Displaced _ => raise Match
      | Def_In_File => raise Match
      | Def_Mock_Array _ => raise Match)

fun body_is_displaced k = (
    case k of
	Def_Body _ => false
      | Def_Der _ => false
      | Def_Primitive _ => raise Match
      | Def_Outer_Alias _ => raise Match
      | Def_Name _ => false
      | Def_Scoped _ => false
      | Def_Refine _ => false
      | Def_Extending _ => false
      | Def_Replaced _ => false
      | Def_Displaced _ => true
      | Def_In_File => false
      | Def_Mock_Array _ => raise Match)

fun body_is_in_file k = (
    case k of
	Def_Body _ => false
      | Def_Der _ => false
      | Def_Primitive _ => raise Match
      | Def_Outer_Alias _ => raise Match
      | Def_Name _ => false
      | Def_Scoped _ => false
      | Def_Refine _ => false
      | Def_Extending _ => false
      | Def_Replaced _ => false
      | Def_Displaced _ => false
      | Def_In_File => true
      | Def_Mock_Array _ => raise Match)

(* Tests if a class is an enumeration (definition) or an enumerator
   (variable).  To discriminate them further, it is a definition when
   it is a package or a variable when it is an instance *)

fun class_is_enum k = (
    case k of
	Def_Body ((u, f, enum), j, cs, nm, cc, ee, aa, ww) => (enum = ENUM)
      | Def_Der _ => raise Match
      | Def_Primitive _ => raise Match
      | Def_Outer_Alias _ => raise Match
      | Def_Name _ => raise Match
      | Def_Scoped _ => raise Match
      | Def_Refine _ => raise Match
      | Def_Extending _ => raise Match
      | Def_Replaced _ => raise Match
      | Def_Displaced _ => raise Match
      | Def_In_File => raise Match
      | Def_Mock_Array _ => raise Match)

fun assert_class_is_body k = (
    case k of
	Def_Body _ => ()
      | _ => raise Match)

(* Tests if a class is a dummy definition. *)

fun class_is_displaced (Defclass ((v, g), k)) = (body_is_displaced k)

fun class_is_in_file (Defclass ((v, g), k)) = (body_is_in_file k)

fun tag_is_root tag = (
    case tag of
	Ctag [""] => raise Match
      | Ctag [] => true
      | Ctag _ => false)

(* Tests if a class is a record of an inner-outer matching. *)

fun class_is_outer_alias k = (
    case k of
	Def_Body _ => false
      | Def_Der _ => false
      | Def_Primitive _ => false
      | Def_Outer_Alias _ => true
      | Def_Name _ => raise Match
      | Def_Scoped _ => raise Match
      | Def_Refine _ => raise Match
      | Def_Extending _ => raise Match
      | Def_Replaced _ => raise Match
      | Def_Displaced _ => raise Match
      | Def_In_File => raise Match
      | Def_Mock_Array _ => raise Match)

(* ================================================================ *)

fun assert_proper_subject subj = (subj <> bad_subject)

(* (It prints a subject in a subtype relation, because a subject
   cannot tell the subtype and object-type relations). *)

fun subject_and_tag_to_string (s : subject_t, ks : string) suffix = (
    let
	val qs = quote_string
	val ss = (subject_print_string s)
    in
	if (ss = ks) then
	    ("* : "^ (qs ss) ^ suffix)
	else
	    ((qs ss) ^" <: "^ (qs ks) ^ suffix)
    end)

fun subject_tag_to_string ((s : subject_t, k : class_tag_t) : scope_t) = (
    (subject_and_tag_to_string (s, (tag_to_string k)) ""))

(* Returns an approximate class print-name. *)

fun class_print_name k = (
    case k of
	Def_Body (mk, j, cs, (tag, c, x), cc, ee, aa, ww) =>
	if (class_is_enum k) then
	    ("enum ("^ (tag_to_string tag) ^")")
	else
	    (tag_to_string tag)
      | Def_Der (tag, cs, n, vv, aa, ww) => (
	"der ("^ (tag_to_string tag) ^")")
      | Def_Primitive (p, _) => "primitive"
      | Def_Outer_Alias (f, subj, _) => (subject_to_string subj)
      | Def_Name n => (name_to_string n)
      | Def_Scoped (n, s) => (
	("("^ (name_to_string n) ^" in "^
	 (subject_tag_to_string s) ^")"))
      | Def_Refine (kx, v, ts, q, (ss, mm), cc, aa, ww) => (class_print_name kx)
      | Def_Extending (_, x, kx) => (class_print_name kx)
      | Def_Replaced (kx, _) => (class_print_name kx)
      | Def_Displaced (tag, _) => (tag_to_string tag)
      | Def_In_File => raise Match
      | Def_Mock_Array _ => raise Match)

(* Replaces subscripts in a subject or a reference.  It drops with
   both subscript expressions and integers. *)

fun pseudo_reference_path path = (
    (map (fn (id, ss) => (id, [])) path))

fun drop_subscripts rr = (
    (map (fn (id, _) => id) rr))

(* Returns a variable after dropping all subscripts.  The result is
   not a proper variable reference. *)

fun pseudo_variable x = (
    case x of
	Vref (SOME VAR, rr) => Subj (VAR, (map (fn (id, _) => (id, [])) rr))
      | _ => raise Match)

(* Returns components of a subject as a list of IDs. *)

fun pseudo_path subj = (
    case subj of
	Subj (VAR, cc) => (map (fn (id, _) => id) cc)
  | _ => raise Match)

fun body_name_at_step k = (
    (class_print_name k) ^"@"^ (cook_step_to_string (cook_step k)))

fun subject_body_to_string (s : subject_t, k : definition_body_t) = (
    let
	val suffix = (" @"^ (cook_step_to_string (cook_step k)))
    in
	(subject_and_tag_to_string (s, (class_print_name k)) suffix)
    end)

(* ================================================================ *)

(* Tests if a class is a package, otherwise it is an instance.  Note
   that an instance is processed as a package in early stages, but
   this test is precise for a class stored in the instance_tree. *)

fun class_is_package k = (
    case k of
	Def_Body ((u, f, b), j, cs, nm, cc, ee, aa, ww) => (f = PKG)
      | Def_Der _ => false
      | Def_Primitive _ => false
      | Def_Outer_Alias (f, _, _) => (f = PKG)
      | Def_Name _ => raise Match
      | Def_Scoped _ => raise Match
      | Def_Refine _ => raise Match
      | Def_Extending _ => raise Match
      | Def_Replaced _ => raise Match
      | Def_Displaced _ => raise Match
      | Def_In_File => raise Match
      | Def_Mock_Array _ => raise Match)

fun class_is_instance k = (not (class_is_package k))

fun class_is_function k = (
    case k of
	Def_Body ((u, f, b), j, (t, p, q), nm, cc, ee, aa, ww) => (
	case t of
	    Function pure => (true, pure)
	  | _ => (false, false))
      | Def_Der _ => (false, false)
      | Def_Primitive _ => (false, false)
      | Def_Outer_Alias _ => raise Match
      | Def_Name _ => raise Match
      | Def_Scoped _ => raise Match
      | Def_Refine _ => raise Match
      | Def_Extending _ => raise Match
      | Def_Replaced _ => raise Match
      | Def_Displaced _ => raise Match
      | Def_In_File => raise Match
      | Def_Mock_Array _ => raise Match)

(* ================================================================ *)

fun declaration_to_string (d as Defvar (v, q, k, c, a, w)) = (
    ("("^ (id_to_string v) ^" : "^ (class_print_name k) ^")"))

fun modifier_to_string m = (
    case m of
	Mod_Redefine (r, d, h) => (
	case d of
	    Defclass ((v, g), k) => (
	    ((id_to_string v) ^"="^ (class_print_name k))))
      | Mod_Elemental_Redefine (z, r, d, h) => (
	case d of
	    Defclass ((v, g), k) => (
	    ((id_to_string v) ^"="^ (class_print_name k))))
      | Mod_Redeclare (r, d, h) => (
	case d of
	    Defvar (v, q, k, c, a, w) => (
	    ((id_to_string v) ^":"^ (class_print_name k))))
      | Mod_Elemental_Redeclare (z, r, d, h) => (
	case d of
	    Defvar (v, q, k, c, a, w) => (
	    ((id_to_string v) ^":"^ (class_print_name k))))
      | Mod_Entry (ef, n, mm, w) => (
	((name_to_string n) ^"="^ (modifier_list_to_string mm)))
      | Mod_Value e0 => "value=<expr>")

and modifier_list_to_string mm = (
    "{"^ ((String.concatWith ", ") (map modifier_to_string mm)) ^"}")

fun subscript_list_to_string ss = (
    (String.concat (map (fn _ => "[]") ss)))

fun body_is_root k = (
    case k of
	Def_Body (mk, j, cs, (tag, n, x), cc, ee, aa, ww) => (
	(tag = the_root_tag))
      | Def_Der _ => raise Match
      | Def_Primitive _ => raise Match
      | Def_Outer_Alias _ => raise Match
      | Def_Name _ => raise Match
      | Def_Scoped _ => raise Match
      | Def_Refine _ => raise Match
      | Def_Extending _ => raise Match
      | Def_Replaced _ => raise Match
      | Def_Displaced _ => raise Match
      | Def_In_File => raise Match
      | Def_Mock_Array _ => raise Match)

fun class_is_root_body k = (
    case k of
	Def_Body _ => (body_is_root k)
      | Def_Der _ => false
      | Def_Primitive _ => raise Match
      | Def_Outer_Alias _ => raise Match
      | Def_Name _ => false
      | Def_Scoped _ => false
      | Def_Refine _ => false
      | Def_Extending _ => false
      | Def_Replaced _ => false
      | Def_Displaced _ => false
      | Def_In_File => false
      | Def_Mock_Array _ => raise Match)

fun variability_order v = (
    case v of
	Continuous => 3
      | Discrete => 2
      | Parameter => 1
      | Constant => 0)

fun name_of_element_union cv = (
    case cv of
	EL_Class (Defclass ((v, _), _)) => v
      | EL_State (Defvar (v, _, _, _, _, _)) => v)

(*val name_of_naming = name_of_element_union*)

(* Some characters in identifiers need be protected (escaped), that
   is, {"@", ".", "%"}.  "@" and "." are internally used as
   separators, "%" is used for escaping.  Other characters may be
   escaped for clean printing. *)

val escape_char = Char.toString

fun escape_string s = (String.translate escape_char s)

fun unescape_string s = raise Match

(* Returns the prefix and the last part of a tag.  Note that the
   returned pair is swapped.  Its inverse is qualify_name. *)

fun tag_prefix (Ctag nn) : (id_t * class_tag_t) = (
    let
	val _ = if ((Ctag nn) <> bad_tag) then () else raise Match
	val (prefix, n) = (split_last nn)
    in
	(Id n, Ctag prefix)
    end)

fun subject_prefix (Subj (ns, cc)) = (
    let
	val (prefix, c) = (split_last cc)
    in
	(Subj (ns, prefix), c)
    end)

fun compose_subject (Subj (ns, cc)) (Id v) (index : int list) = (
    Subj (ns, cc @ [(Id v, index)]))

fun compose_subject_with_index subj0 (index : int list) = (
    let
	val (prefix, (v, ss0)) = (subject_prefix subj0)
	val ss1 = (merge_subscripts index ss0)
	val subj1 = (compose_subject prefix v ss1)
    in
	subj1
    end)

fun tag_to_subject (Ctag nn) = (
    Subj (PKG, (map (fn v => (Id v, [])) nn)))

(* Tests if a subject has no subscripts. *)

fun subject_has_subscripts (Subj (ns, cc)) = (
    (List.exists (fn (v, ss) => (not (null ss))) cc))

(* Checks if a subject has no subscripts. *)

fun assert_subject_has_no_subscripts subj = (
    if (not (subject_has_subscripts subj)) then () else raise Match)

(* Checks if the last part of a subject has no subscripts. *)

fun assert_subject_is_not_array subj = (
    case subj of
	Subj (ns, []) => ()
      | Subj (ns, cc) => (
	let
	    val (prefix, (v, ss)) = (split_last cc)
	    val _ = if (null ss) then () else raise Match
	in
	    ()
	end))

(* Simply converts a subject to a class-tag.  It assumes a given
   subject refers to a package (a class that is not an instance).
   Care should be taken because it may return a tag of a (lexically)
   non-existing class. *)

fun subject_to_tag subj = (
    case subj of
	Subj (VAR, _) => NONE
      | Subj (PKG, cc) => (
	if (subject_has_subscripts subj) then
	    NONE
	else
	    SOME (Ctag (map (fn (Id v, ss) => v) cc))))

fun tag_as_displaced_class tag = (
    let
	val (v, g) = (tag_prefix tag)
	val subj = (tag_to_subject tag)
	val (enclosing, _) = (subject_prefix subj)
    in
	Defclass ((v, g), Def_Displaced (tag, enclosing))
    end)

fun marker_of_body k = (
    case k of
	Def_Body ((u, f, b), j, cs, nm, cc, ee, aa, ww) => b
      | Def_Der _ => raise Match
      | Def_Primitive _ => raise Match
      | Def_Outer_Alias _ => raise Match
      | Def_Name _ => raise Match
      | Def_Scoped _ => raise Match
      | Def_Refine _ => raise Match
      | Def_Extending _ => raise Match
      | Def_Replaced _ => raise Match
      | Def_Displaced _ => raise Match
      | Def_In_File => raise Match
      | Def_Mock_Array _ => raise Match)

fun subject_of_class k = (
    case k of
	Def_Body (mk, subj, cs, nm, cc, ee, aa, ww) => (
	if (subj = bad_subject) then
	    raise Match
	else
	    subj)
      | Def_Der _ => raise Match
      | Def_Primitive (P_Enum tag0, L_Enum (tag1, v)) => (
	let
	    val _ = if (tag0 = tag1) then () else raise Match
	    val subj = (tag_to_subject (qualify_name (v, tag1)))
	in
	    subj
	end)
      | Def_Primitive _ => raise Match
      | Def_Outer_Alias (f, subj, _) => subj
      | Def_Name _ => raise Match
      | Def_Scoped _ => raise Match
      | Def_Refine _ => raise Match
      | Def_Extending _ => raise Match
      | Def_Replaced _ => raise Match
      | Def_Displaced _ => raise Match
      | Def_In_File => raise Match
      | Def_Mock_Array _ => raise Match)

fun naming_of_class k = (
    case k of
	Def_Body (mk, subj, cs, (tag, c, x), cc, ee, aa, ww) => (
	if (subj = bad_subject orelse tag = bad_tag) then
	    raise Match
	else
	    (subj, tag))
      | Def_Der _ => raise Match
      | Def_Primitive _ => raise Match
      | Def_Outer_Alias _ => raise Match
      | Def_Name _ => raise Match
      | Def_Scoped _ => raise Match
      | Def_Refine _ => raise Match
      | Def_Extending _ => raise Match
      | Def_Replaced _ => raise Match
      | Def_Displaced _ => raise Match
      | Def_In_File => raise Match
      | Def_Mock_Array _ => raise Match)

fun enclosing_of_body k = (
    case k of
	Def_Body (mk, j, cs, (c, n, enclosing), cc, ee, aa, ww) => (
	let
	    val _ = if (enclosing <> bad_subject) then () else raise Match
	in
	    enclosing
	end)
      | Def_Der _ => raise Match
      | Def_Primitive _ => raise Match
      | Def_Outer_Alias _ => raise Match
      | Def_Name _ => raise Match
      | Def_Scoped _ => raise Match
      | Def_Refine _ => raise Match
      | Def_Extending _ => raise Match
      | Def_Replaced _ => raise Match
      | Def_Displaced _ => raise Match
      | Def_In_File => raise Match
      | Def_Mock_Array _ => raise Match)

fun identity_name_of_body k = (
    case k of
	Def_Body (mk, j, cs, (c, naming, e), cc, ee, aa, ww) => (
	let
	    val _ = if (naming <> bad_subject) then () else raise Match
	in
	    naming
	end)
      | Def_Der _ => raise Match
      | Def_Primitive _ => raise Match
      | Def_Outer_Alias _ => raise Match
      | Def_Name _ => raise Match
      | Def_Scoped _ => raise Match
      | Def_Refine _ => raise Match
      | Def_Extending _ => raise Match
      | Def_Replaced _ => raise Match
      | Def_Displaced _ => raise Match
      | Def_In_File => raise Match
      | Def_Mock_Array _ => raise Match)

(* Records a defining class to a definition body, which indicates
   where the body is defined.  It is used to obtain an enclosing
   class, (which is the prefix of the subject).  This assignment takes
   place when a lookup finds a class that is a definition body.  Note
   that a defining class can be either a package or an instance, thus,
   it is named by a subject. *)

fun assign_enclosing k enclosing = (
    case k of
	Def_Body (mk, j, cs, (c, n, enc_), cc, ee, aa, ww) => (
	let
	    val _ = if ((cook_step k) = E0) then () else raise Match
	    val _ = if (enclosing <> bad_subject) then () else raise Match
	    val _ = if (enc_ = bad_subject) then () else raise Match
	in
	    Def_Body (mk, j, cs, (c, n, enclosing), cc, ee, aa, ww)
	end)
      | Def_Der _ => k
      | Def_Primitive _ => raise Match
      | Def_Outer_Alias _ => raise Match
      | Def_Name _ => k
      | Def_Scoped _ => k
      | Def_Refine _ => k
      | Def_Extending _ => k
      | Def_Replaced _ => k
      | Def_Displaced (tag, enc) => (
	let
	    val _ = if (enclosing <> bad_subject) then () else raise Match
	    val _ = if (enc = bad_subject) then () else raise Match
	in
	    Def_Displaced (tag, enclosing)
	end)
      | Def_In_File => raise Match
      | Def_Mock_Array _ => raise Match)

fun class_is_main k = ((marker_of_body k) <> BASE)

fun class_is_enumeration_definition k = (
    (class_is_enum k) andalso (class_is_package k))

(* Tests if a class is an enumerator definition in the instance_tree.
   See register_enumerators_for_enumeration. *)

fun class_is_enumerator_definition k = (
    case k of
	Def_Body _ => false
      | Def_Der _ => false
      | Def_Primitive (P_Enum tag_, L_Enum (tag, v)) => true
      | Def_Primitive _ => false
      | Def_Outer_Alias _ => false
      | Def_Name _ => raise Match
      | Def_Scoped _ => raise Match
      | Def_Refine _ => raise Match
      | Def_Extending _ => raise Match
      | Def_Replaced _ => raise Match
      | Def_Displaced _ => raise Match
      | Def_In_File => raise Match
      | Def_Mock_Array _ => raise Match)

(* Tests if a class is an (internal) primitive type. *)

fun class_is_primitive k = (
    case k of
	Def_Body _ => false
      | Def_Der _ => false
      | Def_Primitive _ => true
      | Def_Outer_Alias _ => raise Match
      | Def_Name _ => raise Match
      | Def_Scoped _ => raise Match
      | Def_Refine _ => raise Match
      | Def_Extending _ => raise Match
      | Def_Replaced _ => raise Match
      | Def_Displaced _ => raise Match
      | Def_In_File => raise Match
      | Def_Mock_Array _ => raise Match)

(* Tests if a class is a simple-type, that is, Real, Integer, Boolean,
   String, enumerations, types extending them, and arrays of them. *)

fun class_is_simple_type k = (
    let
	fun tag_is_simple_type tag = (
	    case tag of
		Ctag [""] => raise Match
	      | Ctag [] => false
	      | Ctag ["Real"] => true
	      | Ctag ["Integer"] => true
	      | Ctag ["Boolean"] => true
	      | Ctag ["String"] => true
	      | _ => false)
    in
	case k of
	    Def_Body (mk, j, cs, (tag, n, x), cc, ee, aa, ww) => (
	    let
		(*val _ = if (step_is_at_least E2 k) then () else raise Match*)
	    in
		(class_is_enum k) orelse (tag_is_simple_type tag)
	    end)
	  | Def_Der _ => false
	  | Def_Primitive _ => true
	  | Def_Outer_Alias _ => raise Match
	  | Def_Name _ => raise Match
	  | Def_Scoped _ => raise Match
	  | Def_Refine (kx, v, ts, q, (ss, mm), cc, aa, ww) => (
	    (class_is_simple_type kx))
	  | Def_Extending _ => raise Match
	  | Def_Replaced _ => raise Match
	  | Def_Displaced (tag, _) => (tag_is_simple_type tag)
	  | Def_In_File => raise Match
	  | Def_Mock_Array _ => raise Match
    end)

fun class_is_boolean k = (
    case k of
	Def_Body (mk, j, cs, (tag, n, x), cc, ee, aa, ww) => (
	let
	    val _ = if (step_is_at_least E3 k) then () else raise Match
	in
	    (tag = Ctag ["Boolean"])
	end)
      | Def_Der _ => false
      | Def_Primitive _ => false
      | _ => raise Match)

fun kind_of_class k = (
    case k of
	Def_Body (mk, j, (kind, p, q), nm, cc, ee, aa, ww) => SOME kind
      | Def_Der _ => NONE
      | Def_Primitive _ => NONE
      | Def_Outer_Alias _ => raise Match
      | Def_Name _ => raise Match
      | Def_Scoped _ => raise Match
      | Def_Refine _ => raise Match
      | Def_Extending _ => raise Match
      | Def_Replaced _ => raise Match
      | Def_Displaced _ => raise Match
      | Def_In_File => raise Match
      | Def_Mock_Array _ => raise Match)

(* Note functions never have instances. *)

fun kind_is_function k = (
    case (kind_of_class k) of
	SOME (Function _) => (
	    let
		val _ = if (class_is_package k) then () else raise Match
	    in
		true
	    end)
      | _ => false)

fun kind_is_record k = (
    case (kind_of_class k) of
	SOME Record => true
      | _ => false)

(* Tests if a class definition is not modified.  A reference in a
   package in an instance (such as "x.P1.c") can be simplified as one
   in a fully-qualified package ("P0.P1.c"). *)

fun class_is_unmodified k = raise Match

fun class_name_of_instance k = (
    case k of
	Def_Body (mk, j, cs, (tag, name, enclosing), cc, ee, aa, ww) => name
      | Def_Der _ => raise Match
      | Def_Primitive _ => raise Match
      | Def_Outer_Alias _ => raise Match
      | Def_Name _ => raise Match
      | Def_Scoped _ => raise Match
      | Def_Refine _ => raise Match
      | Def_Extending _ => raise Match
      | Def_Replaced _ => raise Match
      | Def_Displaced _ => raise Match
      | Def_In_File => raise Match
      | Def_Mock_Array _ => raise Match)

(* Tests a class is a connector.  It only returns true on expandable
   connectors when expandable=true. *)

fun class_is_connector expandable k = (
    case k of
	Def_Body (mk, j, (t, p, q), nm, cc, ee, aa, ww) => (
	case t of
	    Connector x => ((not expandable) orelse x)
	  | _ => false)
      | Def_Der _ => false
      | Def_Primitive _ => false
      | Def_Outer_Alias _ => raise Match
      | Def_Name _ => raise Match
      | Def_Scoped _ => raise Match
      | Def_Refine _ => raise Match
      | Def_Extending _ => raise Match
      | Def_Replaced _ => raise Match
      | Def_Displaced _ => raise Match
      | Def_In_File => raise Match
      | Def_Mock_Array (_, [], SOME x) => (class_is_connector expandable x)
      | Def_Mock_Array (_, array, dummy) => (
	(List.all (class_is_connector expandable) array)))

(* Tests a variable is a non-array. *)

fun variable_is_monomer k = (
    case k of
	Def_Body _ => true
      | Def_Der _ => true
      | Def_Primitive _ => true
      | Def_Outer_Alias _ => raise Match
      | Def_Name _ => raise Match
      | Def_Scoped _ => raise Match
      | Def_Refine _ => raise Match
      | Def_Extending _ => raise Match
      | Def_Replaced _ => raise Match
      | Def_Displaced _ => raise Match
      | Def_In_File => raise Match
      | Def_Mock_Array _ => false)

fun variable_is_simple_type k = (
    case k of
	Def_Body _ => (class_is_enum k) orelse (class_is_simple_type k)
      | Def_Der _ => false
      | Def_Primitive _ => raise Match
      | Def_Outer_Alias _ => raise Match
      | Def_Name _ => raise Match
      | Def_Scoped _ => raise Match
      | Def_Refine _ => raise Match
      | Def_Extending _ => raise Match
      | Def_Replaced _ => raise Match
      | Def_Displaced _ => raise Match
      | Def_In_File => raise Match
      | Def_Mock_Array _ => false)

(* Returns true if a subject j0 contains j1 as a subcomponet (that is,
   a.b is a supersubject of a.b.c) or identical. *)

fun subject_is_prefix j0 j1 = (
    case (j0, j1) of
	(Subj (VAR, rr0), Subj (VAR, rr1)) => (
	(list_prefix (op =) rr0 rr1))
      | _ => raise Match)

fun subject_is_component subj0 subj1 = (
    (subject_is_prefix subj1 subj0))

(* Chooses a non-nil expression, or errs if both are non-nil. *)

fun choose_non_nil x0 x1 = (
    let
	val _ = if (x0 = NIL orelse x1 = NIL) then () else raise Match
    in
	if (x1 <> NIL) then x1 else x0
    end)

(* ================================================================ *)

(*fun scan_as_subject0 (s : string) : subject_t = (
    (name_to_subject (Name (String.fields (fn c => (c = #".")) s))))*)

(* Scans a string as a subject.  This is an utitily for interactive
   use. *)

fun scan_string_as_subject (s : string) : subject_t = (
    let
	val error_bad_literal_subject = Match

	fun id0 c = (Char.isAlpha c) orelse (c = #"_")
	fun idn c = (Char.isAlphaNum c) orelse (c = #"_")
	fun skip_ws ss0 = (#2 (Substring.splitl Char.isSpace ss0))

	fun scan_id ss0 = (
	    let
		val ss1 = (skip_ws ss0)
		val (pp0, ss2) = (Substring.splitl id0 ss1)
		val (pp1, ss3) = (Substring.splitl idn ss2)
	    in
		((Substring.span (pp0, pp1)), ss3)
	    end)

	fun scan_index ii0 ss0 = (
	    let
		val ss1 = (skip_ws ss0)
		val (pp0, ss2) = (Substring.splitl Char.isDigit ss1)
		val dd0 = valOf (Int.fromString (Substring.string pp0))
		val ss2 = (skip_ws ss2)
	    in
		case (Substring.getc ss2) of
		    NONE => raise error_bad_literal_subject
		  | SOME (#",", ss3) => (scan_index (ii0 @ [dd0]) ss3)
		  | SOME (#"]", ss3) => ((ii0 @ [dd0]), ss3)
		  | SOME _ => raise error_bad_literal_subject
	    end)

	fun scan_optional_index ss0 = (
	    let
		val ss1 = (skip_ws ss0)
	    in
		case (Substring.getc ss1) of
		    NONE => ([], ss1)
		  | SOME (#".", ss2) => ([], ss1)
		  | SOME (#"[", ss3) => (scan_index [] ss3)
		  | SOME _ => raise error_bad_literal_subject
	    end)

	fun scan_path path0 ss0 = (
	    let
		val (pp0, ss1) = (scan_id ss0)
		val id = Id (Substring.string pp0)
		val (index, ss2) = (scan_optional_index ss1)
		val path1 = (path0 @ [(id, index)])
		val ss3 = (skip_ws ss2)
	    in
		case (Substring.getc ss3) of
		    NONE => path1
		  | SOME (#".", ss2) => (scan_path path1 ss2)
		  | SOME _ => raise error_bad_literal_subject
	    end)

	val ss0 = (Substring.full s)
	val ss1 = (skip_ws ss0)
    in
	case (Substring.getc ss1) of
	    NONE => Subj (VAR, [])
	  | SOME (#".", ss2) => Subj (PKG, (scan_path [] ss2))
	  | SOME (_, _) => Subj (VAR, (scan_path [] ss1))
    end)

end
