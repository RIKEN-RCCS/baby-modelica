(* postbinder.sml -*-Coding: us-ascii-unix;-*- *)
(* Copyright (C) 2018-2021 RIKEN R-CCS *)

(* NAME RESOLVER, SECOND PART.  Second resolving resolves a variable
   reference in equations/algorithms sections. *)

structure postbinder :
sig
    type definition_body_t
    type binder_t
    type ctx_t

    val bind_model : bool -> unit
    val substitute_outer : unit -> unit
    val bind_in_instance : bool -> definition_body_t -> bool

    val bind_in_class :
	ctx_t -> binder_t -> definition_body_t -> definition_body_t
end = struct

open ast
open plain
open small1

type ctx_t = binder.ctx_t
type binder_t = binder.binder_t

val class_tree = classtree.class_tree
val instance_tree = classtree.instance_tree
val fetch_class_by_scope = classtree.fetch_class_by_scope
val store_to_instance_tree = classtree.store_to_instance_tree
val fetch_from_instance_tree = classtree.fetch_from_instance_tree
val component_is_outer_alias = classtree.component_is_outer_alias
val traverse_tree = classtree.traverse_tree
val substitute_outer_reference = classtree.substitute_outer_reference

val find_class = finder.find_class

val assemble_package = cooker.assemble_package

val make_reference = binder.make_reference
(*val bind_in_class = binder.bind_in_class*)
val bind_in_simple_type = binder.bind_in_simple_type
val bind_in_expression = binder.bind_in_expression
val discern_connector_component = binder.discern_connector_component
val make_iterator_binder = binder.make_iterator_binder

val walk_in_class = walker.walk_in_class
val walk_in_expression = walker.walk_in_expression
val walk_in_equation = walker.walk_in_equation
val walk_in_statement = walker.walk_in_statement
val substitute_expression = walker.substitute_expression

val secure_reference = builder.secure_reference

fun tr_bind (s : string) = if true then (print (s ^"\n")) else ()

(* ================================================================ *)

(* Binds variables in a class and its base classes.  (It handles
   for-iterators and the general walker routine cannot be used here).
   It does not bind in equation/algorithm-sections when a class is a
   package.  It replaces a variable with the result of an application
   of the binder.  A context ctx displays a main class, and k0 can be
   the main or its bases. *)

fun bind_in_class ctx binder k0 = (
    if (class_is_simple_type k0) then
	let
	    val buildphase = false
	    val k1 = (bind_in_simple_type buildphase binder k0)
	    val _ = (assert_cook_step E5 k1)
	in
	    k1
	end
    else
	case k0 of
	    Def_Body (mk, j, cs, nm, cc0, ee0, aa, ww) => (
	    let
		val _ = if (step_is_at_least E3 k0) then () else raise Match
		(*val ctx = {k = kp}*)
		(*fun binder w = raise error_undefined_variable*)

		val walk_x = (bind_in_expression ctx false binder)
		val walk_e = (bind_in_class_element ctx binder)
		val cc1 = (walk_x cc0)
		val ee1 = (map walk_e ee0)
		val k1 = Def_Body (mk, j, cs, nm, cc1, ee1, aa, ww)
		val k2 = (set_cook_step E5 k1)
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

and bind_in_class_element ctx binder e0 = (
    let
	val {k = kp} = ctx
	val walk_q = (bind_in_equation kp binder)
	val walk_s = (bind_in_statement kp binder)
	fun walk_pair (c, kx) = (c, (bind_in_class ctx binder kx))

	val package = (class_is_package kp)
    in
	case e0 of
	    Import_Clause _ => raise Match
	  | Extends_Clause _ => raise Match
	  | Element_Class _ => e0
	  | Element_State _ => e0
	  | Redefine_Class _ => e0
	  | Redeclare_State _ => e0
	  | Element_Enumerators _ => raise Match
	  | Element_Equations (u, qq0) => (
	    if (package) then
		e0
	    else
		let
		    val _ = tr_bind (";; - [bind] Bind in equations in ("^
				     (class_print_name kp) ^")")

		    val qq1 = (map walk_q qq0)
		in
		    Element_Equations (u, qq1)
		end)
	  | Element_Algorithms (u, ss0) => (
	    if (package) then
		e0
	    else
		let
		    val _ = tr_bind (";; - [bind] Bind in statements in ("^
				     (class_print_name kp) ^")")

		    val ss1 = (map walk_s ss0)
		in
		    Element_Algorithms (u, ss1)
		end)
	  | Element_External (n, s, w) => e0
	  | Element_Annotation a => e0
	  | Element_Import _ => e0
	  | Element_Base _ => e0
	  | Base_List _ => e0
	  | Base_Classes bb0 => (
	    let
		val bb1 = (map walk_pair bb0)
	    in
		Base_Classes bb1
	    end)
    end)

and bind_in_modifier kp binder (m : modifier_t) = (
    let
	val ctx = {k = kp}
	val walk_x = (bind_in_expression ctx false binder)
	val walk_m = (bind_in_modifier kp binder)
	val walk_h = (bind_in_constraint kp binder)
	val walk_k = (bind_in_class ctx binder)
    in
	case m of
	    Mod_Redefine (r, d0, h0) => (
	    let
		val Defclass ((v, g), k0) = d0
		val k1 = (walk_k k0)
		val h1 = (Option.map walk_h h0)
		val d1 = Defclass ((v, g), k1)
	    in
		Mod_Redefine (r, d1, h1)
	    end)
	  | Mod_Elemental_Redefine (z, r, d0, h0) => (
	    let
		val Defclass ((v, g), k0) = d0
		val k1 = (walk_k k0)
		val h1 = (Option.map walk_h h0)
		val d1 = Defclass ((v, g), k1)
	    in
		Mod_Elemental_Redefine (z, r, d1, h1)
	    end)
	  | Mod_Redeclare (r, d0, h0) => (
	    let
		val Defvar (v, q, k0, c, aa, ww) = d0
		val k1 = (walk_k k0)
		val h1 = (Option.map walk_h h0)
		val d1 = Defvar (v, q, k1, c, aa, ww)
	    in
		Mod_Redeclare (r, d1, h1)
	    end)
	  | Mod_Elemental_Redeclare (z, r, d0, h0) => (
	    let
		val Defvar (v, q, k0, c, aa, ww) = d0
		val k1 = (walk_k k0)
		val h1 = (Option.map walk_h h0)
		val d1 = Defvar (v, q, k1, c, aa, ww)
	    in
		Mod_Elemental_Redeclare (z, r, d1, h1)
	    end)
	  | Mod_Entry (ef, n, m0, w) => (
	    let
		val m1 = (map walk_m m0)
	    in
		Mod_Entry (ef, n, m1, w)
	    end)
	  | Mod_Value e0 => (
	    let
		val e1 = (walk_x e0)
	    in
		(Mod_Value e1)
	    end)
    end)

and bind_in_constraint kp binder (r : constraint_t) = (
    let
	val ctx = {k = kp}
	val cooker = assemble_package
	(*val walk_x = (bind_in_expression {k = kp} false binder)*)
	val walk_m = (bind_in_modifier kp binder)

	val subj = (subject_of_class kp)
	val (k0, mm0, aa, ww) = r
    in
	case k0 of
	    Def_Body _ => raise Match
	  | Def_Der _ => raise Match
	  | Def_Primitive _ => raise Match
	  | Def_Name cn => (
	    case (find_class cooker (subj, kp) cn) of
		NONE => raise (error_class_not_found cn kp)
	      | SOME k1 => (
		let
		    val mm1 = (map walk_m mm0)
		in
		    (k1, mm1, aa, ww)
		end))
	  | Def_Scoped _ => raise Match
	  | Def_Refine _ => raise Match
	  | Def_Extending _ => raise Match
	  | Def_Replaced _ => raise Match
	  | Def_Displaced _ => raise Match
	  | Def_In_File => raise Match
	  | Def_Mock_Array _ => raise Match
    end)

and bind_in_equation kp binder q0 = (
    let
	val ctx = {k = kp}
	val walk_x = (bind_in_expression ctx false binder)
	val walk_m = (bind_in_modifier kp binder)
	val walk_q = (bind_in_equation kp binder)
	val walk_n_e = (fn (n, e) => (n, (walk_x e)))
	val walk_x_qq = (fn (e, qq) => ((walk_x e), (map walk_q qq)))
    in
	case q0 of
	    Eq_Eq ((x0, y0), Annotation aa0, ww) => (
	    Eq_Eq (((walk_x x0), (walk_x y0)),
		   Annotation (map walk_m aa0), ww))
	  | Eq_Connect ((x0, y0), Annotation aa0, ww) => (
	    let
		val subj = (subject_of_class kp)
		val x1 = (walk_x x0)
		val y1 = (walk_x y0)
		val aa1 = (map walk_m aa0)
		val sidex = (discern_connector_component subj x1)
		val sidey = (discern_connector_component subj y1)
		val x2 = Cref (x1, sidex)
		val y2 = Cref (y1, sidey)
		val q1 = Eq_Connect ((x2, y2), Annotation aa1, ww)
	    in
		q1
	    end)
	  | Eq_If (c0, Annotation aa0, ww) => (
	    Eq_If ((map walk_x_qq c0),
		   Annotation (map walk_m aa0), ww))
	  | Eq_When (c0, Annotation aa0, ww) => (
	    Eq_When ((map walk_x_qq c0),
		     Annotation (map walk_m aa0), ww))
	  | Eq_For ((ii0, qq0), Annotation aa0, ww) => (
	    let
		val (binder1, ii1) = (make_iterator_binder
					  {k = kp} false binder ii0)
		val walk_q = (bind_in_equation kp binder1)
		val walk_m = (bind_in_modifier kp binder1)
		val qq1 = (map walk_q qq0)
		val aa1 = (map walk_m aa0)
	    in
		Eq_For ((ii1, qq1), Annotation aa1, ww)
	    end)
	  | Eq_App ((x0, yy0), Annotation aa0, ww) => (
	    Eq_App (((walk_x x0), (map walk_x yy0)),
		    Annotation (map walk_m aa0), ww))
    end)

and bind_in_statement kp binder s0 = (
    let
	val ctx = {k = kp}
	val walk_x = (bind_in_expression ctx false binder)
	val walk_m = (bind_in_modifier kp binder)
	val walk_s = (bind_in_statement kp binder)
	val walk_n_e = (fn (n, e) => (n, (walk_x e)))
	val walk_x_ss = (fn (e, ss) => ((walk_x e), (map walk_s ss)))
    in
	case s0 of
	    St_Break (Annotation aa0, ww) => (
	    St_Break (Annotation (map walk_m aa0), ww))
	  | St_Return (Annotation aa0, ww) => (
	    St_Return (Annotation (map walk_m aa0), ww))
	  | St_Assign (x0, y0, Annotation aa0, ww) => (
	    St_Assign ((walk_x x0), (walk_x y0),
		       Annotation (map walk_m aa0), ww))
	  | St_Call (x0, y0, z0, Annotation aa0, ww) => (
	    St_Call ((map walk_x x0), (walk_x y0), (map walk_x z0),
		     Annotation (map walk_m aa0), ww))
	  | St_If (c0, Annotation aa0, ww) => (
	    St_If ((map walk_x_ss c0),
		   Annotation (map walk_m aa0), ww))
	  | St_For (ii0, ss0, Annotation aa0, ww) => (
	    let
		val (binder1, ii1) = (make_iterator_binder
					  ctx false binder ii0)
		val walk_s = (bind_in_statement kp binder1)
		val walk_m = (bind_in_modifier kp binder1)
		val ss1 = (map walk_s ss0)
		val aa1 = (map walk_m aa0)
	    in
		St_For (ii1, ss1, Annotation aa1, ww)
	    end)
	  | St_While (e0, ss0, Annotation aa0, ww) => (
	    St_While ((walk_x e0), (map walk_s ss0),
		      Annotation (map walk_m aa0), ww))
	  | St_When (cc0, Annotation aa0, ww) => (
	    St_When ((map walk_x_ss cc0),
		     Annotation (map walk_m aa0), ww))
    end)

(* ================================================================ *)

fun secure_references_in_class kp = (
    let
	val ctx = kp
	val buildphase = false
	val efix = (fn (x, _) => ((secure_reference ctx buildphase x), ()))
	val ewalk = (walk_in_expression efix)
	val qwalk = (walk_in_equation (fn (q, a) => (q, a)) ewalk)
	val swalk = (walk_in_statement (fn (s, a) => (s, a)) ewalk)
	val walker = {vamp_q = qwalk, vamp_s = swalk}
	val (_, _) = (walk_in_class walker (kp, ()))
    in
	()
    end)

(* Makes a record accessible as a package if it is instantiated.  It
   is because a record itself may be accessed (not as an instance) in
   such as instantiation. *)

fun secure_record_class kp = (
    if ((kind_is_record kp) andalso (class_is_instance kp)) then
	let
	    val record = (class_name_of_instance kp)
	    val var = (subject_as_reference record)
	    val ctx = kp
	    val _ = (secure_reference ctx false var)
	in
	    ()
	end
    else
	())

(* Resolves variable references in a package/instance.  It returns
   true if some instances are processed, so that it can repeat the
   process until it stabilizes.  It, with scanning=true, processes all
   instances, because the building routine may leave some instances in
   a partially resolved state (such as simple-types, whose value
   attribute is only resolved). *)

fun bind_in_instance (scanning : bool) k0 = (
    if (class_is_outer_alias k0) then
	false
    else if (class_is_enumerator_definition k0) then
	false
    else if (class_is_package k0) then
	false
    else if ((not scanning) andalso (step_is_at_least E5 k0)) then
	false
    else
	let
	    val _ = if (step_is_at_least E3 k0) then () else raise Match
	    val _ = if (not (class_is_primitive k0)) then () else raise Match

	    val ctx = {k = k0}
	    val subj = (subject_of_class k0)
	    val binder = (make_reference k0 false)
	    val k1 = (bind_in_class ctx binder k0)
	    val _ = if ((cook_step k1) = E5) then () else raise Match
	    val _ = (store_to_instance_tree subj k1)
	    val _ = (secure_references_in_class k1)
	    val _ = (secure_record_class k1)
	in
	    (*
	    if ((kind_is_record k1) andalso (class_is_instance k1)) then
		let
		    val record = (class_name_of_instance k1)
		    val var = (subject_as_reference record)
		    val ctx = k1
		    val _ = (secure_reference ctx false var)
		in
		    true
		end
	    else
		true
	    *)
	    true
	end)

(* Calls the variable resolving procedure on packages/instances in the
   trees.  It returns true if some instances are processed.  It skips
   classes that are named but are not used as packages (which have the
   step=E0).  It accesses the component slot after processing the
   class. *)

fun bind_instances_loop (scanning : bool) node0 = (
    let
	val (subj, kx, cx) = node0
	val kp = (! kx)

	val _ = if ((cook_step kp) <> E0) then () else raise Match
	val _ = if ((class_is_package kp) orelse (step_is_at_least E3 kp))
		then () else raise Match

	val changes0 = (bind_in_instance scanning kp)
	(* KEEP ORDERING. *)
	val c0 = (! cx)
	val components = (List.filter (not o component_is_outer_alias) c0)

	val _ = if (null components) then ()
		else if (not (class_is_simple_type kp)) then ()
		else if (class_is_enum kp) then ()
		else raise error_attribute_access_to_simple_type

	val changes1
	    = (List.concat
		   (map (fn (Slot (v, dim, nodes, dummy)) =>
			    (map (bind_instances_loop scanning) nodes))
			components))
    in
	(List.exists (fn x => x) (changes0 :: changes1))
    end)

(* Binds variables in the model.  Call it with true.  It repeatedly
   calls the binding procedure until settled, because values and
   equations in accessed instances introduce new references. *)

fun bind_model scanning = (
    let
	val changes0 = (bind_instances_loop scanning instance_tree)
	val changes1 = (bind_instances_loop scanning class_tree)
    in
	if (changes0 orelse changes1) then
	    (bind_model false)
	else
	    ()
    end)

(* ================================================================ *)

val substitute_outer_in_instance
    = (substitute_expression
	   (fn _ => (fn (w, _) => ((substitute_outer_reference w), []))))

fun substitute_outer () = (
    ignore (traverse_tree substitute_outer_in_instance (instance_tree, [])))

(* ================================================================ *)

end
