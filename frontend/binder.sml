(* binder.sml -*-Coding: us-ascii-unix;-*- *)
(* Copyright (C) 2018-2020 RIKEN R-CCS *)

(* NAME RESOLVER, FIRST PART.  Name resolving attaches a prefix to a
   variable reference to make it a full composite reference. *)

(*AHO*) (* NO BINDING IN ANNOTATIONS. *)

structure binder :
sig
    type definition_body_t
    type expression_t
    type binder_t
    type ctx_t

    val make_reference :
	definition_body_t -> bool -> expression_t -> expression_t

    val bind_in_expression :
	ctx_t -> bool -> binder_t -> expression_t -> expression_t
    val bind_in_value :
	ctx_t -> bool -> definition_body_t -> definition_body_t
    val bind_in_scoped_expression :
	bool -> definition_body_t -> expression_t -> expression_t

    val bind_in_class :
	ctx_t -> binder_t -> definition_body_t -> definition_body_t
end = struct

open ast
open plain
open small1

type binder_t = expression_t -> expression_t
type ctx_t = {k : definition_body_t}

val class_tree = classtree.class_tree
val instance_tree = classtree.instance_tree
val fetch_class_by_scope = classtree.fetch_class_by_scope
val store_to_instance_tree = classtree.store_to_instance_tree
val subject_to_instance_tree_path = classtree.subject_to_instance_tree_path

val find_class = finder.find_class
val find_name_initial_part = finder.find_name_initial_part

val assemble_package = cooker.assemble_package

val obtain_array_dimension = operator.obtain_array_dimension

fun tr_bind (s : string) = if true then (print (s ^"\n")) else ()
fun tr_bind_vvv (s : string) = if false then (print (s ^"\n")) else ()
fun tr_build (s : string) = if true then (print (s ^"\n")) else ()

(* ================================================================ *)

(* Tests a global reference, which starts with "" and is considered
   bound. *)

fun reference_is_global x0 = (
    case x0 of
	Vref (_, []) => raise Match
      | Vref (NONE, (Id "", []) :: _) => true
      | Vref (NONE, (Id "", _) :: _) => raise Match
      | Vref (NONE, (Id _, _) :: _) => false
      | Vref (SOME _, _) => raise Match
      | _ => raise Match)

(* Appends a path of a variable reference to a variable declaration.
   It requires the names of the head of a reference and the tail of a
   declaration match. *)

fun extend_reference subj rr1 = (
    case rr1 of
	[] => raise Match
      | (id1, ss1) :: _ => (
	let
	    val _ = (assert_no_subscript_to_subject subj)
	    val _ = (assert_match_subject_name id1 subj)
	    val Subj (ns, _) = subj
	    val Vref (_, rr0) = (subject_as_reference subj)
	    val (prefix, _) = (split_last rr0)
	in
	    Vref (SOME ns, (prefix @ rr1))
	end))

(* Makes a reference in a class.  The first part of a path matches to
   a resolved class.  The name postfix needs to be secured as a proper
   reference. *)

fun refer_in_package kp subj rr = (
    case rr of
	[] => raise Match
      | (id, []) :: _ => (extend_reference subj rr)
      | _ => raise error_subscripts_to_package)

(* Makes a reference in a variable. *)

fun refer_in_variable kp (d as Defvar _) subj rr = (
    let
	val _ = if (not (class_is_package kp)) then ()
		else if (declaration_is_constant d) then ()
		else raise error_variable_in_static_class
    in
	case rr of
	    [] => raise Match
	  | _ => (extend_reference subj rr)
    end)

(* Resolves a variable reference in the given package/instance.  It is
   passed to binding routines.  It adds a prefix to "x.y" as
   "a.b.x.y", when "a.b" is a class B and B contains a declaration of
   "x".  It also resolves functions and constants. *)

fun make_reference kp (_ : bool) w0 = (
    case w0 of
	Vref (_, []) => raise Match
      | Vref (NONE, rr as (id, ss_) :: rr1) => (
	if (reference_is_global w0) then
	    Vref (SOME PKG, (drop_dot_of_package_root PKG rr))
	else
	    let
		val cooker = assemble_package
		val subjkp = (subject_of_class kp)
	    in
		case (find_name_initial_part cooker E3 (subjkp, kp) id) of
		    NONE => raise (error_variable_name_not_found id kp)
		  | SOME (Naming (_, subj, _, _, (z, r, EL_Class dx, h))) => (
		    let
			val x0 = (refer_in_package kp subj rr)
		    in
			x0
		    end)
		  | SOME (Naming (_, subj, _, _, (z, r, EL_State dx, h))) => (
		    let
			val x0 = (refer_in_variable kp dx subj rr)
		    in
			x0
		    end)
	    end)
      | Vref (SOME _, _) => w0
      | _ => raise Match)

(* Makes a binder of for-iterators.  It returns a pair of a binder and
   a bound iterator list.  It adds each iterator variable into the
   scope of the binder. *)

fun make_iterator_binder ctx buildphase binder iters = (
    let
	fun loop (binder0, acc0) iters0 = (
	    case iters0 of
		[] => (binder0, acc0)
	      | (v0, x0) :: tt => (
		let
		    val walk_x = (bind_in_expression ctx buildphase binder0)
		    val x1 = (walk_x x0)
		    val acc1 = (acc0 @ [(v0, x1)])
		    val binder1 = (make_reference_on_iterator binder0 v0)
		in
		    (loop (binder1, acc1) tt)
		end))
    in
	(loop (binder, []) iters)
    end)

(* Binds a for-iterator variable.  It just checks that the scope
   includes a variable, but it does not distingish the nesting levels.
   (A for-iterator is Integer, Boolean, or enumerations). *)

and make_reference_on_iterator binder id w0 = (
    case w0 of
	Vref (_, []) => raise Match
      | Vref (NONE, rr as (v0, ss0) :: tt) => (
	if (v0 = id) then
	    let
		val _ = if (null ss0) then ()
			else raise error_subscripts_to_iterator
		val _ = if (null tt) then ()
			else raise error_components_to_iterator
	    in
		Iref id
	    end
	else
	    (binder w0))
      | Vref (SOME _, _) => w0
      | _ => raise Match)

(* Walks an expression and calls an binder on a variable reference.
   It folds constants when buildphase=true, because buildphase=true
   means it is called to deal with an array dimension. *)

and bind_in_expression ctx buildphase binder w0 = (
    let
	val walk_x = (bind_in_expression ctx buildphase binder)
	val walk_n_x = (fn (n, x) => (n, (walk_x x)))
	val walk_x_x = (fn (x, y) => ((walk_x x), (walk_x y)))
	val walk_x_option = (Option.map walk_x)
	val walk_vref = (fn (n, s) => (n, (map walk_x s)))
    in
	case w0 of
	    NIL => NIL
	  | Colon => Colon
	  | Otherwise => Otherwise
	  | Scoped (e, scope) => (
	    let
		val (subj1, k1) = (fetch_class_by_scope scope)
		val _ = (assert_match_subject subj1 k1)
		val _ = if (step_is_at_least E3 k1) then () else raise Match
		val binder1 = (make_reference k1 buildphase)
		val walk_x1 = (bind_in_expression ctx buildphase binder1)
	    in
		(walk_x1 e)
	    end)
	  | Vref (_, []) => raise Match
	  | Vref (NONE, rr0) => (
	    let
		val rr1 = (map walk_vref rr0)
		val w1 = Vref (NONE, rr1)
		val w2 = (binder w1)
		(*val _ = (secure_reference ctx buildphase w2)*)
	    in
		(walk_x w2)
	    end)
	  | Vref (SOME _, _) => (
	    if (not buildphase) then
		w0
	    else
		w0)
	  | Opr _ => w0
	  | App (x0, a0) => (
	    App ((walk_x x0), (map walk_x a0)))
	  | ITE c0 => (
	    ITE (map walk_x_x c0))
	  | Der a0 => (
	    Der (map walk_x a0))
	  | Pure a0 => (
	    Pure (map walk_x a0))
	  | Closure (n, a0) => (
	    Closure (n, (map walk_x a0)))
	  | L_Number x => w0
	  | L_String s => w0
	  | L_Bool x => w0
	  | L_Enum (c, s) => w0
	  | Array_Triple (x0, y0, z0) => (
	    Array_Triple ((walk_x x0), (walk_x y0), (walk_x_option z0)))
	  | Array_Constructor a0 => (
	    Array_Constructor (map walk_x a0))
	  | Array_Comprehension (x0, ii0) => (
	    let
		val (binder1, ii1) = (make_iterator_binder
					  ctx buildphase binder ii0)
		val walk_x = (bind_in_expression ctx buildphase binder1)
		val x1 = (walk_x x0)
	    in
		Array_Comprehension (x1, ii1)
	    end)
	  | Array_Concatenation a0 => (
	    Array_Concatenation (map (map walk_x) a0))
	  | Tuple a0 => (
	    Tuple (map walk_x a0))
	  | Reduction_Argument (x0, u0) => (
	    Reduction_Argument ((walk_x x0), (map walk_n_x u0)))
	  | Named_Argument (n, x0) => (
	    Named_Argument (n, (walk_x x0)))
	  | Pseudo_Split (x, s) => (
	    Pseudo_Split ((walk_x x), s))
	  | Component_Ref (x, v) => (
	    Component_Ref ((walk_x x), v))
	  (*| Instance _ => w0*)
	  | Instances _ => w0
	  | Iref _ => w0
	  | Cref _ => w0
	  | Array_fill (e, s) => (
	    Array_fill ((walk_x e), (walk_x s)))
	  | Array_diagonal e => (
	    Array_diagonal (walk_x e))
    end)

(* Binds elements in a simple-type.  This is used, because general
   walkers do not traverse the elements in simple-types. *)

and bind_in_simple_type buildphase k0 = (
    case k0 of
	Def_Body _ => (
	let
	    (*val attributes = not buildphase*)
	    val _ = if (class_is_simple_type k0) then () else raise Match
	    val _ = if (step_is_at_least E3 k0) then () else raise Match

	    val subj = (subject_of_class k0)
	    val walk_p = (bind_in_simple_type_element buildphase k0)
	    val ee0 = (body_elements k0)
	    val ee1 = (map walk_p ee0)
	    val k1 = (replace_body_elements k0 ee1)
	    val k2 = (set_cook_step E5 k1)
	    val _ = (store_to_instance_tree subj k2)
	in
	    k2
	end)
      | _ => raise Match)

and bind_in_simple_type_element buildphase kp e0 = (
    case e0 of
	Import_Clause _ => raise Match
      | Extends_Clause _ => raise Match
      | Element_Class _ => e0
      | Element_State (z, r, d0, h) => (
	let
	    (*val attributes = not buildphase*)
	    val Defvar (v, q, k0, c, a, w) = d0
	    val _ = if (class_is_primitive k0) then () else raise Match
	in
	    if ((not buildphase) orelse (v = Id "value")) then
		let
		    val k1 = (bind_in_primitive_type buildphase k0)
		    val dx = Defvar (v, q, k1, c, a, w)
		in
		    Element_State (z, r, dx, h)
		end
	    else
		Element_State (z, r, d0, h)
	end)
      | Redefine_Class _ => e0
      | Redeclare_State _ => e0
      | Element_Enumerators _ => e0
      | Element_Equations _ => e0
      | Element_Algorithms _ => e0
      | Element_External _ => e0
      | Element_Annotation _ => e0
      | Element_Import _ => e0
      | Element_Base _ => e0
      | Base_List _ => e0
      | Base_Classes _ => e0)

and bind_in_primitive_type buildphase k0 = (
	case k0 of
	    Def_Primitive (t, x0) => (
	    let
		fun binder w = raise error_undefined_variable
		val walk_x = (bind_in_expression {k = k0} buildphase binder)
		val x1 = (walk_x x0)
	    in
		Def_Primitive (t, x1)
	    end)
	  | _ => raise Match)

(* Binds variables in an instance appearing as a value.  It processes
   only the simple-types, but does nothing on other instances, because
   component variables will be instantiated elsewhere.  It is called
   in constant folding, when buildphase=true.  It processes only the
   value attribute, when buildphase=true, which is only needed as a
   value.  It checks re-entering this when buildphase=true.
   Re-entering will cause a failure in constant folding later.  It
   sets step=E4 early then finally sets step=E5, to detect
   re-entering. *)

fun bind_in_value ctx buildphase k0 = (
    case k0 of
	Def_Mock_Array (dim, array0, dummy) => (
	let
	    val array1 = (map (bind_in_value ctx buildphase) array0)
	in
	    Def_Mock_Array (dim, array1, dummy)
	end)
      | Def_Body _ => (
	let
	    val _ = if (step_is_at_least E3 k0) then () else raise Match
	in
	    if (not buildphase) then
		(bind_in_value_declaration ctx buildphase k0)
	    else if (step_is_at_least E5 k0) then
		k0
	    else if (step_is_at_least E4 k0) then
		let
		    val _ = (warn_cycle_in_dimensions ())
		in
		    k0
		end
	    else
		let
		    val subj = (subject_of_class k0)
		    val k1 = (set_cook_step E4 k0)
		    val _ = (store_to_instance_tree subj k1)
		    val k2 = (bind_in_value_declaration ctx buildphase k1)
		in
		    k2
		end
	end)
      | Def_Der _ => k0
      | Def_Primitive (P_Enum tag_, L_Enum (tag, v)) => k0
      | Def_Primitive _ => raise Match
      | _ => raise Match)

and bind_in_value_declaration ctx buildphase k0 = (
    case k0 of
	Def_Body _ => (
	if (not (class_is_simple_type k0)) then
	    k0
	else
	    let
		(*val attributes = (not buildphase)*)
		val subj = (subject_of_class k0)
		val k2 = (bind_in_simple_type buildphase k0)
	    in
		k2
	    end)
      | Def_Der _ => k0
      | _ => raise Match)

(* Binds variables, only in expressions of their own scopes.  It is
   used for modifiers and subscripts which have their environments of
   scopes. *)

fun bind_in_scoped_expression buildphase k0 w0 = (
    let
	val _ = if (buildphase) then () else raise Match
	fun binder w = raise error_undefined_variable
	val ctx = {k = k0}
	val walk_x = (bind_in_expression ctx buildphase binder)
	val w1 = (walk_x w0)
    in
	w1
    end)

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
	    val k1 = (bind_in_simple_type buildphase k0)
	    val _ = (assert_cook_step E5 k1)
	in
	    k1
	end
    else
	case k0 of
	    Def_Body (mk, j, cs, (c, n, x), ee0, aa, ww) => (
	    let
		val _ = if (step_is_at_least E3 k0) then () else raise Match
		(*val ctx = {k = kp}*)
		(*fun binder w = raise error_undefined_variable*)

		val walk_e = (bind_in_class_element ctx binder)
		val ee1 = (map walk_e ee0)
		val k1 = Def_Body (mk, j, cs, (c, n, x), ee1, aa, ww)
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
	val walk_q = (bind_in_equation ctx binder)
	val walk_s = (bind_in_statement ctx binder)
	fun walk_pair (c, kx) = (c, (bind_in_class ctx binder kx))

	val {k = kp} = ctx
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

and bind_in_modifier ctx binder (m : modifier_t) = (
    let
	val {k = kp} = ctx
	val walk_x = (bind_in_expression ctx false binder)
	val walk_m = (bind_in_modifier ctx binder)
	val walk_h = (bind_in_constraint ctx binder)
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

and bind_in_constraint ctx binder (r : constraint_t) = (
    let
	val {k = kp} = ctx
	val cooker = assemble_package
	(*val walk_x = (bind_in_expression {k = kp} false binder)*)
	val walk_m = (bind_in_modifier ctx binder)

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

and bind_in_equation ctx binder q0 = (
    let
	val {k = kp} = ctx
	val walk_x = (bind_in_expression ctx false binder)
	val walk_m = (bind_in_modifier ctx binder)
	val walk_q = (bind_in_equation ctx binder)
	val walk_n_e = (fn (n, e) => (n, (walk_x e)))
	val walk_x_qq = (fn (e, qq) => ((walk_x e), (map walk_q qq)))
    in
	case q0 of
	    Eq_Eq ((x0, y0), Annotation aa0, ww) => (
	    Eq_Eq (((walk_x x0), (walk_x y0)),
		   Annotation (map walk_m aa0), ww))
	  | Eq_Connect ((x0, y0), Annotation aa0, ww) => (
	    Eq_Connect (((walk_x x0), (walk_x y0)),
			Annotation (map walk_m aa0), ww))
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
		val walk_q = (bind_in_equation ctx binder1)
		val walk_m = (bind_in_modifier ctx binder1)
		val qq1 = (map walk_q qq0)
		val aa1 = (map walk_m aa0)
	    in
		Eq_For ((ii1, qq1), Annotation aa1, ww)
	    end)
	  | Eq_App ((x0, yy0), Annotation aa0, ww) => (
	    Eq_App (((walk_x x0), (map walk_x yy0)),
		    Annotation (map walk_m aa0), ww))
    end)

and bind_in_statement ctx binder s0 = (
    let
	val {k = kp} = ctx
	val walk_x = (bind_in_expression ctx false binder)
	val walk_m = (bind_in_modifier ctx binder)
	val walk_s = (bind_in_statement ctx binder)
	val walk_n_e = (fn (n, e) => (n, (walk_x e)))
	val walk_x_ss = (fn (e, ss) => ((walk_x e), (map walk_s ss)))
    in
	case s0 of
	    St_Break (Annotation a0, w) => (
	    St_Break (Annotation (map walk_m a0), w))
	  | St_Return (Annotation a0, w) => (
	    St_Return (Annotation (map walk_m a0), w))
	  | St_Assign (x0, y0, Annotation a0, w) => (
	    St_Assign ((walk_x x0), (walk_x y0),
		       Annotation (map walk_m a0), w))
	  | St_Call (x0, y0, z0, Annotation a0, w) => (
	    St_Call ((map walk_x x0), (walk_x y0), (map walk_x z0),
		     Annotation (map walk_m a0), w))
	  | St_If (c0, Annotation a0, w) => (
	    St_If ((map walk_x_ss c0),
		   Annotation (map walk_m a0), w))
	  | St_For (ii0, ss0, Annotation a0, w) => (
	    let
		val (binder1, ii1) = (make_iterator_binder
					  ctx false binder ii0)
		val walk_s = (bind_in_statement ctx binder1)
		val walk_m = (bind_in_modifier ctx binder1)
		val ss1 = (map walk_s ss0)
		val a1 = (map walk_m a0)
	    in
		St_For (ii1, ss1, Annotation a1, w)
	    end)
	  | St_While (e0, s0, Annotation a0, w) => (
	    St_While ((walk_x e0), (map walk_s s0),
		      Annotation (map walk_m a0), w))
	  | St_When (c0, Annotation a0, w) => (
	    St_When ((map walk_x_ss c0),
		     Annotation (map walk_m a0), w))
    end)

end
