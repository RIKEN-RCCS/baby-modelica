(* binder.sml -*-Coding: us-ascii-unix;-*- *)
(* Copyright (C) 2018-2021 RIKEN R-CCS *)

(* A NAME RESOLVER, FIRST PART.  Name resolving attaches a prefix to a
   variable reference to make it a full composite reference. *)

(*AHO*) (* NO BINDING IN ANNOTATIONS. *)

structure binder :
sig
    type subject_t
    type definition_body_t
    type id_t
    type expression_t
    type binder_t
    type ctx_t

    val make_reference :
	definition_body_t -> bool -> expression_t -> expression_t

    val discern_connector_component :
	subject_t -> expression_t -> bool

    val make_iterator_binder :
	ctx_t -> bool -> binder_t -> (id_t * expression_t) list
	-> (binder_t * (id_t * expression_t) list)

    val bind_in_value__ :
	ctx_t -> bool -> definition_body_t -> definition_body_t
    val bind_in_scoped_expression :
	bool -> definition_body_t -> expression_t -> expression_t

    val bind_in_simple_type :
	bool -> binder_t -> definition_body_t -> definition_body_t
    val bind_in_expression :
	ctx_t -> bool -> binder_t -> expression_t -> expression_t
end = struct

open plain ast common message small0

type binder_t = expression_t -> expression_t
type ctx_t = {k : definition_body_t}

val class_tree = classtree.class_tree
val instance_tree = classtree.instance_tree
val fetch_from_instance_tree = classtree.fetch_from_instance_tree
val store_to_instance_tree = classtree.store_to_instance_tree
val fetch_class_by_part = classtree.fetch_class_by_part
val subject_to_instance_tree_path = classtree.subject_to_instance_tree_path

val find_name_initial_part = finder.find_name_initial_part

val assemble_package = blender.assemble_package

val obtain_array_dimension = operator.obtain_array_dimension

fun trace n (s : string) = if n <= 3 then (print (s ^"\n")) else ()

(* ================================================================ *)

(* Takes a declared component of a reference in a class pointed by a
   subject.  It returns an ID or NONE if a reference is not a
   component.  It assumes the subscripts are the same. *)

fun take_declared_component subj w = (
    case w of
	Vref (_, []) => raise Match
      | Vref (NONE, _) => raise Match
      | Vref (SOME ns1, rr) => (
	let
	    val path1 = (drop_subscripts rr)
	    val Subj (ns0, cc) = subj
	    val path0 = (drop_subscripts cc)
	in
	    if ((ns0 = VAR andalso ns1 = VAR)
		andalso (list_prefix (op =) path0 path1)
		andalso ((length path0) < (length path1))) then
		SOME (List.nth (path1, (length path0)))
	    else
		NONE
	end)
      | _ => raise Match)

(* Discriminates the side (inside/outside) of a connector.  It takes a
   class by a subject and a reference.  It checks a reference is
   declared in the class and it is a connector.  It requires a
   reference is before resolving the inner-outer relation. *)

fun discern_connector_component subj w = (
    case (take_declared_component subj w) of
	NONE => false
      | SOME id => (
	let
	    val component = (compose_subject subj id [])
	    val k = surely (fetch_from_instance_tree component)
	in
	    (class_is_connector false k)
	end))

(* ================================================================ *)

(* Tests a global reference, which starts with "" and is considered
   bound. *)

fun reference_is_in_package_root x0 = (
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
	    val vref = (subject_as_reference subj)
	    val rr0 = (path_of_reference vref)
	    val (prefix, _) = (split_last rr0)
	in
	    Vref (SOME ns, (prefix @ rr1))
	end))

(* Appends a variable reference similarily to extend_reference except
   when it is a local variable. *)

fun make_reference_in_function kp subj rr = (
    let
	val (name0, _) = (subject_prefix subj)
	val name1 = (subject_of_class kp)
    in
	if (name0 = name1) then
	    Lref (rr, name1)
	else
	    (extend_reference subj rr)
    end)

(* Makes a reference in a class.  The first part of a path matches to
   a resolved class.  The name postfix needs to be secured as a proper
   reference. *)

fun refer_in_package kp subj rr = (
    case rr of
	[] => raise Match
      | (id, []) :: _ => (extend_reference subj rr)
      | _ => raise error_subscripts_to_package)

(* Makes a reference in a variable.  A variable name is included both
   in the tail of a subject and in the head of a reference path. *)

fun refer_in_variable kp (d as Defvar _) subj rr = (
    let
	val _ = if (not (class_is_non_function_package kp)) then ()
		else if (declaration_is_constant d) then ()
		else raise error_variable_in_static_class
    in
	case rr of
	    [] => raise Match
	  | _ => (
	    if (not (kind_is_function kp)) then
		(extend_reference subj rr)
	    else
		(make_reference_in_function kp subj rr))
    end)

(* Resolves a variable reference in the given package/instance.  It is
   passed to binding routines.  It adds a prefix to "x.y" as
   "a.b.x.y", when "a.b" is a class B and B contains a declaration of
   "x".  It also resolves functions and constants. *)

fun make_reference kp (_ : bool) w0 = (
    case w0 of
	Vref (_, []) => raise Match
      | Vref (NONE, rr as (id, ss_) :: rr1) => (
	if (reference_is_in_package_root w0) then
	    Vref (SOME PKG, (drop_dot_of_package_root PKG rr))
	else
	    let
		val subjkp = (subject_of_class kp)
	    in
		case (find_name_initial_part kp id) of
		    NONE => raise (error_variable_name_not_found id kp)
		  | SOME (Naming (_, subj, _, _, EL_Class (z, r, dx, h))) => (
		    let
			val x0 = (refer_in_package kp subj rr)
		    in
			x0
		    end)
		  | SOME (Naming (_, subj, _, _, EL_State (z, r, dx, h))) => (
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
	val {k = kp} = ctx
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
		val (subj1, k1) = (fetch_class_by_part scope)
		val k2 = (body_of_argument k1)
		val _ = (assert_match_subject subj1 k2)
		val _ = if (step_is_at_least E3 k2) then () else raise Match
		val binder1 = (make_reference k2 buildphase)
		val newctx = {k = k2}
		val walk_x1 = (bind_in_expression newctx buildphase binder1)
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
	  | App (f0, ee0) => (
	    let
		val f1 = (walk_x f0)
		val ee1 = (map walk_x ee0)
		val w1 = App (f1, ee1)
	    in
		if (f1 = Vref (SOME PKG, [(Id "cardinality", [])])) then
		    let
			val _ = if (not buildphase) then ()
				else raise error_cardinality_in_declaration
			val _ = if ((length ee1) = 1) then ()
				else raise error_bad_call_of_cardinality
			val subj = (subject_of_class kp)
			val x0 = (hd ee1)
			val sidex = (discern_connector_component subj x0)
			val x1 = Cref (x0, sidex)
		    in
			App (f1, [x1])
		    end
		else
		    w1
	    end)
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
	  | Lref _ => w0
	  | Cref _ => w0
	  | Array_fill (e, s) => (
	    Array_fill ((walk_x e), (walk_x s)))
	  | Array_diagonal e => (
	    Array_diagonal (walk_x e))
    end)

(* Binds elements in a simple-type.  This is used, because general
   walkers do not traverse the elements in simple-types. *)

and bind_in_simple_type buildphase binder k0 = (
    case k0 of
	Def_Body (mk, cs, nm, cc0, ii, ee0, (aa, ww)) => (
	let
	    (*val attributes = not buildphase*)
	    val _ = if (class_is_simple_type k0) then () else raise Match
	    val _ = if (step_is_at_least E3 k0) then () else raise Match

	    val subj = (subject_of_class k0)
	    val walk_x = (bind_in_expression {k = k0} buildphase binder)
	    val cc1 = (walk_x cc0)
	    val walk_p = (bind_in_simple_type_element buildphase k0)
	    val ee1 = (map walk_p ee0)
	    val k1 = Def_Body (mk, cs, nm, cc1, ii, ee1, (aa, ww))
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
	    val Defvar (v, k0) = d0
	    val _ = if (class_is_primitive k0) then () else raise Match
	in
	    if ((not buildphase) orelse (v = Id "value")) then
		let
		    val k1 = (bind_in_primitive_type buildphase k0)
		    val dx = Defvar (v, k1)
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
	    Def_Primitive (t, x0, va) => (
	    let
		fun binder w = raise error_undefined_variable
		val walk_x = (bind_in_expression {k = k0} buildphase binder)
		val x1 = (walk_x x0)
	    in
		Def_Primitive (t, x1, va)
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

fun bind_in_value__ ctx buildphase k0 = (
    case k0 of
	Def_Mock_Array (dim, array0, dummy) => (
	let
	    val array1 = (map (bind_in_value__ ctx buildphase) array0)
	in
	    Def_Mock_Array (dim, array1, dummy)
	end)
      | Def_Body _ => (
	let
	    val _ = if (step_is_at_least E3 k0) then () else raise Match
	in
	    if (not buildphase) then
		(bind_in_value_declaration__ ctx buildphase k0)
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
		    val k2 = (bind_in_value_declaration__ ctx buildphase k1)
		in
		    k2
		end
	end)
      | Def_Der _ => k0
      | Def_Primitive (P_Enum _, L_Enum _, _) => k0
      | Def_Primitive _ => raise Match
      | _ => raise Match)

and bind_in_value_declaration__ ctx buildphase k0 = (
    case k0 of
	Def_Body _ => (
	if (not (class_is_simple_type k0)) then
	    k0
	else
	    let
		fun binder _ = raise Match
		val k2 = (bind_in_simple_type buildphase binder k0)
	    in
		k2
	    end)
      | Def_Der _ => k0
      | _ => raise Match)

(* Binds variables in an expression of its own scope.  It is used for
   modifiers and subscripts which have their scope environments. *)

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

end
