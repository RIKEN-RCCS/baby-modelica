(* builder.sml -*-Coding: us-ascii-unix;-*- *)
(* Copyright (C) 2018-2021 RIKEN R-CCS *)

(* MODEL BUILDER.  The builder instantiates a model by traversaling
   the state variables. *)

structure builder :
sig
    type class_definition_t
    type definition_body_t
    type expression_t
    type subject_t
    type ctx_t

    val instantiate_class :
	subject_t * definition_body_t -> int list * definition_body_t list
    val secure_reference :
	definition_body_t -> bool -> expression_t -> expression_t
    val instantiate_components : definition_body_t -> unit

    val xreset : unit -> unit
    val xload : string -> class_definition_t
    val xfind : string -> definition_body_t
    val xbuild : string -> unit
end = struct

open ast
open plain
open small1

type ctx_t = {k : definition_body_t}
type binder_t = expression_t -> expression_t

val class_tree = classtree.class_tree
val instance_tree = classtree.instance_tree
val fetch_class_by_scope = classtree.fetch_class_by_scope
val store_to_instance_tree = classtree.store_to_instance_tree
val assert_stored_in_instance_tree = classtree.assert_stored_in_instance_tree
val unwrap_array_of_instances = classtree.unwrap_array_of_instances
val subject_to_instance_tree_path = classtree.subject_to_instance_tree_path
val component_is_outer_alias = classtree.component_is_outer_alias
val component_is_expandable = classtree.component_is_expandable
val dereference_outer_alias = classtree.dereference_outer_alias
val instantiate_outer_alias = classtree.instantiate_outer_alias
val access_node = classtree.access_node
val find_in_components = classtree.find_in_components

val find_element = finder.find_element
val list_elements = finder.list_elements

val assemble_instance = cooker.assemble_instance
val assemble_package = cooker.assemble_package
val commute_modifier_over_subscript = refiner.commute_modifier_over_subscript

val walk_in_expression = walker.walk_in_expression

val fold_constants = folder.fold_constants

val obtain_array_dimension = operator.obtain_array_dimension

val bind_in_scoped_expression = binder.bind_in_scoped_expression

fun tr_build (s : string) = if true then (print (s ^"\n")) else ()
fun tr_build_vvv (s : string) = if false then (print (s ^"\n")) else ()

(* Tests if a subject stored in the binding is a subcomponent name. *)

fun test_subcomponent subsubj (subj, id) = (
    (subsubj = (compose_subject subj id [])))

(* Converts a literal constant to an integer in an array dimension.
   Colon is handled elsewhere. *)

fun dimension_to_int w = (
    case w of
	L_Number (Z, x) => (
	case (string_is_int x) of
	    NONE => raise error_non_integer_value
	  | SOME v => v)
      | L_Number (R, x) => raise error_non_integer_value
      | _ => raise error_non_constant_array_dimension)

fun find_initializer_value mm = (
    let
	val vv = (List.filter
		      (fn x => case x of
				   Mod_Value _ => true
				 | _ => false)
		      mm)
    in
	case vv of
	    [] => raise error_no_value_in_rhs
	  | [Mod_Value v] => v
	  | _ => raise error_many_values_in_rhs
    end)

fun make_dummy_array_class (dim, array, dummy) = (
    case dim of
	[] => (
	let
	    val _ = if ((length array) = 1) then () else raise Match
	in
	    (hd array)
	end)
      | _ => (
	let
	    val size = (array_size dim)
	    val _ = if ((length array) = size) then () else raise Match
	in
	    if (size = 0) then
		Def_Mock_Array (dim, [], dummy)
	    else
		Def_Mock_Array (dim, array, dummy)
	end))

fun assert_inner_outer_condition binding = (
    let
	val Naming (id, subj, inner, _, (z, r, dd, h)) = binding
	(*val subcomponent = (test_subcomponent subsubj (subj, id))*)
	val subcomponent = (inner = NONE)
	val _ = if ((not ((#Outer r) andalso (not (#Inner r))))
		    orelse (not subcomponent))
		then () else raise Match
    in
	()
    end)

fun assemble_package_if_package (subj, k0) = (
    if (class_is_package k0) then
	(assemble_package E3 (subj, k0))
    else
	k0)

(* ================================================================ *)

(* Instantiates a class.  It repeatedly calls assemble_instance until
   an array dimension is settled.  Repeated calls are needed because
   assemble_instance may return a half-modified class when it has an
   array dimension, because assemble_instance cannot fold constants by
   itself. *)

fun instantiate_class (subj, k0) = (
    let
	val (dim, array, dummy) = (instantiate_with_dimension (subj, k0))
	val _ = (app (assert_cook_step E3) array)
	val k1 = (make_dummy_array_class (dim, array, dummy))
	val _ = (store_to_instance_tree subj k1)
    in
	(dim, array)
    end)

and instantiate_with_dimension (subj, k0) = (
    let
	val _= tr_build_vvv (";; instantiate_with_dimension ("^
			     (subject_print_string subj) ^" : "^
			     (class_print_name k0) ^")...")

	val k1 = (assemble_instance (subj, k0))
    in
	case k1 of
	    Def_Body ((u, f, b), j, cs, nm, cc, ee, aa, ww) => (
	    let
		val _= if (f = VAR) then () else raise Match
		val _ = (assert_cook_step E3 k1)
	    in
		([], [k1], NONE)
	    end)
	  | Def_Der _ => (
	    let
		val _ = (assert_cook_step E3 k1)
	    in
		([], [k1], NONE)
	    end)
	  | Def_Refine (x0, v, ts0, q0, (ss0, mm0), cc0, aa0, ww0) => (
	    let
		val _ = if (v = NONE) then () else raise Match
		val _ = if (not (null ss0)) then () else raise Match
		val ss1 = (map (simplify_expression k0 true) ss0)
		val dim1 = (settle_dimension k1 ss1 mm0)
		val k2 = Def_Refine (x0, v, ts0, q0, ([], []), cc0, aa0, ww0)
		val f = (instantiate_at_index (subj, k2) mm0)
		val dimarraylist = (fill_dimension f [] dim1)
		(*val arraylist = (map #2 dimarraylist)*)
		(*val dimlist = (map #1 dimarraylist)*)
		val (dimlist, arraylist) = (ListPair.unzip dimarraylist)
		val array = (List.concat arraylist)
		val size = (array_size dim1)
		val dummy = if (size <> 0) then NONE else SOME x0
	    in
		if (null dimlist) then
		    (dim1, array, dummy)
		else
		    case (list_unique_value (op =) dimlist) of
			NONE => raise error_dimensions_mismatch
		      | SOME dim0 => (dim1 @ dim0, array, dummy)
	    end)
	  | _ => raise Match
    end)

and instantiate_at_index (subj0, k0) mm0 index = (
    case k0 of
	Def_Refine (x0, v, ts0, q0, (ss_, mm_), cc0, aa0, ww0) => (
	let
	    val _ = if (v = NONE) then () else raise Match
	    val _ = if (null ss_) then () else raise Match
	    val _ = if (null mm_) then () else raise Match
	    val subj1 = (compose_subject_with_index subj0 index)
	    val mm1 = (commute_modifier_over_subscript index mm0)
	    val k1 = Def_Refine (x0, v, ts0, q0, ([], mm1), cc0, aa0, ww0)
	    val (dim, array, dummy) = (instantiate_with_dimension (subj1, k1))
	in
	    (dim, array)
	end)
      | _ => raise Match)

(* Determines a dimension of a declaration.  It needs looking at the
   RHS in cases like "A~x[:]=e". *)

and settle_dimension kp ss mm = (
    if (not (List.exists (fn x => (x = Colon)) ss)) then
	(map dimension_to_int ss)
    else
	let
	    val size = (length ss)
	    val x0 = (find_initializer_value mm)
	    val x2 = (simplify_expression kp true x0)
	    val (dim, fully) = (obtain_array_dimension x2)
	in
	    if (size <= (length dim)) then
		dim
	    else
		if (fully) then
		    raise error_dimensions_mismatch
		else
		    raise error_non_constant_array_dimension
	end)

(* Tries to fold constants to a literal value.  Folding constants
   needs to be step-by-step, because resolving new variables is
   necessary at each step. *)

and simplify_expression ctx buildphase_ w0 = (
    let
	val buildphase = true
	val w1 = (bind_in_scoped_expression buildphase ctx w0)
	val w2 = (secure_reference_in_expression ctx buildphase w1)
	val w3 = (fold_constants ctx buildphase [] w2)
    in
	if (w0 = w3) then
	    w3
	else
	    (simplify_expression ctx buildphase w3)
    end)

and secure_reference_in_expression ctx buildphase_ w0 = (
    let
	val buildphase = true
	val efix = (fn (x, _) => ((secure_reference ctx buildphase x), ()))
	val (w1, _) = (walk_in_expression efix (w0, ()))
    in
	w1
    end)

(* Makes each package/instance in a composite name be accessible in
   the class_tree/instance_tree.  It makes all array elements
   accessible and thus ignores array subscripts (and it can be done
   without folding constants).  It does not secure inside an
   expandable connector because it can contain undeclared elements.
   At each step, it descends a part of a reference in the tree.  The
   next part can be a package, a constant, or an instance, where it is
   an instance only when the current node is an instance. *)

and secure_reference ctx buildphase_ w0 = (
    case w0 of
	Vref (_, []) => raise Match
      | Vref (NONE, _) => raise Match
      | Vref (SOME ns, rr0) => (
	if (reference_is_predefined_variable w0) then
	    w0
	else
	    let
		val root = if (ns = PKG) then class_tree else instance_tree
		val path = (pseudo_reference_path rr0)
		val nodes = (secure_reference_loop ctx false path root)
	    in
		w0
	    end)
      | Iref _ => w0
      | _ => w0)

and secure_reference_loop ctx (retrying : bool) path0 node0 = (
    case path0 of
	[] => [node0]
      | ((id, ss) :: path1) => (
	let
	    val (subj, kx, cx) = node0
	    val k0 = (! kx)
	    val kp = (assemble_package_if_package (subj, k0))
	    val _ = if (kp = (! kx)) then () else raise Match
	    val (_, components) = (access_node E3 false node0)
	in
	    case (find_in_components id components) of
		NONE => (
		if (retrying) then
		    raise error_component_not_found
		else
		    let
			val (dim, array) = (instantiate_element_by_name kp id)
		    in
			(secure_reference_loop ctx true path0 node0)
		    end)
	      | SOME (slot as Slot (_, dim, nodes, dummy)) => (
		if (component_is_outer_alias slot) then
		    let
			val node1 = (dereference_outer_alias slot)
		    in
			(secure_reference_loop ctx true path0 node1)
		    end
		else if (component_is_expandable slot) then
		    nodes
		else
		    (List.concat
			 (map (secure_reference_loop ctx false path1) nodes)))
	end))

(* Checks an access is proper about scalar or array.  It is an error
   an access to a scalar instance has subscripts. *)

and check_reference_subscripts__ (Slot (v, dim, nodes, dummy)) ss = (
    case (dim, nodes) of
	([], []) => raise Match
      | ([], [(_, kx, _)]) => (
	let
	    val kp = (! kx)
	    val package = (class_is_package kp)
	in
	    if (null ss) then
		()
	    else if (package) then
		raise error_subscripts_to_package
	    else
		raise error_subscripts_to_scalar
	end)
      | ([], _) => raise Match
      | (_, []) => (
	if (null ss) then () else raise error_access_to_empty_array)
      | (_, (_, kx, _) :: _) => (
	let
	    val kp = (! kx)
	    val package = (class_is_package kp)
	    val _ = if (not package) then () else raise Match
	in
	    ()
	end))

(* Instantiates a named entry (package/instance) in a class. *)

and instantiate_element_by_name kp id = (
    let
	val subj = (subject_of_class kp)
    in
	case (find_element true kp id) of
	    NONE => raise (error_name_not_found id kp)
	  | SOME binding => (
	    let
		val (dim, array) = (instantiate_element kp binding)
	    in
		(dim, array)
	    end)
    end)

and instantiate_element kp binding = (
    let
	val Naming (id, subj, inner, _, _) = binding
    in
	case (fetch_from_instance_tree subj) of
	    SOME kx => (
	    let
		val (dim, array) = (unwrap_array_of_instances kx)
	    in
		(dim, array)
	    end)
	  | NONE => (
	    case inner of
		SOME truesubj => (
		let
		    val kx = surely (fetch_from_instance_tree truesubj)
		    val var = if (class_is_package kx) then PKG else VAR
		    val k0 = (instantiate_outer_alias var subj truesubj)
		in
		    ([], [k0])
		end)
	      | NONE => (
		let
		    val (dim, array) = (instantiate_named_element kp binding)
		in
		    (dim, array)
		end))
    end)

and instantiate_named_element kp binding = (
    case binding of
	Naming (id, subj, NONE, _, (z, r, EL_Class dx, h)) => (
	let
	    val Defclass (_, k0) = dx
	    val k2 = (assemble_package E3 (subj, k0))
	in
	    ([], [k2])
	end)
      | Naming (id, subj, NONE, _, (z, r, EL_State dx, h)) => (
	let
	    val package = (class_is_package kp)
	    val _ = if ((not package) orelse (declaration_is_constant dx))
		    then () else raise error_non_constant_in_package
	    val Defvar (_, q, k0, c0, aa, ww) = dx
	    val cc1 = (getOpt (c0, NIL))
	    val k1 = Def_Refine (k0, NONE, copy_type, q,
				 ([], []), cc1, aa, ww)
	    val (dim, array) = (instantiate_class (subj, k1))
	in
	    (dim, array)
	end)
      | Naming (id, subj, SOME _, _, _) => raise Match)

(* ================================================================ *)

(* Secures a class referenced by a subject.  This is used to assemble
   a referenced package.  It returns a single class because it is a
   package. *)

fun secure_package_subject__ ctx subj = (
    let
	val Subj (tree, cc) = subj
	val root = if (tree = PKG) then class_tree else instance_tree
	(*val path = (map (fn (id, ss) => (id, [])) cc)*)
	val path = (pseudo_reference_path cc)
	val buildphase = false
	val nodes = (secure_reference_loop ctx false path root)
    in
	case nodes of
	    [node] => (
	    let
		val (subj_, kx, cx) = node
		val k0 = (! kx)
	    in
		k0
	    end)
	  | _ => raise Match
    end)

(* ================================================================ *)

(* Calls a function on a binding when it is a component.  It skips a
   binding of a variable which has inner-outer matching, because it is
   usually already processed.  It is used to traverse the component
   variables. *)

fun call_if_component__ kp f (Naming (v, subsubj, _, _, (z, r, dd, h))) = (
    case dd of
	EL_Class dx => ()
      | EL_State dx => (
	let
	    (*val Defvar (v, q, kx, c, a, w) = dx*)
	    val subj0 = (subject_of_class kp)
	    val subcomponent = (test_subcomponent subsubj (subj0, v))

	    val _ = if ((not ((#Outer r) andalso (not (#Inner r))))
			orelse (not subcomponent)) then () else raise Match

	    val _ = tr_tree_vvv (";; component-variable ("^
				 (subject_print_string subsubj) ^")")
	in
	    if (subcomponent) then
		ignore (f (subsubj, dx))
	    else
		()
	end))

(* Instantiates the components of a class, then repeats instantiating
   in the components.  It skips ones already created, which are
   possibly created during determination of array dimensions. *)

fun instantiate_components k0 = (
    let
	fun instantiate kp binding = (
	    case binding of
		Naming (_, _, _, _, (z, r, EL_Class _, h)) => raise Match
	      | Naming (_, _, _, _, (z, r, EL_State _, h)) => (
		let
		    val (dim, array) = (instantiate_element kp binding)
		in
		    array
		end))
    in
	if (class_is_outer_alias k0) then
	    ()
	else if (class_is_simple_type k0) then
	    ()
	else
	    let
		val _ = (assert_cooked_at_least E3 k0)
		val bindings = (list_elements true k0)
		val (classes, states) =
		      (List.partition binding_is_class bindings)
		val _ = (app assert_inner_outer_condition states)
		val instances = (List.concat (map (instantiate k0) states))
	    in
		(app instantiate_components instances)
	    end
    end)

(* ================================================================ *)

val clear_syntaxer_tables = classtree.clear_syntaxer_tables
val load_file = loader.load_file
val load_class_by_name = loader.load_class_by_name
val find_class = finder.find_class

fun xreset () = (
    let
	val _ = clear_syntaxer_tables ()
	val _ = if true then
		    ignore (load_file "predefined.mo")
		else
		    ()
    in
	()
    end)

fun xload (s : string) = (
    case (load_file s) of
	[] => raise Fail ("No definitions in file ("^ s ^")")
      | (k0 :: _) => k0)

(* To parse a name: (Name (String.fields (fn c => (c = #".")) n)) *)

fun xload_msl (s : string) = (
    valOf (load_class_by_name
	       (make_name_qualified
		    (Name (String.fields (fn c => (c = #".")) s)))))

fun xfind (s : string) = (
    let
	val cooker = assemble_package
	val nn0 = (String.fields (fn c => (c = #".")) s)
	val nn1 = case nn0 of
		     [] => raise Fail ("Empty model name ("^ s ^")")
		   | ("" :: t) => t
		   | x => x
	val name = (Name nn1)
    in
	case (find_class cooker the_package_root name) of
	    NONE => raise Fail ("Class ("^ s ^") not found")
	  | SOME kx => kx
    end)

fun xbuild s = (
    let
	val subj = the_model_subject
	val k0 = (xfind s)
	val (dim, array) = (instantiate_class (subj, k0))
	val _ = if (null dim) then () else raise error_model_is_array
	val _ = if ((length array) = 1) then () else raise error_model_is_array
	val k3 = (hd array)
	(*val v = Id ""*)
	(*val q = no_component_prefixes*)
	(*val var = Defvar (v, q, k3, NONE, Annotation [], Comment [])*)
	val _ = (instantiate_components k3)
    in
	()
    end)

end
