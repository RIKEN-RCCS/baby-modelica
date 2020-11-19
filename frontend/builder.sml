(* builder.sml -*-Coding: us-ascii-unix;-*- *)
(* Copyright (C) 2018-2020 RIKEN R-CCS *)

(* MODEL BUILDER.  Builder instantiates a model by traversaling the
   state variables. *)

structure builder :
sig
    type class_definition_t
    type definition_body_t
    type expression_t
    type subject_t
    type ctx_t

    val secure_reference :
	definition_body_t -> bool -> expression_t -> expression_t
    val secure_subject :
	definition_body_t -> subject_t -> definition_body_t

    val xreset : unit -> unit
    val xload : string -> class_definition_t
    val xfind : string -> subject_t * definition_body_t
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

val find_name_initial_part = finder.find_name_initial_part
val list_elements = finder.list_elements

val assemble_instance = cooker.assemble_instance
val assemble_package = cooker.assemble_package
val commute_modifier_over_subscript = refiner.commute_modifier_over_subscript

val walk_in_expression = walker.walk_in_expression

val fold_constants_in_expression = folder.fold_constants_in_expression
val value_of_instance = folder.value_of_instance

val obtain_array_dimension = operator.obtain_array_dimension

val bind_in_expression = binder.bind_in_expression
val bind_in_scoped_expression = binder.bind_in_scoped_expression
(*val bind_in_instance = binder.bind_in_instance*)
val bind_in_value = binder.bind_in_value

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

(* ================================================================ *)

(* Instantiates a class.  It repeatedly calls assemble_instance until
   an array dimension is settled.  Repeated calls are needed because
   assemble_instance may return a half-modified class when it has an
   array dimension, because assemble_instance cannot fold constants by
   itself. *)

fun instantiate_class (subj, k0) = (
    let
	val (dim, array, dummy)
	    = (instantiate_with_dimension (subj, k0))
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
	    Def_Body ((u, f, b), j, cs, nm, ee, aa, ww) => (
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
	  | Def_Refine (x0, v, ts0, q0, (ss0, mm0), aa0, ww0) => (
	    let
		val _ = if (v = NONE) then () else raise Match
		val _ = if (not (null ss0)) then () else raise Match
		val ss1 = (map (simplify_expression k0 true) ss0)
		val dim1 = (settle_dimension k1 ss1 mm0)
		val k2 = Def_Refine (x0, v, ts0, q0, ([], []), aa0, ww0)
		val f = (instantiate_at_index (subj, k2) mm0)
		val dimarraylist = (fill_dimension f [] dim1)
		val arraylist = (map #2 dimarraylist)
		val array = (List.concat arraylist)
		val dimlist = (map #1 dimarraylist)
		val xdim0 = (list_all_equal (op =) dimlist)
		val size = (array_size dim1)
		val dummy = if (size <> 0) then NONE else SOME x0
	    in
		case xdim0 of
		    NONE => raise error_dimensions_mismatch
		  | SOME NONE => (dim1, array, dummy)
		  | SOME (SOME dim0) => (dim1 @ dim0, array, dummy)
	    end)
	  | _ => raise Match
    end)

and instantiate_at_index (subj0, k0) mm0 index = (
    case k0 of
	Def_Refine (x0, v, ts0, q0, (ss_, mm_), aa0, ww0) => (
	let
	    val _ = if (v = NONE) then () else raise Match
	    val _ = if (null ss_) then () else raise Match
	    val _ = if (null mm_) then () else raise Match
	    val subj1 = (compose_subject_with_index subj0 index)
	    val mm1 = (commute_modifier_over_subscript index mm0)
	    val k1 = Def_Refine (x0, v, ts0, q0, ([], mm1), aa0, ww0)
	    val (dim, array, dummy)
		= (instantiate_with_dimension (subj1, k1))
	in
	    (dim, array)
	end)
      | _ => raise Match)

(* Tries to fold constants to be a literal value.  Folding constants
   needs to be one-step, because binding variables is required at each
   step. *)

and simplify_expression ctx buildphase w0 = (
    let
	val buildphase = true
	val w1 = (bind_in_scoped_expression buildphase ctx w0)
	val w2 = (secure_reference_in_expression ctx buildphase w1)
	val w3 = (fold_constants_in_expression ctx buildphase w2)
    in
	if (w0 = w3) then
	    w3
	else
	    (simplify_expression ctx buildphase w3)
    end)

and secure_reference_in_expression ctx buildphase w0 = (
    let
	val fixer = {fixer = (fn (x, _) =>
				 ((secure_reference ctx buildphase x), ()))}
	val (w1, _) = (walk_in_expression fixer (w0, ()))
    in
	w1
    end)

(* Makes each package/instance in a composite variable reference be
   accessible in the class_tree/instance_tree.  It secures all array
   elements and thus ignores array subscripts (and it can be done
   without folding constants).  At each step, it descends a part of a
   reference in the tree.  The next part can be a package, a constant,
   or an instance, where it is an instance only when the current node
   is an instance. *)

and secure_reference ctx buildphase w0 = (
    case w0 of
	Vref (false, _) => raise Match
      | Vref (true, _) => (
	let
	    val (tree, path) = (pseudo_path_for_reference w0)
	    val root = if (tree = PKG) then class_tree else instance_tree
	    val nodes = (secure_reference_loop ctx buildphase false path root)
	    (*
	    val vars = (map (! o #2) nodes)
	    val _ = (map (bind_in_value {k = ctx} buildphase) vars)
	    *)
	in
	    w0
	end)
      | Iref _ => w0
      | _ => w0)

and secure_reference_loop ctx buildphase (retrying : bool) path0 node0 = (
    case path0 of
	[] => [node0]
      | ((id, ss) :: path1) => (
	let
	    val (subj, kx, cx) = node0
	    val k0 = (! kx)
	    val components = (! cx)

	    val kp = if (class_is_instance k0) then
			 k0
		     else
			 (assemble_package E3 (subj, k0))

	    val _ = if (kp = (! kx)) then () else raise Match
	    val _ = if (step_is_at_least E3 kp) then () else raise Match
	    val _ = if (not (class_is_simple_type kp)) then ()
		    else if (class_is_enum kp) then ()
		    else raise error_attribute_access_to_simple_type
	in
	    case (List.find (fn (Slot (x, _, _, _)) => (x = id)) components) of
		NONE => (
		let
		    val _ = if (not retrying) then () else raise Match
		    val (dim, array) = (instantiate_class_in_class kp id)
		in
		    (secure_reference_loop
			 ctx buildphase true path0 node0)
		end)
	      | SOME (cc as Slot (v_, dim, nodes, dummy)) => (
		let
		    val _ = (check_reference_subscripts cc ss)
		in
		    (List.concat
			 (map (secure_reference_loop
				   ctx buildphase false path1) nodes))
		end)
	end))

(* Checks an access is proper about scalar or array.  It is an error
   an access to a scalar instance has subscripts. *)

and check_reference_subscripts (Slot (v, dim, nodes, dummy)) ss = (
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

and instantiate_class_in_class kp id = (
    let
	val cooker = assemble_package
	(*fun cook_faulting wantedstep (subj, kx) = raise Match*)
	(*val cooker = cook_faulting*)
	val subj = (subject_of_class kp)
	val package = (class_is_package kp)
    in
	case (find_name_initial_part cooker E3 (subj, kp) id) of
	    NONE => raise (error_name_not_found id kp)
	  | SOME (Binding (_, subsubj, _, (z, r, EL_Class d, h))) => (
	    let
		(*val _ = if (package) then ()
		  else raise (error_name_is_class id kp)*)
		val Defclass (_, k0) = d
		val k2 = (assemble_package E3 (subsubj, k0))
	    in
		([], [k2])
	    end)
	  | SOME (Binding (_, subsubj, _, (z, r, EL_State d, h))) => (
	    let
		val _ = if ((not package) orelse (declaration_is_constant d))
			then () else raise error_non_constant_in_package
		val subcomponent = (test_subcomponent subsubj (subj, id))
	    in
		if (subcomponent) then
		    let
			val Defvar (_, q, k0, c, aa, ww) = d
			val k1 = Def_Refine (k0, NONE, copy_type, q,
					     ([], []), aa, ww)
			val _ = print "(AHO) DROP CONDITIONAL\n"
			val (dim, array) = (instantiate_class (subsubj, k1))
		    in
			(dim, array)
		    end
		else
		    case (fetch_from_instance_tree subsubj) of
			NONE => raise Match
		      | SOME (Def_Mock_Array (dim, array, _)) => (dim, array)
		      | SOME k1 => ([], [k1])
	    end)
    end)

(* Determines a dimension of a declaration, which needs looking at the
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

(* ================================================================ *)

(* Secures a class referenced by a subject.  This is used to assemble
   a referenced package.  It returns a single class because it is a
   package. *)

fun secure_subject ctx subj = (
    let
	val Subj (tree, cc) = subj
	val root = if (tree = PKG) then class_tree else instance_tree
	val path = (map (fn (id, ss) => (id, [])) cc)
	val buildphase = false
	val nodes = (secure_reference_loop ctx buildphase false path root)
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

fun call_if_component kp f (Binding (v, subsubj, _, (z, r, dd, h))) = (
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

(* Instantiates a class by one or by an array of it, then traverses
   the instances.  It skips an instantiation when one has been created
   during determination of array dimensions.  Note that the subject is
   always a non-array (at the last part), and it collectively creates
   an array of instances. *)

fun traverse_with_instantiation (subj, d0) = (
    let
	fun traverse kx = (
	    if (class_is_simple_type kx) then
		()
	    else
		let
		    val _ = (assert_match_subject_sans_subscript subj kx)
		    val cooker = assemble_package
		    val bindings = (list_elements cooker true kx)
		    val (classes, states) =
			  (List.partition binding_is_class bindings)
		    val fx = traverse_with_instantiation
		    val _ = (app (call_if_component kx fx) states)
		in
		    ()
		end)

	val _ = (assert_subject_is_not_array subj)
	val Defvar (v, q, k0, c, aa, ww) = d0
	val k1 = Def_Refine (k0, NONE, copy_type, q, ([], []), aa, ww)
	val _ = print "(AHO) DROP CONDITIONAL\n"
    in
	case (fetch_from_instance_tree subj) of
	    SOME kx => (
	    let
		val (dim, array) = (unwrap_array_of_instances kx)
		val ee = (map traverse array)
	    in
		()
	    end)
	  | NONE => (
	    let
		val (dim, array) = (instantiate_class (subj, k1))
		val ee = (map traverse array)
	    in
		()
	    end)
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
	val root = (the_root_subject, the_root_class)
    in
	case (find_class cooker root name) of
	    NONE => raise Fail ("Class ("^ s ^") not found")
	  | SOME (enclosing, kx) => (enclosing, kx)
    end)

fun xbuild s = (
    let
	val subj = the_model_subject
	val (enclosing, k0) = (xfind s)
	val (dim, array) = (instantiate_class (subj, k0))
	val _ = if (null dim) then () else raise Match
	val _ = if ((length array) = 1) then () else raise Match
	val k3 = (hd array)
	val v = Id ""
	val q = no_component_prefixes
	val var = Defvar (v, q, k3, NONE, Annotation [], Comment [])
	val _ = (traverse_with_instantiation (subj, var))
    in
	()
    end)

end
