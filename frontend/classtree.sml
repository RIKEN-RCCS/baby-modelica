(* classtree.sml -*-Coding: us-ascii-unix;-*- *)
(* Copyright (C) 2018-2020 RIKEN R-CCS *)

(* CLASS/INSTANCE TREES. *)

structure classtree :
sig
    type id_t
    type class_tag_t
    type definition_body_t
    type class_definition_t
    type subject_t
    type binding_t
    type scope_t
    type instantiation_t
    type instance_node_t
    type component_slot_t
    type cook_step_t
    type cooker_t

    val class_tree : instance_node_t
    val instance_tree : instance_node_t

    val loaded_classes : (string, class_definition_t) HashTable.hash_table
    val class_bindings : (string, binding_t list) HashTable.hash_table
    val dummy_inners : (string, binding_t) HashTable.hash_table

    val fetch_from_loaded_classes :
	class_tag_t -> class_definition_t option
    val store_to_loaded_classes :
	bool -> class_definition_t -> class_definition_t

    val fetch_from_instance_tree :
	subject_t -> definition_body_t option
    val store_to_instance_tree :
	subject_t -> definition_body_t -> definition_body_t

    val subject_to_instance_tree_path :
	subject_t -> (instantiation_t * (id_t * int list) list)

    val unwrap_array_of_instances :
	definition_body_t -> int list * definition_body_t list

    val list_base_classes :
	definition_body_t -> definition_body_t list
    val list_base_names :
	definition_body_t -> class_tag_t list

    val ensure_in_instance_tree :
	subject_t * definition_body_t -> definition_body_t
    val assemble_package_if_fresh :
	cooker_t -> cook_step_t
	-> subject_t * definition_body_t -> definition_body_t

    val main_class : definition_body_t -> definition_body_t
    val extract_base_classes :
	bool -> definition_body_t
	-> (class_tag_t * definition_body_t) list * definition_body_t
    val extract_base_elements :
	definition_body_t
	-> ((class_tag_t * definition_body_t) list
	    * scope_t list * definition_body_t)

    val fetch_base_class :
	exn -> subject_t * class_tag_t -> definition_body_t
    val fetch_class_by_scope :
	subject_t * class_tag_t -> subject_t * definition_body_t

    val descend_instance_tree :
	(id_t * int list) list -> instance_node_t -> instance_node_t option

    val clear_syntaxer_tables : unit -> unit

    val component_class : component_slot_t -> definition_body_t

    val assert_stored_in_instance_tree :
	subject_t * definition_body_t -> unit
    val assert_package_constraints : instance_node_t -> unit
    val assert_enclosings_are_cooked : definition_body_t -> unit

    val xfetch0 : string -> definition_body_t option
    val xfetch1 : string -> definition_body_t option
end = struct

open plain
open settings
open ast
open small0

fun tr_load (s : string) = if true then (print (s ^"\n")) else ()
fun tr_load_vvv (s : string) = if false then (print (s ^"\n")) else ()

(* ================================================================ *)

val table_size_hint = 500

(* The loaded_classes table contains all loaded classes.  It is not
   the "class-tree".  It is keyed by a class-tag (a qualified name,
   such as ".Modelica.Fluid").  All the names have an initial dot.
   Nested definitions in a class are displaced (which are stored in
   their own entries).  The classes in this table are at step=E0. *)

val loaded_classes : (string, class_definition_t) HashTable.hash_table = (
    HashTable.mkTable (table_size_hint, error_not_found_in_table))

(* The class_bindings table maps a class to its list of bindings.
   Bindings are the names defined in the class.  It is keyed by a
   subject.  (It is keyed by an instance name (subject_t) and a
   CTAG). *)

val class_bindings : (string, binding_t list) HashTable.hash_table = (
    HashTable.mkTable (table_size_hint, Match))

(* The dummy_inners table records an inner created for an unmatched
   outer.  It is a mapping from a variable to a binding.  It is keyed
   by a composite of names and subscripts (subject_t). *)

val dummy_inners : (string, binding_t) HashTable.hash_table = (
    HashTable.mkTable (table_size_hint, Match))

fun clear_table t = (
    (map (fn (n, d) => (HashTable.remove t n))
	      (HashTable.listItemsi t)))

(* Puts a class definition to the class-table.  It returns a
   displaced-tag.  It replaces an existing one when overwrite=true, or
   raise an error. *)

fun store_to_loaded_classes overwrite (d as Defclass ((v, pkg), k)) = (
    let
	val _ = if (definition_is_displaceable d) then () else raise Match
	val _ = if (not (class_is_in_file d)) then () else raise Match
	val _ = if (not (class_is_displaced d)) then () else raise Match
	val tag = (tag_of_definition d)
	val s = (tag_to_string tag)
	val _ = case (HashTable.find loaded_classes s) of
		    NONE => ()
		  | SOME x => (
		    if ((class_is_in_file x) orelse overwrite) then ()
		    else raise (error_duplicate_definitions d))
	val _ = ignore (HashTable.insert loaded_classes (s, d))
	val _ = tr_tree_vvv (";; - Loaded ("^ s ^")")
    in
	Defclass ((v, pkg), Def_Displaced (tag, bad_subject))
    end)

(* It may return a displaced-tag when a package is loaded but the
   class is not yet loaded. *)

fun fetch_from_loaded_classes (tag : class_tag_t) = (
    if (tag_is_root tag) then
	SOME the_root_class_definition
    else
	let
	    val s = (tag_to_string tag)
	in
	    case (HashTable.find loaded_classes s) of
		NONE => NONE
	      | SOME (d as Defclass ((v, g), k)) => (
		case k of
		    Def_Body _ => SOME d
		  | Def_Der _ => raise Match
		  | Def_Primitive _ => raise Match
		  | Def_Name _ => raise Match
		  | Def_Scoped _ => raise Match
		  | Def_Refine _ => raise Match
		  | Def_Extending _ => raise Match
		  | Def_Replaced _ => raise Match
		  | Def_Displaced _ => raise Match
		  | Def_In_File => (
		    SOME (Defclass ((v, g),
				    Def_Displaced (tag, bad_subject))))
		  | Def_Mock_Array _ => raise Match)
	end)

(* ================================================================ *)

type instance_node_t = common.instance_node_t

(* The class_tree is rooted by the unnamed-enclosing-class, and stores
   packages.  It stores packages at step=E0-E5.  It is the same as the
   instance_tree but for a separate root. *)

val class_tree : instance_node_t =
      (the_root_subject, ref the_root_class, ref [])

(* The instance_tree is rooted by the model, and stores the instances
   and their packages.  The instance_tree only stores instances at
   step=E5, but stores packages at step=E0-E5.  A class for instances
   at step=E0-E4 is singular but may have non-null dimension, which
   may generate multiple instances at step=E5. *)

val instance_tree : instance_node_t =
      (the_model_subject, ref Def_In_File, ref [])

(* Accesses a component at an index.  An access with index=[] means
   either as a scalar or as an array.  The returned node has empty
   components for an array (accessing components are forbidden for an
   array). *)

fun access_component subj (Slot (v, dim, ee, dummy)) index = (
    case (index, dim) of
	([], []) => (
	let
	    val _ = if ((length ee) = 1) then () else raise Match
	    val node = (hd ee)
	    val (subjx, kx, _) = node
	    val kp = (! kx)
	    val _ = if (subjx = subj) then () else raise Match
	    val _ = if (step_is_less E1 kp) then ()
		    else (assert_match_subject_sans_subscript subj kp)
	in
	    node
	end)
      | ([], _) => (
	let
	    val array = (map ((op !) o #2) ee)
	    val _ = (app (assert_match_subject_sans_subscript subj) array)
	in
	    (subj, ref (Def_Mock_Array (dim, array, dummy)), ref [])
	end)
      | (_, []) => raise error_array_index_to_scalar
      | (_, _) => (
	let
	    val i = (array_index dim index 0)
	    val _ = if (i < (length ee)) then () else raise error_array_index
	    val node = (List.nth (ee, i))
	in
	    node
	end))

(* Accesses an instance_tree node by an element of a subject.  It may
   return a node or NONE. *)

fun descend_instance_tree_step (v, index) (node0 : instance_node_t) = (
    case node0 of
	(subj, kx, cx) => (
	let
	    val components = (! cx)
	in
	    case (List.find (fn (Slot (x, _, _, _)) => (x = v)) components) of
		NONE => NONE
	      | SOME (slot as Slot (v_, _, array, _)) => (
		let
		    val subjx = (compose_subject subj v [])
		in
		    SOME (access_component subjx slot index)
		end)
	end))

(* Finds an instance or an array of instances, by descending an
   instance_tree.  It returns a temporarily created dummy node, when
   it returns an array of instances. *)

fun descend_instance_tree path0 (node0 : instance_node_t) = (
    case path0 of
	[] => SOME node0
      | ((v, ss) :: path1) => (
	let
	    val node1 = (descend_instance_tree_step (v, ss) node0)
	in
	    case node1 of
		NONE => NONE
	      | SOME node1x => (
		(descend_instance_tree path1 node1x))
	end))

(* Checks if constraints of hierarchy in the instance_tree (actually
   no constraits). *)

fun assert_package_constraints node = (
    let
	val (_, kx, componentsx) = node
	val k = (! kx)
	val components = componentsx
	val package = (class_is_package k)
	val _ = if (not package) then ()
		else if (step_is_at_least E0 k) then ()
		else raise Match
    in
	()
    end)

fun subject_to_instance_tree_path subj = (
    case subj of
	Subj (_, (Id "", _) :: _) => raise Match
      | Subj (VAR, path) => (VAR, path)
      | Subj (PKG, path) => (PKG, path))

(* Fetchs an instance in the instance_tree. *)

fun fetch_from_instance_tree subj : definition_body_t option = (
    let
	val (tree, path) = (subject_to_instance_tree_path subj)
	val root = if (tree = PKG) then class_tree else instance_tree
	val node = (descend_instance_tree path root)
    in
	case node of
	    NONE => NONE
	  | SOME (_, kx, components) => (
	    let
		val k0 = (! kx)
	    in
		SOME k0
	    end)
    end)

(* Stores a package, an instance, or an array of instances.  It
   requires index=[] in the last part of the subject to collectively
   store an array of instances.  It needs a subject argument, because
   an instance array can be empty and a subject cannot be obtained.
   Also, a package at step=E0 is not associated with a subject yet.
   It checks the syntaxing step is increasing until step=E5 (this
   check is mainly for packages).  Classes with step=E5 and higher can
   be stored multiple times.  It uses two nodes, where the parent node
   is used when adding an new entry. *)

fun store_to_instance_tree subj kp = (
    let
	fun store_model (subj, k0) = (
	    let
		val _ = tr_tree (";; - [cook] Register ("^
				 (subject_body_to_string (subj, k0)) ^")")
		val (_, kx, cx) = instance_tree
		val _ = kx := k0
	    in
		k0
	    end)

	fun store_scalar upnode node id (subj, k0) = (
	    let
		val _ = tr_tree (";; - [cook] Register ("^
				 (subject_body_to_string (subj, k0)) ^")")

		val _ = if ((cook_step k0) = E0) then ()
			else (assert_match_subject subj k0)
		val _ = if ((cook_step k0) = E0) then ()
			else if (class_is_package k0) then ()
			else (assert_cooked_at_least E3 k0)
	    in
		case (upnode, node) of
		    ((_, kx, cx), NONE) => (
		    let
			val _ = (assert_package_constraints upnode)
			val newnode = (subj, ref k0, ref [])
			val one = Slot (id, [], [newnode], NONE)
			val components = (! cx)
			val _ = cx := (components @ [one])
		    in
			k0
		    end)
		  | (_, SOME (_, kx, cx)) => (
		    let
			val step = (cook_step k0)
			val _ = if (step_is_at_least E5 k0) then ()
				else if (step_is_less step (! kx)) then ()
				else raise Match
			val _ = kx := k0
		    in
			k0
		    end)
	    end)

	fun array_node aggsubj k0 = (
	    let
		val _ = if (not (class_is_package k0)) then () else raise Match
		val _ = (assert_cooked_at_least E3 k0)
		val _ = (assert_match_subject_sans_subscript aggsubj k0)
	    in
		((subject_of_class k0), ref k0, ref [])
	    end)

	fun store_array upnode node id aggsubj (dim, array, dummy) = (
	    let
		val _ = tr_tree (";; - [cook] Register ("^
				 (if (null array) then
				      (subject_print_string aggsubj)
				  else
				      (subject_body_to_string
					   (aggsubj, (hd array))))
				 ^")")
	    in
		case (upnode, node) of
		    ((_, kx, cx), NONE) => (
		    let
			val newnodes = (map (array_node aggsubj) array)
			val one = Slot (id, dim, newnodes, dummy)
			val components = (! cx)
			val _ = cx := (components @ [one])
		    in
			kp
		    end)
		  | (_, SOME _) => raise Match
	    end)
    in
	if (subj = the_model_subject) then
	    (store_model (subj, kp))
	else
	    let
		val (tree, path) = (subject_to_instance_tree_path subj)
		val (prefix, (id, ss)) = (split_last path)
		val root = if (tree = PKG) then class_tree else instance_tree
		val upnode = surely (descend_instance_tree prefix root)
		val node = (descend_instance_tree [(id, ss)] upnode)
	    in
		case kp of
		    Def_Body _ => (
		    (store_scalar upnode node id (subj, kp)))
		  | Def_Der _ => (
		    (store_scalar upnode node id (subj, kp)))
		  | Def_Primitive (P_Enum _ , e) => (
		    (store_scalar upnode node id (subj, kp)))
		  | Def_Primitive (_ , e) => raise Match
		  | Def_Name _ => raise Match
		  | Def_Scoped _ => raise Match
		  | Def_Refine _ => (
		    (store_scalar upnode node id (subj, kp)))
		  | Def_Extending _ => raise Match
		  | Def_Replaced _ => raise Match
		  | Def_Displaced _ => (
		    (store_scalar upnode node id (subj, kp)))
		  | Def_In_File => raise Match
		  | Def_Mock_Array (dim, classes, dummy) => (
		    let
			val _ = if (null ss) then () else raise Match
			val _ = if (node = NONE) then () else raise Match
		    in
			(store_array upnode node id subj (dim, classes, dummy))
		    end)
	    end
    end)

(* Extracts an array from a temporarily created array class. *)

fun unwrap_array_of_instances k = (
    case k of
	Def_Mock_Array (dims, array, dummy) => (dims, array)
      | _ => ([], [k]))

fun clear_instance_tree () = (
    let
	val (_, kx, components) = class_tree
	val _ = kx := the_root_class
	val _ = components := []
	val (_, kx, components) = instance_tree
	val _ = kx := Def_In_File
	val _ = components := []
    in () end)

fun assert_stored_in_instance_tree (subj, k) = (
    case (fetch_from_instance_tree subj) of
	NONE => raise Match
      | SOME x => if (x = k) then () else raise Match)

fun main_class kp = (
    if (class_is_main kp) then
	kp
    else
	let
	    val subj = (subject_of_class kp)
	    val km = surely (fetch_from_instance_tree subj)
	    val _ = if (class_is_main km) then () else raise Match
	in
	    km
	end)

(* ================================================================ *)

(* Removes a Base_Classes element from a class.  It returns a removed
   class along with a list.  Only a main (non-base) class has a
   Base_Classes element, and it errs if it is not when
   canbenone=false. *)

fun extract_base_classes canbenone (k0 : definition_body_t) = (
    let
	val (basesopt, k1) = (extract_bases_in_main_class k0)
    in
	case basesopt of
	    NONE => if (canbenone) then ([], k1) else raise Match
	  | SOME bases => (bases, k1)
    end)

(* Removes a Base_List element from a class.  It returns a removed
   class along with a list. *)

fun extract_base_list (k0 : definition_body_t) = (
    let
	fun base_list e = (
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
	      | Base_List _ => true
	      | Base_Classes _ => false)

	fun content e = (
	    case e of
		Base_List u => u
	      | _ => raise Match)

	val (bb, ee) = (List.partition base_list (body_elements k0))
	val bases = (List.concat (map content bb))
	val k1 = (replace_body_elements k0 ee)
    in
	(bases, k1)
    end)

(* Removes elements of Base_Classes and Base_List from a class, and
   returns a class along with them.  It can be called with a base
   class, which contains no Base_Classes. *)

fun extract_base_elements (k0 : definition_body_t) = (
    let
	val (classes, k1) = (extract_base_classes true k0)
	val (list, k2) = (extract_base_list k1)
    in
	(classes, list, k2)
    end)

(* Returns a list of all base classes of its main class.  Note that
   the list of bases is stored in the main class. *)

fun obtain_base_list k0 = (
    case (extract_bases_in_main_class k0) of
	(SOME bb, _) => bb
      | (NONE, _) => (
	let
	    val subj = (subject_of_class k0)
	    val main = surely (fetch_from_instance_tree subj)
	in
	    case (extract_bases_in_main_class main) of
		(SOME bb, _) => bb
	      | (NONE, _) => raise Match
	end))

(* Returns a list of bases.  A list of the base classes are only
   recorded in the main class, and thus, a class selects its bases
   from the list.  Note that only a main class contains a single list
   of the base classes.  But, as an exception, classes may temporarily
   contain multiple lists during gathering base classes. *)

fun list_base_classes k0 = (
    let
	fun select bases (_, tag) = (
	    case (List.find (fn (x, b) => (x = tag)) bases) of
		NONE => raise Match
	      | SOME (tag, b) => b)

	val bases = (obtain_base_list k0)
	val (names, _) = (extract_base_list k0)
    in
	(map (select bases) names)
    end)

fun list_base_names k = (map (fn (v, tag) => tag) (#1 (extract_base_list k)))

(* Returns a list of base classes. *)

fun list_bases_of_main_class (k0 : definition_body_t) = (
    let
	val (maybebases, _) = (extract_bases_in_main_class k0)
    in
	case maybebases of
	    NONE => []
	  | SOME bases => (map #2 bases)
    end)

(* Stores a class if it does not exist in instance_tree.  It is
   usually used with unprocessed classes. *)

fun ensure_in_instance_tree (subj, kp) = (
    case (fetch_from_instance_tree subj) of
	SOME kx => (
	let
	    val _ = if ((cook_step kp) = E0) then ()
		    else if ((cook_step kx) = E0) then ()
		    else if (innate_tag kx = innate_tag kp) then ()
		    else raise Match
	in
	    kx
	end)
      | NONE => (
	(store_to_instance_tree subj kp)))

(* Calls assemble_package on a class.  All indirect calls to
   assemble_package are through this. *)

fun assemble_package_if_fresh (cooker : cooker_t) step (subj, k0) = (
    let
	val _ = if (step_compare step (op >=) E1) then () else raise Match
	val _ = if (step_compare step (op <=) E3) then () else raise Match

	(*val k1 = (ensure_in_instance_tree (subj, k0))*)
	val k1 = k0
	val _ = if ((cook_step k1) <> E1) then ()
		else warn_cycle_in_lookup ()
    in
	if ((cook_step k1) = E0) then
	    (cooker step (subj, k1))
	else
	    k1
    end)

(* ================================================================ *)

(* Returns a class having the given tag among the main or base
   classes.  It is used to find a declaring class.  It is needed
   because only main classes are named by instance/package names but
   base classes are nameless. *)

fun seek_declaring_class ex kp tag = (
    if ((tag_of_body kp) = tag) then
	SOME kp
    else if (step_is_less E3 kp) then
	raise ex
    else
	let
	    val bases = (obtain_base_list kp)
	in
	    case (List.find (fn (x, kx) => (x = tag)) bases) of
		NONE => NONE
	      | SOME (_, kx) => SOME kx
	end)

fun fetch_base_class ex (subj, tag) = (
    case (fetch_from_instance_tree subj) of
	NONE => raise Match
      | SOME kx => (
	surely (seek_declaring_class ex kx tag)))

fun fetch_class_by_scope (subj, tag) = (
    let
	val ex = Match
	val k0 = (fetch_base_class ex (subj, tag))
	val subj1 = (subject_of_class k0)
    in
	(subj1, k0)
    end)

fun component_class (Slot (v, dim, nodes, dummy)) = (
    if (dim = []) then
	let
	    val _ = if ((length nodes) = 1) then () else raise Match
	    val (subj, kx, components) = (hd nodes)
	in
	    (! kx)
	end
    else if ((array_size dim) = 0) then
	case dummy of
	    NONE => raise Match
	  | SOME k => Def_Mock_Array (dim, [], dummy)
    else
	let
	    val array = (map (! o #2) nodes)
	in
	    case dummy of
		NONE => Def_Mock_Array (dim, array, dummy)
	      | SOME _ => raise Match
	end)

(* ================================================================ *)

fun assert_enclosings_are_cooked k0 = (
    let
	val _ = if (step_is_at_least E3 k0) then () else raise Match
	val tag = (tag_of_body k0)
	val (_, pkg) = (tag_prefix tag)
    in
	if (pkg = the_root_tag) then
	    ()
	else
	    let
		val subj = (tag_to_subject pkg)
		val k1 = surely (fetch_from_instance_tree subj)
	    in
		(assert_enclosings_are_cooked k1)
	    end
    end)

(* ================================================================ *)

fun clear_syntaxer_tables () = (
    let
	val _ = (clear_table loaded_classes)
	val _ = (clear_table dummy_inners)
	val _ = (clear_table class_bindings)
	val _ = (clear_instance_tree ())
    in () end)

(* ================================================================ *)

fun dump_table t = (
    (HashTable.appi (fn (n, d) => (print (n ^ "\n"))) t))

fun dump_loaded_classes () = (dump_table loaded_classes)

fun xfetch0 (s : string) = (
    let
	val d0 = (fetch_from_loaded_classes
		      (make_name_qualified
			   (Name (String.fields (fn c => (c = #".")) s))))
    in
	case d0 of
	    NONE => NONE
	  | SOME (Defclass ((v, g), k0)) => SOME k0
    end)

(* Returns a subject for name, where a dot prefix of a name indicates
   a package-root. *)

fun name_to_subject (Name (nn : string list)) = (
    case nn of
	[""] => Subj (VAR, [])
      | ("" :: tt) => Subj (PKG, (map (fn v => (Id v, [])) tt))
      | _ => Subj (VAR, (map (fn v => (Id v, [])) nn)))

(* The model is accessible by "", but "." is illegal and the
   package-root is inaccessible. *)

fun xfetch1 (s : string) = (
    (fetch_from_instance_tree
	 (name_to_subject (Name (String.fields (fn c => (c = #".")) s)))))

fun xfetch2 (subjtag : string) = (
    let
	val key = subjtag
    in
	(HashTable.find class_bindings key)
    end)

end
