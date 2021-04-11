(* classtree.sml -*-Coding: us-ascii-unix;-*- *)
(* Copyright (C) 2018-2021 RIKEN R-CCS *)

(* CLASS/INSTANCE TREES. *)

structure classtree :
sig
    type id_t
    type class_tag_t
    type definition_body_t
    type subject_t
    type naming_t
    type scope_t
    type instantiation_t
    type instance_node_t
    type component_slot_t
    type cook_step_t
    type cooker_t
    type inner_outer_slot_t
    type expression_t

    val class_tree : instance_node_t
    val instance_tree : instance_node_t
    val package_root_node : instance_node_t
    val model_root_node : instance_node_t

    val loaded_classes : (string, definition_body_t) HashTable.hash_table
    val class_bindings : (string, naming_t list) HashTable.hash_table
    val dummy_inners : (string, naming_t) HashTable.hash_table

    val inner_outer_table : inner_outer_slot_t ref

    val fetch_from_loaded_classes :
	class_tag_t -> definition_body_t option
    val store_to_loaded_classes :
	bool -> definition_body_t -> definition_body_t

    val fetch_from_instance_tree :
	subject_t -> definition_body_t option
    val store_to_instance_tree :
	subject_t -> definition_body_t -> definition_body_t

    val insert_outer_alias :
	instantiation_t -> subject_t -> subject_t -> definition_body_t
    val substitute_outer_reference : expression_t -> expression_t

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
    val fetch_class_by_part :
	subject_t * class_tag_t -> subject_t * definition_body_t

    val fetch_instance_tree_node : subject_t -> instance_node_t option
    val descend_instance_tree_node :
	id_t -> instance_node_t -> component_slot_t option

    val traverse_tree :
	(definition_body_t * 'a -> 'a) -> instance_node_t * 'a -> 'a
    val traverse_tree_with_stop :
	(definition_body_t * 'a -> bool * 'a) -> instance_node_t * 'a -> 'a

    val access_node :
	cook_step_t -> bool -> instance_node_t
	-> (definition_body_t * component_slot_t list)

    val dereference_outer_alias : component_slot_t -> instance_node_t
    val component_is_outer_alias : component_slot_t -> bool
    val component_is_expandable : component_slot_t -> bool
    val component_class : component_slot_t -> definition_body_t

    val find_in_components :
	id_t -> component_slot_t list -> component_slot_t option

    val clear_syntaxer_tables : unit -> unit

    val enumerate_instances :
	(subject_t * 'a list -> 'a list) -> id_t list
	-> 'a list -> 'a list

    val dummy_scope : unit -> scope_t

    val assert_stored_in_instance_tree :
	subject_t * definition_body_t -> unit
    val assert_package_constraints : instance_node_t -> unit
    val assert_enclosings_are_cooked : definition_body_t -> unit

    val xfetch0 : string -> definition_body_t option
    val xfetch1 : string -> definition_body_t option
end = struct

open plain ast common message small0

fun trace n (s : string) = if n <= 1 then (print (s ^"\n")) else ()

(* ================================================================ *)

val table_size_hint = 500

(* The loaded_classes table contains all loaded classes.  It is not
   the "class-tree".  It is keyed by a class-tag (a fully qualified
   name, such as ".Modelica.Fluid").  A name string has an initial
   dot.  Nested definitions in a class are displaced (which are stored
   in their own entries).  The classes in this table are at
   step=E0. *)

val loaded_classes : (string, definition_body_t) HashTable.hash_table = (
    HashTable.mkTable (table_size_hint, error_not_found_in_table))

(* The class_bindings table maps a class to its list of bindings.
   Bindings are the names defined in the class.  It is keyed by a
   subject.  (It is keyed by an instance name (subject_t) and a
   CTAG). *)

val class_bindings : (string, naming_t list) HashTable.hash_table = (
    HashTable.mkTable (table_size_hint, Match))

(* The dummy_inners table records an inner created for an unmatched
   outer.  Keys are subjects. *)

val dummy_inners : (string, naming_t) HashTable.hash_table = (
    HashTable.mkTable (table_size_hint, Match))

fun clear_table t = (
    (map (fn (n, d) => (HashTable.remove t n))
	      (HashTable.listItemsi t)))

(* Puts a class definition to the class-table.  It returns a
   displaced-tag.  It replaces an existing one when overwrite=true, or
   raise an error. *)

fun store_to_loaded_classes overwrite k = (
    let
	val _ = if (body_is_displaceable k) then () else raise Match
	val _ = if (not (body_is_in_file k)) then () else raise Match
	val _ = if (not (body_is_displaced k)) then () else raise Match
	val tag = (tag_of_body k)
	val s = (tag_to_string tag)
	val _ = case (HashTable.find loaded_classes s) of
		    NONE => ()
		  | SOME kx => (
		    if ((body_is_in_file kx) orelse overwrite) then ()
		    else raise (error_duplicate_definitions k))
	val _ = ignore (HashTable.insert loaded_classes (s, k))
	val _ = trace 5 (";; - Loaded ("^ s ^")")
    in
	Def_Displaced (tag, bad_subject)
    end)

(* Fetches a class from the loaded_classes table.  It may return a
   displaced-tag when a package is loaded but the class is not yet
   loaded. *)

fun fetch_from_loaded_classes (tag : class_tag_t) = (
    if (tag_is_root tag) then
	SOME the_package_root
    else
	let
	    val s = (tag_to_string tag)
	in
	    case (HashTable.find loaded_classes s) of
		NONE => NONE
	      | SOME k => (
		case k of
		    Def_Body _ => (
		    let
			val _ = if ((tag_of_body k) = tag) then ()
				else raise Match
		    in
			SOME k
		    end)
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
		  | Def_In_File tag1 => (
		    let
			val _ = if (tag = tag1) then () else raise Match
			val kx = Def_Displaced (tag, bad_subject)
		    in
			SOME kx
		    end)
		  | Def_Mock_Array _ => raise Match)
	end)

(* ================================================================ *)

type instance_node_t = common.instance_node_t
type component_slot_t = common.component_slot_t

(* The class_tree is rooted by the unnamed-enclosing-class, and stores
   packages.  It stores packages at step=E0-E5.  It is the same as the
   instance_tree but for a separate root. *)

val class_tree : instance_node_t =
      (the_package_root_subject, ref the_package_root, ref [])

(* The instance_tree is rooted by the model, and stores the instances
   and their packages.  The instance_tree only stores instances at
   step=E5, but stores packages at step=E0-E5.  A class for instances
   at step=E0-E4 is singular but may have non-null dimension, which
   may generate multiple instances at step=E5. *)

val instance_tree : instance_node_t =
      (the_model_subject, ref (Def_In_File bad_tag), ref [])

val package_root_node = class_tree
val model_root_node = instance_tree

fun assert_inner_outer (outer, inner) = (
    let
	val (prefix0, (id0, ss0)) = (subject_prefix outer)
	val (prefix1, (id1, ss1)) = (subject_prefix inner)
	val _ = if (subject_is_prefix prefix1 prefix0)
		then () else raise Match
	val _ = if (null ss0) then () else raise Match
	val _ = if (null ss1) then () else raise Match
	val _ = if (id0 = id1) then () else raise Match
    in
	()
    end)

fun component_is_outer_alias (Slot (id, dim, nodes, dummy)) = (
    case nodes of
	[] => false
      | [(_, kx, cx)] => (
	case (! kx) of
	    Def_Outer_Alias _ => true
	  | _ => false)
      | _ => false)

(* Tests if subcomponents are expandable connectors.  It returns false
   if nodes is empty, though it does not matter. *)

fun component_is_expandable (Slot (id, dim, nodes, dummy)) = (
    let
	fun check (subj, kx, cx) = (class_is_connector true (! kx))
    in
	(List.exists check nodes)
    end)

fun outer_alias_of_component (Slot (id, dim, nodes, dummy)) = (
    case nodes of
	[] => raise Match
      | [(_, kx, cx)] => (
	case (! kx) of
	    Def_Outer_Alias (vc, outer, inner) => inner
	  | _ => raise Match)
      | _ => raise Match)

(* Accesses a component in the instance_tree at an index.  An access
   with index=[] means either as a scalar or as an array.  An array is
   returned as a dummy node containing a Def_Mock_Array. *)

fun access_component subj (Slot (v, dim, ee, dummy)) (index : int list) = (
    case (index, dim) of
	([], []) => (
	let
	    val _ = if ((length ee) = 1) then () else raise Match
	    val node = (hd ee)
	    val (subjx, kx, _) = node
	    val kp = (! kx)
	    val _ = if (subject_equal_sans_subscript subj subjx) then ()
		    else raise Match
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
      | (_, []) => raise error_indexing_to_scalar
      (*
      | (_, _) => (
	let
	    val i = (array_index dim index 0)
	    val _ = if (i < (length ee)) then () else raise error_array_index
	    val node = (List.nth (ee, i))
	in
	    node
	end)
      *)
      | (_, _) => (
	let
	    val (dim1, ee1) = (array_access index (dim, ee))
	in
	    (access_component subj (Slot (v, dim1, ee1, dummy)) [])
	end))

fun find_in_components id components = (
    (List.find (fn (Slot (x, _, _, _)) => (x = id)) components))

(* Descends the instance_tree by one step. *)

fun descend_instance_tree_node id (node0 : instance_node_t) = (
    let
	val (subj, kx, cx) = node0
	val components = (! cx)
    in
	case (find_in_components id components) of
	    NONE => NONE
	  | SOME slot => SOME slot
    end)

(* Accesses an instance_tree node by a part of a subject.  It may
   return an instance_tree node or NONE. *)

fun descend_instance_tree_step__ (id, index) (node0 : instance_node_t) = (
    let
	val (subj, kx, cx) = node0
	val components = (! cx)
    in
	case (find_in_components id components) of
	    NONE => NONE
	  | SOME slot => (
	    let
		val subjx = (compose_subject subj id [])
	    in
		SOME (access_component subjx slot index)
	    end)
    end)

(* Finds an instance or an array of instances, by descending an
   instance_tree.  It may return a temporarily created dummy node,
   when it returns an array of instances.  It trails an inner-outer
   alias. *)

fun descend_instance_tree path0 (node0 : instance_node_t) = (
    case path0 of
	[] => SOME node0
      | ((id, index) :: path1) => (
	let
	    val (subj, kx, cx) = node0
	    val components = (! cx)
	in
	    case (find_in_components id components) of
		NONE => NONE
	      | SOME slot => (
		if (component_is_outer_alias slot) then
		    let
			val inner = (outer_alias_of_component slot)
			val (Subj (_, path2), _) = (subject_prefix inner)
			val newpath = path2 @ path0
			val root = instance_tree
		    in
			(descend_instance_tree path1 root)
		    end
		else
		    let
			val subjx = (compose_subject subj id [])
			val node1 = (access_component subjx slot index)
		    in
			(descend_instance_tree path1 node1)
		    end)
	end))

(* Checks if constraints of hierarchy in the instance_tree (actually
   no constraits). *)

fun assert_package_constraints node = (
    let
	val (_, kx, cx) = node
	val k = (! kx)
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

fun fetch_instance_tree_node subj : instance_node_t option = (
    let
	val (ns, path) = (subject_to_instance_tree_path subj)
	val root = if (ns = PKG) then class_tree else instance_tree
    in
	(descend_instance_tree path root)
    end)

(* Fetchs an instance in the instance_tree.  It trails an inner-outer
   alias, thus, it never returns an inner-outer alias. *)

fun fetch_from_instance_tree subj : definition_body_t option = (
    case (fetch_instance_tree_node subj) of
	NONE => NONE
      | SOME (_, kx, cx) => (
	let
	    val k0 = (! kx)
	in
	    SOME k0
	end))

(* Follows an inner-outer alias node.  Note that it returns a node
   above one pointed by an alias. *)

fun dereference_outer_alias (slot as Slot (id, dim, nodes, dummy)) = (
    case nodes of
	[] => raise Match
      | [(_, kx, cx)] => (
	case (! kx) of
	    Def_Outer_Alias (vc, outer, inner) => (
	    let
		val (tree, path) = (subject_to_instance_tree_path inner)
		val root = if (tree = PKG) then class_tree else instance_tree
		val (prefix, (aliasid, ss)) = (split_last path)
		val _ = if (id = aliasid) then () else raise Match
		val upnode = (descend_instance_tree prefix root)
	    in
		surely upnode
	    end)
	  | _ => raise Match)
      | _ => raise Match)

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
		val _ = trace 3 (";; - [cook] Register ("^
				 (subject_body_to_string (subj, k0)) ^")")
		val (_, kx, cx) = instance_tree
		val _ = kx := k0
	    in
		k0
	    end)

	fun store_scalar upnode node id (subj, k0) = (
	    let
		val _ = trace 3 (";; - [cook] Register ("^
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
		val _ = trace 3 (";; - [cook] Register ("^
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
		  | Def_Primitive (P_Enum _ , e, _) => (
		    (store_scalar upnode node id (subj, kp)))
		  | Def_Primitive (_ , e, _) => raise Match
		  | Def_Outer_Alias _ => (
		    (store_scalar upnode node id (subj, kp)))
		  | Def_Argument _ => (
		    (store_scalar upnode node id (subj, kp)))
		  | Def_Named _ => raise Match
		  | Def_Scoped _ => raise Match
		  | Def_Refine _ => (
		    (store_scalar upnode node id (subj, kp)))
		  | Def_Extending _ => raise Match
		  | Def_Replaced _ => raise Match
		  | Def_Displaced _ => (
		    (store_scalar upnode node id (subj, kp)))
		  | Def_In_File _ => raise Match
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
	val (_, kx0, cx0) = class_tree
	val _ = kx0 := the_package_root
	val _ = cx0 := []
	val (_, kx1, cx1) = instance_tree
	val _ = kx1 := Def_In_File bad_tag
	val _ = cx1 := []
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

datatype inner_outer_slot_t
    = Entry of name_t * name_t
    | Alist of (string * inner_outer_slot_t) list

(* The inner_outer_table table records a mapping from an outer to an
   inner.  It records variable references with subscripts dropped.
   Note that an inner is a prefix of an outer, when the last part
   which is identical is dropped. *)

val inner_outer_table = ref (Alist [])

fun clear_inner_outer_table () = (
    inner_outer_table := (Alist []))

fun make_singleton_slot e path = (
    (foldr (fn (k, s) => Alist [(k, s)]) e path))

fun insert_outer_loop e slot0 path0 = (
    case (slot0, path0) of
	(Entry _, []) => (
	let
	    val _ = if (e = slot0) then ()
		    else raise error_duplicate_inner_outer
	in
	    slot0
	end)
      | (Alist _, []) => raise Match
      | (Entry _, v :: path1) => raise Match
      | (Alist alist0, v :: path1) => (
	let
	    val (entry, others)
		= (List.partition (fn (s, _) => (s = v)) alist0)
	in
	    case entry of
		[] => (
		let
		    val s = (make_singleton_slot e path1)
		    val alist1 = ((v, s) :: others)
		in
		    Alist alist1
		end)
	      | [(_, slot1)] => (
		let
		    val s = (insert_outer_loop e slot1 path1)
		    val alist1 = ((v, s) :: others)
		in
		    Alist alist1
		end)
	      | _ => raise Match
	end))

fun assert_prefix_but_last x y = (
    let
	val (x1, x2) = (split_last x)
	val (y1, y2) = (split_last y)
    in
	if ((list_prefix (op =) x1 y1) andalso x2 = y2) then ()
	else raise Match
    end)

fun record_inner_outer outer inner = (
    let
	fun subject_path (Subj (ns, path)) = (
	    let
		val _ = if (ns = VAR) then () else raise Match
	    in
		(map (fn (Id s, _) => s) path)
	    end)

	val opath = (subject_path outer)
	val ipath = (subject_path inner)
	val _ = (assert_prefix_but_last ipath opath)
	val e = Entry (Name opath, Name ipath)
	val new = (insert_outer_loop e (! inner_outer_table) opath)
	val _ = inner_outer_table := new
    in
	()
    end)

(* Inserts an alias instance to record an inner-outer matching in the
   instance_tree.  An outer reference will be substituted by an inner
   reference, but it is delayed until processing connectors.  It is
   because the place where a connector is declared matters in
   distinguishing the side of a connector. *)

fun insert_outer_alias var outer inner = (
    let
	val _ = (assert_inner_outer (outer, inner))
	val k = Def_Outer_Alias (var, outer, inner)
	val _ = (store_to_instance_tree outer k)
	val _ = (record_inner_outer outer inner)
    in
	k
    end)

fun substitute_outer_loop slot0 (prefix0, suffix0) = (
    case (slot0, suffix0) of
	(Entry (Name outer, Name inner), _) => (
	let
	    val (prefix1, (id, ss)) = (split_last prefix0)
	    val prefix2 = (List.take (prefix1, ((length inner) - 1)))
	    val path = (prefix2 @ [(id, ss)] @ suffix0)
	    val _ = trace 5 (";; substitute_outer ("^
			     (name_to_string (Name outer)) ^", "^
			     (name_to_string (Name inner)) ^")")
	in
	    (substitute_outer_loop (! inner_outer_table) ([], path))
	end)
      | (Alist alist, []) => (prefix0 @ suffix0)
      | (Alist alist, (Id v, ss) :: suffix1) => (
	case (List.partition (fn (s, _) => (s = v)) alist) of
	    ([], _) => (prefix0 @ suffix0)
	  | ([(_, slot1)], _) => (
	    let
		val prefix1 = prefix0 @ [(Id v, ss)]
	    in
		(substitute_outer_loop slot1 (prefix1, suffix1))
	    end)
	  | _ => raise Match))

fun substitute_outer_reference w0 = (
    case w0 of
	Vref (_, []) => raise Match
      | Vref (NONE, _) => raise Match
      | Vref (SOME ns, rr0) => (
	let
	    val rrx = (substitute_outer_loop (! inner_outer_table) ([], rr0))
	in
	    Vref (SOME ns, rrx)
	end)
      | _ => w0)

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

fun fetch_class_by_part (subj, tag) = (
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
	    val (subj, kx, cx) = (hd nodes)
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
	if (pkg = the_package_root_tag) then
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
	val _ = (clear_inner_outer_table ())
    in () end)

(* ================================================================ *)

(* Accesses an instance-tree node and returns an instance and a list
   of components.  It may access a package-tree node, too.  Components
   include packages.  Each component is Slot(v,d,a,_), where ID "v", a
   dimension "d", and an array of nodes "a".  It takes a required step
   E3 or E5. *)

fun access_node step (exclude_outer_alias : bool) node0 = (
    let
	val (subj, kx, cx) = node0
	val kp = (! kx)
	val components = (! cx)

	val _ = if ((cook_step kp) <> E0) then () else raise Match
	val _ = if (step_is_at_least E3 kp) then () else raise Match
	val _ = if ((class_is_package kp) orelse (step_is_at_least step kp))
		then () else raise Match
	val _ = if (null components) then ()
		else if (not (class_is_simple_type kp)) then ()
		else if (class_is_enum kp) then ()
		else raise error_attribute_access_to_simple_type
    in
	if (not exclude_outer_alias) then
	    (kp, components)
	else
	    (kp, (List.filter (not o component_is_outer_alias) components))
    end)

(* Calls f on each package/instance with a folding argument in the
   class_tree/instance_tree.  It calls f with (node,acc) for
   folding. *)

fun traverse_tree f (node0, acc0) = (
    let
	val (kp, components) = (access_node E5 true node0)
	val acc1 = (f (kp, acc0))
	val acc2 = (foldl (fn (Slot (v, dim, nodes, _), accx) =>
			      (foldl (traverse_tree f) accx nodes))
			  acc1 components)
    in
	acc2
    end)

(* Calls f on each package/instance in the class_tree/instance_tree,
   but stops traversing.  It calls f with (node,acc) and assumes f
   returns a boolean along with a folding result.  It will not descend
   to its components when f returns false. *)

fun traverse_tree_with_stop f (node0, acc0) = (
    let
	val (kp, components) = (access_node E5 true node0)
	val (stop, acc1) = (f (kp, acc0))
    in
	if (not stop) then
	    acc1
	else
	    (foldl (fn (Slot (v, dim, nodes, _), accx) =>
		       (foldl (traverse_tree_with_stop f) accx nodes))
		   acc1 components)
    end)

(* ================================================================ *)

fun enumerate_in_node f path0 (node, acc) = (
    let
	val (subj, kx, cx) = node
	(*val components = (! cx)*)
	val (kp, components) = (access_node E5 true node)
    in
	case path0 of
	    [] => f (subj, acc)
	  | (id :: path1) => (
	    case (find_in_components id components) of
		NONE => raise Match
	      | SOME (slot as (Slot (id_, dim, nodes, dummy))) => (
		let
		    val _ = if (not (component_is_outer_alias slot))
			    then () else raise Match
		in
		    (foldl (enumerate_in_node f path1) acc nodes)
		end))
    end)

(* Enumerates all instances with a given pseudo variable.  That is,
   given a.b.c, it enumerates a[i].b[j].c[k] for all array indices
   (i,j,k).  It folds by calling f (subj,acc). *)

fun enumerate_instances f path acc = (
    (enumerate_in_node f path (instance_tree, acc)))

(* ================================================================ *)

(* Returns a scope of the model.  It is used to make a properly scoped
   expression by wrapping literal constants. *)

fun dummy_scope () = (
    let
	val (_, kx, _) = instance_tree
	val model = (! kx)
	val tag = (tag_of_body model)
    in
	(the_model_subject, tag)
    end)

(* ================================================================ *)

fun dump_table t = (
    (HashTable.appi (fn (n, k) => (print (n ^ "\n"))) t))

fun dump_loaded_classes () = (dump_table loaded_classes)

fun xfetch0 (s : string) = (
    (fetch_from_loaded_classes
	 (make_name_qualified
	      (Name (String.fields (fn c => (c = #".")) s)))))

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
    (fetch_from_instance_tree (scan_string_as_subject s)))

fun xfetch1__ (s : string) = (
    (fetch_from_instance_tree
	 ))

fun xfetch2 (subjtag : string) = (
    let
	val key = subjtag
    in
	(HashTable.find class_bindings key)
    end)

end
