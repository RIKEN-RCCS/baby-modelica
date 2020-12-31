(* connector.sml -*-Coding: us-ascii-unix;-*- *)
(* Copyright (C) 2018-2020 RIKEN R-CCS *)

(* CONNECTOR HANDLING.  It removes the uses of "connect" equations,
   "Connections", "inStream()", "actualStream()", and
   "cardinality()". *)

structure connector :
sig
    type expression_t
    type subject_t

    (*val xbind : unit -> unit*)
    (*val discern_connector : unit -> unit*)

    val connect_connectors :
	unit -> ((subject_t * bool) * (subject_t * bool) * subject_t) list

    val xbind :
	unit -> ((subject_t * bool) * (subject_t * bool) * subject_t) list

end = struct

open ast plain
open small1

fun tr_conn (s : string) = if true then (print (s ^"\n")) else ()
fun tr_conn_vvv (s : string) = if false then (print (s ^"\n")) else ()

val list_elements = finder.list_elements

val instance_tree = classtree.instance_tree
val traverse_tree = classtree.traverse_tree
val store_to_instance_tree = classtree.store_to_instance_tree
val unwrap_array_of_instances = classtree.unwrap_array_of_instances
val fetch_from_instance_tree = classtree.fetch_from_instance_tree
val fetch_instance_tree_node = classtree.fetch_instance_tree_node

val expression_is_literal = expression.expression_is_literal
val find_iterator_range = expression.find_iterator_range

val fold_constants = folder.fold_constants
val explicitize_range = folder.explicitize_range

val bind_in_scoped_expression = binder.bind_in_scoped_expression

val instantiate_class = builder.instantiate_class
val traverse_with_instantiation = builder.traverse_with_instantiation

val walk_in_class = walker.walk_in_class
val walk_in_expression = walker.walk_in_expression
val walk_in_equation = walker.walk_in_equation
val walk_in_statement = walker.walk_in_statement

val expand_equations_for_connects = syntaxer.expand_equations_for_connects

(* ================================================================ *)

(* Operators in Connections package (equation operators).
   Connect+false is for a connect equation (weak edge), Connect+true
   is for Connections.branch() (hard edge).  Root+true is for
   Connections.root(), Root+false is Connections.potentialRoot(). *)

datatype edge_marker_t = Edge of bool
datatype root_marker_t = Root of bool

(* ================================================================ *)

(* Drops a prefix of a reference which refers to a class pointed by a
   subject.  It returns NONE if a reference is not a component of the
   class.  A returned path is non-empty (a reference should be a
   component).  It assumes the indices (of a class) are equal. *)

fun strip_component_reference subj w = (
    let
	val Subj (ns0, cc0) = subj
	val Subj (ns1, cc1) = w
    in
	if ((ns0 = VAR andalso ns1 = VAR)
	    andalso (list_prefix (op =) cc0 cc1)
	    andalso ((length cc0) < (length cc1))) then
	    SOME (List.drop (cc1, (length cc0)))
	else
	    NONE
    end)

(* Converts a reference to a subject by simplifying subscripts to
   literal integers.  It errs if subscripts are not simplified to
   literals. *)

fun literalize_subscripts kp w0 = (
    let
	fun mapr f (x0, x1) = (x0, f x1)
	val simplify = (fold_constants kp false [])
    in
	case w0 of
	    Vref (_, []) => raise Match
	  | Vref (NONE, _) => raise Match
	  | Vref (SOME ns, rr0) => (
	    let
		val w1 = Vref (SOME ns, (map (mapr (map simplify)) rr0))
	    in
		(reference_as_subject w1)
	    end)
    end)

(* Returns a type/record of a connector instance. *)

fun record_of_connect k = (
    case k of
	Def_Body (mk, j, cs, nm, ee, aa, ww) => (
	Def_Body (mk, j, cs, nm, ee, aa, ww))
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
      | Def_Outer_Alias _ => raise Match)

fun unmark_expandable_connector k = (
    case k of
	Def_Body (mk, j, (Connector true, p, q), nm, ee, aa, ww) => (
	Def_Body (mk, j, (Connector false, p, q), nm, ee, aa, ww))
      | Def_Body _ => raise Match
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
      | Def_Outer_Alias _ => raise Match)

fun marked_as_stream k = (
    case k of
	Def_Body (_, _, (t, p, (Stream, _, _)), _, _, _, _) => true
      | Def_Body (_, _, (t, p, (_, _, _)), _, _, _, _) => false
      | _ => raise error_connector_is_not_record)

fun marked_as_flow k = (
    case k of
	Def_Body (_, _, (t, p, (Flow, _, _)), _, _, _, _) => true
      | Def_Body (_, _, (t, p, (_, _, _)), _, _, _, _) => false
      | _ => raise error_connector_is_not_record)

fun connector_is_stream (subj, b) = (
    let
	fun test_stream (Slot (id, dim, nodes, dummy)) = (
	    (List.exists (fn (j, kx, cx) => (marked_as_stream (! kx))) nodes))

	val (_, kx, cx) = surely (fetch_instance_tree_node subj)
	val components = (! cx)
    in
	(List.exists test_stream components)
    end)

(* Tests if a type/record appearing a connector is an overdetermined
   one (i.e., it defines an equalityConstraint function). *)

fun connector_is_overdetermined subj = (
    let
	val kp = surely (fetch_from_instance_tree subj)
	fun cooker u_ (subj_, k_) = raise Match
	val bindings = (list_elements cooker true kp)
	val id = Id "equalityConstraint"
    in
	case (find_in_bindings id bindings) of
	    NONE => false
	  | SOME (Naming (_, _, _, _, (z, r, EL_Class dx, h))) => true
	  | SOME (Naming (_, _, _, _, (z, r, EL_State dx, h))) => false
    end)

(* Lists component names of a record.  It errs for an array of
   records. *)

fun names_in_record subj = (
    let
	val (_, kx, cx) = surely (fetch_instance_tree_node subj)
	val kp = (! kx)
	val components = (! cx)
    in
	case (unwrap_array_of_instances kp) of
	    ([], _) => (
	    (map (fn (Slot (id, dim, nodes, dummy)) => id) components))
	  | (_, []) => raise Match
    end)

(* ================================================================ *)

fun collect_connects_in_equation kp (q0, acc0) = (
    let
	val subj = (subject_of_class kp)
    in
	case q0 of
	    Eq_Eq _ => (q0, acc0)
	  | Eq_Connect ((Cref (x0, sidex), Cref (y0, sidey)), aa, ww) => (
	    let
		val x1 = (literalize_subscripts kp x0)
		val y1 = (literalize_subscripts kp y0)
	    in
		(q0, (((x1, sidex), (y1, sidey), subj) :: acc0))
	    end)
	  | Eq_Connect ((_, _), aa, ww) => raise Match
	  | Eq_If _ => (q0, acc0)
	  | Eq_When _ => (q0, acc0)
	  | Eq_App _ => (q0, acc0)
	  | Eq_For _ => (q0, acc0)
    end)

fun collect_connects_in_instance (k0, acc0) = (
    if (class_is_outer_alias k0) then
	acc0
    else if (class_is_enumerator_definition k0) then
	acc0
    else if (class_is_package k0) then
	acc0
    else
	let
	    val _ = if (not (class_is_primitive k0)) then () else raise Match
	in
	    let
		val efix = (fn (e, a) => (e, a))
		val qfix = (collect_connects_in_equation k0)
		val qwalk = (walk_in_equation qfix efix)
		val swalk = (fn (s, a) => (s, a))
		val walker = {vamp_q = qwalk, vamp_s = swalk}
		val (k1, acc1) = (walk_in_class walker (k0, acc0))
	    in
		acc1
	    end
	end)

(* Collects connect equations. *)

fun collect_connects () = (
    (traverse_tree collect_connects_in_instance (instance_tree, [])))

(* ================================================================ *)

fun find_expansion_loop subj cc0 = (
    case cc0 of
	[] => NONE
      | (id, index) :: cc1 => (
	let
	    val subsubj = (compose_subject subj id index)
	in
	    case (fetch_from_instance_tree subsubj) of
		NONE => NONE
	      | SOME kx => (
		if (class_is_connector true kx) then
		    if ((length cc1) = 1) then
			SOME (subsubj, (hd cc1))
		    else
			NONE
		else
		    (find_expansion_loop subsubj cc1))
	end))

(* Finds a reference "m...m.c.d", with "m" a possibly empty component
   that is not an expandable connector, "c" an expandable connector,
   and "d" a component.  It signifies an addition of a component to an
   expandable connector.  During a search, fetching an instance never
   fails, because the model builder has instantiated all instances
   except expandable connectors. *)

fun find_expansion subj w = (
    case (strip_component_reference subj w) of
	NONE => NONE
      | SOME cc => (find_expansion_loop subj cc))

fun test_expansion pair = (
    let
	val ((x, sidex), (y, sidey), subj) = pair
    in
	case ((find_expansion subj x), (find_expansion subj y)) of
	    (NONE, NONE) => NONE
	  | (SOME ((cx, (id, ss))), NONE) => (
	    SOME (cx, (id, ss), sidex, y, sidey))
	  | (NONE, SOME ((cy, (id, ss)))) => (
	    SOME (cy, (id, ss), sidey, x, sidex))
	  | (SOME _, SOME _) => raise error_mutual_expandable_connectors
    end)

(* Selects a dimension from a list of descriptions, each of which is
   either an index value (false,i) or a dimension value (true,i).  It
   returns a common value of a dimension set if any, or a maximum
   value of an index set. *)

fun pick_dimension_value descriptions = (
    let
	val _ = if (not (null descriptions)) then () else raise Match
	val (d0, i0) = (List.partition #1 descriptions)
	val dset = (map #2 d0)
	val iset = (map #2 i0)
    in
	if (null dset) then
	    (foldl Int.max 0 iset)
	else
	    case (list_unique_value (op =) dset) of
		NONE => raise error_nonunique_dimension
	      | SOME v => v
    end)

fun compact_expansion_set pairs = (
    case pairs of
	[] => raise Match
      | (x, (id, _), sidex, _, _) :: _ => (
	let
	    fun strip ((x_, (id_, ss0), sidex_, y, sidey), acc) = (
		let
		    val _ = if (x_ = x) then () else raise Match
		    val _ = if (id_ = id) then () else raise Match
		    val _ = if (sidex_ = sidex) then () else raise Match

		    val k0 = surely (fetch_from_instance_tree y)
		    val (dim, array) = (unwrap_array_of_instances k0)
		    val _ = if (not (null array)) then ()
			    else raise error_empty_array_connector
		    val k1 = (record_of_connect (hd array))
		    val dimension = ((map (fn i => (false, i)) ss0)
				     @ (map (fn i => (true, i)) dim))
		in

		    (dimension, (k1, sidey)) :: acc
	    end)

	    val connectset = (foldl strip [] pairs)
	in
	    (x, id, sidex, connectset)
	end))

(* Chooses an appropriate record class.  It takes a list of pairs of a
   type/record and its side.  It just returns a first type/record and
   does not consider the input/output direction. *)

fun select_record_class sidex classes = (
    let
	val _ = print "(AHO) EXPANDING CONNECTOR IGNORES I/O\n"
    in
	(#1 (hd classes))
    end)

fun make_record_instances subj dim0 k0 = (
    let
	val dim1 = (map z_literal dim0)
	val q = (Effort, Continuous, Modeless)
	val k1 = Def_Refine (k0, NONE, copy_type, q,
			     (dim1, []), Annotation [], Comment [])
	val (dim, array) = (instantiate_class (subj, k1))
    in
	(dim, array)
    end)

(* Fills a slot of an expandable connector.  It takes peer connectors
   for one slot of a connector. *)

fun expand_connector pairs = (
    let
	val (subj, id, sidex, connectset) = (compact_expansion_set pairs)
	val dimensions = (map #1 connectset)
	val _ = if (list_all_equal (op =) (map length dimensions)) then ()
		else raise error_dimensions_mismatch
	val dim = (map pick_dimension_value (list_transpose dimensions))
	val classes = (map #2 connectset)
	val k0 = (select_record_class sidex classes)
	val subsubj = (compose_subject subj id [])
	val (dim, array) = (make_record_instances subsubj dim k0)
	val _ = (app traverse_with_instantiation array)
    in
	(dim, array)
    end)

(* Selects an expandable connector at the shallowest in the instance
   hierarchy. *)

fun select_prior_connector pairs = (
    let
	fun depth (Subj (ns, cc)) = (length cc)
	fun select_d d (x, _, _, _, _) = (d = (depth x))
	fun select_x s (x, _, _, _, _) = (s = x)

	val _ = if (not (null pairs)) then () else raise Match

	val depths = (map (fn (x, _, _, _, _) => (depth x)) pairs)
	val min = (foldl Int.min (hd depths) depths)
	val (x, _, _, _, _) = valOf (List.find (select_d min) pairs)
	val group = (List.filter (select_x x) pairs)
    in
	(x, group)
    end)

(* Expands expandable connectors.  It changes an expandable connector
   to a normal connector, and repeats the process until all expandable
   connectors are settled. *)

fun expand_expandable_connectors connects = (
    let
	fun eq ((_, (id0, _), _, _, _), (_, (id1, _), _, _, _)) = (id0 = id1)

	val pairs = (gather_some test_expansion connects)
    in
	case pairs of
	    [] => ()
	  | _ => (
	    let
		val (subj, group) = (select_prior_connector pairs)
		val groups = (list_groups eq group)
		val _ = (app (ignore o expand_connector) groups)
		val k0 = surely (fetch_from_instance_tree subj)
		val k1 = (unmark_expandable_connector k0)
		val _ = (store_to_instance_tree subj k1)
	    in
		(expand_expandable_connectors connects)
	    end)
    end)

(* ================================================================ *)

fun unique_array_size subjs = (
    let
	val pairs = (map (unwrap_array_of_instances
			  o surely o fetch_from_instance_tree) subjs)
	val dims = (map #1 pairs)
    in
	case (list_unique_value (op =) dims) of
	    NONE => raise error_mismatch_connector_arrays
	  | SOME dim => dim
    end)

fun equate_connections_stream connectors = (
    let
	fun slot_is_flow subj id = (
	    let
		val subsubj = (compose_subject subj id [])
		val kx = surely (fetch_from_instance_tree subsubj)
	    in
		(marked_as_flow kx)
	    end)

	val subjs = (map #1 connectors)
	val namelist = (map names_in_record subjs)
	val names = (remove_duplicates (op =) (List.concat namelist))
	val _ = if (List.all (fn x => (length x = (length names))) namelist)
		then () else raise error_mismatch_connection_list
	val subj = (hd subjs)
	val flow = (List.find (slot_is_flow subj) names)
    in
	[]
    end)

fun equate_connections_nonstream connectors = []

fun equate_connections_array stream connectors = (
    let
	val equatorfn = if (stream) then equate_connections_stream
			else equate_connections_nonstream

	fun indexing index (subj, side) = (
	    ((compose_subject_with_index subj index), side))

	fun equate index = (
	    (equatorfn (map (indexing index) connectors)))

	val subjs = (map #1 connectors)
    in
	case (unique_array_size subjs) of
	    [] => (equatorfn connectors)
	  | dim => (List.concat (iterate_dimension equate dim))
    end)

fun equate_connections connectors = (
    let
	val stream = (List.exists connector_is_stream connectors)
    in
	(equate_connections_array stream connectors)
    end)

(* ================================================================ *)

fun connect_connectors () = (
    let
	val _ = (expand_equations_for_connects ())
	val cc0 = (collect_connects ())
	val _ = (expand_expandable_connectors cc0)
	val cc1 = (map (fn (x, y, subj) => [x, y]) cc0)
	val cc2 = (make_unions (op =) cc1)
	val _ = (map equate_connections cc2)
    in
	cc0
    end)

(* ================================================================ *)

val bind_model = postbinder.bind_model
val substitute_outer = postbinder.substitute_outer

fun xbind () = (
    let
	val _ = (bind_model true)
	val _ = (substitute_outer ())
	val v = (connect_connectors ())
    in
	v
    end)

end
