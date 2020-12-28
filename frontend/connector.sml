(* connector.sml -*-Coding: us-ascii-unix;-*- *)
(* Copyright (C) 2018-2020 RIKEN R-CCS *)

(* CONNECTOR HANDLING.  It removes the uses of "connect",
   "Connections", "inStream()", "actualStream()", and
   "cardinality()". *)

structure connector :
sig
    type expression_t
    type subject_t

    val discern_connects : unit -> unit

    val xbind : unit -> unit
    val xconnect :
	unit -> ((subject_t * bool) * (subject_t * bool) * subject_t) list
end = struct

open ast plain
open small1

fun tr_conn (s : string) = if true then (print (s ^"\n")) else ()
fun tr_conn_vvv (s : string) = if false then (print (s ^"\n")) else ()

val instance_tree = classtree.instance_tree
val traverse_tree = classtree.traverse_tree
val store_to_instance_tree = classtree.store_to_instance_tree
val unwrap_array_of_instances = classtree.unwrap_array_of_instances

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
	(*val rr0 = (drop_subscripts cc0)*)
	val Subj (ns1, cc1) = w
	(*val rr1 = (drop_subscripts cc1)*)
    in
	if ((ns0 = VAR andalso ns1 = VAR)
	    andalso (list_prefix (op =) cc0 cc1)
	    andalso ((length cc0) < (length cc1))) then
	    SOME (List.drop (cc1, (length cc0)))
	else
	    NONE
    end)

(* Tests if a referenced connector is an outside one.  It takes a
   reference and a class by a subject.  It checks some prefix of the
   reference is declared in the class and it is a connector.  It
   requires a reference is before resolving the inner-outer
   relation. *)

fun reference_is_connector_component subj w = (
    case (strip_component_reference subj w) of
	NONE => false
      | SOME [] => raise Match
      | SOME ((id, ss) :: _) => (
	let
	    val component = (compose_subject subj id [])
	    val k = surely (fetch_from_instance_tree component)
	in
	    (class_is_connector false k)
	end))

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

(* ================================================================ *)

fun discern_connects_in_equation kp (q0, acc0) = (
    let
	val subj = (subject_of_class kp)
    in
	case q0 of
	    Eq_Eq _ => (q0, acc0)
	  | Eq_Connect ((x0 as Vref _, y0 as Vref _), aa, ww) => (
	    let
		val x1 = (literalize_subscripts kp x0)
		val y1 = (literalize_subscripts kp y0)
		val sidex = (reference_is_connector_component subj x1)
		val sidey = (reference_is_connector_component subj y1)
		val x2 = Cref (x1, sidex)
		val y2 = Cref (y1, sidey)
		val q1 = Eq_Connect ((x2, y2), aa, ww)
	    in
		(q1, acc0)
	    end)
	  | Eq_Connect ((_, _), aa, ww) => raise Match
	  | Eq_If _ => (q0, acc0)
	  | Eq_When _ => (q0, acc0)
	  | Eq_App _ => (q0, acc0)
	  | Eq_For _ => (q0, acc0)
    end)

fun discern_connects_in_instance (k0, acc0) = (
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
		val subj = (subject_of_class k0)
		val efix = (fn (e, a) => (e, a))
		val qfix = (discern_connects_in_equation k0)
		val qwalk = (walk_in_equation qfix efix)
		val swalk = (fn (s, a) => (s, a))
		val walker = {vamp_q = qwalk, vamp_s = swalk}
		val (k1, _) = (walk_in_class walker (k0, ()))
		val _ = (store_to_instance_tree subj k1)
	    in
		acc0
	    end
	end)

(* Discriminates the side (inside/outside) of connections, and records
   that information in connect equations. *)

fun discern_connects () = (
    ignore (traverse_tree discern_connects_in_instance (instance_tree, [])))

(* ================================================================ *)

fun collect_connects_in_equation kp (q0, acc0) = (
    let
	val subj = (subject_of_class kp)
    in
	case q0 of
	    Eq_Eq _ => (q0, acc0)
	  | Eq_Connect ((Cref (x, sidex), Cref (y, sidey)), aa, ww) => (
	    (q0, (((x, sidex), (y, sidey), subj) :: acc0)))
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

fun connect_connects () = (
    let
	val _ = (expand_equations_for_connects ())
	val cc0 = (collect_connects ())
	val _ = (expand_expandable_connectors cc0)
	(*val cc1 = (make_unions (op =) cc0)*)
    in
	cc0
    end)

(* ================================================================ *)

val bind_model = postbinder.bind_model
val replace_outer = postbinder.replace_outer

fun xbind () = (
    let
	val _ = (bind_model true)
	val _ = (discern_connects ())
	val _ = (replace_outer ())
    in
	()
    end)

fun xconnect () = (connect_connects ())

end
