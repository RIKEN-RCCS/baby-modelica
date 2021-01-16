(* connector.sml -*-Coding: us-ascii-unix;-*- *)
(* Copyright (C) 2018-2021 RIKEN R-CCS *)

(* CONNECTOR HANDLING.  It removes the uses of "connect" equations,
   "Connections", "inStream()", "actualStream()", and
   "cardinality()". *)

structure connector :
sig
    type expression_t
    type subject_t

    val xbind : unit -> unit
    val xconnect : unit -> unit
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

val walk_in_class = walker.walk_in_class
val walk_in_expression = walker.walk_in_expression
val walk_in_equation = walker.walk_in_equation
val walk_in_statement = walker.walk_in_statement

val fetch_displaced_class = loader.fetch_displaced_class

val fold_constants = folder.fold_constants
val explicitize_range = folder.explicitize_range

val bind_in_scoped_expression = binder.bind_in_scoped_expression

val instantiate_class = builder.instantiate_class
val traverse_with_instantiation = builder.traverse_with_instantiation

val bind_in_instance = postbinder.bind_in_instance

val expand_equations_for_connects = syntaxer.expand_equations_for_connects

(* ================================================================ *)

(* Operators in Connections package (equation operators).
   Connect+false is for a connect equation (weak edge), Connect+true
   is for Connections.branch() (hard edge).  Root+true is for
   Connections.root(), Root+false is Connections.potentialRoot(). *)

datatype edge_marker_t = Edge of bool
datatype root_marker_t = Root of bool

(* ================================================================ *)

(* Makes a mix-in name of an inStream variable. *)

fun mixin_variable v = (
    let
	val (supsubj, (Id n0, ss)) = (subject_prefix v)
	val n1 = n0 ^ "__mix_in_"
    in
	(compose_subject supsubj (Id n1) ss)
    end)

fun is_mixin v = (
    let
	val (_, (Id n, _)) = (subject_prefix v)
    in
	(String.isSuffix "__mix_in_" n)
    end)

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
	  | _ => raise Match
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

fun connect_rule_marker k = (
    case k of
	Def_Body (_, _, (t, p, (efs, _, _)), _, _, _, _) => efs
      | _ => raise error_connector_is_not_record)

fun marked_as_effort k = ((connect_rule_marker k) = Effort)

fun marked_as_flow k = ((connect_rule_marker k) = Flow)

fun marked_as_stream k = ((connect_rule_marker k) = Stream)

fun rule_of_variable k = (connect_rule_marker k)

(* Lists component names of a record.  It errs if a record is an array
   of records. *)

fun names_in_record subj = (
    let
	val (j, kx, cx) = surely (fetch_instance_tree_node subj)
	val kp = (! kx)
	val components = (! cx)
    in
	case (unwrap_array_of_instances kp) of
	    ([], _) => (
	    (map (fn (Slot (id, dim, nodes, _)) => id) components))
	  | (_, _) => raise Match
    end)

(* Tests if there exists a record slot declared as a stream.  It
   traverses the instance nodes. *)

fun connector_is_stream (subj, side) = (
    let
	fun test_node (subj, kx, cx) = (marked_as_stream (! kx))

	fun test_slot (Slot (id, dim, nodes, _)) = (
	    ((List.exists test_node nodes)
	     orelse (List.exists test_components nodes)))

	and test_components (subj, kx, cx) = (List.exists test_slot (! cx))

	val node = surely (fetch_instance_tree_node subj)
    in
	(test_components node)
    end)

(* Finds a record slot declared as a flow.  It does search in nested
   records. *)

fun find_flow_variable (subj, side) = (
    let
	fun getclass (subj, kx, cx) = (! kx)

	fun test_node (subj, kx, cx) = (marked_as_flow (! kx))

	fun find_in_slot (Slot (id, dim, nodes, _)) = (
	    ((map getclass (List.filter test_node nodes))
	     @ (List.concat (map find_in_components nodes))))

	and find_in_components (subj, kx, cx) = (
	    (List.concat (map find_in_slot (! cx))))

	val node = surely (fetch_instance_tree_node subj)
    in
	case (find_in_components node) of
	    [] => NONE
	  | [k] => SOME (subject_of_class k)
	  | _ => raise error_multiple_flow_variables
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

fun global_function name = Instances ([], [Subj (PKG, [(Id name, [])])])

fun choose_connect_rule r0 rules = (
    case (list_unique_value (op =) rules) of
	NONE => raise error_connect_rule_disagree
      | SOME r1 => (
	case (r0, r1) of
	    (Effort, _) => r1
	  | (_, Effort) => r0
	  | (Flow, Flow) => Flow
	  | (Stream, Stream) => Stream
	  | (Flow, Stream) => raise error_connect_rule_conflict
	  | (Stream, Flow) => raise error_connect_rule_conflict))

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

fun is_inside side = (side = false)

fun is_outside side = (side = true)

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

fun make_loop_rule connectors = (
    let
	fun term (subj, side) = Instances ([], [subj])

	fun equalize x y = (
	    Eq_Eq ((x, y), Annotation [], Comment []))

	val terms = (map term connectors)
    in
	case terms of
	    [] => raise Match
	  | x0 :: tl => (map (equalize x0) tl)
    end)

fun make_point_rule connectors = (
    let
	fun negate e = (
	    App (Opr Opr_mul, [L_Number (R, "-1"), e]))

	fun term (subj, side) = (
	    let
		val e = Instances ([], [subj])
		val v = if (not side) then e else (negate e)
	    in
		v
	    end)

	val terms = (map term connectors)
    in
	[Eq_Eq ((L_Number (R, "0"),
		 App ((global_function "sum"),
		      [Array_Constructor terms])),
		Annotation [], Comment [])]
    end)

(* It uses "semiLinear" for "positiveMax". *)

fun stream_equation iqconnector otherconnectors = (
    let
	val one = L_Number (R, "1")

	val zero = L_Number (R, "0")

	fun term v = Instances ([], [v])

	fun mixin v = Instances ([], [(mixin_variable v)])

	fun negate e = (
	    App (Opr Opr_mul, [L_Number (R, "-1"), e]))

	fun denominator_term (flow, stream, side) = (
	    if (is_inside side) then
		(* j-term *)
		App ((global_function "semiLinear"),
		     [(negate (term flow)), one, zero])
	    else
		(* k-term *)
		App ((global_function "semiLinear"),
		     [(term flow), one, zero]))

	fun denominator iqconnector otherconnectors = (
	    App ((global_function "sum"),
		 (map denominator_term otherconnectors)))

	fun numerator_term (flow, stream, side) = (
	    if (is_inside side) then
		(* j-term *)
		App ((global_function "semiLinear"),
		     [(negate (term flow)), (term stream), zero])
	    else
		(* k-term *)
		App ((global_function "semiLinear"),
		     [(term flow), (mixin stream), zero]))

	fun numerator iqconnector otherconnectors = (
	    App ((global_function "sum"),
		 (map numerator_term otherconnectors)))

	val (_, stream, side) = iqconnector
	val lhs = if (is_inside side) then (mixin stream) else (term stream)
    in
	[Eq_Eq ((lhs,
		 App (Opr Opr_div,
		      [(numerator iqconnector otherconnectors),
		       (denominator iqconnector otherconnectors)])),
		Annotation [], Comment [])]
    end)

fun list_mixin_variables connectors = (
    (List.concat
	 (map (fn (stream, side) => (
		   if (is_inside side) then [(mixin_variable stream)] else []))
	      connectors)))

fun make_stream_rule flows connectors = (
    let
	fun tuple (flow, (stream, side)) = (flow, stream, side)

	val mixins = (list_mixin_variables connectors)
	val flowconnectors = (map tuple (ListPair.zipEq (flows, connectors)))
	val eqns = (foldl_one_and_others
			(fn (one, others, acc) =>
			    (stream_equation one others) @ acc)
			[] flowconnectors)
    in
	(mixins, eqns)
    end)

(* Makes equations, by switching either on simple-types, records, or
   arrays.  It returns a pair of mix-in variables and equations.  It
   makes an empty list for empty arrays. *)

fun equate_connections rule0 flows connectors = (
    let
	fun connect_in_record rule flows sides subjs id = (
	    let
		val subsubjs = (map (fn j => (compose_subject j id [])) subjs)
		val connectors = (ListPair.zipEq (subsubjs, sides))
	    in
		(equate_connections rule flows connectors)
	    end)

	fun connect_with_sides rule flows sides subjs = (
	    let
		val connectors = (ListPair.zipEq (subjs, sides))
	    in
		(equate_connections rule flows connectors)
	    end)

	fun check_identical_lists namelist = (
	    let
		val slots = (remove_duplicates (op =) (List.concat namelist))
		val n = (length slots)
		val _ = if (List.all (fn x => (length x) = n) namelist)
			then () else raise error_connect_record_disagree
	    in
		slots
	    end)

	val subjs = (map #1 connectors)
	val sides = (map #2 connectors)
	val variables = (map (surely o fetch_from_instance_tree) subjs)
	val simpletypes = (map variable_is_simple_type variables)
	val monomers = (map variable_is_monomer variables)
    in
	if (List.exists (fn x => x) simpletypes) then
	    let
		val _ = if (List.all (fn x => x) simpletypes) then ()
			else raise error_connect_record_disagree
		val rules = (map rule_of_variable variables)
		val rule1 = (choose_connect_rule rule0 rules)
	    in
		case rule1 of
		    Effort => ([], (make_loop_rule connectors))
		  | Flow => ([], (make_point_rule connectors))
		  | Stream => (make_stream_rule flows connectors)
	    end
	else if (List.exists (fn x => x) monomers) then
	    let
		val _ = if (List.all (fn x => x) monomers) then ()
			else raise error_connect_record_disagree
		val rules = (map rule_of_variable variables)
		val rule1 = (choose_connect_rule rule0 rules)
		val subjs = (map subject_of_class variables)
		val namelist = (map names_in_record subjs)
		val slots = (check_identical_lists namelist)
		val x = (map (connect_in_record rule1 flows sides subjs) slots)
		val mixins = (List.concat (map #1 x))
		val eqns = (List.concat (map #2 x))
	    in
		(mixins, eqns)
	    end
	else
	    let
		val descs = (map unwrap_array_of_instances variables)
		val dims = (map #1 descs)
		val arrays = (map #2 descs)
		val subjarrays = (map (map subject_of_class) arrays)
		val sets = (list_transpose subjarrays)
		val dim = case (list_unique_value (op =) dims) of
			      NONE => raise error_connect_record_disagree
			    | SOME d => d
		val _ = if ((not ((array_size dim) = 0)) orelse (null sets))
			then () else raise Match
		val x = (map (connect_with_sides rule0 flows sides) sets)
		val mixins = (List.concat (map #1 x))
		val eqns = (List.concat (map #2 x))
	    in
		(mixins, eqns)
	    end
    end)

fun make_connect_equations connectors = (
    let
	val stream = (List.exists connector_is_stream connectors)
    in
	if (not (stream)) then
	    (equate_connections Effort [] connectors)
	else
	    let
		val flowset = (map find_flow_variable connectors)
		val _ = if (List.all isSome flowset) then ()
			else raise error_missing_flow_variables
		val flows = (map valOf flowset)
	    in
		(equate_connections Effort flows connectors)
	    end
    end)

(* ================================================================ *)

(*
fun substitute_operators_in_instance (k0, acc0) = (
    if (class_is_outer_alias k0) then
	acc0
    else if (class_is_enumerator_definition k0) then
	acc0
    else if (class_is_package k0) then
	acc0
    else
	let
	    val _ if (not (class_is_primitive k0)) then () else raise Match

	    val subj = (subject_of_class k0)
	    val efix = (fn (w, _) => ((substitute_outer_reference w), ()))
	    val ewalk = (walk_in_expression efix)
	    val qwalk = (walk_in_equation (fn (q, a) => (q, a)) ewalk)
	    val swalk = (walk_in_statement (fn (s, a) => (s, a)) ewalk)
	    val walker = {vamp_q = qwalk, vamp_s = swalk}
	    val (k1, _) = (walk_in_class walker (k0, ()))
	    val _ = (store_to_instance_tree subj k1)
	in
	    acc0
	end)

(* Substitutes the uses of inStream(), actualStream(), and
   cardinality(). *)

fun substitute_operators () = (
    ignore (traverse_tree substitute_operators_in_instance
			  (instance_tree, [])))
*)

(* ================================================================ *)

fun insert_connect_equations eqns = (
    let
	val section = Element_Equations (false, eqns)
	val (subj, kx, cx) = instance_tree
	val model0 = (! kx)
    in
	case model0 of
	    Def_Body (mk, j, cs, nm, ee0, aa, ww) => (
	    let
		val ee1 = (ee0 @ [section])
		val model1 = Def_Body (mk, j, cs, nm, ee1, aa, ww)
		val _ = (kx := model1)
	    in
		()
	    end)
	  | _ => raise Match
    end)

fun insert_mixin_variable mixin = (
    let
	val _ = if (is_mixin mixin) then () else raise Match
	val x0 = Def_Displaced (Ctag ["Real"], the_root_subject)
	val k0 = (fetch_displaced_class E0 x0)
	val (dim, array) = (instantiate_class (mixin, k0))
	val _ = if (null dim) then () else raise Match
	val k1 = (hd array)
	val _ = (bind_in_instance false k1)
    in
	()
    end)

fun connect_connectors () = (
    let
	val _ = (expand_equations_for_connects ())
	val cc0 = (collect_connects ())
	val _ = (expand_expandable_connectors cc0)
	val cc1 = (map (fn (x, y, subj) => [x, y]) cc0)
	val cc2 = (make_unions (op =) cc1)
	val x = (map make_connect_equations cc2)
	val mixins = (List.concat (map #1 x))
	val eqns = (List.concat (map #2 x))
	val _ = (insert_connect_equations eqns)
	val _ = (app insert_mixin_variable mixins)
    in
	()
    end)

(* ================================================================ *)

val bind_model = postbinder.bind_model
val substitute_outer = postbinder.substitute_outer

fun xbind () = (
    let
	val _ = (bind_model true)
	val _ = (substitute_outer ())
    in
	()
    end)

fun xconnect () = (
    let
	val _ = (connect_connectors ())
    in
	()
    end)

end
