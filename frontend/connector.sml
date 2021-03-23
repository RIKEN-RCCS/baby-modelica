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
    val xconnect : unit -> subject_t list * subject_t list * subject_t list
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
val enumerate_instances = classtree.enumerate_instances
val access_node = classtree.access_node
val dummy_scope = classtree.dummy_scope

val expression_to_string = dumper.expression_to_string
val expression_is_literal = expression.expression_is_literal
val find_iterator_range = expression.find_iterator_range

val walk_in_class = walker.walk_in_class
val walk_in_expression = walker.walk_in_expression
val walk_in_equation = walker.walk_in_equation
val walk_in_statement = walker.walk_in_statement
val substitute_expression = walker.substitute_expression

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

datatype edge_marker_t__ = Edge of bool
datatype root_marker_t__ = Root of bool

(* ================================================================ *)

fun is_inside side = (side = false)

fun is_outside side = (side = true)

fun operator_suffix name = (
    case name of
	"inStream" => "_mix_in_"
      | "actualStream" => "_actual_in_"
      | "cardinality" => "_cardinality_"
      | _ => raise Match)

(* Makes a mix-in name of an inStream variable. *)

fun mixin_variable v = (
    let
	val suffix = (operator_suffix "inStream")
	val (supsubj, (Id n0, ss)) = (subject_prefix v)
    in
	(compose_subject supsubj (Id (n0 ^"_"^ suffix)) ss)
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
	Def_Body (mk, j, cs, nm, cc, ee, aa, ww) => (
	Def_Body (mk, j, cs, nm, cc, ee, aa, ww))
      | Def_Der _ => raise Match
      | Def_Primitive _ => raise Match
      | Def_Outer_Alias _ => raise Match
      | Def_Name _ => raise Match
      | Def_Scoped _ => raise Match
      | Def_Refine _ => raise Match
      | Def_Extending _ => raise Match
      | Def_Replaced _ => raise Match
      | Def_Displaced _ => raise Match
      | Def_In_File => raise Match
      | Def_Mock_Array _ => raise Match)

fun unmark_expandable_connector k = (
    case k of
	Def_Body (mk, j, (Connector true, p, q), nm, cc, ee, aa, ww) => (
	Def_Body (mk, j, (Connector false, p, q), nm, cc, ee, aa, ww))
      | Def_Body _ => raise Match
      | Def_Der _ => raise Match
      | Def_Primitive _ => raise Match
      | Def_Outer_Alias _ => raise Match
      | Def_Name _ => raise Match
      | Def_Scoped _ => raise Match
      | Def_Refine _ => raise Match
      | Def_Extending _ => raise Match
      | Def_Replaced _ => raise Match
      | Def_Displaced _ => raise Match
      | Def_In_File => raise Match
      | Def_Mock_Array _ => raise Match)

fun connect_rule_marker k = (
    case k of
	Def_Body (mk, j, (t, p, (efs, _, _)), nm, cc, ee, aa, ww) => efs
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

fun instance_is_enabled k = (
    case k of
	Def_Body (mk, j, cs, nm, L_Bool b, ee, aa, ww) => b
      | Def_Body _ => raise error_conditional_is_not_determined
      | Def_Der _ => raise Match
      | Def_Primitive _ => raise Match
      | Def_Outer_Alias _ => raise Match
      | Def_Name _ => raise Match
      | Def_Scoped _ => raise Match
      | Def_Refine _ => raise Match
      | Def_Extending _ => raise Match
      | Def_Replaced _ => raise Match
      | Def_Displaced _ => raise Match
      | Def_In_File => raise Match
      | Def_Mock_Array _ => raise Match)

(* ================================================================ *)

fun expression_is_boolean_literal w = (
    ((expression_is_literal w)
     andalso
     case w of
         L_Bool _ => true
       | _ => false))

(* Evaluates a condition of a conditional component and sets the
   condition as a boolean literal.  It returns an enabled state. *)

fun enable_instance enable0 k0 = (
    let
	val simplify = (fold_constants k0 false [])
    in
	if (not (class_is_ordinary_instance k0)) then
	    enable0
	else
	    case k0 of
	        Def_Body (mk, j, cs, nm, cc0, ee, aa, ww) => (
		let
		    val subj = (subject_of_class k0)
		    val cc1 = (simplify cc0)
		    val cc2 = if (cc1 = NIL) then L_Bool true else cc1
		    val _ = if (expression_is_boolean_literal cc2) then ()
			    else raise error_non_constant_conditional
		    val enable1 = (enable0 andalso (literal_to_bool cc2))
		    val cc3 = L_Bool enable1
		    val k1 = Def_Body (mk, j, cs, nm, cc3, ee, aa, ww)
		    val _ = (store_to_instance_tree subj k1)
		in
		    enable1
		end)
	      | Def_Der _ => raise Match
	      | Def_Primitive _ => raise Match
	      | Def_Outer_Alias _ => raise Match
	      | Def_Name _ => raise Match
	      | Def_Scoped _ => raise Match
	      | Def_Refine _ => raise Match
	      | Def_Extending _ => raise Match
	      | Def_Replaced _ => raise Match
	      | Def_Displaced _ => raise Match
	      | Def_In_File => raise Match
	      | Def_Mock_Array _ => raise Match
    end)

(* Evaluates a condtion of a condtional component and descends the
   tree.  It disables subcomponents of a disabled component if
   enable0=false. *)

fun enable_component_node enable0 node = (
    let
	val (kp, components) = (access_node E5 node)
	val enable1 = (enable_instance enable0 kp)
	val _ = (app (fn (Slot (v, dim, nodes, _)) =>
			 (app (enable_component_node enable1) nodes))
		     components)
    in
	()
    end)

(* Disables conditional components by scanning all instances. *)

fun disable_components () = (
    (enable_component_node true instance_tree))

(* ================================================================ *)

(* Lists connector pairs when not disabled. *)

fun make_connects (x0, sidex) (y0, sidey) subj acc0 = (
    let
	fun connect ((x, y), acc) = (
	    if ((instance_is_enabled x) andalso (instance_is_enabled y)) then
		let
		    val x0 = (subject_of_class x)
		    val y0 = (subject_of_class y)
		in
		    (acc @ [((x0, sidex), (y0, sidey), subj)])
		end
	    else
		acc)

	val kx = surely (fetch_from_instance_tree x0)
	val ky = surely (fetch_from_instance_tree y0)
	val (dimx, xx) = (unwrap_array_of_instances kx)
	val (dimy, yy) = (unwrap_array_of_instances ky)
	val _ = if (dimx = dimy) then ()
		else raise error_mismatch_connector_arrays
    in
	(foldl connect acc0 (ListPair.zipEq (xx, yy)))
    end)

fun collect_connects_in_equation kp (q0, acc0) = (
    case q0 of
	Eq_Eq _ => (q0, acc0)
      | Eq_Connect ((Cref (x0, sidex), Cref (y0, sidey)), aa, ww) => (
	let
	    val x1 = (literalize_subscripts kp x0)
	    val y1 = (literalize_subscripts kp y0)
	    val subj = (subject_of_class kp)
	in
	    (q0, (make_connects (x1, sidex) (y1, sidey) subj acc0))
	end)
      | Eq_Connect ((_, _), aa, ww) => raise Match
      | Eq_If _ => (q0, acc0)
      | Eq_When _ => (q0, acc0)
      | Eq_App _ => (q0, acc0)
      | Eq_For _ => (q0, acc0))

fun collect_connects_in_instance (k0, acc0) = (
    if (not (class_is_ordinary_instance k0)) then
	acc0
    else
	let
	    val efix = (fn (e, a) => (e, a))
	    val qfix = (collect_connects_in_equation k0)
	    val qwalk = (walk_in_equation qfix efix)
	    val swalk = (fn (s, a) => (s, a))
	    val walker = {vamp_q = qwalk, vamp_s = swalk}
	    val (k1, acc1) = (walk_in_class walker (k0, acc0))
	in
	    acc1
	end)

(* Collects connect-equations.  It attaches an instance name (a
   subject) to a connect-equation where it is found. *)

fun collect_connects () = (
    (traverse_tree collect_connects_in_instance (instance_tree, [])))

(* ================================================================ *)

(* Groups a list of (subj,x) to a list of (subj,[x0,x1,...]) for the
   elements in the same array.  The returned subject has an empty
   subscript.  It assumes the elements of a list are ordered by array
   index. *)

fun group_to_array (ee : (subject_t * 'a) list) = (
    let
	fun same_array ((subj0, n0), (subj1, n1)) = (
	    (subject_equal_sans_subscript subj0 subj1))

	fun merge ee = (
	    case ee of
		[] => raise Match
	      | (subjx, _) :: _ => (
		((drop_last_subscript_of_subject subjx), (map #2 ee))))
    in
	(map merge (list_groups same_array ee))
    end)

fun insert_cardinality_variable (subj, nn) = (
    let
	val scope = (dummy_scope ())

	fun scoped x = (Scoped (x, scope))

	fun initializer nn = (
	    case nn of
		[n] => [Mod_Value ((scoped o z_literal) n)]
	      | _ => [Mod_Value
			  (scoped (Array_Constructor (map z_literal nn)))])

	val connector = surely (fetch_from_instance_tree subj)
	val (dim0, _) = (unwrap_array_of_instances connector)

	val _ = if ((array_size dim0) = (length nn)) then () else raise Match

	val suffix = (operator_suffix "cardinality")
	val (supsubj, (Id s, _)) = (subject_prefix subj)
	val variable = (compose_subject supsubj (Id (s ^"_"^ suffix)) [])
	val values = (initializer nn)
	val dimension = (map (scoped o z_literal) dim0)

	val k0 = Def_Displaced (Ctag ["Integer"], the_root_subject)
	val k1 = (fetch_displaced_class E0 k0)
	val q = (Effort, Constant, Modeless)
	val k2 = Def_Refine (k1, NONE, copy_type, q, (dimension, values),
			     NIL, Annotation [], Comment [])
	val (dim1, array1) = (instantiate_class (variable, k2))
	val _ = if (dim0 = dim1) then () else raise Match
	val _ = (map (bind_in_instance false) array1)

	val k4 = surely (fetch_from_instance_tree variable)
	val (_, array2) = (unwrap_array_of_instances k4)
	(*val _ = if ((cook_step k4) = E5) then () else raise Match*)
    in
	()
    end)

(* Counts connect-equations on each pseudo variable in vv.  The
   results are stored as equations of cardinality of connectors.  It
   counts only on the inside part.  For counting on a pseudo variable
   v=m.c.d.e, the counter counts the occurrences of prefixes {m.c,
   m.c.d, m.c.d.e}. *)

fun count_connects vv cc = (
    let
	val insides = (foldl
			   (fn (((x, sidex), (y, sidey), subj), acc) => (
				((if (is_inside sidex) then [x] else [])
				 @ (if (is_inside sidey) then [y] else [])
				 @ acc))) [] cc)

	fun prefix subj x = (subject_is_prefix x subj)

	fun count (subj, acc) = (
	    let
		val n = (list_count_true (prefix subj) insides)
	    in
		(acc @ [(subj, n)])
	    end)

	val paths = (map pseudo_path vv)
	val counts = (List.concat
			  (map (fn path =>
				   (enumerate_instances count path []))
			       paths))
	val countset = (group_to_array counts)
    in
	countset
    end)

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
			     (dim1, []), NIL, Annotation [], Comment [])
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
		 [Array_Constructor
		      (map denominator_term otherconnectors)]))

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
		 [Array_Constructor
		      (map numerator_term otherconnectors)]))

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

fun make_seal_equation v = (
    Eq_Eq ((L_Number (R, "0"), Instances ([], [v])),
	   Annotation [], Comment []))

(* Collects flow components which are not connected.  It is to seal
   flow components like quick-connects.  It takes the all connectors
   in connect-equations.  Components are considered as connected when
   they are subcomponents of a connected connectors. *)

fun collect_unconnected_flow_components connected = (
    let
	fun collect (node, acc0) = (
	    let
		val (subj, _, _) = node
		val (kp, components) = (access_node E5 node)
	    in
		if (List.exists (subject_is_component subj) connected) then
		    acc0
		else
		    let
			val acc1 = if (marked_as_flow kp) then
				       acc0 @ [subj]
				   else
				       acc0
			val acc2 = (foldl (fn (Slot (_, _, nodes, _), acc) =>
					      (foldl collect acc nodes))
					  acc1 components)
		    in
			acc2
		    end
	    end)
    in
	(collect (instance_tree, []))
    end)

(* ================================================================ *)

fun substitute_operator_expression kp (w0, acc0) = (
    let
	val simplify = (fold_constants kp false [])

	fun modify name ee0 (w0, acc0) = (
	    case ee0 of
		[Vref (_, [])] => raise Match
	      | [Vref (NONE, _)] => raise Match
	      | [x as Vref (SOME VAR, rr0)] => (
		let
		    val (prefix, (Id v0, ss)) = (split_last rr0)
		    val v1 = Id (v0 ^"_"^ (operator_suffix name))
		    val w1 = Vref (SOME VAR, prefix @ [(v1, ss)])
		    val (ins0, acs0, crd0) = acc0
		    val acc1
			= case name of
			      "inStream" => (x :: ins0, acs0, crd0)
			    | "actualStream" => (ins0, x :: acs0, crd0)
			    | "cardinality" => (ins0, acs0, x :: crd0)
			    | _ => raise Match
		in
		    (w1, acc1)
		end)
	      | [Vref (SOME PKG, _)] => (
		raise (error_bad_intrinsic_call name))
	      | [Instances ([], [subj])] => (
		(modify name [(subject_as_reference subj)] (w0, acc0)))
	      | [Cref (x as Vref (SOME VAR, rr), _)] => (
		(modify name [x] (w0, acc0)))
	      | [Cref (Instances ([], [subj]), _)] => (
		(modify name [(subject_as_reference subj)] (w0, acc0)))
	      | [_] => raise (error_bad_intrinsic_call name)
	      | _ => raise (error_bad_intrinsic_call name))

	fun check name ee0 (w0, acc0) = (
	    case name of
		"inStream" => (modify "inStream" ee0 (w0, acc0))
	      | "actualStream" => (modify "actualStream" ee0 (w0, acc0))
	      | "cardinality" => (modify "cardinality" ee0 (w0, acc0))
	      | _ => (w0, acc0))
    in
	case w0 of
	    App (f0, ee0) => (
	    let
		val f1 = (simplify f0)
	    in
		case f1 of
		    Vref (SOME PKG, [(Id name, [])]) => (
		    (check name ee0 (w0, acc0)))
		  | Instances ([], [Subj (PKG, [(Id name, [])])]) => (
		    (check name ee0 (w0, acc0)))
		  | _ => (w0, acc0)
	    end)
	  | _ => (w0, acc0)
    end)

val substitute_operators_in_instance
    = (substitute_expression substitute_operator_expression)

(* Substitutes the uses of operators with corresponding variables for
   inStream(), actualStream(), and cardinality().  It collects and
   returns arguments for each of the operators. *)

fun substitute_connector_operators () = (
    (traverse_tree substitute_operators_in_instance
		   (instance_tree, ([], [], []))))

(* ================================================================ *)

fun insert_equations_section eqns = (
    let
	val section = Element_Equations (false, eqns)
	val (subj, kx, cx) = instance_tree
	val model0 = (! kx)
    in
	case model0 of
	    Def_Body (mk, j, cs, nm, cc, ee0, aa, ww) => (
	    let
		val ee1 = (ee0 @ [section])
		val model1 = Def_Body (mk, j, cs, nm, cc, ee1, aa, ww)
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
	val k2 = surely (fetch_from_instance_tree mixin)
	val _ = if ((cook_step k2) = E5) then () else raise Match
    in
	()
    end)

fun connect_connectors (instream, actualstream, cardinality) = (
    let
	val _ = (expand_equations_for_connects ())

	val cc0 = (collect_connects ())
	val countset = (count_connects cardinality cc0)
	val _ = (app insert_cardinality_variable countset)

	val _ = (expand_expandable_connectors cc0)

	val cc1 = (map (fn (x, y, subj) => [x, y]) cc0)
	val cc2 = (make_unions (op =) cc1)
	val x = (map make_connect_equations cc2)
	val mixins = (List.concat (map #1 x))
	val eqns0 = (List.concat (map #2 x))
	val _ = (insert_equations_section eqns0)
	val _ = (app insert_mixin_variable mixins)

	val connectors = (map #1 (foldl (op @) [] cc1))
	val flows = (collect_unconnected_flow_components connectors)
	val eqns1 = (map make_seal_equation flows)
	val _ = (insert_equations_section eqns1)
    in
	()
    end)

(* ================================================================ *)

val bind_in_model = postbinder.bind_in_model
val substitute_outer = postbinder.substitute_outer

fun xbind () = (
    let
	val _ = (bind_in_model ())
	val _ = (substitute_outer ())
    in
	()
    end)

fun xconnect () = (
    let
	val uniquify = ((remove_duplicates (op =)) o (map pseudo_variable))

	val _ = (disable_components ())
	val vvv = (substitute_connector_operators ())
	val instream = (uniquify (#1 vvv))
	val actualstream = (uniquify (#2 vvv))
	val cardinality = (uniquify (#3 vvv))
	val _ = (connect_connectors (instream, actualstream, cardinality))
    in
	(instream, actualstream, cardinality)
    end)

end
