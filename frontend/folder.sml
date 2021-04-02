(* folder.sml -*-Coding: us-ascii-unix;-*- *)
(* Copyright (C) 2018-2021 RIKEN R-CCS *)

(* CONSTANT FOLDER FOR DECLARATIONS.  Constant-folding works on
   expressions after binding, which resolves variable names to a fully
   qualified state.  It requires all referenced variables are in a
   bound state beforehand, becuase it does not call the binding
   process. *)

structure folder :
sig
    type definition_body_t
    type class_definition_t
    type expression_t
    type id_t

    val fold_constants :
	definition_body_t -> bool -> (id_t * expression_t) list
	-> expression_t -> expression_t

    val explicitize_range : expression_t -> expression_t list
end = struct

open plain
open ast
(*open small0*)
open small1
open expression

val fetch_from_instance_tree = classtree.fetch_from_instance_tree

val simple_type_attribute = simpletype.simple_type_attribute

val simplify_ite = walker.simplify_ite
val expression_is_literal = expression.expression_is_literal

(*val unary_operator = operator.unary_operator*)
(*val binary_operator = operator.binary_operator*)
(*val relational_operator = operator.relational_operator*)
val fold_operator_application = operator.fold_operator_application
val fold_pseudo_split = operator.fold_pseudo_split
val bool_order = operator.bool_order
val enumerator_order = operator.enumerator_order
val take_enumarator_element = simpletype.take_enumarator_element

val expression_to_string = dumper.expression_to_string

fun tr_expr (s : string) = if true then (print (s ^"\n")) else ()
fun tr_expr_vvv (s : string) = if false then (print (s ^"\n")) else ()

(*fun loop_bind_components (subj, kx) = raise Match*)

(* Arranges a non-empty list as an array of arrays with regard to a
   dimension. *)

fun make_explicit_array dim0 vv0 = (
    let
	val size = (array_size dim0)
	val _ = if (size <> 0) then () else raise Match
	val _ = if ((length vv0) = size) then () else raise Match
    in
	case dim0 of
	    [] => raise Match
	  | [r] => Array_Constructor vv0
	  | r :: dim1 => (
	    let
		val subsize = (array_size dim1)
		val vv1 = (list_partition_by_n subsize vv0)
		val vv2 = (map (make_explicit_array dim1) vv1)
	    in
		Array_Constructor vv2
	    end)
    end)

(* ================================================================ *)

fun make_primitive_type name v = (
    Def_Primitive (name, v))

fun primitive_type_is_number p = (
    case p of
	P_Number R => true
      | P_Number Z => true
      | _ => false)

fun primitive_type_is_integer p = (
    case p of
	P_Number Z => true
      | _ => false)

fun primitive_type_is_boolean p = (
    case p of
	P_Boolean => true
      | _ => false)

fun primitive_type_is_string p = (
    case p of
	P_String => true
      | _ => false)

(* Takes a value of a class (kp) for an original reference (w0).  It
   takes a value-attribute of a simple-type.  Or, it converts a
   function reference to an Instances expression. *)

fun value_of_instance w0 kp = (
    case kp of
	Def_Body (mk, subj, cs, nm, cc, ee, aa, ww) => (
	if (not (class_is_simple_type kp)) then
	    let
		val _ = if (class_is_package kp) then
			    if (step_is_at_least E3 kp) then ()
			    else raise Match
			else
			    if (step_is_at_least E5 kp) then ()
			    else raise Match
	    in
		if (class_is_package kp) then
		    w0
		else
		    Instances ([], [subj])
	    end
	else
	    let
		val _ = if (step_is_at_least E3 kp) then () else raise Match
		val v = (simple_type_attribute kp (Id "value"))
	    in
		if (v = NIL) then
		    w0
		else
		    v
	    end)
      | Def_Mock_Array (dim, array, dummy) => (
	let
	    val _ = if (dim <> []) then () else raise Match
	    val vv = (map (value_of_instance NIL) array)
	in
	    if ((array_size dim) = 0) then
		(*w0*)
		Instances ([0], [])
	    else if (List.exists (fn v => (v = NIL)) vv) then
		(*w0*)
		Instances (dim, (map subject_of_class array))
	    else
		(make_explicit_array dim vv)
	end)
      | Def_Der _ => w0
      | Def_Primitive (P_Enum tag_, L_Enum (tag, v)) => L_Enum (tag, v)
      | Def_Primitive _ => raise Match
      | _ => raise Match)

fun value_of_reference w0 = (
    case w0 of
	Vref (_, []) => raise Match
      | Vref (NONE, _) => raise Match
      | Vref (SOME _, _) => (
	let
	    val subj = (reference_as_subject w0)
	in
	    case (fetch_from_instance_tree subj) of
		NONE => raise error_no_instance_found
	      | SOME k0 => (value_of_instance w0 k0)
	end)
      | _ => raise Match)

(* Simplifies an expression.  It does not repeat simplifying when
   oneshot=true.  An environment holds bindings of iterator variables,
   or it is null and ignored.  It assumes entries in an environment
   are already simplified. *)

fun fold_expression ctx oneshot env w0 = (
    let
	val walk_x = (fold_expression ctx oneshot env)
	val walk_n_x = (fn (n, x) => (n, (walk_x x)))
	val walk_x_x = (fn (x, y) => ((walk_x x), (walk_x y)))
	val walk_x_option = (Option.map walk_x)

	val _ = tr_expr_vvv (";; fold_expression ("^
			     (expression_to_string w0) ^")")
    in
	case w0 of
	    NIL => NIL
	  | Colon => Colon
	  | Otherwise => Otherwise
	  | Scoped _ => raise Match
	  | Vref (_, []) => raise Match
	  | Vref (NONE, _) => raise Match
	  | Vref (SOME _, _) => (
	    let
		val (w1, literals) = (fold_subscripts ctx oneshot env w0)
	    in
		if (not literals) then
		    w1
		else if (w0 <> w1 andalso oneshot) then
		    (* DO NOT REPEAT FOLDING. *)
		    w1
		else
		    (value_of_reference w1)
	    end)
	  | Opr _ => w0
	  | App (f0, xx0) => (
	    let
		val f1 = (walk_x f0)
		val xx1 = (map walk_x xx0)
		val w1 = App (f1, xx1)
	    in
		if (w0 <> w1 andalso oneshot) then
		    (* DO NOT REPEAT FOLDING. *)
		    w1
		else
		    (fold_operator_application (f1, xx1))
	    end)
	  | ITE cc0 => (
	    let
		val cc1 = (map walk_x_x cc0)
		val w1 = ITE cc1
	    in
		(simplify_ite w1)
	    end)
	  | Der xx0 => (
	    let
		val xx1 = (map walk_x xx0)
		val w1 = Der xx1
	    in
		w1
	    end)
	  | Pure xx0 => (
	    let
		val xx1 = (map walk_x xx0)
		val w1 = Pure xx1
	    in
		w1
	    end)
	  | Closure (n, xx0) => (
	    let
		val xx1 = (map walk_x xx0)
		val w1 = Closure (n, xx1)
	    in
		w1
	    end)
	  | L_Number _ => w0
	  | L_Bool _ => w0
	  | L_Enum _ => w0
	  | L_String _ => w0
	  | Array_Triple (x0, y0, z0) => (
	    let
		val x1 = (walk_x x0)
		val y1 = (walk_x y0)
		val z1 = (walk_x_option z0)
		val w1 = Array_Triple (x1, y1, z1)
	    in
		w1
	    end)
	  | Array_Constructor xx0 => (
	    let
		val xx1 = (map walk_x xx0)
		val w1 = Array_Constructor xx1
	    in
		w1
	    end)
	  | Array_Comprehension (x0, uu0) => (
	    let
		val x1 = (walk_x x0)
		val uu1 = (map walk_n_x uu0)
		val w1 = Array_Comprehension (x1, uu1)
	    in
		w1
	    end)
	  | Array_Concatenation uu0 => (
	    let
		val uu1 = (map (map walk_x) uu0)
		val w1 = Array_Concatenation uu1
	    in
		w1
	    end)
	  | Tuple xx0 => (
	    let
		val xx1 = (map walk_x xx0)
		val w1 = Tuple xx1
	    in
		w1
	    end)
	  | Reduction_Argument (x0, uu0) => (
	    let
		val x1 = (walk_x x0)
		val uu1 = (map walk_n_x uu0)
		val w1 = Reduction_Argument (x1, uu1)
	    in
		w1
	    end)
	  | Named_Argument (n, x0) => (
	    let
		val x1 = (walk_x x0)
		val w1 = Named_Argument (n, x1)
	    in
		w1
	    end)
	  | Pseudo_Split (x0, ss) => (
	    let
		val x1 = (walk_x x0)
		val w1 = Pseudo_Split (x1, ss)
	    in
		if (w0 <> w1 andalso oneshot) then
		    (* DO NOT REPEAT FOLDING. *)
		    w1
		else
		    (fold_pseudo_split w1)
	    end)
	  | Component_Ref _ => w0
	  (*| Instance (dim, kk, _) => w0*)
	  | Instances _ => w0
	  | Iref id => (
	    if (null env) then
		w0
	    else
		case (List.find (fn (v, x) => (v = id)) env) of
		    NONE => raise Match
		  | SOME (_, NIL) => w0
		  | SOME (_, x) => x)
	  | Lref _ => w0
	  | Cref (x0, b) => (
	    let
		val x1 = (walk_x x0)
		val w1 = Cref (x1, b)
	    in
		w1
	    end)
	  | Array_fill (x, n) => w0
	  | Array_diagonal x => w0
    end)

(* Tries to simplify array subscripts.  It returns a variable
   reference and a boolean indicating indices are all literals. *)

and fold_subscripts ctx oneshot env w0 = (
    case w0 of
	Vref (_, []) => raise Match
      | Vref (NONE, _) => raise Match
      | Vref (SOME ns, rr0) => (
	let
	    fun mapr f (x0, x1) = (x0, f x1)
	    val convert = (fold_expression ctx oneshot env)
	    val rr1 = (map (mapr (map convert)) rr0)
	    val ok = (List.all ((List.all expression_is_literal) o #2) rr1)
	in
	    (Vref (SOME ns, rr1), ok)
	end)
      | _ => raise Match)

(* Simplifies an expression.  It does not repeat simplifying when
   oneshot=true.  It is to give a chance that the resolver routines to
   assure referenced variables are instantiated in the build-phase.
   An environment holds iterator bindings of for-equations. *)

fun fold_constants kp oneshot env w0 = (
    let
	val _= if ((not oneshot) orelse (null env)) then () else raise Match
	val ctx = {k = kp}
	val w1 = (fold_expression ctx oneshot env w0)
	val _ = tr_expr_vvv (";; fold_constants ("^
			     (expression_to_string w0) ^"=>"^
			     (expression_to_string w1) ^")")
    in
	w1
    end)

(* ================================================================ *)

(* Converts a (constant) iterator range to an L_Number list. *)

fun explicitize_range w = (
    let
	fun literal_is_real w = (
	    case w of
		L_Number (ty, s) => (ty = R)
	      | L_Bool _ => false
	      | L_Enum _ => false
	      | _ => raise error_non_scalar_literal)

	fun z_scalar_literal w = (
	    case w of
		L_Number (_, s) => w
	      | L_Bool _ => (z_literal (bool_order w))
	      | L_Enum _ => (z_literal (enumerator_order w))
	      | _ => raise error_non_scalar_literal)

	fun r_scalar_literal w = (
	    case w of
		L_Number (_, s) => w
	      | L_Bool _ => (r_literal (Real.fromInt (bool_order w)))
	      | L_Enum _ => (r_literal (Real.fromInt (enumerator_order w)))
	      | _ => raise error_non_scalar_literal)

	fun range_by_type k = (
	    case k of
		Def_Mock_Array _ => raise error_range_on_array
	      | _ => (
		if (class_is_boolean k) then
		    (map z_literal [0, 1])
		else if (class_is_enumeration_definition k) then
		    case (take_enumarator_element k) of
			NONE => raise error_enum_unspecified
		      | SOME [] => raise Match
		      | SOME vv => (
			(map z_literal (z_seq 1 1 (length vv))))
		else
		    raise error_range_on_class))
    in
	if (not (expression_is_literal w)) then
	    raise error_range_iterator
	else
	    case w of
		Array_Triple triple => (
		case (triple_value triple) of
		    (R, s0, s1, s2) => (
		    let
			val lb = (r_value s0)
			val step = (r_value s1)
			val ub = (r_value s2)
			val n = (floor ((ub - lb) / step)) + 1
		    in
			if ((step > 0.0 andalso lb > ub)
			    orelse (step < 0.0 andalso lb < ub)) then
			    []
			else
			    (map r_literal (r_seq lb step n))
		    end)
		  | (Z, s0, s1, s2) => (
		    let
			val lb = (z_value s0)
			val step = (z_value s1)
			val ub = (z_value s2)
			val n = ((ub - lb) div step) + 1
		    in
			if ((step > 0 andalso lb > ub)
			    orelse (step < 0 andalso lb < ub)) then
			    []
			else
			    (map z_literal (z_seq lb step n))
		    end))
	      | Array_Constructor ee => (
		if (List.exists literal_is_real ee) then
		    (map r_scalar_literal ee)
		else
		    (map z_scalar_literal ee))
	      | Array_Comprehension (x, rr) => raise NOTYET
	      | Array_Concatenation _ => raise error_not_vector
	      (*| Instance ([], [k], NONE) => (range_by_type k)*)
	      (*| Instance (_, _, _) => raise error_range_on_array*)
	      | Instances ([], [subj]) => (
		let
		    val k = surely (fetch_from_instance_tree subj)
		in
		    (range_by_type k)
		end)
	      | Instances (_, _) => raise error_range_on_array
	      | _ => raise Match
    end)

end
