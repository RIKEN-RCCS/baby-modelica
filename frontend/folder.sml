(* folder.sml -*-Coding: us-ascii-unix;-*- *)
(* Copyright (C) 2018-2020 RIKEN R-CCS *)

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

    val fold_constants_in_expression :
	definition_body_t -> bool
	-> expression_t -> expression_t

    val simplify_ite : expression_t -> expression_t

    val value_of_instance :
	expression_t -> definition_body_t -> expression_t
end = struct

open plain
open ast
(*open small0*)
open small1

val simple_type_attribute = simpletype.simple_type_attribute

(*val unary_operator = operator.unary_operator*)
(*val binary_operator = operator.binary_operator*)
(*val relational_operator = operator.relational_operator*)
val fold_constants_on_operator = operator.fold_constants_on_operator
val fold_pseudo_split = operator.fold_pseudo_split

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

(* Takes a value of a class (kp) for an original variable reference
   (x0).  It takes a value-attribute of a simple-type. *)

fun value_of_instance x0 kp = (
    case kp of
	Def_Body (mk, j, cs, (c, n, x), ee, aa, ww) => (
	if (not (class_is_simple_type kp)) then
	    let
		val _ = if (class_is_package kp) then
			    if (step_is_at_least E3 kp) then ()
			    else raise Match
			else
			    if (step_is_at_least E5 kp) then ()
			    else raise Match
	    in
		Instance ([], [kp], NONE)
	    end
	else
	    let
		val _ = if (step_is_at_least E3 kp) then () else raise Match
		val v = (simple_type_attribute kp (Id "value"))
	    in
		if (v = NIL) then
		    x0
		else
		    v
	    end)
      | Def_Mock_Array (dim, array, dummy) => (
	let
	    val _ = if (dim <> []) then () else raise Match
	    val vv = (map (value_of_instance NIL) array)
	in
	    if ((array_size dim) = 0) then
		Instance (dim, array, dummy)
	    else if (List.exists (fn v => (v = NIL)) vv) then
		Instance (dim, array, dummy)
	    else
		(make_explicit_array dim vv)
	end)
      | Def_Der _ => x0
      | Def_Primitive (P_Enum tag_, L_Enum (tag, v)) => L_Enum (tag, v)
      | Def_Primitive _ => raise Match
      | _ => raise Match)

(* Tests if it is a constant after constant folding. *)

fun expression_is_constant__ w = (
    let
	fun check variability initialvalue = (
	    case variability of
		Continuous => (expression_is_constant__ initialvalue)
	      | Discrete => (expression_is_constant__ initialvalue)
	      | Parameter => (
		if (not (expression_is_constant__ initialvalue)) then
		    raise error_no_value_to_constant
		else
		    true)
	      | Constant => (
		if (not (expression_is_constant__ initialvalue)) then
		    raise error_no_value_to_constant
		else
		    true))
    in
	case w of
	    NIL => false
	  | Colon => raise Match
	  | Otherwise => raise Match
	  | Scoped _ => raise Match
	  | Vref (_, []) => raise Match
	  | Vref (false, _) => raise Match
	  | Vref (true, (r0 as (Id n, s) :: t)) => (
	    false)
	  | Opr _ => raise Match
	  | App (x0, a0) => false
	  | ITE c0 => false
	  | Der a0 => false
	  | Pure a0 => (List.all expression_is_constant__ a0)
	  | Closure (n, a0) => false
	  | L_Number x => true
	  | L_Bool x => true
	  | L_Enum _ => raise Match
	  | L_String s => true
	  | Array_Triple (x0, y0, z0) => (
	    case z0 of
		NONE => (
		(List.all expression_is_constant__ [x0, y0]))
	      | SOME z1 => (
		(List.all expression_is_constant__ [x0, y0, z1])))
	  | Array_Constructor a0 => (List.all expression_is_constant__ a0)
	  | Array_Comprehension (x0, u0) => false
	  | Array_Concatenation a0 => (
	    (List.all (List.all expression_is_constant__) a0))
	  | Tuple a0 => (List.all expression_is_constant__ a0)
	  | Reduction_Argument (x0, u0) => false
	  | Named_Argument (n, x0) => (expression_is_constant__ x0)
	  | Pseudo_Split (x0, s) => (expression_is_constant__ x0)
	  | Component_Ref _ => raise NOTYET
	  | Instance _ => raise NOTYET
	  | Iref v => raise NOTYET
	  | Array_fill (x, n) => ((expression_is_constant__ x)
				  andalso (expression_is_constant__ n))
	  | Array_diagonal x => (expression_is_constant__ x)
    end)

fun simplify_ite w0 = (
    case w0 of
	ITE cc0 => (
	let
	    val cc1 = foldr
			  (fn (c, tail) =>
			      case (c, tail) of
				  ((Otherwise, v), []) => [(Otherwise, v)]
				| ((Otherwise, v), _) => raise Match
				| ((L_Bool true, v), _) => [(Otherwise, v)]
				| ((L_Bool false, v), _) => tail
				| (_, _) => (c :: tail))
			  [] cc0
	    val ite1 = case ITE cc1 of
			   ITE [(Otherwise, v)] => v
			 | ITE ((Otherwise, v) :: _) => raise Match
			 | ITE _ => ITE cc1
			 | _ => raise Match
	in
	    ite1
	end)
      | _ => raise Match)

fun value_of_reference w0 = (
    case w0 of
	Vref (true, _) => (
	let
	    val subj = (reference_as_subject w0)
	in
	    case (fetch_from_instance_tree subj) of
		NONE => raise error_no_instance_found
	      | SOME k0 => (value_of_instance w0 k0)
	end)
      | _ => raise Match)

(* Returns a pair of an expression and a class.  It does not repeat
   simplifying, to allow binding routines to resolve variable
   references. *)

fun fold_expression ctx needliteral w0 = (
    let
	val walk_x = (fold_expression ctx needliteral)
	val walk_x = (fold_expression ctx needliteral)
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
	  | Vref (false, _) => raise Match
	  | Vref (true, rr0) => (
	    let
		val (w1, literals) = (fold_subscripts_in_reference ctx w0)
	    in
		if (not literals) then
		    w1
		else if (w0 <> w1) then
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
		if (w0 <> w1) then
		    (* DO NOT REPEAT FOLDING. *)
		    w1
		else
		    (fold_constants_on_operator (f1, xx1))
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
		if (w0 <> w1) then
		    (* DO NOT REPEAT FOLDING. *)
		    w1
		else
		    (fold_pseudo_split w1)
	    end)
	  | Component_Ref _ => w0
	  | Instance (dim, kk, _) => w0
	  | Iref _ => w0
	  | Array_fill (x, n) => w0
	  | Array_diagonal x => w0
    end)

(* Tries to fold constants in array indices, and returns a reference
   and a boolean indicating indices are all literals. *)

and fold_subscripts_in_reference ctx w0 = (
    case w0 of
	Vref (_, []) => raise Match
      | Vref (false, _) => raise Match
      | Vref (true, rr0) => (
	let
	    fun mapr f (x0, x1) = (x0, f x1)
	    val convert = (fold_expression ctx true)
	    val rr1 = (map (mapr (map convert)) rr0)
	    val ok = (List.all ((List.all expression_is_literal) o #2) rr1)
	in
	    (Vref (true, rr1), ok)
	end)
      | _ => raise Match)

fun fold_constants_in_expression kp needliteral w0 = (
    let
	(*val _ = if (step_is_at_least E4 kp) then () else raise Match*)
	val ctx = {k = kp}
	val w1 = (fold_expression ctx needliteral w0)
	val _ = tr_expr_vvv (";; fold_constants ("^
			     (expression_to_string w0) ^"=>"^
			     (expression_to_string w1) ^")")
    in
	w1
    end)

end
