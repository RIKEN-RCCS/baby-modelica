(* expression.sml -*-Coding: us-ascii-unix;-*- *)
(* Copyright (C) 2018-2020 RIKEN R-CCS *)

(* Small functions on expressions. *)

structure expression
: sig
    type number_type_t
    type expression_t

    val bool_order : expression_t -> int
    val bool_nth : int -> expression_t
    val bool_size : expression_t -> expression_t -> int
    val enumerator_order : expression_t -> int
    val enumerator_compare : expression_t -> expression_t -> int
    val enumerator_nth : expression_t -> int -> expression_t
    val enumerator_size : expression_t -> expression_t -> int

    val triple_value : expression_t * expression_t * expression_t option
		       -> number_type_t * string * string * string
    val triple_nth : expression_t -> expression_t -> expression_t
		     -> int list -> expression_t
    val triple_size : expression_t -> expression_t -> expression_t -> int
    val range_nth : expression_t -> expression_t -> int list -> expression_t

    val expression_is_literal : expression_t -> bool
end = struct

open ast plain
open small1

fun tr_expr (s : string) = if true then (print (s ^"\n")) else ()
fun tr_expr_vvv (s : string) = if false then (print (s ^"\n")) else ()

val instance_tree = classtree.instance_tree
val traverse_tree = classtree.traverse_tree

val take_enumarator_element = simpletype.take_enumarator_element

(* ================================================================ *)

(* Returns a zero-origin integer indicating the order of a boolean. *)

fun bool_order x = (
    case x of
	L_Bool false => 0
      | L_Bool true => 1
      | _ => raise Match)

(* Returns a boolean at a zero-origin index. *)

fun bool_nth i = (
    case i of
	0 => L_Bool false
      | 1 => L_Bool true
      | _ => raise Match)

fun bool_size x y = (
    let
	val lb = (bool_order x)
	val ub = (bool_order y)
	val z = (ub - lb + 1)
    in
	(Int.max (0, z))
    end)

(* Returns a zero-origin integer indicating the order of an
   enumerator. *)

fun enumerator_order x = (
    case x of
	L_Enum (tag, v) => (
	let
	    val subj = (tag_to_subject tag)
	    val kp = surely (fetch_from_instance_tree subj)
	in
	    case (take_enumarator_element kp) of
		NONE => raise error_enum_unspecified
	      | SOME [] => raise Match
	      | SOME vv => (
		case (list_index (fn (k, a, w) => (v = k)) vv 0) of
		    NONE => raise Match
		  | SOME index => index)
	end)
      | _ => raise Match)

fun enumerator_compare x y = (
    let
	val ix = (enumerator_order x)
	val iy = (enumerator_order y)
    in
	(ix - iy)
    end)

(* Returns an enumerator at a zero-origin index. *)

fun enumerator_nth x i = (
    case x of
	L_Enum (tag, v) => (
	let
	    val subj = (tag_to_subject tag)
	    val kp = surely (fetch_from_instance_tree subj)
	in
	    case (take_enumarator_element kp) of
		NONE => raise error_enum_unspecified
	      | SOME [] => raise Match
	      | SOME vv => (
		let
		    val (k, a, w) = (List.nth (vv, i))
		in
		    L_Enum (tag, k)
		end)
	end)
      | _ => raise Match)

fun enumerator_size x y = (
    let
	val lb = (enumerator_order x)
	val ub = (enumerator_order y)
	val z = (ub - lb + 1)
    in
	(Int.max (0, z))
    end)

fun triple_value (x, y, zo) = (
    case (x, y, zo) of
	(L_Number (t0, s0), L_Number (t1, s1), NONE) => (
	let
	    val ty = case (t0, t1) of (Z, Z) => Z | _ => R
	in
	    (ty, s0, "1", s1)
	end)
      | (L_Number (t0, s0), L_Number (t1, s1), SOME (L_Number (t2, s2))) => (
	let
	    val ty = case (t0, t1, t2) of (Z, Z, Z) => Z | _ => R
	in
	    (ty, s0, s1, s2)
	end)
      | (L_Bool _, L_Bool _, NONE) => (
	let
	    val lb = (bool_order x)
	    val ub = (bool_order y)
	in
	    (Z, (Int.toString lb), "1", (Int.toString ub))
	end)
      | (L_Enum (tag0, v0), L_Enum (tag1, v1), NONE) => (
	let
	    val lb = (enumerator_order x)
	    val ub = (enumerator_order y)
	in
	    (Z, (Int.toString lb), "1", (Int.toString ub))
	end)
      | _ => raise error_bad_triple)

fun triple_nth x y z (index : int list) = (
    case index of
	[] => raise Match
      | [i0] => (
	case (x, y, z) of
	    (L_Number (Z, sx), L_Number (Z, sy), L_Number (Z, sz)) => (
	    let
		val i = (i0 - 1)
		val lb = (z_value sx)
		val ub = (z_value sy)
		val s = (z_value sz)
		val _ = if (i >= 0 andalso i < ((ub + s - lb) div s)) then ()
			else raise error_out_of_range
		val v = (lb + (s * i))
	    in
		(z_literal v)
	    end)
	  | (L_Number (_, sx), L_Number (_, sy), L_Number (_, sz)) => (
	    let
		val i = (Real.fromInt (i0 - 1))
		val lb = (r_value sx)
		val ub = (r_value sy)
		val s = (r_value sz)
		val _ = if (i >= 0.0 andalso i < ((ub + s - lb) / s)) then ()
			else raise error_out_of_range
		val v = (lb + (s * i))
	  in
	      (r_literal v)
	  end)
	  | _ => raise error_bad_triple)
      | _ => raise error_dimensions_mismatch)

fun triple_size x y z = (
    case (x, y, z) of
	(L_Number (Z, sx), L_Number (Z, sy), L_Number (Z, sz)) => (
	let
	    val lb = (z_value sx)
	    val ub = (z_value sy)
	    val s = (z_value sz)
	    val z = ((ub + s - lb) div s)
	in
	    (Int.max (0, z))
	end)
      | (L_Number (_, sx), L_Number (_, sy), L_Number (_, sz)) => (
	let
	    val lb = (r_value sx)
	    val ub = (r_value sy)
	    val s = (r_value sz)
	    val z = (Real.floor ((ub + s - lb) / s))
	in
	    (Int.max (0, z))
	end)
      | _ => raise error_bad_triple)

fun range_nth x y (index : int list) = (
    case index of
	[] => raise Match
      | [i0] => (
	case (x, y) of
	    (L_Number (Z, _), L_Number (Z, _)) => (
	    (triple_nth x y (L_Number (Z, "1")) index))
	  | (L_Bool v0, L_Bool v1) => (
	    let
		val i = (i0 - 1)
		val lb = (bool_order x)
		val ub = (bool_order y)
		val _ = if (i >= 0 andalso i < (ub - lb + 1)) then ()
			else raise error_out_of_range
	    in
		(bool_nth i)
	    end)
	  | (L_Enum (tag0, _), L_Enum (tag1, _)) => (
	    let
		val _ = if (tag0 = tag1) then ()
			else raise error_different_enumerations
		val i = (i0 - 1)
		val lb = (enumerator_order x)
		val ub = (enumerator_order y)
		val _ = if (i >= 0 andalso i < (ub - lb + 1)) then ()
			else raise error_out_of_range
	    in
		(enumerator_nth x (lb + i))
	    end)
	  | _ => raise error_bad_triple)
      | _ => raise error_dimensions_mismatch)

(* ================================================================ *)

(* Tests literal-ness.  It assumes performing partial folding of
   constants beforehand ("partial folding" is defined as acceptance by
   this function).  Otherwise is used as a truth for an else-part. *)

fun expression_is_literal w = (
    case w of
	NIL => raise Match
      | Colon => raise Match
      | Otherwise => true
      | Scoped _ => raise Match
      | Vref (_, []) => raise Match
      | Vref (NONE, _) => raise Match
      | Vref (SOME _, _) => false
      | Opr _ => raise Match
      | App _ => false
      | ITE _ => false
      | Der _ => false
      | Pure _ => raise NOTYET
      | Closure _ => false
      | L_Number _ => true
      | L_Bool _ => true
      | L_Enum _ => true
      | L_String _ => true
      | Array_Triple (x, y, NONE) => (
	(List.all expression_is_literal [x, y]))
      | Array_Triple (x, y, SOME z) => (
	(List.all expression_is_literal [x, y, z]))
      | Array_Constructor ee => (List.all expression_is_literal ee)
      | Array_Comprehension (x, uu) => false
      | Array_Concatenation ee => (
	(List.all (List.all expression_is_literal) ee))
      | Tuple ee => raise error_tuple_in_rhs
      | Reduction_Argument (x, uu) => false
      | Named_Argument (n, x) => (expression_is_literal x)
      | Pseudo_Split (x, s) => (expression_is_literal x)
      | Component_Ref _ => false
      | Instance _ => false
      | Iref _ => false
      | Array_fill _ => false
      | Array_diagonal _ => false)

end
