(* expression.sml -*-Coding: us-ascii-unix;-*- *)
(* Copyright (C) 2018-2020 RIKEN R-CCS *)

(* Small functions on expressions. *)

structure expression
: sig
    type number_type_t
    type expression_t
    type equation_t

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

    val find_iterator_range : expression_t -> equation_t list -> int option
end = struct

open ast plain
open small1

fun tr_expr (s : string) = if true then (print (s ^"\n")) else ()
fun tr_expr_vvv (s : string) = if false then (print (s ^"\n")) else ()

val instance_tree = classtree.instance_tree
val class_tree = classtree.class_tree
val traverse_tree = classtree.traverse_tree
val descend_instance_tree_node = classtree.descend_instance_tree_node

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
      (*| Instance _ => false*)
      | Instances _ => false
      | Iref _ => false
      | Array_fill _ => false
      | Array_diagonal _ => false)

(* ================================================================ *)

(* Scans primary expressions with an iterator v=Iref, while it skips
   subexpressions when an iterator is hidden by another one.  It calls
   f on Vref and g on Iref (every expression, not taking the iterator
   into consideration), but skips other primary expressions. *)

fun scan_for_iterator_e v (f, g) (w, acc0) = (
    let
	val scan_e = scan_for_iterator_e v (f, g)

	fun scan_may_be_hidden_e ((x, uu0), acc0) = (
	    case uu0 of
		[] => (scan_e (x, acc0))
	      | (id, r) :: uu1 => (
		let
		    val acc1 = (scan_e (r, acc0))
		in
		    if (v = Iref id) then
			acc1
		    else
			(scan_may_be_hidden_e ((x, uu1), acc1))
		end))
    in
	case w of
	    NIL => acc0
	  | Colon => acc0
	  | Otherwise => acc0
	  | Scoped _ => raise Match
	  | Vref (_, []) => raise Match
	  | Vref (NONE, _) => raise Match
	  | Vref (SOME _, rr) => (f (w, acc0))
	  | Opr _ => acc0
	  | App (x, xx) => (foldl scan_e acc0 (x :: xx))
	  | ITE cc => (
	    (foldl (fn ((x, y), acc) => (foldl scan_e acc [x, y])) acc0 cc))
	  | Der xx => (foldl scan_e acc0 xx)
	  | Pure xx => (foldl scan_e acc0 xx)
	  | Closure (n, xx) => (foldl scan_e acc0 xx)
	  | L_Number _ => acc0
	  | L_Bool _ => acc0
	  | L_Enum _ => acc0
	  | L_String _ => acc0
	  | Array_Triple (x, y, NONE) => (foldl scan_e acc0 [x, y])
	  | Array_Triple (x, y, SOME z) => (foldl scan_e acc0 [x, y, z])
	  | Array_Constructor xx => (foldl scan_e acc0 xx)
	  | Array_Comprehension (x, uu) => (
	    (scan_may_be_hidden_e ((x, uu), acc0)))
	  | Array_Concatenation xx => (
	    (foldl (fn (yy, acc) => (foldl scan_e acc yy)) acc0 xx))
	  | Tuple xx => raise error_tuple_in_rhs
	  | Reduction_Argument (x, uu) => (
	    (scan_may_be_hidden_e ((x, uu), acc0)))
	  | Named_Argument (n, x) => (scan_e (x, acc0))
	  | Pseudo_Split (x, s) => (scan_e (x, acc0))
	  | Component_Ref (x, c) => (scan_e (x, acc0))
	  (*| Instance _ => acc0*)
	  | Instances _ => acc0
	  | Iref _ => (g (w, acc0))
	  | Array_fill (x, y) => (foldl scan_e acc0 [x, y])
	  | Array_diagonal x => (scan_e (x, acc0))
    end)

fun scan_for_iterator_q v (f, g) (q, acc0) = (
    let
	val scan_e = scan_for_iterator_e v (f, g)
	val scan_q = scan_for_iterator_q v (f, g)

	fun scan_may_be_hidden_q ((qq, uu0), acc0) = (
	    case uu0 of
		[] => (foldl scan_q acc0 qq)
	      | (id, r) :: uu1 => (
		let
		    val acc1 = (scan_e (r, acc0))
		in
		    if (v = Iref id) then
			acc1
		    else
			(scan_may_be_hidden_q ((qq, uu1), acc1))
		end))
    in
	case q of
	    Eq_Eq ((x, y), _, _) => (foldl scan_e acc0 [x, y])
	  | Eq_Connect (((x, _), (y, _)), _, _) => (foldl scan_e acc0 [x, y])
	  | Eq_If (cc, _, _) => (
	    (foldl
		 (fn ((x, qq), acc) => (foldl scan_q (scan_e (x, acc)) qq))
		 acc0 cc))
	  | Eq_When (cc, _, _) => (
	    (foldl
		 (fn ((x, qq), acc) => (foldl scan_q (scan_e (x, acc)) qq))
		 acc0 cc))
	  | Eq_For ((uu, qq), _, _) => (
	    (scan_may_be_hidden_q ((qq, uu), acc0)))
	  | Eq_App ((e, ee), _, _) => (
	    (foldl scan_e acc0 (e :: ee)))
    end)

(* Tests an iterator v=Iref appears in an expression. *)

fun contains_iterator v w = (
    let
	fun f (x, acc) = acc
	fun g (x, acc) = (v = x) orelse acc
    in
	(scan_for_iterator_e v (f, g) (w, false))
    end)

fun unique_range (vv0 : int option list) : int option = (
    let
	val vv1 = (List.mapPartial (fn v => v) vv0)
    in
	case (list_all_equal (op =) vv1) of
	    NONE => raise error_varying_iterator_range
	  | SOME NONE => NONE
	  | SOME (SOME v) => SOME v
    end)

fun find_range_in_reference_loop v (node0, rr0) : int option = (
    let
	fun select bitmap dim = (
	    (foldl (fn ((b, x), acc) => if b then x :: acc else acc)
		   [] (ListPair.zip (bitmap, dim))))
    in
	case rr0 of
	    [] => NONE
	  | (c as (id, ss)) :: rr1 => (
	    case (descend_instance_tree_node id node0) of
		NONE => raise Match
	      | SOME (Slot (_, dim, array, _)) => (
		let
		    val _ = if ((length ss) <= (length dim)) then ()
			    else raise Match

		    val bitmap = (map (contains_iterator v) ss)
		    val gg0 = (map SOME (select bitmap dim))
		    val rrx = (map (fn node => (node, rr1)) array)
		    val gg1 = (map (find_range_in_reference_loop v) rrx)
		in
		    (unique_range (gg0 @ gg1))
		end))
    end)

(* Returns an iterator range as an integer for an iterator v=Iref,
   when an iterator is found in the subscripts.  It is not called when
   an iterator is hidden by another nested iteration. *)

fun find_range_in_reference v (w, acc0) : int option = (
    case w of
	Vref (_, []) => raise Match
      | Vref (NONE, _) => raise Match
      | Vref (SOME ns, rr0) => (
	let
	    val root = if (ns = PKG) then class_tree else instance_tree
	    val g0 = (find_range_in_reference_loop v (root, rr0))
	in
	    (unique_range [g0, acc0])
	end)
      | _ => raise Match)

(* Returns a range value (as an integer) of an iterator v=Iref. *)

fun find_iterator_range v qq = (
    let
	fun f (x, acc) = (find_range_in_reference v (x, acc))
	fun g (x, acc) = acc
    in
	(foldl (scan_for_iterator_q v (f, g)) NONE qq)
    end)

(* ================================================================ *)

end
