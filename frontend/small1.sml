(* small1.sml -*-Coding: us-ascii-unix;-*- *)
(* Copyright (C) 2018-2020 RIKEN R-CCS *)

(* SMALL FUNCTIONS FOR ELABORATION (second halt). *)

structure small1 = struct

open plain
open ast
open message
open small0

val fetch_from_instance_tree = classtree.fetch_from_instance_tree

(* Converts a subject to a variable reference, by simply making an
   integer index to a literal expression. *)

fun subject_as_reference (Subj (ns, cc0)) = (
    let
	fun mapr f (x0, x1) = (x0, (f x1))
	val cc1 = (attach_dot_of_package_root ns cc0)
	val rr = (map (mapr (map z_literal)) cc1)
    in
	Vref (true, rr)
    end)

(* Converts a variable reference to a subject, requiring array
   subscripts being literals.  It is called when it is certain that
   array subscripts are literals. *)

fun reference_as_subject x = (
    case x of
	Vref (_, []) => raise Match
      | Vref (false, _) => raise Match
      | Vref (true, rr) => (
	let
	    fun mapr f (x0, x1) = (x0, f x1)
	    val ns = (discriminate_reference_root x)
	    val cc0 = (map (mapr (map literal_to_int)) rr)
	    val cc1 = (drop_dot_of_package_root ns cc0)
	in
	    Subj (ns, cc1)
	end)
      | _ => raise Match)

(* Tests literalness.  It assumes performing partial folding of
   constants beforehand ("partial folding" is defined by this
   function). *)

fun expression_is_literal w = (
    case w of
	NIL => raise Match
      | Colon => raise Match
      | Otherwise => raise Match
      | Scoped _ => raise Match
      | Vref (_, []) => raise Match
      | Vref (false, _) => raise Match
      | Vref (true, _) => false
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
