(* small1.sml -*-Coding: us-ascii-unix;-*- *)
(* Copyright (C) 2018-2020 RIKEN R-CCS *)

(* SMALL FUNCTIONS FOR ELABORATION (second halt). *)

structure small1 = struct

open plain
open ast
open message
open small0

val fetch_from_instance_tree = classtree.fetch_from_instance_tree

fun extend_subject subj cc = (
    case cc of
	[] => raise Match
      | _ => (
	let
	    (*val _ = (assert_no_subscript_to_subject subj)*)
	    val Subj (ns, path) = subj
	in
	    Subj (ns, (path @ cc))
	end))

(* Converts a variable reference to a subject, requiring array
   subscripts being literals.  It is called only when it is certain
   that array subscripts are literals and the referenced variable is
   instantiated. *)

fun reference_as_subject x = (
    case x of
	Vref (_, []) => raise Match
      | Vref (NONE, _) => raise Match
      | Vref (SOME ns, rr) => (
	let
	    fun mapr f (x0, x1) = (x0, f x1)
	    val cc0 = (map (mapr (map literal_to_int)) rr)
	    (*val cc1 = (drop_dot_of_package_root ns cc0)*)
	in
	    Subj (ns, cc0)
	end))

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
