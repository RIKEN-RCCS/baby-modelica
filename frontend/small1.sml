(* small1.sml -*-Coding: us-ascii-unix;-*- *)
(* Copyright (C) 2018-2021 RIKEN R-CCS *)

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

end
