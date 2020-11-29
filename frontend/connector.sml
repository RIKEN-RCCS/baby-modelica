(* connector.sml -*-Coding: us-ascii-unix;-*- *)
(* Copyright (C) 2018-2020 RIKEN R-CCS *)

(* CONNECTOR HANDLING. *)

structure connector

(*
: sig
xcollect
end
*)

= struct

open plain
open ast
open small0

fun tr_conn (s : string) = if true then (print (s ^"\n")) else ()
fun tr_conn_vvv (s : string) = if false then (print (s ^"\n")) else ()

val instance_tree = classtree.instance_tree
val traverse_tree = classtree.traverse_tree

val walk_in_class = walker.walk_in_class
val Q_Walker = walker.Q_Walker

(* ================================================================ *)

fun drop_subscripts rr = (
    (map (fn (id, _) => id) rr))

fun reference_is_subcomponent subj w = (
    case w of
	Vref (_, []) => raise Match
      | Vref (NONE, _) => raise Match
      | Vref (SOME ns0, rr0) => (
	let
	    val rr1 = (drop_subscripts rr0)
	    val (prefix, _) = (split_last rr1)
	    val Subj (ns1, cc0) = subj
	    val cc1 = (drop_subscripts cc0)
	in
	    (ns0 = ns1) andalso (cc1 = prefix)
	end)
      | _ => raise Match)

fun collect_connects_in_equation kp (q0, acc0) = (
    let
	val subj = (subject_of_class kp)
    in
	case q0 of
	    Eq_Eq _ => (q0, acc0)
	  | Eq_Connect ((x, y), aa, ww) => (
	    let
		val cx = (reference_is_subcomponent subj x)
		val cy = (reference_is_subcomponent subj y)
	    in
		(q0, ((x, cx, y, cy) :: acc0))
	    end)
	  | Eq_If _ => (q0, acc0)
	  | Eq_When _ => (q0, acc0)
	  | Eq_App _ => (q0, acc0)
	  | Eq_For _ => (q0, acc0)
    end)

fun collect_connects_in_instance (k0, acc0) = (
    if (class_is_alias k0) then
	acc0
    else if (class_is_enumerator_definition k0) then
	acc0
    else if (class_is_package k0) then
	acc0
    else
	let
	    val _ = if (not (class_is_primitive k0)) then () else raise Match

	    val subj = (subject_of_class k0)
	    val walker = (collect_connects_in_equation k0)
	    val ctx = {walker = Q_Walker walker}
	    val (k1, acc1) = (walk_in_class ctx (k0, acc0))
	in
	    acc1
	end)

fun collect_connects () = (
    (traverse_tree collect_connects_in_instance (instance_tree, [])))

(* ================================================================ *)

fun xcollect () = (collect_connects ())

end
