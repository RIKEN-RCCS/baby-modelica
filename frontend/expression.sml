(* expression.sml -*-Coding: us-ascii-unix;-*- *)
(* Copyright (C) 2018-2020 RIKEN R-CCS *)

(* EXPRESSION HANDLING. *)

structure expression
: sig

end = struct

open ast plain
open small1

fun tr_expr (s : string) = if true then (print (s ^"\n")) else ()
fun tr_expr_vvv (s : string) = if false then (print (s ^"\n")) else ()

val instance_tree = classtree.instance_tree
val traverse_tree = classtree.traverse_tree

val walk_in_class = walker.walk_in_class
val Q_Walker = walker.Q_Walker

end
