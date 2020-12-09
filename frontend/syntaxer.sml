(* syntaxer.sml -*-Coding: us-ascii-unix;-*- *)
(* Copyright (C) 2018-2020 RIKEN R-CCS *)

(* Simple transformations. *)

structure syntaxer :
sig
end = struct

open ast plain
open small1

fun tr_conv (s : string) = if true then (print (s ^"\n")) else ()
fun tr_conv_vvv (s : string) = if false then (print (s ^"\n")) else ()

(* Removes record constructors taking class instances (casting). *)

end
