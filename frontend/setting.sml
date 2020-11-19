(* settings.sml -*-Coding: us-ascii-unix;-*- *)
(* Copyright (C) 2018-2021 RIKEN R-CCS *)

(* LIBRARY PATHS. *)

structure settings  :
sig
    val modelica_paths : string list
    val modelica_msl : string
    val make_modelica_versioned_path : string list -> string list
end = struct

fun get_paths () = (
    let
	val env = (OS.Process.getEnv "MODELICAPATH")
    in
	case env of
	    NONE => raise (Fail "Set MODELICAPATH\n")
	  | SOME s => (
	    (String.fields (fn c => (c = #":")) s))
    end)

fun get_msl () = (
    let
	val env = (OS.Process.getEnv "MODELICAMSL")
    in
	case env of
	    NONE => "3.2.3"
	  | SOME s => s
    end)

val modelica_paths = (get_paths ())
val modelica_msl = (get_msl ())

(* Maps a qualified name (the empty string is a prefix for the unnamed
   root) to a versioned file path of the MSL. *)

fun make_modelica_versioned_path qn = (
    case qn of
	[] => raise Match
      | ("" :: name) => (
	case name of
	    [] => raise Match
	  | ("Modelica" :: nn) => (
	    (("Modelica" ^" "^ modelica_msl) :: nn))
	  | ("ModelicaServices" :: nn) => (
	    (("ModelicaServices" ^" "^ modelica_msl) :: nn))
	  | _ => name)
      | _ => raise Match)

end
