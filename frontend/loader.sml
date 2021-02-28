(* loader.sml -*-Coding: us-ascii-unix;-*- *)
(* Copyright (C) 2018-2021 RIKEN R-CCS *)

(* PARSER CALLER. *)

structure loader :
sig
    type id_t
    type class_tag_t
    type subject_t
    type definition_body_t
    type class_definition_t
    type cook_step_t

    val load_class_by_name : class_tag_t -> class_definition_t option
    val load_file : string -> class_definition_t list
    val lookup_class_in_root :
	id_t -> (subject_t * definition_body_t) option
    val fetch_enclosing_class : definition_body_t -> definition_body_t
    val fetch_displaced_class :
	cook_step_t -> definition_body_t -> definition_body_t
end = struct

open plain
open settings
open ast
open small0

val loaded_classes = classtree.loaded_classes
val fetch_from_loaded_classes = classtree.fetch_from_loaded_classes
val store_to_loaded_classes = classtree.store_to_loaded_classes
val fetch_base_class = classtree.fetch_base_class

fun tr_load (s : string) = if true then (print (s ^"\n")) else ()
fun tr_load_vvv (s : string) = if false then (print (s ^"\n")) else ()

(* ================================================================ *)

(* Lists possible class names in a package directory.  Classes are
   files with a ".mo" extension or directories containing a file
   "package.mo". *)

fun list_directory_entries (path : string) : string list = (
    let
	val r = [OS.FileSys.A_READ]
	val dir = (OS.FileSys.openDir path)
	fun collect sum = (
	    case (OS.FileSys.readDir dir) of
		NONE => sum
	      | SOME s => (
		let
		    val n = String.size s
		    val u = if (n > 3) then
				(String.substring (s, 0, (n - 3)))
			    else
				""
		    val f = path ^ "/" ^ s
		    val p = f ^ "/" ^ "package.mo"
		in
		    if (s = "package.mo") then
			(collect sum)
		    else if ((n > 3) andalso
			     (String.isSuffix ".mo" s) andalso
			     (OS.FileSys.access (f, r))) then
			(collect (u :: sum))
		    else if ((OS.FileSys.access (f, r)) andalso
			     (OS.FileSys.isDir f) andalso
			     (OS.FileSys.access (p, r))) then
			(collect (s :: sum))
		    else
			(collect sum)
		end))
	val ls = collect []
	val _ = (OS.FileSys.closeDir dir)
    in
	ls
    end)

(* Tests if a file path (like "/A/B/C") is for a class definition, and
   returns either SOME(true,"/A/B/C"), SOME(false,"/A/B/C.mo"), or
   NONE.  The first case is for a directory containing
   "package.mo". *)

fun test_file_path_as_class (path : string) : (bool * string) option = (
    let
	val r = [OS.FileSys.A_READ]
	val p = path ^ "/package.mo"
	val f = path ^ ".mo"
    in
	if ((OS.FileSys.access (path, r)) andalso
	    (OS.FileSys.isDir path) andalso
	    (OS.FileSys.access (p, r))) then
	    (SOME (true, path))
	else if (OS.FileSys.access (f, r)) then
	    (SOME (false, f))
	else
	    NONE
    end)

(* Stores class definitions in the class-table.  It takes the result
   of parsing. *)

fun record_classes ((enclosing, dd) : class_definition_list_t) = (
    let
	val pkg = (make_name_qualified enclosing)
    in
	(map (record_class_body pkg) dd)
    end)

(* Stores a class definition in the loaded_classes table.  It sets an
   enclosing class name to each class to identify the qualified name.
   It ejects definition bodies inside a class and stores them as
   separate entries.  An ejected body is replaced by a displaced-tag.
   An ejected body of an extends-redeclaration is given by a base
   class name.  Note that some additional elements may be added later
   from the directory entries under the package name. *)

and record_class_body pkg (d0 as Defclass _) = (
    let
	fun name_of_extends_redeclaration (x, m) = (
	    case x of
		Def_Name n => (
		case n of
		    Name [] => raise Match
		  | Name [s] => Id s
		  | Name _ => raise Match)
	      | _ => raise Match)

	fun record_e pkg e = (
	    case e of
		Import_Clause _ => e
	      | Extends_Clause _ => e
	      | Element_Class (z, r, d0, h) => (
		let
		    val d1 = (record_class_body pkg d0)
		in
		    Element_Class (z, r, d1, h)
		end)
	      | Element_State _ => e
	      | Redefine_Class (z, r, d0, h) => (
		let
		    val d1 = (record_class_body pkg d0)
		in
		    Redefine_Class (z, r, d1, h)
		end)
	      | Redeclare_State _ => e
	      | Element_Enumerators _ => e
	      | Element_Equations _ => e
	      | Element_Algorithms _ => e
	      | Element_External _ => e
	      | Element_Annotation _ => e
	      | Element_Import _ => raise Match
	      | Element_Base _ => raise Match
	      | Base_List _ => raise Match
	      | Base_Classes _ => raise Match)

	fun record_extends_redeclaration pkg (g, bx, x0) = (
	    let
		val id = (name_of_extends_redeclaration bx)
	    in
		case x0 of
		    Def_Body _ => (
		    let
			(*
			val _ = if (j = bad_subject) then () else raise Match
			val tag = (qualify_name (id, pkg))
			val ee1 = (map (record_e tag) ee0)
			val k1 = Def_Body (mk, j, cs, (tag, n, x), ee1, aa, ww)
			*)
			val e0 = Defclass ((id, bad_tag), x0)
			val e1 = (record_class_body pkg e0)
			val Defclass ((_, _), x1) = e1
		    in
			Def_Extending (false, bx, x1)
		    end)
		  | _ => raise Match
	    end)

	val Defclass ((id, _), k0) = d0
    in
	case k0 of
	    Def_Body (mk, j, cs, (c_, n, x), cc, ee0, aa, ww) => (
	    let
		val _ = if (c_ = bad_tag) then () else raise Match
		val _ = if (j = bad_subject) then () else raise Match
		val _ = if (n = bad_subject) then () else raise Match
		val _ = if (x = bad_subject) then () else raise Match
		val tag = (qualify_name (id, pkg))
		val ee1 = (map (record_e tag) ee0)
		val k1 = Def_Body (mk, j, cs, (tag, n, x), cc, ee1, aa, ww)
		val d1 = Defclass ((id, pkg), k1)
		val d2 = (store_to_loaded_classes false d1)
	    in
		d2
	    end)
	  | Def_Der (c, cs, n, vv, a, w) => (
	    let
		val tag = (qualify_name (id, pkg))
		val k1 = Def_Der (tag, cs, n, vv, a, w)
		val d1 = Defclass ((id, pkg), k1)
	    in
		d1
	    end)
	  | Def_Primitive _ => raise Match
	  | Def_Name _ => (
	    Defclass ((id, pkg), k0))
	  | Def_Scoped _ => raise Match
	  | Def_Refine (kx, NONE, ts, q, (ss, mm), cc, aa, ww) => (
	    Defclass ((id, pkg), k0))
	  | Def_Refine (kx, SOME _, ts, q, (ss, mm), cc, aa, ww) => raise Match
	  | Def_Extending (true, bx, kx) => raise Match
	  | Def_Extending (false, bx, kx) => (
	    let
		val k1 = (record_extends_redeclaration pkg (false, bx, kx))
		val d1 = Defclass ((id, pkg), k1)
	    in
		d1
	    end)
	  | Def_Replaced _ => raise Match
	  | Def_Displaced _ => raise Match
	  | Def_In_File => raise Match
	  | Def_Mock_Array _ => raise Match
    end)

(* Loads a named class in libraries.  It loads either the ".mo" file
   or the "package.mo" file.  It returns NONE on an error.  The caller
   shall issue an error. *)

fun load_class_in_file (tag0 : class_tag_t) = (
    let
	val _ = tr_load_vvv (";; load_class_in_file ("^
			     (tag_to_string tag0) ^")")
    in
	case (check_library_paths tag0) of
	    NONE => NONE
	  | SOME (pkgmo, tag1, file) => (
	    let
		val _ = (load_file_or_directory pkgmo tag1 file)
	    in
		case (HashTable.find loaded_classes (tag_to_string tag1)) of
		    NONE => NONE
		  | SOME k => SOME k
	    end)
    end)

(* The first argument (pkgmo) is false when loading a class file
   ".mo", or true when loading a package file "package.mo". *)

and load_file_or_directory pkgmo (qn : class_tag_t) path = (
    if (pkgmo = false) then
	let
	    val qs = quote_string
	    val f = path
	    val msg = ((qs (tag_to_string qn)) ^" in "^ (qs f))
	    val _ = tr_load (";; - [load] Load ("^ msg ^")")
	    val _ = (record_classes (lexer.parse_file f))
	in
	    ()
	end
    else
	let
	    val qs = quote_string
	    val f = (path ^ "/package.mo")
	    val msg = ((qs (tag_to_string qn)) ^" in "^ (qs f))
	    val _ = tr_load (";; - [load] Load (" ^ msg ^ ")")
	    val _ = (record_classes (lexer.parse_file f))
	    val pkg = qn
	    val _ = (insert_package_directory_entries pkg path)
	in
	    ()
	end)

(* Adds the classes that are defined in separate files into the
   package definition (e.g., files are either "A" or "A.mo" in the
   package directory).  Note that it skips entries if there are
   existing entries with the same names, in case that the classes may
   be loaded early explicitly (possibly to change some
   definitions). *)

and insert_package_directory_entries (pkg : class_tag_t) (path : string) = (
    let
	(* test_body is definition_is_body but a bit more strict. *)
	fun test_body (Defclass ((v, g), k)) = (
	    case k of
		Def_Body _ => true
	      | Def_Der _ => false
	      | Def_Primitive _ => raise Match
	      | Def_Name _ => false
	      | Def_Scoped _ => raise Match
	      | Def_Refine _ => false
	      | Def_Extending _ => raise Match
	      | Def_Replaced _ => raise Match
	      | Def_Displaced _ => raise Match
	      | Def_In_File => raise Match
	      | Def_Mock_Array _ => raise Match)

	fun member_class e = (
	    case e of
		Import_Clause _ => []
	      | Extends_Clause _ => []
	      | Element_Class (_, _, d, _) => [(tag_of_definition d)]
	      | Element_State _ => []
	      | Redefine_Class _ => []
	      | Redeclare_State _ => []
	      | Element_Enumerators _ => raise Match
	      | Element_Equations _ => []
	      | Element_Algorithms _ => []
	      | Element_External _ => []
	      | Element_Annotation _ => []
	      | Element_Import _ => raise Match
	      | Element_Base _ => raise Match
	      | Base_List _ => raise Match
	      | Base_Classes _ => raise Match)

	fun make_placeholder pkg v = (
	    let
		val id = Id v
		val tag = (qualify_name (id, pkg))
	    in
		Defclass ((id, pkg), Def_Displaced (tag, bad_subject))
	    end)

	fun make_element_class c = (
	    Element_Class (Public, no_element_prefixes, c, NONE))

	fun test_not_existing d = (
	    let
		val s = (tag_to_string (tag_of_definition d))
	    in
		case (HashTable.find loaded_classes s) of
		    NONE => true
		  | SOME _ => (
		    let
			val _ = (warn_skip_defined d)
		    in
			false
		    end)
	    end)

	fun drop_already_loaded kp classes0 = (
	    (List.filter test_not_existing classes0))

	fun test_non_member cc d = (
	    let
		val tag = (tag_of_definition d)
	    in
		if (not (List.exists (fn x => (x = tag)) cc)) then
		    true
		else
		    let
			val _ = (warn_drop_duplicate_definitions d)
		    in
			false
		    end
	    end)

	fun drop_duplicate kp c1 = (
	    let
		val existings = (gather_in_elements member_class kp)
		val filtered = (List.filter (test_non_member existings) c1)
	    in
		filtered
	    end)

	fun change_displaced_to_filed (Defclass ((v, pkg), k)) = (
	    case k of
		Def_Body _ => raise Match
	      | Def_Der _ => raise Match
	      | Def_Primitive _ => raise Match
	      | Def_Name _ => raise Match
	      | Def_Scoped _ => raise Match
	      | Def_Refine _ => raise Match
	      | Def_Extending _ => raise Match
	      | Def_Replaced _ => raise Match
	      | Def_Displaced _ => Defclass ((v, pkg), Def_In_File)
	      | Def_In_File => raise Match
	      | Def_Mock_Array _ => raise Match)

	fun store_in_file_marker (d0 as Defclass ((v, pkg), b)) = (
	    let
		val d1 = (change_displaced_to_filed d0)
		val s = (tag_to_string (tag_of_definition d1))
		val _ = ignore (HashTable.insert loaded_classes (s, d1))
	    in
		()
	    end)

	fun merge_and_store k0 classes = (
	    let
		val ee0 = (class_elements k0)
		val ee1 = (ee0 @ (map make_element_class classes))
		val k1 = (replace_class_elements k0 ee1)
		val _ = (store_to_loaded_classes true k1)
		val _ = (app store_in_file_marker classes)
	    in
		()
	    end)

	val _ = tr_load_vvv (";; - Reading a package directory ("^
			     path ^")...")
	val entries = (list_directory_entries path)
	val s = (tag_to_string pkg)
	val d0 =
	      case (HashTable.find loaded_classes s) of
		  NONE => (raise (error_class_loaded_but_missing s))
		| SOME dx => dx
	val classes0 = (map (make_placeholder pkg) entries)
	val classes1 = (drop_already_loaded d0 classes0)
	val classes2 = (drop_duplicate d0 classes1)

	val _ = tr_load_vvv (";; AHO pkg entries={"^
			     ((String.concatWith " ")
				  (map name_of_definition classes2)) ^"}")

	val _ = if (null classes2) then
		    ()
		else if (not (test_body d0)) then
		    ignore (warn_skip_directory_entries d0)
		else
		    ignore (merge_and_store d0 classes2)

	val _ = tr_load_vvv (";; - Reading a package directory ("^
			     path ^")... done")
    in
	()
    end)

(* Tests if a file or a directory exists for the named class.  It
   returns a boolean, a class-tag, and a file path.  The boolean
   indicates the path is for "package.mo". *)

and check_library_paths (qn : class_tag_t) : (bool * class_tag_t * string) option = (
    let
	val (Name nn) = (tag_as_name qn)
	val path = Name (make_modelica_versioned_path nn)
    in
	case (list_find_some
		  (fn rootpath =>
		      (test_file_path_as_class
			   (make_file_path rootpath path)))
		  modelica_paths) of
	    SOME (b, s) => SOME (b, qn, s)
	  | NONE => NONE
    end)

(* ================================================================ *)

(* Loads a named class.  It is an error if the definition of the class
   is not found.  (It is certain that an enclosing class is already
   loaded, when it is called from looking up in a class scope).  Note
   that finding a displaced-tag in the table means the file is not
   loaded yet. *)

fun load_class_by_name (tag : class_tag_t) : class_definition_t option = (
    let
	val s = (tag_to_string tag)
    in
	case (HashTable.find loaded_classes s) of
	    SOME k1 => (
	    if (not (class_is_in_file k1)) then
		SOME k1
	    else
		case (load_class_in_file tag) of
		    SOME kx => SOME kx
		  | NONE => (raise (error_file_for_class_not_found tag)))
	  | NONE => (
	    if (class_is_at_top_level tag) then
		case (load_class_in_file tag) of
		    SOME kx => SOME kx
		  | NONE => raise (error_name_not_found_up_to_top_level tag)
	    else
		raise Match)
    end)

(* Loads a class whose loading is delayed (stored as a
   displaced-tag). *)

fun load_displaced_body (k : definition_body_t) = (
    case k of
	Def_Body _ => k
      | Def_Der _ => k
      | Def_Primitive _ => raise Match
      | Def_Name _ => k
      | Def_Scoped _ => raise Match
      | Def_Refine _ => k
      | Def_Extending _ => raise Match
      | Def_Replaced _ => k
      | Def_Displaced (tag, _) => (
	case (load_class_by_name tag) of
	    SOME kx => (definition_body kx)
	  | NONE => raise Match)
      | Def_In_File => raise Match
      | Def_Mock_Array _ => raise Match)

fun fetch_or_load_class_in_root (tag : class_tag_t) : class_definition_t option = (
    case (fetch_from_loaded_classes tag) of
	SOME d0 => (
	let
	    val Defclass ((v, g), k0) = d0
	    val k1 = (load_displaced_body k0)
	    val d1 = Defclass ((v, g), k1)
	in
	    SOME d1
	end)
      | NONE => (
	case (load_class_by_name tag) of
	    SOME k => SOME k
	  | NONE => NONE))

fun lookup_class_in_root (Id v) = (
    let
	val _ = tr_load_vvv (";; - lookup_class_in_root ("^ v ^")")
	val tag = (Ctag [v])
    in
	case (fetch_or_load_class_in_root tag) of
	    NONE => raise (error_name_not_found (Id v) the_root_class)
	  | SOME d => (
	    let
		val Defclass ((v_, g), k) = d
		val subj = (tag_to_subject tag)
	    in
		SOME (subj, k)
	    end)
    end)

fun fetch_loaded_class (ci : class_tag_t) : definition_body_t = (
    case (fetch_from_loaded_classes ci) of
	SOME k => (load_displaced_body (definition_body k))
      | NONE => raise error_never_happen)

(* Fetches an enclosing class.  It respects the lexical enclosing
   relation. *)

fun fetch_enclosing_class (kp : definition_body_t) = (
    let
	val _ = tr_load_vvv (";; fetch_enclosing_class")
	val _ = if (class_is_body kp) then () else raise Match
    in
	if (class_is_encapsulated kp) then
	    the_root_class
	else
	    let
		val supsubj = (enclosing_of_body kp)
		val tag = (tag_of_body kp)
		val (_, pkg) = (tag_prefix tag)
		val ex = error_cycle_in_lookup_enclosing
		val kx = (fetch_base_class ex (supsubj, pkg))
	    in
		kx
	    end
    end)

(* Fetches a class for a displaced-tag from package_classes or
   loaded_classes.  It takes a wanted state of a class as
   wantedstep=E0 or E3, and returns a class in the step or lower.
   Thus, it fetches a class from loaded_classes when wantedstep=E0, or
   from package_classes or loaded_classes when wantedstep=E3. *)

fun fetch_displaced_class wantedstep (k : definition_body_t) = (
    case k of
	Def_Body _ => k
      | Def_Der _ => k
      | Def_Primitive _ => raise Match
      | Def_Name _ => k
      | Def_Scoped _ => k
      | Def_Refine _ => k
      | Def_Extending _ => k
      | Def_Replaced _ => k
      | Def_Displaced (tag, enc) => (
	let
	    (*AHO*)
	    val _ = if (enc <> bad_subject) then () else raise Match
	    val k0 = (fetch_loaded_class tag)
	    val (v, pkg) = (tag_prefix tag)
	    val enclosing = if (enc <> bad_subject) then
				enc
			    else
				(tag_to_subject pkg)
	    val k1 = (assign_enclosing k0 enclosing)
	in
	    k1
	end)
      | Def_In_File => raise Match
      | Def_Mock_Array _ => raise Match)

fun load_file (filename : string) = (
    let
	val msg = (quote_string filename)
	val _ = tr_load (";; - [load] Load (" ^ msg ^ ")")
	val dd = (record_classes (lexer.parse_file filename))
    in
	dd
    end)

end
