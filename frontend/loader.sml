(* loader.sml -*-Coding: us-ascii-unix;-*- *)
(* Copyright (C) 2018-2021 RIKEN R-CCS *)

(* A PARSER CALLER. *)

structure loader :
sig
    type id_t
    type class_tag_t
    type subject_t
    type definition_body_t
    type class_definition_t
    type cook_step_t

    val load_class_by_name : class_tag_t -> definition_body_t option
    val load_file : string -> definition_body_t list
    val lookup_class_in_package_root :
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

fun trace n (s : string) = if (n <= 3) then (print (s ^"\n")) else ()

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

(* Stores class definitions in the loaded_classes table.  It takes the
   result of parsing. *)

fun record_classes ((enclosing, dd) : class_definition_list_t) = (
    let
	fun record pkg1 d = (
	    let
		val Defclass ((id, pkg0), k0) = d
		val _ = if (pkg0 = bad_tag) then () else raise Match
	    in
		(record_class_body (id, pkg1) k0)
	    end)

	val pkg = (make_name_qualified enclosing)
    in
	(map (record pkg) dd)
    end)

(* Stores a class definition in the loaded_classes table.  It sets an
   enclosing class name to each class to identify the qualified name.
   It ejects definition bodies inside a class and stores them as
   separate entries.  An ejected body is replaced by a displaced-tag.
   An ejected body of an extends-redeclaration is given by a base
   class name.  Note that some additional elements may be added later
   from the directory entries under the package name. *)

and record_class_body (id, pkg) k0 = (
    let
	fun name_of_extends_redeclaration (x, m) = (
	    case x of
		Def_Named n => (
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
		    val Defclass ((id, pkg_), k0) = d0
		    val _ = if (pkg_ = bad_tag) then () else raise Match
		    val k1 = (record_class_body (id, pkg) k0)
		    val d1 = Defclass ((id, pkg), k1)
		in
		    Element_Class (z, r, d1, h)
		end)
	      | Element_State _ => e
	      | Redefine_Class (z, r, d0, h) => (
		let
		    val Defclass ((id, pkg_), k0) = d0
		    val _ = if (pkg_ = bad_tag) then () else raise Match
		    val k1 = (record_class_body (id, pkg) k0)
		    val d1 = Defclass ((id, pkg), k1)
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
			val x1 = (record_class_body (id, pkg) x0)
		    in
			Def_Extending (false, bx, x1)
		    end)
		  | _ => raise Match
	    end)
    in
	case k0 of
	    Def_Body (mk, cs, (j, n, c_, x), cc, ee0, aa, ww) => (
	    let
		val _ = if (c_ = bad_tag) then () else raise Match
		val _ = if (j = bad_subject) then () else raise Match
		val _ = if (n = bad_subject) then () else raise Match
		val _ = if (x = bad_subject) then () else raise Match
		val tag = (qualify_name (id, pkg))
		val ee1 = (map (record_e tag) ee0)
		val k1 = Def_Body (mk, cs, (j, n, tag, x), cc, ee1, aa, ww)
		val d1 = Defclass ((id, pkg), k1)
		val d2 = (store_to_loaded_classes false d1)
	    in
		Def_Displaced (tag, bad_subject)
	    end)
	  | Def_Der (c, cs, n, vv, a, w) => (
	    let
		val tag = (qualify_name (id, pkg))
		val k1 = Def_Der (tag, cs, n, vv, a, w)
	    in
		k1
	    end)
	  | Def_Primitive _ => raise Match
	  | Def_Outer_Alias _ => raise Match
	  | Def_Argument _ => raise Match
	  | Def_Named _ => k0
	  | Def_Scoped _ => raise Match
	  | Def_Refine (_, NONE, _, _, _, _, _, _) => k0
	  | Def_Refine (_, SOME _, _, _, _, _, _, _) => raise Match
	  | Def_Extending (true, bx, kx) => raise Match
	  | Def_Extending (false, bx, kx) => (
	    let
		val k1 = (record_extends_redeclaration pkg (false, bx, kx))
	    in
		k1
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
	val _ = trace 5 (";; load_class_in_file ("^
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
		  | SOME d => (
		    let
			val Defclass ((v, g), k) = d
		    in
			SOME k
		    end)
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
	    val _ = trace 3 (";; - [load] Load ("^ msg ^")")
	    val _ = (record_classes (lexer.parse_file f))
	in
	    ()
	end
    else
	let
	    val qs = quote_string
	    val f = (path ^ "/package.mo")
	    val msg = ((qs (tag_to_string qn)) ^" in "^ (qs f))
	    val _ = trace 3 (";; - [load] Load (" ^ msg ^ ")")
	    val _ = (record_classes (lexer.parse_file f))
	    val pkg = qn
	    val _ = (insert_package_directory_entries pkg path)
	in
	    ()
	end)

(* Adds the classes that are defined in separate files into the
   package definition (e.g., files are either "A" or "A.mo" in the
   package directory).  Note that it skips an entry if there is an
   existing entry with the same name, in case that a class may be
   loaded early explicitly. *)

and insert_package_directory_entries (pkg : class_tag_t) (path : string) = (
    let
	fun test_body k = (
	    case k of
		Def_Body _ => true
	      | Def_Der _ => false
	      | Def_Primitive _ => raise Match
	      | Def_Outer_Alias _ => raise Match
	      | Def_Argument _ => raise Match
	      | Def_Named _ => false
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
		Def_Displaced (tag, bad_subject)
	    end)

	fun make_element_class k = (
	    let
		val tag = (tag_of_displaced k)
		val (v, g) = (tag_prefix tag)
		val d = Defclass ((v, g), k)
	    in
		Element_Class (Public, no_element_prefixes, d, NONE)
	    end)

	fun test_not_member k = (
	    let
		val s = (tag_to_string (tag_of_body k))
	    in
		case (HashTable.find loaded_classes s) of
		    NONE => true
                  | SOME _ => (
                    let
			val _ = (warn_skip_file_in_package_directory k)
                    in
			false
                    end)
	    end)

	(* This test_non_member is redundant. *)

	fun test_non_member existings k = (
	    let
		val tag = (tag_of_body k)
	    in
		if (not (List.exists (fn x => (x = tag)) existings)) then
		    true
		else
		    let
			val _ = (warn_skip_file_in_package_directory k)
		    in
			false
		    end
	    end)

	fun drop_duplicate kp kk0 = (
	    let
		val existings = (gather_in_body_elements member_class kp)
		val kk1 = (List.filter test_not_member kk0)
		val kk2 = (List.filter (test_non_member existings) kk1)
	    in
		kk2
	    end)

	fun store_in_file_marker k0 = (
	    let
		val tag = (tag_of_displaced k0)
		val (v, g) = (tag_prefix tag)
		val dx = Defclass ((v, g), Def_In_File)
		val s = (tag_to_string tag)
		val _ = ignore (HashTable.insert loaded_classes (s, dx))
	    in
		()
	    end)

	fun merge_and_store k0 classes = (
	    let
		val tag = (tag_of_body k0)
		val (v, g) = (tag_prefix tag)
		val ee0 = (body_elements k0)
		val ee1 = (ee0 @ (map make_element_class classes))
		val k1 = (replace_body_elements k0 ee1)
		val d1 = Defclass ((v, g), k1)
		val _ = (store_to_loaded_classes true d1)
		val _ = (app store_in_file_marker classes)
	    in
		()
	    end)

	val _ = trace 5 (";; - Reading a package directory ("^
			 path ^")...")

	val entries = (list_directory_entries path)
	val s = (tag_to_string pkg)
	val kp =
	      case (HashTable.find loaded_classes s) of
		  NONE => (raise (error_class_loaded_but_missing s))
		| SOME dx => (
		  let
		      val Defclass ((v, g), kx) = dx
		  in
		      kx
		  end)
	val classes0 = (map (make_placeholder pkg) entries)
	val classes2 = (drop_duplicate kp classes0)

	val _ = trace 5 (";; AHO pkg entries={"^
			 ((String.concatWith " ")
			      (map name_of_displaced classes2)) ^"}")

	val _ = if (null classes2) then
		    ()
		else if (not (test_body kp)) then
		    ignore (warn_skip_directory_entries kp)
		else
		    ignore (merge_and_store kp classes2)

	val _ = trace 5 (";; - Reading a package directory ("^
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

fun load_class_by_name (tag : class_tag_t) : definition_body_t option = (
    let
	val s = (tag_to_string tag)
    in
	case (HashTable.find loaded_classes s) of
	    SOME d0 => (
	    if (not (class_is_in_file d0)) then
		let
		    val Defclass ((v, g), k0) = d0
		in
		    SOME k0
		end
	    else
		case (load_class_in_file tag) of
		    SOME k1 => SOME k1
		  | NONE => (raise (error_file_for_class_not_found tag)))
	  | NONE => (
	    if (class_is_at_top_level tag) then
		case (load_class_in_file tag) of
		    SOME k2 => SOME k2
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
      | Def_Outer_Alias _ => raise Match
      | Def_Argument _ => raise Match
      | Def_Named _ => k
      | Def_Scoped _ => raise Match
      | Def_Refine _ => k
      | Def_Extending _ => raise Match
      | Def_Replaced _ => k
      | Def_Displaced (tag, _) => (
	case (load_class_by_name tag) of
	    SOME kx => kx
	  | NONE => raise Match)
      | Def_In_File => raise Match
      | Def_Mock_Array _ => raise Match)

fun fetch_or_load_class_in_root (tag : class_tag_t) : definition_body_t option = (
    case (fetch_from_loaded_classes tag) of
	SOME d0 => (
	let
	    val Defclass ((v, g), k0) = d0
	    val k1 = (load_displaced_body k0)
	in
	    SOME k1
	end)
      | NONE => (
	case (load_class_by_name tag) of
	    SOME k => SOME k
	  | NONE => NONE))

fun lookup_class_in_package_root (Id v) = (
    let
	val _ = trace 5 (";; - lookup_class_in_package_root ("^ v ^")")

	val tag = (Ctag [v])
    in
	case (fetch_or_load_class_in_root tag) of
	    NONE => raise (error_name_not_found (Id v) the_package_root)
	  | SOME k => (
	    let
		val subj = (tag_to_subject tag)
	    in
		SOME (subj, k)
	    end)
    end)

fun fetch_loaded_class (ci : class_tag_t) : definition_body_t = (
    case (fetch_from_loaded_classes ci) of
	SOME d => (
	let
	    val Defclass ((v_, g_), k) = d
	in
	    (load_displaced_body k)
	end)
      | NONE => raise error_never_happen)

(* Fetches an enclosing class.  It respects the lexical enclosing
   relation. *)

fun fetch_enclosing_class (kp : definition_body_t) = (
    let
	val _ = trace 5 (";; fetch_enclosing_class")

	val _ = if (class_is_body kp) then () else raise Match
    in
	if (class_is_encapsulated kp) then
	    the_package_root
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
      | Def_Outer_Alias _ => raise Match
      | Def_Argument _ => raise Match
      | Def_Named _ => k
      | Def_Scoped _ => k
      | Def_Refine _ => k
      | Def_Extending _ => k
      | Def_Replaced _ => k
      | Def_Displaced (tag, enclosing) => (
	let
	    val _ = if (enclosing <> bad_subject) then () else raise Match
	    val k0 = (fetch_loaded_class tag)
	    val k1 = (assign_enclosing k0 enclosing)
	in
	    k1
	end)
      | Def_In_File => raise Match
      | Def_Mock_Array _ => raise Match)

fun load_file (filename : string) = (
    let
	val msg = (quote_string filename)
	val _ = trace 3 (";; - [load] Load (" ^ msg ^ ")")
	val kk = (record_classes (lexer.parse_file filename))
    in
	kk
    end)

end
