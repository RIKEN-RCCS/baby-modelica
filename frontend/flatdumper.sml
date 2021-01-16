(* flatdumper.sml -*-Coding: us-ascii-unix;-*- *)
(* Copyright (C) 2018-2021 RIKEN R-CCS *)

(* DUMPER OF A FLAT MODEL. *)

(* The dumper does not dump empty arrays (dimension-size=0), so it is
   needed to remove the references to them. *)

structure flatdumper
: sig
    val xdump : unit -> unit
end = struct

open plain
open ast
open small0

val package_root_node = classtree.package_root_node
val model_root_node = classtree.model_root_node
val subject_to_instance_tree_path = classtree.subject_to_instance_tree_path
val extract_base_classes = classtree.extract_base_classes
val traverse_tree = classtree.traverse_tree

val simple_type_attribute = simpletype.simple_type_attribute
val type_of_simple_type = simpletype.type_of_simple_type
val take_enumarator_element = simpletype.take_enumarator_element

fun tr_flat (s : string) = if true then (print (s ^"\n")) else ()
fun tr_flat_vvv (s : string) = if false then (print (s ^"\n")) else ()

(* ================================================================ *)

fun variability_to_string variability = (
    case variability of
	Constant => "constant"
      | Parameter => "parameter"
      | Discrete => "discrete"
      | Continuous => "")

(*val expression_to_string = dumper.expression_to_string*)

fun expression_to_string w = (
    let
	fun ref_to_string rr = (
	    ((String.concatWith ".")
		 (map (fn (Id v, []) => v | (Id v, e) => (v ^ "[]")) rr)))

	fun for_index_to_string (Id v, x) = (
	    ("("^ v ^" : "^ (expression_to_string x) ^")"))

	fun predefined_operator_to_string p = (
	    case p of
		Opr_id => "+"
	      | Opr_neg => "-"
	      | Opr_id_ew => ".+"
	      | Opr_neg_ew => ".-"
	      | Opr_add => "+"
	      | Opr_sub => "-"
	      | Opr_add_ew => ".+"
	      | Opr_sub_ew => ".-"
	      | Opr_mul => "*"
	      | Opr_div => "/"
	      | Opr_mul_ew => ".*"
	      | Opr_div_ew => "./"
	      | Opr_expt => "exp"
	      | Opr_expt_ew => ".exp"
	      | Opr_not => "not"
	      | Opr_and => "and"
	      | Opr_ior => "ior"
	      | Opr_concat => "concat"
	      | Opr_eq => "="
	      | Opr_ne => "<>"
	      | Opr_gt => ">"
	      | Opr_lt => "<"
	      | Opr_ge => ">="
	      | Opr_le => "<=")
    in
	case w of
	    NIL => raise Match
	  | Colon => ":"
	  | Otherwise => "Otherwise"
	  | Scoped (x1, scope) => raise Match
	  | Vref (_, []) => raise Match
	  | Vref (NONE, rr) => raise Match
	  | Vref (SOME ns, rr0) => (
	    if (ns = PKG) then
		(ref_to_string ((Id "", []) :: rr0))
	    else
		(ref_to_string rr0))
	  | Opr p => (predefined_operator_to_string p)
	  | App (f, aa) => (
	    let
		val s = ((String.concatWith " ")
			     (map expression_to_string (f :: aa)))
	    in
		("(App "^ s ^")")
	    end)
	  | ITE cc => (
	    let
		val s = ((String.concatWith " ")
			     (map (fn (x, y) =>
				      ("("^ (expression_to_string x)
				       ^" => "^
				       (expression_to_string y) ^")")) cc))
	    in
		("(ITE "^ s ^")")
	    end)
	  | Der aa => (
	    let
		val s = ((String.concatWith " ")
			     (map expression_to_string aa))
	    in
		("(Der "^ s ^")")
	    end)
	  | Pure aa => (
	    let
		val s = ((String.concatWith " ")
			     (map expression_to_string aa))
	    in
		("(Pure "^ s ^")")
	    end)
	  | Closure (n, aa) => (
	    let
		val s = ((String.concatWith " ")
			     ((name_to_string n)
			      :: (map expression_to_string aa)))
	    in
		("(Closure "^ s ^")")
	    end)
	  | L_Number (_, s) => s
	  | L_Bool x => if x then "true" else "false"
	  | L_Enum (tag, Id v) => (
	    ("(ENUM "^ (tag_to_string tag) ^"."^ v ^")"))
	  | L_String s => ("\""^ s ^"\"")
	  | Array_Triple (x0, y0, NONE) => (
	    let
		val sx = (expression_to_string x0)
		val sy = (expression_to_string y0)
	    in
		("(Triple "^ sx ^" : "^ sy ^")")
	    end)
	  | Array_Triple (x0, y0, SOME z0) => (
	    let
		val sx = (expression_to_string x0)
		val sy = (expression_to_string y0)
		val sz = (expression_to_string z0)
	    in
		("(Triple "^ sx ^" : "^ sy ^" : "^ sz ^")")
	    end)
	  | Array_Constructor aa => (
	    let
		val s = ((String.concatWith " ")
			     (map expression_to_string aa))
	    in
		("(Array_Constructor "^ s ^")")
	    end)
	  | Array_Comprehension (x, uu) => (
	    let
		val s = ((String.concatWith " ")
			     ((expression_to_string x)
			      :: (map for_index_to_string uu)))
	    in
		("(Comprehension"^ s ^")")
	    end)
	  | Array_Concatenation aa => (
	    let
		val s = ((String.concatWith " ; ")
			     (map ((String.concatWith " , ")
				   o (map expression_to_string))
				  aa))
	    in
		("(Array_Concatenation "^ s ^")")
	    end)
	  | Tuple aa => (
	    let
		val s = ((String.concatWith " ")
			     (map expression_to_string aa))
	    in
		("(Tuple "^ s ^")")
	    end)
	  | Reduction_Argument (x, uu) => (
	    let
		val s = ((String.concatWith " ")
			     ((expression_to_string x)
			      :: (map for_index_to_string uu)))
	    in
		("(Reduction_Argument"^ s ^")")
	    end)
	  | Named_Argument (n, x) => (
	    let
		val s0 = (name_to_string n)
		val s1 = (expression_to_string x)
	    in
		(""^ s0 ^"="^ s1 ^"")
	    end)
	  | Pseudo_Split (x, ss) => (
	    let
		val s0 = (expression_to_string x)
		val s1 = ((String.concatWith ",")
			      (map Int.toString ss))
	    in
		("(Pseudo_Split "^ s0 ^"["^ s1 ^"])")
	    end)
	  | Component_Ref (x, id) => (
	    let
		val s0 = (expression_to_string x)
		val s1 = (id_to_string id)
	    in
		("(Component_Ref "^ s0 ^", "^ s1 ^")")
	    end)
	  (*
	  | Instance (d, kk, _) => (
	    let
		val class_name = (subject_to_string o subject_of_class)
		val ds = ((String.concatWith ",")
			      (map Int.toString d))
	    in
		if (null d) then
		    case kk of
			[k] => (
			("(Instance "^ (class_name k) ^")"))
		      | _ => raise Match
		else
		    case kk of
			[] => ("(Instance ["^ ds ^"])")
		      | (k :: _) => (
			("(Instance ["^ ds ^"] "^ (class_name k) ^")"))
	    end)
	  *)
	  | Instances ([], [subj]) => (
	    ("(Instance "^ (subject_to_string subj) ^")"))
	  | Instances ([], _) => raise Match
	  | Instances (dim, subjs) => (
	    let
		val _ = if (not (null dim)) then () else raise Match
		val ds = ((String.concatWith ",")
			      (map Int.toString dim))
	    in
		case subjs of
		    [] => ("(Instance ["^ ds ^"])")
		  | (subj :: _) => (
		    ("(Instance ["^ ds ^"] "^ (subject_to_string subj) ^")"))
	    end)
	  | Iref v => (id_to_string v)
	  | Cref (e, b) => (expression_to_string e)
	  | Array_fill (e, n) => (
	    let
		val se = (expression_to_string e)
		val sn = (expression_to_string n)
	    in
		("(fill ("^ se ^","^ sn ^")")
	    end)
	  | Array_diagonal v => (
	    let
		val sv = (expression_to_string v)
	    in
		("(diagonal ("^ sv ^")")
	    end)
    end)

(* ================================================================ *)

(* Packages are processed to step=E3, but some packages which are
   named but unused remain at step=E0 (.Modelica.Icons.Package). *)

fun collect_variables root = (
    let
	val the_time = Subj (VAR, [(Id "time", [])])
	val the_end = Subj (VAR, [(Id "end", [])])

	fun collect (kp, acc) = (
	    if (step_is_less E3 kp) then
		acc
	    else
		let
		    val subj = (subject_of_class kp)
		in
		    if (class_is_outer_alias kp) then
			(* THIS WILL BE REMOVED. *)
			acc
		    else if (class_is_enumerator_definition kp) then
			acc
		    else if (class_is_package kp) then
			acc
		    else if (subj = the_time orelse subj = the_end) then
			acc
		    else if (class_is_simple_type kp) then
			let
			    val _ = if (step_is_at_least E5 kp) then ()
				    else raise Match
			in
			    acc @ [kp]
			end
		    else
			acc
		end)

	val node = if (root = PKG) then package_root_node else model_root_node
	val vars = (traverse_tree collect (node, []))
    in
	vars
    end)

fun collect_enumerations root = (
    let
	fun collect (kp, acc) = (
	    if (class_is_outer_alias kp) then
		(* THIS WILL BE REMOVED. *)
		acc
	    else if (class_is_enumerator_definition kp) then
		acc
	    else if (step_is_less E3 kp) then
		acc
	    else if (class_is_enumeration_definition kp) then
		let
		    val _ = if ((cook_step kp) = E3) then () else raise Match
		in
		    acc @ [kp]
		end
	    else
		acc)

	val node = if (root = PKG) then package_root_node else model_root_node
	val vars = (traverse_tree collect (node, []))
    in
	vars
    end)

fun collect_records root = (
    let
	fun class_is_record_definition k = (
	    (kind_is_record k) andalso (class_is_package k))

	fun collect (kp, acc) = (
	    if (class_is_outer_alias kp) then
		(* THIS WILL BE REMOVED. *)
		acc
	    else if (class_is_enumerator_definition kp) then
		acc
	    else if (step_is_less E3 kp) then
		acc
	    else if (class_is_record_definition kp) then
		let
		    val _ = if ((cook_step kp) = E3) then () else raise Match
		in
		    acc @ [kp]
		end
	    else
		acc)

	val node = if (root = PKG) then package_root_node else model_root_node
	val vars = (traverse_tree collect (node, []))
    in
	vars
    end)

fun collect_functions root = (
    let
	fun partial k = (
	    case k of
		Def_Body (mk, j, (t, {Partial, ...}, q), nm, ee, aa, ww) => (
		Partial)
	      | _ => raise Match)

	fun collect (kp, acc) = (
	    if (class_is_outer_alias kp) then
		(* THIS WILL BE REMOVED. *)
		acc
	    else if (class_is_enumerator_definition kp) then
		acc
	    else if (step_is_less E3 kp) then
		acc
	    else if ((kind_is_function kp) andalso (not (partial kp))) then
		let
		    val _ = if (step_is_at_least E3 kp) then ()
			    else raise Match
		in
		    acc @ [kp]
		end
	    else
		acc)

	val node = if (root = PKG) then package_root_node else model_root_node
	val funs = (traverse_tree collect (node, []))
    in
	funs
    end)

fun collect_equations initial () = (
    let
	fun eqn0 (e, acc) = (
	    case e of
		Import_Clause _ => raise Match
	      | Extends_Clause _ => raise Match
	      | Element_Class _ => acc
	      | Element_State _ => acc
	      | Redefine_Class _ => acc
	      | Redeclare_State _ => acc
	      | Element_Enumerators _ => acc
	      | Element_Equations (b, _) => (
		if (initial = b) then acc @ [e] else acc)
	      | Element_Algorithms _ => acc
	      | Element_External _ => acc
	      | Element_Annotation a => acc
	      | Element_Import _ => acc
	      | Element_Base _ => acc
	      | Base_List _ => acc
	      | Base_Classes bb => acc)

	fun eqn1 ((tag, kx), acc) = (
	    let
		val qq = (foldl eqn0 [] (body_elements kx))
	    in
		if (not (null qq)) then
		    acc @ [(tag, qq)]
		else
		    acc
	    end)

	(* Include equations in simple-types. *)

	fun collect (kp, acc) = (
	    if (class_is_outer_alias kp) then
		(* THIS WILL BE REMOVED. *)
		acc
	    else
		let
		    val (bases, _) = (extract_base_classes false kp)
		    val subj = (subject_of_class kp)
		    val tag = (tag_of_body kp)
		    val classes = [(tag, kp)] @ bases
		    val ee = (foldl eqn1 [] classes)
		in
		    if (not (null ee)) then
			acc @ [(subj, ee)]
		    else
			acc
		end)

	val node = model_root_node
	val eqns = (traverse_tree collect (node, []))
    in
	eqns
    end)

(* ================================================================ *)

val predefined_type_names = [
    "Real",
    "Integer",
    "Boolean",
    "String",
    "StateSelect",
    "AssertionLevel",
    "Clock",
    "ExternalObject",
    "Connections"]

fun declaraton_of_real k = (
    let
	fun quote x = (expression_to_string x)

	fun opt_slot k v preset = (
	    if (v = preset orelse v = NIL) then ""
	    else (k ^"="^ (quote v)))

	val empty_string = L_String ""
	val real_zero = L_Number (Z, "0")
	val truth_value = L_Bool true
	val false_value = L_Bool false
	val stateselect_default
	    = Vref (SOME PKG,
		    [(Id "StateSelect", []), (Id "default", [])])
	val inf
	    = Vref (SOME PKG,
		    [(Id "Modelica", []),
		     (Id "Constants", []), (Id "inf", [])])
	val min_default = App (Opr Opr_neg, [inf])
	val max_default = App (Opr Opr_id, [inf])
    in
	case k of
	    Def_Body ((u, f, b), subj, (t, p, q), (c, n, x), ee, aa, ww) => (
	    let
		val (analogical, variability, modality) = q

		val value_ = (simple_type_attribute k (Id "value"))
		val quantity_ = (simple_type_attribute k (Id "quantity"))
		val unit_ = (simple_type_attribute k (Id "unit"))
		val displayUnit_ = (simple_type_attribute k (Id "displayUnit"))
		val min_ = (simple_type_attribute k (Id "min"))
		val max_ = (simple_type_attribute k (Id "max"))
		val start_ = (simple_type_attribute k (Id "start"))
		val fixed_ = (simple_type_attribute k (Id "fixed"))
		val nominal_ = (simple_type_attribute k (Id "nominal"))
		val unbounded_ = (simple_type_attribute k (Id "unbounded"))
		val stateSelect_ = (simple_type_attribute k (Id "stateSelect"))

		val fixed_default =
		      if ((variability_order variability)
			  <= (variability_order Parameter)) then
			  truth_value
		      else
			  false_value

		val vs = (variability_to_string variability)
		val ts = "Real"
		val ms = ("("^
			  (String.concatWith
			       ", "
			       (List.filter
				    (fn x => (x <> ""))
				    [(opt_slot "quantity" quantity_
					       empty_string),
				     (opt_slot "unit" unit_ empty_string),
				     (opt_slot "displayUnit" displayUnit_
					       empty_string),
				     (opt_slot "min" min_ min_default),
				     (opt_slot "max" max_ max_default),
				     (opt_slot "start" start_ real_zero),
				     (opt_slot "nominal" nominal_ NIL),
				     (opt_slot "fixed" fixed_ fixed_default),
				     (opt_slot "unbounded" unbounded_
					       false_value),
				     (opt_slot "stateSelect" stateSelect_
					       stateselect_default)]))
			  ^")")
		val ns = (subject_to_string subj)
		val xs = if (value_ <> NIL) then
			     "= "^ (quote value_)
			 else
			     ""
		val ss = ((String.concatWith
			       " "
			       (List.filter (fn x => (x <> ""))
					    [vs, ts, ms, ns, xs]))
			  ^";")
	    in
		ss
	    end)
	  | Def_Der _ => ""
	  | Def_Primitive _ => raise Match
	  | Def_Name _ => raise Match
	  | Def_Scoped _ => raise Match
	  | Def_Refine _ => raise Match
	  | Def_Extending _ => raise Match
	  | Def_Replaced _ => raise Match
	  | Def_Displaced _ => raise Match
	  | Def_In_File => raise Match
	  | Def_Mock_Array _ => raise Match
    end)

fun dump_variable s k = (
    let
	val sx = case (type_of_simple_type k) of
		     P_Number R => (declaraton_of_real k)
		   | P_Number Z => ""
		   | P_Boolean => ""
		   | P_String => ""
		   | P_Enum tag =>  ""
	val ss = if (sx = "") then "" else (sx ^"\n")
	val _ = (TextIO.output (s, ss))
    in
	()
    end)

fun dump_enumeration s k = (
    let
	fun predefined tag = (
	    case tag of
		Ctag [n] => (List.exists (fn x => (x = n))
					 predefined_type_names)
	      | _ => false)
    in
	case k of
	    Def_Body (mk, j, (t, p, q), nm, ee, aa, ww) => (
	    let
		val tag = (tag_of_body k)
		val name = (subject_to_string (subject_of_class k))
		val vv = surely (take_enumarator_element k)
		val ss0 = ("type "^ name ^" = enumeration (")
		val ss1 = ((String.concatWith ", ")
			       (map (id_to_string o #1) vv))
		val ss2 = (");\n")
		val ss = ss0 ^ ss1 ^ ss2
	    in
		if (not (predefined tag)) then
		    (TextIO.output (s, ss))
		else
		    ()
	    end)
	  | _ => raise Match
    end)

fun dump_record s k = (
    let
	fun predefined tag = (
	    case tag of
		Ctag [n] => (List.exists (fn x => (x = n))
					 predefined_type_names)
	      | _ => false)
    in
	case k of
	    Def_Body (mk, j, (t, p, q), nm, ee, aa, ww) => (
	    let
		val tag = (tag_of_body k)
		val name = (subject_to_string (subject_of_class k))
		val ss0 = ("record "^ name ^"\n")
		val ss1 = "/* ... */\n"
		val ss2 = ("end "^ name ^";\n")
		val ss = ss0 ^ ss1 ^ ss2 ^ "\n"
	    in
		if (not (predefined tag)) then
		    (TextIO.output (s, ss))
		else
		    ()
	    end)
	  | _ => raise Match
    end)

fun dump_function s k = (
    let
	fun predefined tag = (
	    case tag of
		Ctag [n] => (List.exists (fn x => (x = n))
					 predefined_function_names)
	      | _ => false)
    in
	case k of
	    Def_Body (mk, j, (t, p, q), nm, ee, aa, ww) => (
	    let
		val tag = (tag_of_body k)
		val name = (subject_to_string (subject_of_class k))
		val dummy = ("/* function (predefined) "^ name ^" */\n")
		val ss = ("/* function "^ name ^" */\n")
	    in
		if ((predefined tag)) then
		    (TextIO.output (s, dummy))
		else
		    (TextIO.output (s, ss))
	    end)
	  | _ => raise Match
    end)

fun for_index_to_string i = (
    case i of
	(v, Colon) => (id_to_string v)
      | (v, e) => ((id_to_string v) ^" in "^ (expression_to_string e)))

fun dump_equation s q = (
    let
	fun dump_conditional key s ((e, qq), start) = (
	    case e of
		Otherwise => (
		if (not start) then
		    let
			(*val _ = if (not start) then () else raise Match*)
			val _ = (TextIO.output (s, "else\n"))
			val _ = (app (dump_equation s) qq)
		    in
			false
		    end
		else
		    let
			val _ = (app (dump_equation s) qq)
		    in
			false
		    end)
	      | _ => (
		let
		    val _ = if (start) then
				(TextIO.output (s, (key ^" ")))
			    else
				(TextIO.output (s, (("else"^ key) ^" ")))
		    val _ = (TextIO.output
				 (s, ("("^ (expression_to_string e) ^")")))
		    val _ = (TextIO.output (s, " then\n"))
		    val _ = (app (dump_equation s) qq)
		in
		    false
		end))
    in
	case q of
	    Eq_Eq ((e0, e1), aa, ww) => (
	    let
		val _ = (TextIO.output
			     (s, ("("^
				  (expression_to_string e0)
				  ^" = "^
				  (expression_to_string e1) ^")\n")))
	    in
		()
	    end)
	  | Eq_Connect ((Cref (e0, side0), Cref (e1, side1)), aa, ww) => (
	    let
		val _ = (TextIO.output
			     (s, ("/*connect ("^
				  (expression_to_string e0)
				  (*^(if side0 then "(+)" else "(-)")*)
				  ^", "^
				  (expression_to_string e1)
				  (*^(if side1 then "(+)" else "(-)")*)
				  ^")*/\n")))
	    in
		()
	    end)
	  | Eq_Connect ((e0, e1), aa, ww) =>
	    (*raise Match*)
	      (
		let
		    val _ = (TextIO.output
				 (s, ("/*connect ("^
				      (expression_to_string e0)
				      ^", "^
				      (expression_to_string e1)
				      ^")*/\n")))
		in
		    ()
		end)
	  | Eq_If (cc, aa, ww) => (
	    let
		val _ = (foldl (dump_conditional "if" s) true cc)
	    in
		()
	    end)
	  | Eq_When (cc, aa, ww) => (
	    let
		val _ = (foldl (dump_conditional "when" s) true cc)
		val _ = (TextIO.output (s, "end when\n"))
	    in
		()
	    end)
	  | Eq_For ((ii, qq), aa, ww) => (
	    let
		val _ = (TextIO.output (s, "for "))
		val ss = ((String.concatWith)
			      ", "
			      (map for_index_to_string ii))
		val _ = (TextIO.output (s, ss))
		val _ = (TextIO.output (s, " loop\n"))
		val _ = (app (dump_equation s) qq)
		val _ = (TextIO.output (s, "end for\n"))
	    in
		()
	    end)
	  | Eq_App ((f, ee), aa, ww) => (
	    let
		val _ = (TextIO.output (s, (expression_to_string f)))
		val _ = (TextIO.output (s, "("))
		val _ = (TextIO.output
			     (s, ((String.concatWith)
				      "," (map expression_to_string ee))))
		val _ = (TextIO.output (s, ")\n"))
	    in
		()
	    end)
    end)

fun dump_equations s (subj, ee) = (
    let
	fun dump_eqn0 s e = (
	    case e of
		Element_Equations (b, qq) => (
		let
		    val _ = if b then
				(TextIO.output (s, "initial equation\n"))
			    else
				(TextIO.output (s, "equation\n"))
		    val _ = (app (dump_equation s) qq)
		in
		    ()
		end)
	      | _ => raise Match)

	fun dump_eqn1 s (tag, ee) = (
	    let
		val bn = (tag_to_string tag)
		val _ = (TextIO.output (s, "/* Class "^ bn ^" */\n"))
		val _ = (app (dump_eqn0 s) ee)
	    in
		()
	    end)

	val cn = (subject_to_string subj)
	val _ = (TextIO.output (s, "\n"))
	val _ = (TextIO.output (s, "/* Component "^ cn ^" */\n"))
	val _ = (app (dump_eqn1 s) ee)
    in
	()
    end)

fun dump_flat_model () = (
    let
	val _ = tr_flat (";; Flatten a model in \"x.mo\"...")

	fun class_is_constant k = (
	    case k of
		Def_Body (mk, j, (t, p, q), nm, ee, aa, ww) => (
		let
		    val (lg, vc, io) = q
		in
		    vc = Constant orelse vc = Parameter
		end)
	      | Def_Der _ => false
	      | _ => raise Match)

	val filename = "x.mo"
	val s = (TextIO.openOut filename)

	(* File prologue. *)

	val _ = (TextIO.output (s, "/* flat model x.mo */\n"))
	val _ = (TextIO.output (s, "within ;\n"))
	val _ = (TextIO.output (s, "model X\n"))

	(* Constants. *)

	val _ = (TextIO.output (s, "\n"))
	val _ = (TextIO.output (s, "/* Constants in packages. */\n"))
	val _ = (TextIO.output (s, "\n"))
	val vars0 = (collect_variables PKG)
	val _ = (app (dump_variable s) vars0)

	(* Variables. *)

	val _ = (TextIO.output (s, "\n"))
	val _ = (TextIO.output (s, "/* Constants in the model. */\n"))
	val _ = (TextIO.output (s, "\n"))
	val vars1 = (collect_variables VAR)
	val (vars2, vars3) = (List.partition class_is_constant vars1)
	val _ = (app (dump_variable s) vars2)

	val _ = (TextIO.output (s, "\n"))
	val _ = (TextIO.output (s, "/* State variables. */\n"))
	val _ = (TextIO.output (s, "\n"))
	val _ = (app (dump_variable s) vars3)

	(* Enumerations, records, functions. *)

	val _ = (TextIO.output (s, "\n"))
	val _ = (TextIO.output (s, "/* Enumerations. */\n"))
	val _ = (TextIO.output (s, "\n"))

	val enums0 = (collect_enumerations PKG)
	val enums1 = (collect_enumerations VAR)
	val _ = (app (dump_enumeration s) enums0)
	val _ = (app (dump_enumeration s) enums1)

	val _ = (TextIO.output (s, "\n"))
	val _ = (TextIO.output (s, "/* Records. */\n"))
	val _ = (TextIO.output (s, "\n"))

	val recs0 = (collect_records PKG)
	val recs1 = (collect_records VAR)
	val _ = (app (dump_record s) recs0)
	val _ = (app (dump_record s) recs1)

	val _ = if ((null recs0) andalso (null recs1))
		then (TextIO.output (s, "\n")) else ()
	val _ = (TextIO.output (s, "/* Functions. */\n"))
	val _ = (TextIO.output (s, "\n"))

	val funs0 = (collect_functions PKG)
	val funs1 = (collect_functions VAR)
	val _ = (app (dump_function s) funs0)
	val _ = (app (dump_function s) funs1)

	(* Equation sections. *)

	val _ = (TextIO.output (s, "\n"))
	val _ = (TextIO.output (s, "/* Equations. */\n"))

	val eqns0 = (collect_equations false ())
	val _ = (app (dump_equations s) eqns0)

	val eqns1 = (collect_equations true ())
	val _ = (app (dump_equations s) eqns1)

	(* File epilogue. *)

	val _ = (TextIO.output (s, "end X;\n"))
	val _ = (TextIO.closeOut s)
    in
	()
    end)

(* ================================================================ *)

fun xdump s = (
    let
	val _ = (dump_flat_model ())
    in
	()
    end)

end
