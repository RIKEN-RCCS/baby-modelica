(* dumper.sml -*-Coding: us-ascii-unix;-*- *)
(* Copyright (C) 2018-2021 RIKEN R-CCS *)

(* SMALL FUNCTIONS FOR TRACE PRINTING. *)

structure dumper :
sig
    type expression_t
    val expression_to_string : expression_t -> string
end = struct

open plain
open ast
open small0

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
	    NIL => "NIL"
	  | Colon => ":"
	  | Otherwise => "otherwise"
	  | Scoped (x1, scope) => ("(scoped "^ (expression_to_string x1) ^")")
	  | Vref (_, []) => raise Match
	  | Vref (NONE, rr) => (ref_to_string rr)
	  | Vref (SOME ns, rr) => (
	    (ref_to_string rr))
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
	  | L_Bool x => if x then "#T" else "#F"
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
		val ds = ((String.concatWith ",")
			      (map Int.toString dim))
	    in
		case subjs of
		    [] => ("(Instance ["^ ds ^"])")
		  | (k :: _) => (
		    ("(Instance ["^ ds ^"] "^ (subject_to_string k) ^")"))
	    end)
	  | Iref v => (
	    let
		val sv = (id_to_string v)
	    in
		("(#iterator ("^ sv ^")")
	    end)
	  | Lref (rr, j) => (
	    (ref_to_string rr))
	  | Cref (x, b) => (expression_to_string x)
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

end
