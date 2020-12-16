(* operator.sml -*-Coding: us-ascii-unix;-*- *)
(* Copyright (C) 2018-2020 RIKEN R-CCS *)

(* PREDEFINED OPERATORS. *)

structure operator :
sig
    type definition_body_t
    type expression_t

    (*
    val unary_operator :
	string -> definition_body_t -> expression_t
    val binary_operator :
	string -> definition_body_t -> definition_body_t
	-> expression_t
    val relational_operator :
	string -> definition_body_t -> definition_body_t
	-> expression_t
    *)

    val fold_operator_application :
	expression_t * expression_t list -> expression_t

    val obtain_array_dimension :
	expression_t -> int list * bool

    val fold_pseudo_split :
	expression_t -> expression_t

    val bool_order : expression_t -> int
    val enumerator_order : expression_t -> int
end = struct

open ast plain
open small1
open expression

fun tr_expr (s : string) = if true then (print (s ^"\n")) else ()
fun tr_expr_vvv (s : string) = if false then (print (s ^"\n")) else ()

val take_enumarator_element = simpletype.take_enumarator_element

val expression_is_literal = expression.expression_is_literal

datatype operator_type_t
    = ARITHMETIC_UOP | ARITHMETIC_BOP
      | BOOLEAN_UOP | BOOLEAN_BOP | STRING_CONCAT_OP | RELATIONAL_OP

fun operator_type f = (
    case f of
	Opr_id => ARITHMETIC_UOP
      | Opr_neg => ARITHMETIC_UOP
      | Opr_id_ew => ARITHMETIC_UOP
      | Opr_neg_ew => ARITHMETIC_UOP
      | Opr_add => ARITHMETIC_BOP
      | Opr_sub => ARITHMETIC_BOP
      | Opr_add_ew => ARITHMETIC_BOP
      | Opr_sub_ew => ARITHMETIC_BOP
      | Opr_mul => ARITHMETIC_BOP
      | Opr_div => ARITHMETIC_BOP
      | Opr_mul_ew => ARITHMETIC_BOP
      | Opr_div_ew => ARITHMETIC_BOP
      | Opr_expt => ARITHMETIC_BOP
      | Opr_expt_ew => ARITHMETIC_BOP
      | Opr_not => BOOLEAN_UOP
      | Opr_and => BOOLEAN_BOP
      | Opr_ior => BOOLEAN_BOP
      | Opr_concat => STRING_CONCAT_OP
      | Opr_eq => RELATIONAL_OP
      | Opr_ne => RELATIONAL_OP
      | Opr_gt => RELATIONAL_OP
      | Opr_lt => RELATIONAL_OP
      | Opr_ge => RELATIONAL_OP
      | Opr_le => RELATIONAL_OP)

fun operator_is_unary f = ((operator_type f) = ARITHMETIC_UOP)
fun operator_is_binary f = ((operator_type f) = ARITHMETIC_BOP)

fun operator_is_boolean f = ((operator_type f) = BOOLEAN_UOP
			     orelse (operator_type f) = BOOLEAN_BOP)
fun operator_is_relational f = ((operator_type f) = RELATIONAL_OP)
fun operator_is_concat f = ((operator_type f) = STRING_CONCAT_OP)

(*
fun global_function_name k = (
    case k of
	Def_Body (mk, j, cs, (tag, n, x), ee, aa, ww) => (
	case tag of
	    Ctag [name] => SOME name
	  | _ => NONE)
      | _ => NONE)
*)

fun global_function_name k = (
    case k of
	Instances ([], [Subj (ns, [(Id name, [])])]) => SOME name
      | _ => NONE)

fun empty_global_function__ name = (
    let
	val subj = Subj (PKG, [(Id name, [])])
	val tag = Ctag [name]
    in
	Def_Body ((E5, PKG, MAIN),
		  subj,
		  (Function false, no_class_prefixes,
		   no_component_prefixes),
		  (tag, the_root_subject, the_root_subject),
		  [Base_List [], Base_Classes []],
		  Annotation [], Comment [])
    end)

(* Tests equality of reals.  It compares their string
   representations. *)

fun r_equal x y = (
    (r_literal x) = (r_literal y))

fun expression_is_true x = (*AHO*) raise Match
fun expression_is_integer x = (*AHO*) false
fun expression_is_constant x = (*AHO*) false

(* Calculates the dimension of an (array) expression.  It returns a
   pair (dim,true) if completely known or a pair (dim,false) if
   partially known, where ([],true) indicates a scalar and ([],false)
   indicates completely unknown.  IT SHOULD ACCEPT A VAST SET OF
   EXPRESSIONS, BUT CURRENTLY, IT ONLY ACCEPTS A SMALL SET.  It should
   accept user-defined functions, constructors of arrays and matrices
   {"{}", "[]"}, predefined functions {array, identity, diagonal,
   zeros, ones, fill, linspace}, {transpose, outerProduct, symmetric,
   cross, skew}, and {cat}.  The current unaccepted set includes
   {user-defined-functions, transpose, outerProduct, symmetric, cross,
   skew, cat}. *)

fun obtain_array_dimension w : int list * bool = (
    case w of
	NIL => raise Match
      | Colon => raise Match
      | Otherwise => raise Match
      | Scoped _ => raise Match
      | Vref (_, []) => raise Match
      | Vref (NONE, _) => raise Match
      | Vref (SOME _, _) => ([], false)
      | Opr _ => raise Match
      | App _ => ([], false)
      | ITE cc => (
	let
	    val ce = (List.find (fn (c, e) => (expression_is_true c)) cc)
	in
	    case ce of
		NONE => ([], false)
	      | SOME (c, e) => (obtain_array_dimension e)
	end)
      | Der _ => ([], false)
      | Pure _ => raise NOTYET
      | Closure _ => ([], false)
      | L_Number _ => ([], true)
      | L_Bool _ => ([], true)
      | L_Enum _ => ([], true)
      | L_String _ => ([], true)
      | Array_Triple (x, y, zo) => (
	if (not (expression_is_literal w)) then
	    ([], false)
	else
	    case (x, y, zo) of
		(L_Number _, L_Number _, NONE) => (
		let
		    val z = L_Number (Z, "1")
		in
		    ([(triple_size x z y)], true)
		end)
	      | (L_Number _, L_Number _, SOME (L_Number _)) => (
		let
		    val z = (valOf zo)
		in
		    ([(triple_size x y z)], true)
		end)
	      | (L_Bool _, L_Bool _, NONE) => (
		([(bool_size x y)], true))
	      | (L_Enum (tag0, v0), L_Enum (tag1, v1), NONE) => (
		([(enumerator_size x y)], true))
	      | _ => raise error_bad_triple)
      | Array_Constructor [] => raise Match
      | Array_Constructor ee => (
	let
	    val n0 = (length ee)
	    val xdims = (map obtain_array_dimension ee)
	    val dims = (map #1 xdims)
	    val fully = (List.all #2 xdims)
	in
	    if (fully) then
		let
		    val dim = (hd dims)
		    val _ = if (List.all (fn x => (x = dim)) dims) then ()
			    else raise error_varied_array_dimensions
		in
		    (n0 :: dim, true)
		end
	    else
		let
		    val dim = (list_shortest dims)
		in
		    (n0 :: dim, false)
		end
	end)
      | Array_Comprehension _ => ([], false)
      | Array_Concatenation _ => ([], false)
      | Tuple _ => raise error_tuple_in_rhs
      | Reduction_Argument _ => raise error_bad_syntax
      | Named_Argument _ => raise error_bad_syntax
      | Pseudo_Split (x, index) => (
	case (obtain_array_dimension x) of
	    (_, false) => ([], false)
	  | (dim0, true) => (
	    let
		val _ = if ((length dim0) >= (length index)) then ()
			else raise error_split_array_dimension
		val pairs = (ListPair.zip (index, dim0))
		val _ = if (List.all (op <=) pairs) then ()
			else raise error_split_array_dimension
		val dim1 = (List.drop (dim0, (length index)))
	    in
		(dim1, true)
	    end))
      | Component_Ref _ => raise NOTYET
      (*| Instance (dim, kk, _) => (dim, true)*)
      | Instances ([], [subj]) => (
	let
	    val k = surely (fetch_from_instance_tree subj)
	in
	    case k of
		Def_Mock_Array (dim, array, dummy) => (dim, true)
	      | _ => ([], true)
	end)
      | Instances ([], _) => raise Match
      | Instances (dim, subjs) => (dim, true)
      | Iref v => raise NOTYET
      | Array_fill (e, n) => (
	if (not (expression_is_literal n)) then
	    ([], false)
	else
	    case n of
		L_Number (Z, s) => (
		case (obtain_array_dimension e) of
		    (nn, fully) => ((z_value s) :: nn, fully))
	      | L_Number (R, s) => raise error_bad_size
	      | _ => raise error_bad_size)
      | Array_diagonal v => (
	case (obtain_array_dimension v) of
	    ([], fully) => ([], fully)
	  | (n0 :: nn, fully) => ((n0 :: n0 :: nn), fully)))

(* (*AHO*) Note that it may create an empty array by an array
   constructor "{}" (which is illegal in the language syntax). *)

fun predefined_size_a a = (
    let
	(*val body = (empty_global_function "size")*)
	(*val f = Instance ([], [body], NONE)*)
	val f = Instances ([], [Subj (PKG, [(Id "size", [])])])
	val original = App (f, [a])
	val (dim, fully) = (obtain_array_dimension a)
	val ee = (map z_literal dim)
    in
	if (fully) then
	    Array_Constructor ee
	else
	    original
    end)

fun predefined_size_a_i a i = (
    let
	(*val body = (empty_global_function "size")*)
	(*val f = Instance ([], [body], NONE)*)
	val f = Instances ([], [Subj (PKG, [(Id "size", [])])])
	val original = App (f, [a, i])
    in
	if (not (expression_is_literal i)) then
	    original
	else
	    let
		val n = ((literal_to_int i) - 1)
		val (dim, fully) = (obtain_array_dimension a)
		val ee = (map z_literal dim)
	    in
		if (n < 0) then
		    raise error_size_with_bad_index
		else if (n >= (length ee)) then
		    if (fully) then
			raise error_size_with_bad_index
		    else
			raise error_unknown_size
		else
		    (List.nth (ee, n))
	    end
    end)

fun predefined_fill e nn = (
    case nn of
	[] => e
      | [n] => Array_fill (e, n)
      | (n :: tl) => Array_fill ((predefined_fill e tl), n))

fun predefined_diagonal v = (
    Array_diagonal v)

(* Simplifies predefined functions or globally defined functions. *)

fun fold_on_global_function (name, args) = (
    let
	(*val body = (empty_global_function name)*)
	(*val f = Instance ([], [body], NONE)*)
	val f = Instances ([], [Subj (PKG, [(Id name, [])])])
	val original = App (f, args)
    in
	case name of
	    "size" => (
	    case args of
		[a] => (predefined_size_a a)
	      | [a, i] => (predefined_size_a_i a i)
	      | _ => raise error_bad_syntax)
	  | "fill" => (
	    case args of
		e :: n :: nn => (predefined_fill e (n :: nn))
	      | _ => raise error_bad_syntax)
	  | "diagonal" => (
	    case args of
		[v] => (predefined_diagonal v)
	      | _ => raise error_bad_syntax)
	  | _ => original
    end)

fun fold_operator_application (f, args) = (
    let
	val original = App (f, args)
	val pow = Math.pow
    in
	case f of
	    Opr n => (
	    if (operator_is_relational n) then
		case args of
		    [L_Number (Z, sx), L_Number (Z, sy)] => (
		    let
			(* Z*Z *)
			val x = (z_value sx)
			val y = (z_value sy)
		    in
			case n of
			    Opr_eq => L_Bool (x = y)
			  | Opr_ne => L_Bool (x <> y)
			  | Opr_gt => L_Bool (x > y)
			  | Opr_lt => L_Bool (x < y)
			  | Opr_ge => L_Bool (x >= y)
			  | Opr_le => L_Bool (x <= y)
			  | _ => raise Match
		    end)
		  | [L_Number (rx_, sx), L_Number (ry_, sy)] => (
		    let
			(* R*R *)
			val x = (r_value sx)
			val y = (r_value sy)
		    in
			case n of
			    Opr_eq => L_Bool (r_equal x y)
			  | Opr_ne => L_Bool (not (r_equal x y))
			  | Opr_gt => L_Bool (x > y)
			  | Opr_lt => L_Bool (x < y)
			  | Opr_ge => L_Bool (x >= y)
			  | Opr_le => L_Bool (x <= y)
			  | _ => raise Match
		    end)
		  | [L_Bool x, L_Bool y] => (
		    case n of
			Opr_eq => L_Bool (x = y)
		      | Opr_ne => L_Bool (x <> y)
		      | Opr_gt => L_Bool (x = true andalso y = false)
		      | Opr_lt => L_Bool (x = false andalso y = true)
		      | Opr_ge => L_Bool (x = true orelse y = false)
		      | Opr_le => L_Bool (x = false orelse y = true)
		      | _ => raise Match)
		  | [L_String x, L_String y] => (
		    case n of
			Opr_eq => L_Bool (x = y)
		      | Opr_ne => L_Bool (x <> y)
		      | Opr_gt => L_Bool (x > y)
		      | Opr_lt => L_Bool (x < y)
		      | Opr_ge => L_Bool (x >= y)
		      | Opr_le => L_Bool (x <= y)
		      | _ => raise Match)
		  | [x as L_Enum (tx, _), y as L_Enum (ty, _)] => (
		    let
			val _ = if (tx = ty) then ()
				else raise error_enum_mismatch
			val cc = (enumerator_compare x y)
		    in
			case n of
			    Opr_eq => L_Bool (cc = 0)
			  | Opr_ne => L_Bool (cc <> 0)
			  | Opr_gt => L_Bool (cc > 0)
			  | Opr_lt => L_Bool (cc < 0)
			  | Opr_ge => L_Bool (cc >= 0)
			  | Opr_le => L_Bool (cc <= 0)
			  | _ => raise Match
		    end)
		  | _ => original
	    else if (operator_is_boolean n) then
		case n of
		    Opr_not => (
		    case args of
			[L_Bool x] => L_Bool (not x)
		      | _ => original)
		  | Opr_and => (
		    case args of
			[L_Bool x, L_Bool y] => L_Bool (x andalso y)
		      | _ => original)
		  | Opr_ior => (
		    case args of
			[L_Bool x, L_Bool y] => L_Bool (x orelse y)
		      | _ => original)
		  | _ => raise Match
	    else if (operator_is_concat n) then
		case args of
		    [L_String sx, L_String sy] => L_String (sx ^ sy)
		  | _ => original
	    else if (operator_is_unary n) then
		case args of
		    [L_Number (Z, sx)] => (
		    (* Z *)
		    let
			val x = (z_value sx)
		    in
			case n of
			    Opr_id => (z_literal x)
			  | Opr_neg => (z_literal (~ x))
			  | Opr_id_ew => (z_literal x)
			  | Opr_neg_ew => (z_literal (~ x))
			  | _ => raise Match
		    end)
		  | [L_Number (R, sx)] => (
		    (* R *)
		    let
			val x = (r_value sx)
		    in
			case n of
			    Opr_id => (r_literal x)
			  | Opr_neg => (r_literal (~ x))
			  | Opr_id_ew => (r_literal x)
			  | Opr_neg_ew => (r_literal (~ x))
			  | _ => raise Match
		    end)
		  | _ => original
	    else if (operator_is_binary n) then
		case args of
		    [L_Number (Z, sx), L_Number (Z, sy)] => (
		    let
			(* Z*Z *)
			val x = (z_value sx)
			val y = (z_value sx)
		    in
			case n of
			    Opr_add => (z_literal (x + y))
			  | Opr_sub => (z_literal (x - y))
			  | Opr_add_ew => (z_literal (x + y))
			  | Opr_sub_ew => (z_literal (x - y))
			  | Opr_mul => (z_literal (x * y))
			  | Opr_div => (z_literal (x div y))
			  | Opr_mul_ew => (z_literal (x * y))
			  | Opr_div_ew => (z_literal (x div y))
			  | _ => raise Match
		    end)
		  | [L_Number (rx_, sx), L_Number (ry_, sy)] => (
		    let
			(* R*R *)
			val x = (r_value sx)
			val y = (r_value sy)
		    in
			case n of
			    Opr_add => (r_literal (x + y))
			  | Opr_sub => (r_literal (x - y))
			  | Opr_add_ew => (r_literal (x + y))
			  | Opr_sub_ew => (r_literal (x - y))
			  | Opr_mul => (r_literal (x * y))
			  | Opr_div => (r_literal (x / y))
			  | Opr_mul_ew => (r_literal (x * y))
			  | Opr_div_ew => (r_literal (x / y))
			  | Opr_expt => (r_literal (pow (x, y)))
			  | Opr_expt_ew => (r_literal (pow (x, y)))
			  | _ => raise Match
		    end)
		  | _ => original
	    else
		raise Match)
	  (*| Instance ([], [kp], NONE) => ( *)
	  (*case (global_function_name kp) of*)
	  (*NONE => original*)
	  (*| SOME v => (fold_on_global_function (v, args)))*)
	  | Instances _ => (
	    case (global_function_name f) of
		NONE => original
	      | SOME v => (fold_on_global_function (v, args)))
	  | _ => original
    end)

(* ================================================================ *)

fun subarray_of_instances (index : int list) (dim0, kk0, dummy) = (
    let
	val _ = if ((length index) <= (length dim0)) then ()
		else raise error_bad_index
	val _ = if (ListPair.all (fn (i, d) => (i <= d)) (index, dim0)) then ()
		else raise error_bad_index
	val dim1 = (array_drop_columns dim0 (length index))
	val size = (array_size dim1)
	val offset = (array_index dim0 index 0)
	val kk1 = (List.take ((List.drop (kk0, offset)), size))
	val subjs = (map subject_of_class kk1)
    in
	(*Instance (dim1, kk1, dummy)*)
	Instances (dim1, subjs)
    end)

fun fold_pseudo_split w0 = (
    case w0 of
	Pseudo_Split (x, index) => (
	case x of
	    NIL => raise Match
	  | Colon => raise Match
	  | Otherwise => raise Match
	  | Scoped _ => raise Match
	  | Vref (_, []) => raise Match
	  | Vref (NONE, _) => raise Match
	  | Vref (SOME _, _) => w0
	  | Opr _ => raise Match
	  | App _ => w0
	  | ITE _ => w0
	  | Der _ => w0
	  | Pure _ => w0
	  | Closure _ => raise Match
	  | L_Number _ => raise error_split_to_scalar
	  | L_Bool _ => raise error_split_to_scalar
	  | L_Enum _ => raise error_split_to_scalar
	  | L_String _ => raise error_split_to_scalar
	  | Array_Triple (x0, y0, NONE) => (
	    if ((expression_is_constant x0)
		andalso (expression_is_constant y0)) then
		(range_nth x0 y0 index)
	    else
		w0)
	  | Array_Triple (x0, y0, SOME z0) => (
	    if ((expression_is_integer x0)
		andalso (expression_is_integer y0)
		andalso (expression_is_integer z0)
		andalso (expression_is_constant x0)
		andalso (expression_is_constant y0)
		andalso (expression_is_constant z0)) then
		(triple_nth x0 y0 z0 index)
	    else
		w0)
	  | Array_Constructor aa => (
	    case index of
		[] => raise Match
	      | (hd :: tl) => (
		let
		    val e = (List.nth (aa, (hd - 1)))
		in
		    if (null tl) then
			e
		    else
			(fold_pseudo_split (Pseudo_Split (e, tl)))
		end))
	  | Array_Comprehension _ => w0
	  | Array_Concatenation _ => w0
	  | Tuple _ => raise Match
	  | Reduction_Argument _ => raise Match
	  | Named_Argument (n, x) => raise Match
	  | Pseudo_Split (x, ss) => (
	    (Pseudo_Split (x, (merge_subscripts index ss))))
	  | Component_Ref _ => raise NOTYET
          (*| Instance (dim, kk, dummy) => ( *)
	  (*(subarray_of_instances index (dim, kk, dummy)))*)
          | Instances ([], [subj]) => (
	    let
		val k = surely (fetch_from_instance_tree subj)
	    in
		case k of
		    Def_Mock_Array (dim, array, dummy) => (
		    (subarray_of_instances index (dim, array, dummy)))
		  | _ => raise error_split_to_scalar
	    end)
          | Instances ([], _) => raise Match
          | Instances (dim, subjs) => (
	    let
		val array = (map (surely o fetch_from_instance_tree) subjs)
	    in
		(subarray_of_instances index (dim, array, NONE))
	    end)
	  | Iref v => raise error_split_to_scalar
	  | Array_fill _ => w0
	  | Array_diagonal _ => w0)
      | _ => raise Match)

end
