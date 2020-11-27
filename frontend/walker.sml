(* walker.sml -*-Coding: us-ascii-unix;-*- *)
(* Copyright (C) 2018-2020 RIKEN R-CCS *)

(* SCANING IN EXPRESSIONS. *)

structure walker :
sig
    type expression_t
    type definition_body_t
    type 'a fixer_t
    type 'a walker_t

    val walk_in_expression :
	'a fixer_t -> expression_t * 'a -> expression_t * 'a
    val walk_in_class :
	'a walker_t -> definition_body_t * 'a -> definition_body_t * 'a
end = struct

open plain
open ast
open small0

val expression_to_string = dumper.expression_to_string

val simplify_ite = folder.simplify_ite

type 'a fixer_t = {fixer : expression_t * 'a -> expression_t * 'a}
type 'a walker_t = {walker : expression_t * 'a -> expression_t * 'a}

fun tr_expr (s : string) = if true then (print (s ^"\n")) else ()
fun tr_expr_vvv (s : string) = if false then (print (s ^"\n")) else ()

fun walk_in_n_x walk ((n, x0), acc0) = (
    let
	val (x1, acc1) = (walk (x0, acc0))
    in
	((n, x1), acc1)
    end)

fun walk_in_x_option walk (o0, acc0) = (
    case o0 of
	NONE => (NONE, acc0)
      | (SOME x0) => (
	let
	    val (x1, acc1) = (walk (x0, acc0))
	in
	    (SOME x1, acc1)
	end))

fun walk_in_x_x walk ((x0, y0), acc0) = (
    let
	val (x1, acc1) = (walk (x0, acc0))
	val (y1, acc2) = (walk (y0, acc1))
    in
	((x1, y1), acc2)
    end)

fun walk_in_xx walk (xx0, acc0) = (map_along walk (xx0, acc0))

fun walk_in_n_xx walk ((n, xx0), acc0) = (
    let
	val (xx1, acc1) = (map_along walk (xx0, acc0))
    in
	((n, xx1), acc1)
    end)

(* Applies a function in the ctx in element expressions in post-order.
   It need be called after a variable binder.  It does not call the
   function if an expression has no subexpressions. *)

fun walk_in_expression (ctx : 'a fixer_t) (w0, acc0) = (
    let
	val walk_x = (walk_in_expression ctx)
	val walk_n_x = (walk_in_n_x walk_x)
	val walk_x_x = (walk_in_x_x walk_x)
	val walk_x_option = (walk_in_x_option walk_x)
	val walk_subscript = (walk_in_n_xx walk_x)
	val walk_xx = (map_along walk_x)

	val _ = tr_expr_vvv (";; walk_in_expression ("^
			     (expression_to_string w0) ^")")
    in
	case w0 of
	    NIL => (NIL, acc0)
	  | Colon => (Colon, acc0)
	  | Otherwise => (Otherwise, acc0)
	  | Scoped _ => raise Match
	  | Vref (_, []) => raise Match
	  | Vref (NONE, _) => raise Match
	  | Vref (SOME ns, rr0) => (
	    let
		val (rr1, acc1) = (map_along walk_subscript (rr0, acc0))
		val w1 = Vref (SOME ns, rr1)
	    in
		((#fixer ctx) (w1, acc1))
	    end)
	  | Opr _ => (w0, acc0)
	  | App (f0, aa0) => (
	    let
		val (f1, acc1) = (walk_x (f0, acc0))
		val (aa1, acc2) = (map_along walk_x (aa0, acc1))
		val w1 = App (f1, aa1)
	    in
		((#fixer ctx) (w1, acc2))
	    end)
	  | ITE cc0 => (
	    let
		val (cc1, acc1) = (map_along walk_x_x (cc0, acc0))
		val w1 = (simplify_ite (ITE cc1))
	    in
		((#fixer ctx) (w1, acc1))
	    end)
	  | Der aa0 => (
	    let
		val (aa1, acc1) = (map_along walk_x (aa0, acc0))
		val w1 = Der aa1
	    in
		((#fixer ctx) (w1, acc1))
	    end)
	  | Pure aa0 => (
	    let
		val (aa1, acc1) = (map_along walk_x (aa0, acc0))
		val w1 = Pure aa1
	    in
		((#fixer ctx) (w1, acc1))
	    end)
	  | Closure (n, aa0) => (
	    let
		val (aa1, acc1) = (map_along walk_x (aa0, acc0))
		val w1 = Closure (n, aa1)
	    in
		((#fixer ctx) (w1, acc1))
	    end)
	  | L_Number _ => (w0, acc0)
	  | L_Bool _ => (w0, acc0)
	  | L_Enum _ => (w0, acc0)
	  | L_String _ => (w0, acc0)
	  | Array_Triple (x0, y0, z0) => (
	    let
		val (x1, acc1) = (walk_x (x0, acc0))
		val (y1, acc2) = (walk_x (y0, acc1))
		val (z1, acc3) = (walk_x_option (z0, acc2))
		val w1 = Array_Triple (x1, y1, z1)
	    in
		((#fixer ctx) (w1, acc3))
	    end)
	  | Array_Constructor xx0 => (
	    let
		val (xx1, acc1) = (map_along walk_x (xx0, acc0))
		val w1 = Array_Constructor xx1
	    in
		((#fixer ctx) (w1, acc1))
	    end)
	  | Array_Comprehension (x0, uu0) => (
	    let
		val (x1, acc1) = (walk_x (x0, acc0))
		val (uu1, acc2) = (map_along walk_n_x (uu0, acc1))
		val w1 = Array_Comprehension (x1, uu1)
	    in
		((#fixer ctx) (w1, acc2))
	    end)
	  | Array_Concatenation xx0 => (
	    let
		val (xx1, acc1) = (map_along walk_xx (xx0, acc0))
		val w1 = Array_Concatenation xx1
	    in
		((#fixer ctx) (w1, acc1))
	    end)
	  | Tuple xx0 => (
	    let
		val (xx1, acc1) = (map_along walk_x (xx0, acc0))
		val w1 = Tuple xx1
	    in
		((#fixer ctx) (w1, acc1))
	    end)
	  | Reduction_Argument (x0, uu0) => (
	    let
		val (x1, acc1) = (walk_x (x0, acc0))
		val (uu1, acc2) = (map_along walk_n_x (uu0, acc1))
		val w1 = Reduction_Argument (x1, uu1)
	    in
		((#fixer ctx) (w1, acc2))
	    end)
	  | Named_Argument (n, x0) => (
	    let
		val (x1, acc1) = (walk_x (x0, acc0))
		val w1 = Named_Argument (n, x1)
	    in
		((#fixer ctx) (w1, acc1))
	    end)
	  | Pseudo_Split (x0, ss) => (
	    let
		val (x1, acc1) = (walk_x (x0, acc0))
		val w1 = Pseudo_Split (x1, ss)
	    in
		((#fixer ctx) (w1, acc1))
	    end)
	  | Component_Ref (x0, id) => (
	    let
		val (x1, acc1) = (walk_x (x0, acc0))
		val w1 = Component_Ref (x1, id)
	    in
		((#fixer ctx) (w1, acc1))
	    end)
	  | Instance _ => ((#fixer ctx) (w0, acc0))
	  | Iref _ => ((#fixer ctx) (w0, acc0))
	  | Array_fill (x0, y0) => (
	    let
		val (x1, acc1) = (walk_x (x0, acc0))
		val (y1, acc2) = (walk_x (y0, acc1))
		val w1 = Array_fill (x1, y1)
	    in
		((#fixer ctx) (w1, acc2))
	    end)
	  | Array_diagonal x0 => (
	    let
		val (x1, acc1) = (walk_x (x0, acc0))
		val w1 = Array_diagonal x1
	    in
		((#fixer ctx) (w1, acc1))
	    end)
    end)

(* ================================================================ *)

(* Calls an expression-walker in each expression in a class. *)

fun walk_in_class (ctx : 'a walker_t) ((k0 : definition_body_t), acc0) = (
    if (class_is_simple_type k0) then
	(walk_in_simple_type ctx (k0, acc0))
    else
	case k0 of
	    Def_Body (mk, j, cs, nm, ee0, aa, ww) => (
	    let
		val _ = if (step_is_at_least E3 k0) then () else raise Match
		val walk_e = (walk_in_class_element ctx k0)
		val (ee1, acc1) = (map_along walk_e (ee0, acc0))
	    in
		(Def_Body (mk, j, cs, nm, ee1, aa, ww), acc1)
	    end)
	  | Def_Der _ => (k0, acc0)
	  | Def_Primitive _ => (k0, acc0)
	  | Def_Name _ => raise Match
	  | Def_Scoped _ => raise Match
	  | Def_Refine _ => raise Match
	  | Def_Extending _ => raise Match
	  | Def_Replaced _ => raise Match
	  | Def_Displaced _ => raise Match
	  | Def_In_File => raise Match
	  | Def_Mock_Array _ => raise Match)

and walk_in_class_element (ctx : 'a walker_t) kp ((e0 : element_t), acc0) = (
    let
	val walk_q = (walk_in_equation ctx kp)
	val walk_s = (walk_in_statement ctx kp)
	fun walk_pair ((c, k0), acc0) = (
	    let
		val (k1, acc1) = (walk_in_class ctx (k0, acc0))
	    in
		((c, k1), acc1)
	    end)

	val package = (class_is_package kp)
    in
	case e0 of
	    Import_Clause _ => raise Match
	  | Extends_Clause _ => raise Match
	  | Element_Class _ => (e0, acc0)
	  | Element_State _ => (e0, acc0)
	  | Redefine_Class _ => (e0, acc0)
	  | Redeclare_State _ => (e0, acc0)
	  | Element_Enumerators _ => raise Match
	  | Element_Equations (u, qq0) => (
	    if (package) then
		(e0, acc0)
	    else
		let
		    val _ = tr_expr (";; - [walk] Walk in equations in ("^
				     (class_print_name kp) ^")")

		    val (qq1, acc1) = (map_along walk_q (qq0, acc0))
		    val e1 = Element_Equations (u, qq1)
		in
		    (e1, acc1)
		end)
	  | Element_Algorithms (u, ss0) => (
	    if (package) then
		(e0, acc0)
	    else
		let
		    val _ = tr_expr (";; - [walk] Walk in statements in ("^
				     (class_print_name kp) ^")")

		    val (ss1, acc1) = (map_along walk_s (ss0, acc0))
		    val e1 = Element_Algorithms (u, ss1)
		in
		    (e1, acc1)
		end)
	  | Element_External _ => (e0, acc0)
	  | Element_Annotation _ => (e0, acc0)
	  | Element_Import _ => (e0, acc0)
	  | Element_Base _ => (e0, acc0)
	  | Base_List _ => (e0, acc0)
	  | Base_Classes bb0 => (
	    let
		val (bb1, acc1) = (map_along walk_pair (bb0, acc0))
		val e1 = Base_Classes bb1
	    in
		(e1, acc1)
	    end)
    end)

and walk_in_simple_type (ctx : 'a walker_t) (k0, acc0) = (
    case k0 of
	Def_Body _ => (
	let
	    val walk_e = (walk_in_simple_type_element ctx k0)
	    val _ = if (step_is_at_least E3 k0) then () else raise Match

	    val ee0 = (body_elements k0)
	    val (ee1, acc1) = (map_along walk_e (ee0, acc0))
	    val k1 = (replace_body_elements k0 ee1)
	    val k2 = (set_cook_step E5 k1)
	in
	    (k2, acc1)
	end)
      | _ => raise Match)

and walk_in_simple_type_element (ctx : 'a walker_t) kp (e0, acc0) = (
    case e0 of
	Import_Clause _ => raise Match
      | Extends_Clause _ => raise Match
      | Element_Class _ => (e0, acc0)
      | Element_State (z, r, d0, h) => (
	let
	    val Defvar (v, q, k0, c, a, w) = d0
	    val _ = if (class_is_primitive k0) then () else raise Match
	in
	    let
		val (k1, acc1) = (walk_in_primitive_type ctx kp (k0, acc0))
		val d1 = Defvar (v, q, k1, c, a, w)
	    in
		(Element_State (z, r, d1, h), acc1)
	    end
	end)
      | Redefine_Class _ => (e0, acc0)
      | Redeclare_State _ => (e0, acc0)
      | Element_Enumerators _ => (e0, acc0)
      | Element_Equations _ => (e0, acc0)
      | Element_Algorithms _ => (e0, acc0)
      | Element_External _ => (e0, acc0)
      | Element_Annotation _ => (e0, acc0)
      | Element_Import _ => (e0, acc0)
      | Element_Base _ => (e0, acc0)
      | Base_List _ => (e0, acc0)
      | Base_Classes _ => (e0, acc0))

and walk_in_primitive_type ctx kp (k0, acc0) = (
    case k0 of
	Def_Primitive (ty, x0) => (
	let
	    val walk_x = (#walker ctx)
	    val (x1, acc1) = (walk_x (x0, acc0))
	in
	    (Def_Primitive (ty, x1), acc1)
	end)
      | _ => raise Match)

and walk_in_modifier (ctx : 'a walker_t) kp ((m0 : modifier_t), acc0) = (
    let
	val walk_x = (#walker ctx)
	val walk_m = (walk_in_modifier ctx kp)
	val walk_h = (walk_in_constraint ctx kp)
	val walk_k = (walk_in_class ctx)
	fun id m = m
    in
	case m0 of
	    Mod_Redefine (r, d0, h0) => (
	    let
		val Defclass ((v, g), k0) = d0
		val (k1, acc1) = (walk_k (k0, acc0))
		val d1 = Defclass ((v, g), k1)
		val (h1, acc2) = (walk_in_x_option walk_h (h0, acc1))
		val m1 = Mod_Redefine (r, d1, h1)
		val m2 = (id m1)
	    in
		(m2, acc2)
	    end)
	  | Mod_Elemental_Redefine (z, r, d0, h0) => (
	    let
		val Defclass ((v, g), k0) = d0
		val (k1, acc1) = (walk_k (k0, acc0))
		val d1 = Defclass ((v, g), k1)
		val (h1, acc2) = (walk_in_x_option walk_h (h0, acc1))
		val m1 = Mod_Elemental_Redefine (z, r, d1, h1)
		val m2 = (id m1)
	    in
		(m2, acc2)
	    end)
	  | Mod_Redeclare (r, d0, h0) => (
	    let
		val Defvar (v, q, k0, c, aa, ww) = d0
		val (k1, acc1) = (walk_k (k0, acc0))
		val d1 = Defvar (v, q, k1, c, aa, ww)
		val (h1, acc2) = (walk_in_x_option walk_h (h0, acc1))
		val m1 = Mod_Redeclare (r, d1, h1)
		val m2 = (id m1)
	    in
		(m2, acc2)
	    end)
	  | Mod_Elemental_Redeclare (z, r, d0, h0) => (
	    let
		val Defvar (v, q, k0, c, aa, ww) = d0
		val (k1, acc1) = (walk_k (k0, acc0))
		val d1 = Defvar (v, q, k1, c, aa, ww)
		val (h1, acc2) = (walk_in_x_option walk_h (h0, acc1))
		val m1 = Mod_Elemental_Redeclare (z, r, d1, h1)
		val m2 = (id m1)
	    in
		(m2, acc2)
	    end)
	  | Mod_Entry (ef, n, mm0, w) => (
	    let
		val (mm1, acc1) = (map_along walk_m (mm0, acc0))
		val m1 = Mod_Entry (ef, n, mm1, w)
		val m2 = (id m1)
	    in
		(m2, acc1)
	    end)
	  | Mod_Value x0 => (
	    let
		val (x1, acc1) = (walk_x (x0, acc0))
		val m1 = Mod_Value x1
		val m2 = (id m1)
	    in
		(m2, acc1)
	    end)
    end)

and walk_in_constraint (ctx : 'a walker_t) kp ((h0 : constraint_t), acc0) = (
    let
	val walk_m = (walk_in_modifier ctx kp)
	fun id h = h

	val subj = (subject_of_class kp)
	val (k0, mm0, Annotation aa0, ww) = h0
	val (mm1, acc1) = (map_along walk_m (mm0, acc0))
	val (aa1, acc2) = (map_along walk_m (aa0, acc1))
	val h1 = (k0, mm1, Annotation aa1, ww)
	val h2 = (id h1)
    in
	(h2, acc2)
    end)

and walk_in_equation (ctx : 'a walker_t) kp ((q0 : equation_t), acc0) = (
    let
	val walk_x = (#walker ctx)
	val walk_m = (walk_in_modifier ctx kp)
	val walk_q = (walk_in_equation ctx kp)
	fun walk_x_qq ((x0, qq0), acc0) = (
	    let
		val (x1, acc1) = (walk_x (x0, acc0))
		val (qq1, acc2) = (map_along walk_q (qq0, acc1))
	    in
		((x1, qq1), acc2)
	    end)
	fun id q = q
    in
	case q0 of
	    Eq_Eq ((x0, y0), Annotation aa0, ww) => (
	    let
		val (x1, acc1) = (walk_x (x0, acc0))
		val (y1, acc2) = (walk_x (y0, acc1))
		val (aa1, acc3) = (map_along walk_m (aa0, acc2))
		val q1 = Eq_Eq ((x1, y1), Annotation aa1, ww)
		val q2 = (id q1)
	    in
		(q2, acc3)
	    end)
	  | Eq_Connect ((x0, y0), Annotation aa0, ww) => (
	    let
		val (x1, acc1) = (walk_x (x0, acc0))
		val (y1, acc2) = (walk_x (y0, acc1))
		val (aa1, acc3) = (map_along walk_m (aa0, acc2))
		val q1 = Eq_Connect ((x1, y1), Annotation aa1, ww)
		val q2 = (id q1)
	    in
		(q2, acc3)
	    end)
	  | Eq_If (c0, Annotation aa0, ww) => (
	    let
		val (c1, acc1) = (map_along walk_x_qq (c0, acc0))
		val (aa1, acc2) = (map_along walk_m (aa0, acc1))
		val q1 = Eq_If (c1, Annotation aa1, ww)
		val q2 = (id q1)
	    in
		(q2, acc2)
	    end)
	  | Eq_When (c0, Annotation aa0, ww) => (
	    let
		val (c1, acc1) = (map_along walk_x_qq (c0, acc0))
		val (aa1, acc2) = (map_along walk_m (aa0, acc1))
		val q1 = Eq_When (c1, Annotation aa1, ww)
		val q2 = (id q1)
	    in
		(q2, acc2)
	    end)
	  | Eq_App ((x0, yy0), Annotation aa0, ww) => (
	    let
		val (x1, acc1) = (walk_x (x0, acc0))
		val (yy1, acc2) = (map_along walk_x (yy0, acc1))
		val (aa1, acc3) = (map_along walk_m (aa0, acc2))
		val q1 = Eq_App ((x1, yy1), Annotation aa1, ww)
		val q2 = (id q1)
	    in
		(q2, acc3)
	    end)
	  | Eq_For ((ii, qq0), Annotation aa0, ww) => (
	    let
		val newctx = ctx
		val walk_m = (walk_in_modifier newctx kp)
		val walk_q = (walk_in_equation newctx kp)
		val (qq1, acc1) = (map_along walk_q (qq0, acc0))
		val (aa1, acc2) = (map_along walk_m (aa0, acc1))
		val q1 = Eq_For ((ii, qq1), Annotation aa1, ww)
		val q2 = (id q1)
	    in
		(q2, acc2)
	    end)
    end)

and walk_in_statement (ctx : 'a walker_t) kp ((s0 : statement_t), acc0) = (
    let
	val walk_x = (#walker ctx)
	val walk_m = (walk_in_modifier ctx kp)
	val walk_s = (walk_in_statement ctx kp)
	val walk_n_x = (walk_in_n_x walk_x)
	fun walk_x_ss ((x0, ss0), acc0) = (
	    let
		val (x1, acc1) = (walk_x (x0, acc0))
		val (ss1, acc2) = (map_along walk_s (ss0, acc1))
	    in
		((x1, ss1), acc2)
	    end)
	fun id s = s
    in
	case s0 of
	    St_Break (Annotation mm0, ww) => (
	    let
		val (mm1, acc1) = (map_along walk_m (mm0, acc0))
		val s1 = St_Break (Annotation mm1, ww)
		val s2 = (id s1)
	    in
		(s2, acc1)
	    end)
	  | St_Return (Annotation mm0, ww) => (
	    let
		val (mm1, acc1) = (map_along walk_m (mm0, acc0))
		val s1 = St_Return (Annotation mm1, ww)
		val s2 = (id s1)
	    in
		(s2, acc1)
	    end)
	  | St_Assign (x0, y0, Annotation mm0, ww) => (
	    let
		val (x1, acc1) = (walk_x (x0, acc0))
		val (y1, acc2) = (walk_x (y0, acc1))
		val (mm1, acc3) = (map_along walk_m (mm0, acc2))
		val s1 = St_Assign (x1, y1, Annotation mm1, ww)
		val s2 = (id s1)
	    in
		(s2, acc3)
	    end)
	  | St_Call (xx0, y0, zz0, Annotation mm0, ww) => (
	    let
		val (xx1, acc1) = (map_along walk_x (xx0, acc0))
		val (y1, acc2) = (walk_x (y0, acc1))
		val (zz1, acc3) = (map_along walk_x (zz0, acc2))
		val (mm1, acc4) = (map_along walk_m (mm0, acc3))
		val s1 = St_Call (xx1, y1, zz1, Annotation mm1, ww)
		val s2 = (id s1)
	    in
		(s2, acc4)
	    end)
	  | St_If (cc0, Annotation mm0, ww) => (
	    let
		val (cc1, acc1) = (map_along walk_x_ss (cc0, acc0))
		val (mm1, acc2) = (map_along walk_m (mm0, acc1))
		val s1 = St_If (cc1, Annotation mm1, ww)
		val s2 = (id s1)
	    in
		(s2, acc2)
	    end)
	  | St_While (x0, ss0, Annotation mm0, ww) => (
	    let
		val (x1, acc1) = (walk_x (x0, acc0))
		val (ss1, acc2) = (map_along walk_s (ss0, acc1))
		val (mm1, acc3) = (map_along walk_m (mm0, acc2))
		val s1 = St_While (x1, ss1, Annotation mm1, ww)
		val s2 = (id s1)
	    in
		(s2, acc3)
	    end)
	  | St_When (cc0, Annotation mm0, ww) => (
	    let
		val (cc1, acc1) = (map_along walk_x_ss (cc0, acc0))
		val (mm1, acc2) = (map_along walk_m (mm0, acc1))
		val s1 = St_When (cc1, Annotation mm1, ww)
		val s2 = (id s1)
	    in
		(s2, acc2)
	    end)
	  | St_For (ii, ss0, Annotation mm0, ww) => (
	    let
		val newctx = ctx
		val walk_s = (walk_in_statement newctx kp)
		val walk_m = (walk_in_modifier newctx kp)
		val (ss1, acc1) = (map_along walk_s (ss0, acc0))
		val (mm1, acc2) = (map_along walk_m (mm0, acc1))
		val s1 = St_For (ii, ss1, Annotation mm1, ww)
		val s2 = (id s1)
	    in
		(s2, acc2)
	    end)
    end)

end
