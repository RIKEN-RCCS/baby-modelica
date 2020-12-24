(* postbinder.sml -*-Coding: us-ascii-unix;-*- *)
(* Copyright (C) 2018-2020 RIKEN R-CCS *)

(* NAME RESOLVER, SECOND PART.  Second resolving resolves a variable
   reference in equations/algorithms sections. *)

structure postbinder :
sig
    val bind_model : bool -> unit
    val replace_outer : unit -> unit
end = struct

open ast
open plain
open small1

val class_tree = classtree.class_tree
val instance_tree = classtree.instance_tree
val fetch_class_by_scope = classtree.fetch_class_by_scope
val store_to_instance_tree = classtree.store_to_instance_tree
val fetch_from_instance_tree = classtree.fetch_from_instance_tree
val component_is_outer_alias = classtree.component_is_outer_alias
val traverse_tree = classtree.traverse_tree
val replace_outer_reference = classtree.replace_outer_reference

val make_reference = binder.make_reference
val bind_in_class = binder.bind_in_class

val walk_in_class = walker.walk_in_class
val walk_in_expression = walker.walk_in_expression
val walk_in_equation = walker.walk_in_equation
val walk_in_statement = walker.walk_in_statement

val secure_reference = builder.secure_reference

(* ================================================================ *)

fun secure_references_in_class kp = (
    let
	val ctx = kp
	val buildphase = false
	val efix = (fn (x, _) => ((secure_reference ctx buildphase x), ()))
	val ewalk = (walk_in_expression efix)
	val qwalk = (walk_in_equation (fn (q, a) => (q, a)) ewalk)
	val swalk = (walk_in_statement (fn (s, a) => (s, a)) ewalk)
	val walker = {vamp_q = qwalk, vamp_s = swalk}
	val (_, _) = (walk_in_class walker (kp, ()))
    in
	()
    end)

(* Resolves variable references in a package/instance.  It returns
   true if some instances are processed, so that it can repeat the
   process until it stabilizes.  It, with scanning=true, processes all
   instances, because the building routine may leave some instances in
   a partially resolved state (such as simple-types, whose value
   attribute is only resolved). *)

fun bind_in_instance (scanning : bool) k0 = (
    if (class_is_outer_alias k0) then
	false
    else if (class_is_enumerator_definition k0) then
	false
    else if (class_is_package k0) then
	false
    else if ((not scanning) andalso (step_is_at_least E5 k0)) then
	false
    else
	let
	    val _ = if (step_is_at_least E3 k0) then () else raise Match
	    val _ = if (not (class_is_primitive k0)) then () else raise Match

	    val ctx = {k = k0}
	    val subj = (subject_of_class k0)
	    val binder = (make_reference k0 false)
	    val k1 = (bind_in_class ctx binder k0)
	    val _ = if ((cook_step k1) = E5) then () else raise Match
	    val _ = (store_to_instance_tree subj k1)
	    val _ = (secure_references_in_class k1)
	in
	    if ((kind_is_record k1) andalso (class_is_instance k1)) then
		let
		    val record = (class_name_of_instance k1)
		    val var = (subject_as_reference record)
		    val ctx = k1
		    val _ = (secure_reference ctx false var)
		in
		    true
		end
	    else
		true
	end)

(* Resolves variables in packages/instances.  It skips classes which
   are named but are not used as packages (which have the step=E0).
   It accesses the component slot after processing the class. *)

fun bind_instances_loop (scanning : bool) node0 = (
    let
	val (subj, kx, cx) = node0
	val kp = (! kx)

	val _ = if ((cook_step kp) <> E0) then () else raise Match
	val _ = if ((class_is_package kp) orelse (step_is_at_least E3 kp))
		then () else raise Match

	val changes0 = (bind_in_instance scanning kp)
	(* KEEP ORDERING. *)
	val c0 = (! cx)
	val components = (List.filter (not o component_is_outer_alias) c0)

	val _ = if (null components) then ()
		else if (not (class_is_simple_type kp)) then ()
		else if (class_is_enum kp) then ()
		else raise error_attribute_access_to_simple_type

	val changes1
	    = (List.concat
		   (map (fn (Slot (v, dim, nodes, dummy)) =>
			    (map (bind_instances_loop scanning) nodes))
			components))
    in
	(List.exists (fn x => x) (changes0 :: changes1))
    end)

(* Binds variables in the model.  Call it with true.  It repeatedly
   calls the bind procedure until settled, because values and
   equations in accessed instances introduce new references. *)

fun bind_model scanning = (
    let
	val changes0 = (bind_instances_loop scanning instance_tree)
	val changes1 = (bind_instances_loop scanning class_tree)
    in
	if (changes0 orelse changes1) then
	    (bind_model false)
	else
	    ()
    end)

(* ================================================================ *)

fun replace_outer_in_instance (k0, acc0) = (
    if (class_is_outer_alias k0) then
	acc0
    else if (class_is_enumerator_definition k0) then
	acc0
    else if (class_is_package k0) then
	acc0
    else
	let
	    val _ = if (not (class_is_primitive k0)) then () else raise Match
	in
	    let
		val subj = (subject_of_class k0)
		val efix = (fn (w, _) => ((replace_outer_reference w), ()))
		val ewalk = (walk_in_expression efix)
		val qwalk = (walk_in_equation (fn (q, a) => (q, a)) ewalk)
		val swalk = (walk_in_statement (fn (s, a) => (s, a)) ewalk)
		val walker = {vamp_q = qwalk, vamp_s = swalk}
		val (k1, _) = (walk_in_class walker (k0, ()))
		val _ = (store_to_instance_tree subj k1)
	    in
		acc0
	    end
	end)

fun replace_outer () = (
    ignore (traverse_tree replace_outer_in_instance (instance_tree, [])))

(* ================================================================ *)

end
