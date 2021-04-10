(* message.sml -*-Coding: us-ascii-unix;-*- *)
(* Copyright (C) 2018-2021 RIKEN R-CCS *)

(* ERROR EXCEPTIONS/MESSAGES. *)

structure message = struct

open plain
open ast
open common

(* ================================================================ *)

val error_internal = Fail "(internal)"
val NOTYET = Fail "(internal) notyet"

val error_already_issued = Match
val error_never_happen = Match
val error_entity_exists = Match

val error_name_is_empty = (Fail "name is empty")

fun error_name_not_found id k = (
    Fail ("name ("^ (id_to_string id) ^") not found in "^
	  (class_print_name k)))

fun error_class_name_not_found (n : name_t) k = (
    Fail ("class name ("^ (name_to_string n)
	  ^") not found in "^ (class_print_name k)))

fun error_class_not_found (n : name_t) _ = (
    Fail ("class not found"))

fun error_name_not_found_up_to_top_level qn = (
    Fail ("Name ("^ (tag_to_string qn) ^") not found"))

fun error_variable_name_not_found id k = (
    Fail ("variable name ("^ (id_to_string id)
	  ^") not found in "^ (class_print_name k)))

fun error_name_is_class id k = (
    Fail ("a class name instead of a variable name ("^ (id_to_string id)
	  ^") found in "^ (class_print_name k)))

fun error_name_is_state id k = (
    Fail ("a class name instead of a variable name ("^ (id_to_string id)
	  ^") found in "^ (class_print_name k)))

fun error_file_for_class_not_found qn = (
    Fail ("File not found for class ("^ (tag_to_string qn) ^")"))

fun error_tag_not_found__ (Ctag nn) = (
    Fail ("class name ("^ (tag_to_string (Ctag nn)) ^") not found"))

fun error_class_loaded_but_missing s = (
    Fail ("load_class ("^ s ^")" ^" file loaded, but class not found"))

fun error_state_found_for_class (Name cn) k = (
    Fail ("class name ("^ (name_to_string (Name cn))
	  ^") not found in "^ (class_print_name k)))

fun error_variable_found_for_class__ (Name cn) k = (
    Fail ("variable found instead of a class ("^ (name_to_string (Name cn))
	  ^") in "^ (class_print_name k)))

fun error_outer_in_package d b = (
    Fail ("outer in a class as a package use"))

fun error_incompatible_outers d0 d1 = Match
fun error_no_import_name v = Match
fun error_inner_class v = Match
val error_variable_in_static_class = Match
fun error_duplicate_declarations v = Match

val error_constraint_with_subscripts = Match
(*Fail "constraint with subscripts"*)

fun error_replaceable_base context = (
    Fail ("a replaceable class is used as a base"))

fun warn_classes_similar k0 k1 = (
    print (";; "^ "Warning: similar base classes\n"))

fun warn_no_compatibility_test () = (
    if false then
	print (";; "^ "Warning: no compatibility test yet\n")
    else
	())

fun warn_no_array_compatibility_test () = (
    if false then
	print (";; "^ "Warning: no array compatibility test yet\n")
    else
	())

fun warn_skip_file_in_package_directory k = (
    print (";; "^ "Warning: Package directory entry is skipped for "^
	   (name_of_displaced k) ^"\n"))

fun warn_skip_directory_entries k = (
    print (";; "^ "Warning: Ignore directory entries for "^
	   (tag_to_string (tag_of_body k)) ^"\n"))

fun warn_drop_annotations () = (
    print (";; "^ "Warning: Drop annotations\n"))

fun warn_drop_comments () = (
    print (";; "^ "Warning: Drop comments\n"))

val error_each_in_redeclare = Fail "each in renaming modifier"

val error_each_is_needed = Fail "each is required"

fun error_modifiers_to_der m = Fail "applying modifiers to der"

fun error_subscripts_to_der s = Fail "applying subscripts to der"

val error_modifiers_remain = Fail "some modifiers remain"

val error_unhandled_renaming = Fail "(internal) renaming handled elsewhere"

fun error_redeclare_to_class m = Fail "object redeclaration to class"

fun error_redefine_to_state m = Fail "object redeclaration to class"

fun error_value_to_class m = Fail "object redeclaration to class"

val warning_multiple_extends = "Warning: multiple extends of a single base"

fun error_cycle_in_lookup_dependency k = Match

val error_condition_in_modifiers = Match

fun error_no_replaceables r k = Match

val error_condition_in_modifiers = Match

val error_constraint_with_subscripts = Match

fun error_cycle_in_extends_relation siblings = (
    Fail "cycle_in_extends_relation")

val error_both_value_and_initializer = Match

val error_bad_value_parameter = Match

fun warn_final_incompatible () = (
    print "WARNING: Finals are maybe incompatible\n")

val error_not_replaceable = Match

fun warn_redeclaration_compatibility () = (
    print "WARNING: Redeclaration may be non-portable\n")

fun warn_compatibility_not_checked () = (
    print "WARNING: Compatibility is not checked\n")

val error_incompatible_analogical = Fail "Analogical incompatible"

val error_incompatible_variability = Fail "Variability incompatible"

val error_incompatible_mode = Fail "Both input and output"

val error_split_named_entry = Fail "splitting named entry"

fun warn_split_named_entry () = (
    print "WARNING: EACH ASSUMED\n")

fun error_inner_outer_in_package v = Match

fun error_unhandled_outer d = Match

fun warn_no_inner (ne : naming_element_t) = (
    print ("WARNING: No matching inner is found for "^
	   (id_to_string (name_of_naming_element ne)) ^" in ?\n"))

val error_undefined_variable = Match

val error_non_constant_conditional = Match

fun error_constant_required variability = Match

val error_no_value_to_constant = Match

fun error_bad_u_operator__ n opr = Match

fun error_bad_b_operator__ n opr = Match

fun error_bad_relational_operator n opr = Match

val error_bad_b_operator_types = Match

val error_no_qualified_name = Match

val error_empty_name = (Fail "empty name")

fun warn_ignore_fixed () = (
    print (";; "^ "Warning: the value in the attribute fixed ignored\n"))

fun warn_cycle_in_lookup () = (
    print "WARNING: A cycle in a lookup for importing/extending\n")

fun warn_skip_lookup_in_bases () = (
    print "WARNING: Bases are skipped in a lookup\n")

fun warn_cycle_in_dimensions () = (
    print "WARNING: A maybe circular dependency in dimension expressions\n")

val error_bad_array_dimension = Match

val error_non_constant_array_dimension = Match

val error_instance_reference_thru_package = Match

val error_attribute_access_to_simple_type = Match

val error_subscripts_to_package = Match

val error_package_name_not_found = Match

val error_global_name_not_found = Match

val error_subscripts_to_package = Match

val error_name_not_found_in_package = Match

val error_non_constant_in_package = Match

val error_no_value_in_rhs = Match

val error_many_values_in_rhs = Match

val error_continuous_integer = Match

val error_continuous_boolean = Match

val error_continuous_string = Match

val error_no_instance_found = Match

val error_no_arguments_to_function = Match

val error_bad_number_of_arguments_to_function = Match

val error_bad_array_constructor = Match

val error_bad_syntax = Match

val error_tuple_in_rhs = Match

val error_varied_array_dimensions = Match

val error_bad_triple = Match

val error_size_of_scalar = Match

val error_size_with_bad_index = Match

val error_enum_unspecified = Match

val error_enum_empty = Match

val error_bad_index = Match

val error_split_to_scalar = Match

val error_syntax = Match

val error_dimensions_mismatch = Match

val error_different_enumerations = Match

val error_out_of_range = Match

val error_size_in_real = Match

val error_unknown_size = Match

val error_bad_size = Match

val error_access_to_empty_array = Match

val error_modifier_to_attribute = Match

val error_enum_mismatch = Match

val error_name_is_not_class = Match

fun error_outer_package context = Match

val error_array_modifier_to_attribute = Match

val error_bad_modifier_to_attribute = Match

val error_cycle_in_lookup_enclosing = Match

val error_subscripts_to_iterator = Match

val error_components_to_iterator = Match

val error_component_not_found = Match

val error_subscripts_to_scalar = Match

val error_split_array_dimension = Match

val error_indexing_to_scalar = Match

val error_no_instantiated_instance = Match

val error_not_found_in_table = Fail "(internal) not found"

fun error_duplicate_definitions k = (
    Fail ("duplicate definitions ("^ (tag_to_string (tag_of_body k)) ^")"))

val error_duplicate_inner_outer = Match

val error_conditional_containing_connect = Match

val error_non_boolean = Match

val error_range_iterator = Match

val error_non_scalar_literal = Match

val error_not_vector = Match

val error_range_on_array = Match

val error_range_on_class = Match

val error_bad_reference = Match

val error_varying_iterator_range = Match

val error_unknown_iterator_range = Match

val error_when_contains_connectors = Match

val error_connector_in_package = Match

val error_mutual_expandable_connectors = Match

val error_bad_dimension = Match

val error_empty_array_connector = Match

val error_nonunique_dimension = Match

val error_bad_call_of_cardinality = Match

val error_cardinality_in_declaration = Match

val error_connector_is_not_record = Match

val error_mismatch_connection_list = Match

val error_mismatch_connector_arrays = Match

val error_connect_rule_conflict = Match

val error_connect_rule_disagree = Match

val error_connect_record_disagree = Match

val error_multiple_flow_variables = Match

val error_missing_flow_variables = Match

fun error_bad_intrinsic_call name = Match

val error_conditional_is_not_determined = Match

val error_model_is_array = Match

val error_conditional_on_redeclared_state = Match

end
