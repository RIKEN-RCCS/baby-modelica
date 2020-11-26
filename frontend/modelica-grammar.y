/* modelica-grammar.y  -*-Mode: Fundamental;-*- */
/* Copyright (C) 2018-2020 RIKEN R-CCS */

%{

(* Parser rules of Modelica-3.4. *)

(* Load "ast.sml", "parser.sml", and "lexer.sml" in this order,
   because the generated "parser.sml" depends on "ast.sml". *)

structure parser :
sig

type yylexstate_t = {s : TextIO.instream, line : int, column : int,
		     unget : char list, end_as_id : bool}
type yyv_t = ast.vs_t

type yylex_t = yylexstate_t -> int * yyv_t * yylexstate_t
type yysm_t = {
  yydebug : bool ref,
  yystate : int ref,
  yynerrs : int ref,
  yyerrflag : int ref,
  yychar : int ref,
  yysp : int ref,
  yyval : yyv_t ref,
  yylval : yyv_t ref,
  yyss : int Array.array,
  yyvs : yyv_t Array.array,
  yylexstate : yylexstate_t ref}

val yyparse : bool -> yylex_t -> yylexstate_t -> yysm_t
val yyvs_ref : yysm_t -> int -> yyv_t

val ADD_OPERATOR : int
val ALGORITHM : int
val AND : int
val ANNOTATION : int
val BLOCK : int
val BREAK : int
val CLASS : int
val CONNECT : int
val CONNECTOR : int
val CONSTANT : int
val CONSTRAINEDBY : int
val DEF : int
val DER : int
val DISCRETE : int
val EACH : int
val ELSE : int
val ELSEIF : int
val ELSEWHEN : int
val ENCAPSULATED : int
val END : int
val ENUMERATION : int
(*val EOF : int*)
val EQUATION : int
val EXP_OPERATOR : int
val EXPANDABLE : int
val EXTENDS : int
val EXTERNAL : int
val FALSE : int
val FINAL : int
val FLOW : int
val FOR : int
val FUNCTION : int
val IDENT : int
val IF : int
val IMPORT : int
val IMPURE : int
val IN : int
(*val INITIAL : int*)
val INITIALALGORITHM : int
val INITIALEQUATION : int
val INNER : int
val INPUT : int
val LOOP : int
val MODEL : int
val MUL_OPERATOR : int
val NOT : int
val OPERATOR : int
val OR : int
val OUTER : int
val OUTPUT : int
val PACKAGE : int
val PARAMETER : int
val PARTIAL : int
val PROTECTED : int
val PUBLIC : int
val PURE : int
val RECORD : int
val REDECLARE : int
val RELATIONAL_OPERATOR : int
val REPLACEABLE : int
val RETURN : int
val STREAM : int
val STRING : int
val THEN : int
val TRUE : int
val TYPE : int
val UNSIGNED_NUMBER : int
val WHEN : int
val WHILE : int
val WITHIN : int

end = struct

open ast

type yylexstate_t = {s : TextIO.instream, line : int, column : int,
		     unget : char list, end_as_id : bool}

val yylexstate_dummy = {s=TextIO.stdIn, line=0, column=0,
			unget=[#"_"], end_as_id=false}

type yyv_t = ast.vs_t

type yylex_t = yylexstate_t -> int * yyv_t * yylexstate_t

val yyvalue_null = (ast.VS_TOKEN "0")

fun set_end_as_id b {s=s0, line=l0, column=c0, unget=u0, end_as_id=_} = (
    {s=s0, line=l0, column=c0, unget=u0, end_as_id=b})

(* Use ++ instead of @ because @ is taken by byacc. *)

val op ++ = List.@
infixr 5 ++

%}

%start stored_definition

%union ast.vs_t {}

/* Token for syntactic values. */

/*%token <VS_TOKEN> EOF*/
%token <VS_TOKEN> IDENT
%token <VS_TOKEN> STRING
%token <VS_TOKEN> UNSIGNED_NUMBER

/* Token for keywords. */

%token <VS_TOKEN> ALGORITHM
%token <VS_TOKEN> AND
%token <VS_TOKEN> ANNOTATION
%token <VS_TOKEN> BLOCK
%token <VS_TOKEN> BREAK
%token <VS_TOKEN> CLASS
%token <VS_TOKEN> CONNECT
%token <VS_TOKEN> CONNECTOR
%token <VS_TOKEN> CONSTANT
%token <VS_TOKEN> CONSTRAINEDBY
%token <VS_TOKEN> DER
%token <VS_TOKEN> DISCRETE
%token <VS_TOKEN> EACH
%token <VS_TOKEN> ELSE
%token <VS_TOKEN> ELSEIF
%token <VS_TOKEN> ELSEWHEN
%token <VS_TOKEN> ENCAPSULATED
%token <VS_TOKEN> END
%token <VS_TOKEN> ENUMERATION
%token <VS_TOKEN> EQUATION
%token <VS_TOKEN> EXPANDABLE
%token <VS_TOKEN> EXTENDS
%token <VS_TOKEN> EXTERNAL
%token <VS_TOKEN> FALSE
%token <VS_TOKEN> FINAL
%token <VS_TOKEN> FLOW
%token <VS_TOKEN> FOR
%token <VS_TOKEN> FUNCTION
%token <VS_TOKEN> IF
%token <VS_TOKEN> IMPORT
%token <VS_TOKEN> IMPURE
%token <VS_TOKEN> IN
%token <VS_TOKEN> INITIALEQUATION
%token <VS_TOKEN> INITIALALGORITHM
%token <VS_TOKEN> INNER
%token <VS_TOKEN> INPUT
%token <VS_TOKEN> LOOP
%token <VS_TOKEN> MODEL
%token <VS_TOKEN> NOT
%token <VS_TOKEN> OPERATOR
%token <VS_TOKEN> OR
%token <VS_TOKEN> OUTER
%token <VS_TOKEN> OUTPUT
%token <VS_TOKEN> PACKAGE
%token <VS_TOKEN> PARAMETER
%token <VS_TOKEN> PARTIAL
%token <VS_TOKEN> PROTECTED
%token <VS_TOKEN> PUBLIC
%token <VS_TOKEN> PURE
%token <VS_TOKEN> RECORD
%token <VS_TOKEN> REDECLARE
%token <VS_TOKEN> REPLACEABLE
%token <VS_TOKEN> RETURN
%token <VS_TOKEN> STREAM
%token <VS_TOKEN> THEN
%token <VS_TOKEN> TRUE
%token <VS_TOKEN> TYPE
%token <VS_TOKEN> WHEN
%token <VS_TOKEN> WHILE
%token <VS_TOKEN> WITHIN

/* Token for syntactic characters. */

%token <VS_TOKEN> DEF
/*%token EQ*/
/*%token COLON*/
/*%token SEMICOLON*/
/*%token DOT*/
/*%token COMMA*/
/*%token LP*/
/*%token RP*/
/*%token LB*/
/*%token RB*/
/*%token LC*/
/*%token RC*/
%token <VS_TOKEN> RELATIONAL_OPERATOR
%token <VS_TOKEN> ADD_OPERATOR
%token <VS_TOKEN> MUL_OPERATOR
%token <VS_TOKEN> EXP_OPERATOR

%type <VS_CLASS_DEFINITION> class_definition
%type <VS_CLASS_DEFINITION> short_class_definition
%type <VS_CLASS_DEFINITION_LIST> class_definition_loop_
%type <VS_CLASS_PREFIX> class_kind_
%type <VS_CLASS_PREFIX> class_prefixes
%type <VS_CLASS_SPECIFIER> class_specifier
%type <VS_CLASS_SPECIFIER> der_class_specifier
%type <VS_CLASS_SPECIFIER> long_class_specifier
%type <VS_CLASS_SPECIFIER> short_class_specifier
%type <VS_COMPONENT> component_clause_1
%type <VS_COMPONENT_LIST> component_clause
%type <VS_COMPONENT_PREFIX> type_prefix
%type <VS_COMPONENT_TYPE_SPECIFIER> type_prefix_type_specifier_
%type <VS_CONSTRAINT> constraining_clause
%type <VS_DECLARATION> component_declaration
%type <VS_DECLARATION> component_declaration_1
%type <VS_DECLARATION> declaration
%type <VS_DECLARATION_LIST> component_list
%type <VS_EACH_OR_FINAL> optional_each_or_final_
%type <VS_ELEMENT> algorithm_section
%type <VS_ELEMENT> equation_section
%type <VS_ELEMENT> extends_clause
%type <VS_ELEMENT> external_part_
%type <VS_ELEMENT_LIST> composition
%type <VS_ELEMENT_LIST> element
%type <VS_ELEMENT_LIST> element_list
%type <VS_ELEMENT_LIST> element_list_loop_
%type <VS_ELEMENT_LIST> import_clause
%type <VS_ELEMENT_PREFIXES> element_prefix_
%type <VS_EQUATION_LIST> equation
%type <VS_EQUATION_LIST> equation_loop_
%type <VS_EXPRESSION> argument_fn_
%type <VS_EXPRESSION> arithmetic_expression
%type <VS_EXPRESSION> component_reference
%type <VS_EXPRESSION> condition_attribute
%type <VS_EXPRESSION> expression
%type <VS_EXPRESSION> factor
%type <VS_EXPRESSION> function_argument
%type <VS_EXPRESSION> logical_expression
%type <VS_EXPRESSION> logical_factor
%type <VS_EXPRESSION> logical_term
%type <VS_EXPRESSION> named_argument
%type <VS_EXPRESSION> primary
%type <VS_EXPRESSION> relation
%type <VS_EXPRESSION> simple_expression
%type <VS_EXPRESSION> term
%type <VS_EXPRESSION> array_arguments
%type <VS_EXPRESSION_LIST> array_arguments_non_first
%type <VS_EXPRESSION_LIST> array_subscripts
%type <VS_EXPRESSION_LIST> array_subscripts_loop_
%type <VS_EXPRESSION_LIST> expression_list
%type <VS_EXPRESSION_LIST> function_arguments
%type <VS_EXPRESSION_LIST> function_arguments_non_first
%type <VS_EXPRESSION_LIST> function_call_args
%type <VS_EXPRESSION_LIST> named_arguments
%type <VS_EXPRESSION_LIST> output_expression_list
%type <VS_EXPRESSION_LIST> subscript
%type <VS_EXPRESSION_LIST_LIST> expression_list_rows_
%type <VS_FOR_INDEX> for_index
%type <VS_FOR_INDEX_LIST> for_indices
%type <VS_ID_LIST> ident_list_
%type <VS_ID_LIST> import_list
%type <VS_IDENT_COMMENT_LIST> enum_list
%type <VS_IDENT_COMMENT_LIST> enumeration_literal
%type <VS_LANGUAGE> language_specification
%type <VS_MAIN> stored_definition
%type <VS_MODIFIER> argument
%type <VS_MODIFIER> element_modification
%type <VS_MODIFIER> element_modification_or_replaceable
%type <VS_MODIFIER> element_redeclaration
%type <VS_MODIFIER> element_replaceable
%type <VS_MODIFIER_LIST> argument_list
%type <VS_MODIFIER_LIST> class_modification
%type <VS_MODIFIER_LIST> modification
%type <VS_NAME> name
%type <VS_NAME> type_specifier
%type <VS_NAME> within_clause_
%type <VS_PREFIX_REDECLARE> redeclare_
%type <VS_STATEMENT> external_function_call
%type <VS_STATEMENT> for_statement
%type <VS_STATEMENT> if_statement
%type <VS_STATEMENT> statement_body_
%type <VS_STATEMENT> when_statement
%type <VS_STATEMENT> while_statement
%type <VS_STATEMENT_LIST> statement
%type <VS_STATEMENT_LIST> statement_loop_
%type <VS_STRING_LIST> string_comment
%type <VS_STRING_LIST> string_comment_list_
%type <VS_TEST_EQUATIONS_LIST> else_part_equation_
%type <VS_TEST_EQUATIONS_LIST> elseif_equation_loop_
%type <VS_TEST_EQUATIONS_LIST> elsewhen_equation_loop_
%type <VS_TEST_EXPRESSION_LIST> elseif_expression_loop_
%type <VS_TEST_STATEMENTS_LIST> else_part_statement_
%type <VS_TEST_STATEMENTS_LIST> elseif_statement_loop_
%type <VS_TEST_STATEMENTS_LIST> elsewhen_statement_loop_
%type <VS_TYPE_FLOW_OR_STREAM> flow_or_stream_
%type <VS_TYPE_INPUT_OR_OUTPUT> base_prefix
%type <VS_TYPE_VARIABILITY> variability_
%type <VS_ANNOTATION> annotation
%type <VS_COMMENT> comment
%type <VS_EQUATION> connect_clause
%type <VS_EQUATION> equation_body_
%type <VS_EQUATION> for_equation
%type <VS_EQUATION> if_equation
%type <VS_EQUATION> when_equation
%type <VS_NOTHING> subscripts_in_
%type <VS_NOTHING> subscripts_out_

%%

/* Rules from Modelica Language Specification 3.4 */

/* B.2.1 Stored Definition - Within */

/* See (13.2.2.3 The within Clause). */

stored_definition
	: class_definition_loop_ {
		((Name []), $1)}
	| within_clause_ class_definition_loop_ {
		($1, $2)}
	;

/* See (13.2.2.3 The within Clause). */

within_clause_
	: WITHIN ";" {
		(Name [])}
	| WITHIN name ";" {
		$2}
	;

class_definition_loop_
	: /*empty*/ {
		[]}
	| class_definition_loop_ class_definition ";" {
		($1 ++ [$2])}
	| class_definition_loop_ FINAL class_definition ";" {
		($1 ++ [set_class_final $3])}
	;

/* B.2.2 Class Definition */

/* class-definition's appear in a toplevel stored-definition and in
   class components as element's. */

class_definition
	: class_prefixes class_specifier {
		(set_class_prefixes $1 $2)}
	| ENCAPSULATED class_prefixes class_specifier {
		let
		    val (k, p) = $2
		    val pp = (k, (set_encapsulated p))
		in
		    (set_class_prefixes pp $3)
		end}
	;

class_prefixes
	: class_kind_
	| PARTIAL class_kind_ {
		case $2 of
		    (k, p) => (k, (set_partial p))}
	;

/* A pair operator-function is a combination of an operator and a
   function.  See (4.6 Specialized Classes). */

class_kind_
	: CLASS {
		(Class, no_class_prefixes)}
	| MODEL {
		(Model, no_class_prefixes)}
	| RECORD {
		(Record, no_class_prefixes)}
	| OPERATOR RECORD {
		(Operator_Record, no_class_prefixes)}
	| BLOCK {
		(Block, no_class_prefixes)}
	| CONNECTOR {
		(Connector, no_class_prefixes)}
	| EXPANDABLE CONNECTOR {
		(Expandable_Connector, no_class_prefixes)}
	| TYPE {
		(Type, no_class_prefixes)}
	| PACKAGE {
		(Package, no_class_prefixes)}
	| FUNCTION {
		((Function false), no_class_prefixes)}
	| PURE FUNCTION {
		((Function true), no_class_prefixes)}
	| IMPURE FUNCTION {
		((Function false), no_class_prefixes)}
	| OPERATOR FUNCTION {
		((Operator_Function false), no_class_prefixes)}
	| PURE OPERATOR FUNCTION {
		((Operator_Function true), no_class_prefixes)}
	| IMPURE OPERATOR FUNCTION {
		((Operator_Function false), no_class_prefixes)}
	| OPERATOR {
		(Operator, no_class_prefixes)}
	;

class_specifier
	: long_class_specifier
	| short_class_specifier
	| der_class_specifier
	;

/* A class name is an ID.  It will be attached by an enclosing class
   name (which is bad_tag, here) later at after parsing.  The 2nd and
   3rd rules are for an extends-redeclaration.  See (7.3.1 The class
   extends Redeclaration Mechanism). */

long_class_specifier
	: IDENT string_comment composition END IDENT {
		if (not ($1 = $5)) then
		    (syntax_error "END does not match")
		else
		    Defclass ((Id $1, bad_tag),
			      (make_predefinition_body MAIN $3
			       (Annotation []) (Comment $2)))}
	| EXTENDS IDENT string_comment composition END IDENT {
		if (not ($2 = $6)) then
		    (syntax_error "END does not match")
		else
		    let
			val k0 = (make_predefinition_body MAIN $4
				  (Annotation []) (Comment $3))
			val base = (Def_Name (Name [$2]), [])
		    in
			Defclass ((Id $2, bad_tag),
				  Def_Extending (false, base, k0))
		    end}
	| EXTENDS IDENT class_modification string_comment composition END IDENT {
		if (not ($2 = $7)) then
		    (syntax_error "END does not match")
		else
		    let
			val k0 = (make_predefinition_body MAIN $5
				  (Annotation []) (Comment $4))
			val base = (Def_Name (Name [$2]), $3)
		    in
			Defclass ((Id $2, bad_tag),
				  Def_Extending (false, base, k0))
		    end}
	;

/* "enumeration(:)" is an unspecified list, which must be redeclared.
   See (4.8.5 Enumeration Types). */

short_class_specifier
	: IDENT "=" ENUMERATION "(" ":" ")" comment {
		let
		    val body = [Element_Enumerators NONE]
		    val (aa, ww) = $7
		in
		    Defclass ((Id $1, bad_tag),
			      (make_predefinition_body ENUM body aa ww))
		end}
	| IDENT "=" ENUMERATION "(" ")" comment {
		let
		    val body = [Element_Enumerators (SOME [])]
		    val (aa, ww) = $6
		in
		    Defclass ((Id $1, bad_tag),
			      (make_predefinition_body ENUM body aa ww))
		end}
	| IDENT "=" ENUMERATION "(" enum_list ")" comment {
		let
		    val body = [Element_Enumerators (SOME $5)]
		    val (aa, ww) = $7
		in
		    Defclass ((Id $1, bad_tag),
			      (make_predefinition_body ENUM body aa ww))
		end}
	| IDENT "=" base_prefix type_specifier comment {
		let
		    val k = Def_Name $4
		    val (aa, ww) = $5
		in
		    Defclass ((Id $1, bad_tag),
			      (make_short_predefinition k $3 ([], []) aa ww))
		end}
	| IDENT "=" base_prefix type_specifier class_modification comment {
		let
		    val k = Def_Name $4
		    val (aa, ww) = $6
		in
		    Defclass ((Id $1, bad_tag),
			      (make_short_predefinition k $3 ([], $5) aa ww))
		end}
	| IDENT "=" base_prefix type_specifier array_subscripts comment {
		let
		    val k = Def_Name $4
		    val (aa, ww) = $6
		in
		    Defclass ((Id $1, bad_tag),
			      (make_short_predefinition k $3 ($5, []) aa ww))
		end}
	| IDENT "=" base_prefix type_specifier array_subscripts class_modification comment {
		let
		    val k = Def_Name $4
		    val (aa, ww) = $7
		in
		    Defclass ((Id $1, bad_tag),
			      (make_short_predefinition k $3 ($5, $6) aa ww))
		end}
	;

/* Partial "der(v)" can take multiple parameters.  See (12.7.2 Partial
   Derivatives of Functions). */

der_class_specifier
	: IDENT "=" DER "(" type_specifier "," ident_list_ ")" comment {
		let
		    val (aa, ww) = $9
		in
		    Defclass ((Id $1, bad_tag),
			      Def_Der (bad_tag, bad_class, $5, $7, aa, ww))
		end}
	;

ident_list_
	: IDENT {
		[Id $1]}
	| ident_list_ "," IDENT {
		($1 ++ [Id $3])}
	;

base_prefix
	: /*empty*/ {
		Modeless}
	| INPUT {
		Input}
	| OUTPUT {
		Output}
	;

enum_list
	: enumeration_literal
	| enum_list "," enumeration_literal {
		($1 ++ $3)}
	;

enumeration_literal
	: IDENT comment {
		let
		    val (aa, ww) = $2
		in
		    [(Id $1, aa, ww)]
		end}
	;

composition
	: element_list_loop_
	| element_list_loop_ annotation ";" {
		($1 ++ [Element_Annotation $2])}
	| element_list_loop_ EXTERNAL external_part_ ";" {
		($1 ++ [$3])}
	| element_list_loop_ EXTERNAL external_part_ ";" annotation ";" {
		($1 ++ [$3] ++ [Element_Annotation $5])}
	;

/* The default visibility is public.  See (4.1 Access Control).
   Public is specifed in rules element, import-clause, extends-clause,
   equation-section, and algorithm-section. */

element_list_loop_
	: element_list
	| element_list_loop_ PUBLIC element_list {
		($1 ++ (map (set_visibility Public) $3))}
	| element_list_loop_ PROTECTED element_list {
		($1 ++ (map (set_visibility Protected) $3))}
	| element_list_loop_ equation_section {
		($1 ++ [$2])}
	| element_list_loop_ algorithm_section {
		($1 ++ [$2])}
	;

/* See (12.9 External Function Interface). */

external_part_
	: /*empty*/ {
		Element_External (NONE, NONE, Annotation [])}
	| annotation {
		Element_External (NONE, NONE, $1)}
	| language_specification {
		Element_External (SOME $1, NONE, Annotation [])}
	| language_specification annotation {
		Element_External (SOME $1, NONE, $2)}
	| external_function_call {
		Element_External (NONE, SOME $1, Annotation [])}
	| external_function_call annotation {
		Element_External (NONE, SOME $1, $2)}
	| language_specification external_function_call {
		Element_External (SOME $1, SOME $2, Annotation [])}
	| language_specification external_function_call annotation {
		Element_External (SOME $1, SOME $2, $3)}
	;

language_specification
	: STRING {
		$1}
	;

external_function_call
	: IDENT "(" ")" {
		St_Call ([], Vref (NONE, [(Id $1, [])]), [],
			 Annotation [], Comment [])}
	| IDENT "(" expression_list ")" {
		St_Call ([], Vref (NONE, [(Id $1, [])]), $3,
			 Annotation [], Comment [])}
	| component_reference "=" IDENT "(" ")" {
		St_Call ([$1], Vref (NONE, [(Id $3, [])]), [],
			 Annotation [], Comment [])}
	| component_reference "=" IDENT "(" expression_list ")" {
		St_Call ([$1], Vref (NONE, [(Id $3, [])]), $5,
			 Annotation [], Comment [])}
	;

element_list
	: /*empty*/ {
		[]}
	| element_list element ";" {
		($1 ++ $2)}
	;

element
	: import_clause {
		$1}
	| extends_clause {
		[$1]}
	| redeclare_ element_prefix_ component_clause {
		let
		    val h = NONE
		in
		    if (#Redeclare $1) then
			(map (fn c => Redeclare_State (Public, $2, c, h)) $3)
		    else
			(map (fn c => Element_State (Public, $2, c, h)) $3)
		end}
	| redeclare_ element_prefix_ REPLACEABLE component_clause {
		let
		    val r = (set_element_prefix_replaceable $2)
		    val h = NONE
		in
		    if (#Redeclare $1) then
			(map (fn c => Redeclare_State (Public, r, c, h)) $4)
		    else
			(map (fn c => Element_State (Public, r, c, h)) $4)
		end}
	| redeclare_ element_prefix_ REPLACEABLE component_clause constraining_clause comment {
		let
		    val r = (set_element_prefix_replaceable $2)
		    val (t, m) = $5
		    val (aa, ww) = $6
		    val h = SOME (t, m, aa, ww)
		in
		    if (#Redeclare $1) then
			(map (fn c => Redeclare_State (Public, r, c, h)) $4)
		    else
			(map (fn c => Element_State (Public, r, c, h)) $4)
		end}
	| redeclare_ element_prefix_ class_definition {
		let
		    val h = NONE
		in
		    if (#Redeclare $1) then
			[Redefine_Class (Public, $2, $3, h)]
		    else
			[Element_Class (Public, $2, $3, h)]
		end}
	| redeclare_ element_prefix_ REPLACEABLE class_definition {
		let
		    val r = (set_element_prefix_replaceable $2)
		    val h = NONE
		in
		    if (#Redeclare $1) then
			[Redefine_Class (Public, r, $4, h)]
		    else
			[Element_Class (Public, r, $4, h)]
		end}
	| redeclare_ element_prefix_ REPLACEABLE class_definition constraining_clause comment {
		let
		    val r = (set_element_prefix_replaceable $2)
		    val (t, m) = $5
		    val (aa, ww) = $6
		    val h = SOME (t, m, aa, ww)
		in
		    if (#Redeclare $1) then
			[Redefine_Class (Public, r, $4, h)]
		    else
			[Element_Class (Public, r, $4, h)]
		end}
	;

redeclare_
	: /*empty*/ {
		{Redeclare=false}}
	| REDECLARE {
		{Redeclare=true}}
	;

element_prefix_
	: /*empty*/ {
		{Final=false, Inner=false, Outer=false,
		 Replaceable=false}}
	| OUTER {
		{Final=false, Inner=false, Outer=true,
		 Replaceable=false}}
	| INNER {
		{Final=false, Inner=true, Outer=false,
		 Replaceable=false}}
	| FINAL {
		{Final=true, Inner=false, Outer=false,
		 Replaceable=false}}
	| INNER OUTER {
		{Final=false, Inner=true, Outer=true,
		 Replaceable=false}}
	| FINAL INNER {
		{Final=true, Inner=true, Outer=false,
		 Replaceable=false}}
	| FINAL OUTER {
		{Final=true, Inner=false, Outer=true,
		 Replaceable=false}}
	| FINAL INNER OUTER {
		{Final=true, Inner=true, Outer=true,
		 Replaceable=false}}
	;

import_clause
	: IMPORT name comment {
		let
		    val (p, v) = (name_prefix $2)
		    val (aa, ww) = $3
		in
		    [Import_Clause (Public, p, SOME (v, v), aa, ww)]
		end}
	| IMPORT name "." "*" comment {
		let
		    val (p, v) = (name_prefix $2)
		    val (aa, ww) = $5
		in
		    [Import_Clause (Public, $2, NONE, aa, ww)]
		end}
	| IMPORT name "." "{" import_list "}" comment {
		let
		    val (aa, ww) = $7
		in
		    (map
			(fn v =>
			    (Import_Clause
				(Public, $2, SOME (v, v), aa, ww)))
		    $5)
		end}
	| IMPORT IDENT "=" name comment {
		let
		    val (p, v) = (name_prefix $4)
		    val (aa, ww) = $5
		in
		    [Import_Clause
			(Public, p, SOME (v, (Id $2)), aa, ww)]
		end}
	;

import_list
	: ident_list_
	;

/* B.2.3 Extends */

extends_clause
	: EXTENDS type_specifier {
		(Extends_Clause
		    (Public, ($2, []), Annotation []))}
	| EXTENDS type_specifier annotation {
		(Extends_Clause
		    (Public, ($2, []), $3))}
	| EXTENDS type_specifier class_modification {
		(Extends_Clause
		    (Public, ($2, $3), Annotation []))}
	| EXTENDS type_specifier class_modification annotation {
		(Extends_Clause
		    (Public, ($2, $3), $4))}
	;

constraining_clause
	: CONSTRAINEDBY type_specifier {
		(Def_Name $2, [])}
	| CONSTRAINEDBY type_specifier class_modification {
		(Def_Name $2, $3)}
	;

/* B.2.4 Component Clause */

component_clause
	: type_prefix_type_specifier_ component_list {
		(map (make_component_clause $1 []) $2)}
	| type_prefix_type_specifier_ array_subscripts component_list {
		(map (make_component_clause $1 $2) $3)}
	;

type_prefix_type_specifier_
	: type_prefix type_specifier {
		($1, $2)}
	;

type_prefix
	: flow_or_stream_ variability_ base_prefix {
		($1, $2, $3)}
	;

flow_or_stream_
	: /*empty*/ {
		Effort}
	| FLOW {
		Flow}
	| STREAM {
		Stream}
	;

/* See (4.4.4 Component Variability Prefixes). */

variability_
	: /*empty*/ {
		Continuous}
	| DISCRETE {
		Discrete}
	| PARAMETER {
		Parameter}
	| CONSTANT {
		Constant}
	;

component_list
	: component_declaration {
		[$1]}
	| component_list "," component_declaration {
		($1 ++ [$3])}
	;

component_declaration
	: declaration comment {
		let
		    val (aa, ww) = $2
		in
		    case $1 of
			(v, s, m, NONE, Annotation [], Comment []) =>
			    (v, s, m, NONE, aa, ww)
		      | _ => raise Match
		end}
	| declaration condition_attribute comment {
		let
		    val (aa, ww) = $3
		in
		    case $1 of
			(v, s, m, NONE, Annotation [], Comment []) =>
			    (v, s, m, SOME $2, aa, ww)
		      | _ => raise Match
		end}
	;

condition_attribute
	: IF expression {
		$2}
	;

declaration
	: IDENT {
		(Id $1, [], [], NONE, Annotation [], Comment [])}
	| IDENT modification {
		(Id $1, [], $2, NONE, Annotation [], Comment [])}
	| IDENT array_subscripts {
		(Id $1, $2, [], NONE, Annotation [], Comment [])}
	| IDENT array_subscripts modification {
		(Id $1, $2, $3, NONE, Annotation [], Comment [])}
	;

/* B.2.5 Modification */

/* Modifications appear as "IDENT modification" in declarations, or as
   "name modification" in element_modification. */

/* Are modifications (inside an argument-list) by ":=" deprecated?
   See (12.2 Function as a Specialized Class).  It states "A formal
   parameter or local variable may be initialized through a binding
   (=) of a default value in its declaration, see 12.4.4. Using
   assignment (:=) is deprecated." */

/* The 2nd form is for "Foo x(min=0)=10;", where it changes both of
   the value of x and its min attribute. */

modification
	: class_modification {
		$1}
	| class_modification "=" expression {
		($1 ++ [Mod_Value $3])}
	| "=" expression {
		[Mod_Value $2]}
	| DEF expression {
		[Mod_Value $2]}
	;

class_modification
	: "(" ")" {
		[]}
	| "(" argument_list ")" {
		$2}
	;

argument_list
	: argument {
		[$1]}
	| argument_list "," argument {
		($1 ++ [$3])}
	;

argument
	: element_redeclaration
	| element_modification_or_replaceable
	;

element_redeclaration
	: REDECLARE optional_each_or_final_ short_class_definition {
		Mod_Redefine ((set_modifier_prefixes false $2),
			      $3, NONE)}
	| REDECLARE optional_each_or_final_ component_clause_1 {
		Mod_Redeclare ((set_modifier_prefixes false $2),
			      $3, NONE)}
	| REDECLARE optional_each_or_final_ element_replaceable {
		case $3 of
		    Mod_Redefine (_, d, r) =>
			Mod_Redefine ((set_modifier_prefixes true $2),
				      d, r)
		  | Mod_Redeclare (_, d, r) =>
			Mod_Redeclare ((set_modifier_prefixes true $2),
				       d, r)
		  | _ => raise Match}
	;

element_modification_or_replaceable
	: optional_each_or_final_ element_modification {
		case $2 of
		    Mod_Entry (_, n, m, c) =>
			Mod_Entry ($1, n, m, c)
		  | _ => raise Match}
	| optional_each_or_final_ element_replaceable {
		case $2 of
		    Mod_Redefine (_, d, r) =>
			Mod_Redefine ((set_modifier_prefixes true $1),
				      d, r)
		  | Mod_Redeclare (_, d, r) =>
			Mod_Redeclare ((set_modifier_prefixes true $1),
				       d, r)
		  | _ => raise Match}
	;

/* An empty modification can occur for redeclaring a class (e.g.,
   redeclare~A~x;). */

element_modification
	: name string_comment {
		Mod_Entry (no_each_or_final, $1, [], Comment $2)}
	| name modification string_comment {
		Mod_Entry (no_each_or_final, $1, $2, Comment $3)}
	;


/* It makes a modifier with "replaceable" be with "redeclare".  (See
   7.3 Redeclaration). */

element_replaceable
	: REPLACEABLE short_class_definition {
		Mod_Redefine (modifier_prefixes_replaceable,
			      $2, NONE)}
	| REPLACEABLE short_class_definition constraining_clause {
		let
		    val (t, m) = $3
		in
		    Mod_Redefine (modifier_prefixes_replaceable,
				  $2,
				  SOME (t, m, Annotation [], Comment []))
		end}
	| REPLACEABLE component_clause_1 {
		Mod_Redeclare (modifier_prefixes_replaceable,
			       $2, NONE)}
	| REPLACEABLE component_clause_1 constraining_clause {
		let
		    val (t, m) = $3
		in
		    Mod_Redeclare (modifier_prefixes_replaceable,
				   $2,
				   SOME (t, m, Annotation [], Comment []))
		end}
	;

component_clause_1
	: type_prefix_type_specifier_ component_declaration_1 {
		(make_component_clause $1 [] $2)}
	;

component_declaration_1
	: declaration comment {
		let
		    val (aa, ww) = $2
		in
		    case $1 of
			(v, s, m, NONE, Annotation [], Comment []) =>
			    (v, s, m, NONE, aa, ww)
		      | _ => raise Match
		end}
	;

short_class_definition
	: class_prefixes short_class_specifier {
		(set_class_prefixes $1 $2)}
	;

optional_each_or_final_
	: /*empty*/ {
		{Each=false, Final=false}}
	| EACH {
		{Each=true, Final=false}}
	| FINAL {
		{Each=false, Final=true}}
	| EACH FINAL {
		{Each=true, Final=true}}
	;

/* B.2.6 Equations */

equation_section
	: EQUATION equation_loop_ {
		(Element_Equations (false, $2))}
	| INITIALEQUATION equation_loop_ {
		(Element_Equations (true, $2))}
	;

equation_loop_
	: /*empty*/ {
		[]}
	| equation_loop_ equation ";" {
		($1 ++ $2)}
	;

algorithm_section
	: ALGORITHM statement_loop_ {
		(Element_Algorithms (false, $2))}
	| INITIALALGORITHM statement_loop_ {
		(Element_Algorithms (true, $2))}
	;

statement_loop_
	: /*empty*/ {
		[]}
	| statement_loop_ statement ";" {
		($1 ++ $2)}
	;

equation
	: equation_body_ comment {
		[(attach_comment_to_equation $1 $2)]}
	;

equation_body_
	: simple_expression "=" expression {
		Eq_Eq (($1, $3), Annotation [], Comment [])}
	| if_equation
	| for_equation
	| connect_clause
	| when_equation
	| component_reference function_call_args {
		Eq_App (($1, $2), Annotation [], Comment [])}
	;

statement
	: statement_body_ comment {
		[(attach_comment_to_statement $1 $2)]}
	;

statement_body_
	: component_reference DEF expression {
		St_Assign ($1, $3, Annotation [], Comment [])}
	| component_reference function_call_args {
		St_Call ([], $1, $2, Annotation [], Comment [])}
	| "(" output_expression_list ")" DEF component_reference function_call_args {
		St_Call ($2, $5, $6, Annotation [], Comment [])}
	| BREAK {
		St_Break (Annotation [], Comment [])}
	| RETURN {
		St_Return (Annotation [], Comment [])}
	| if_statement
	| for_statement
	| while_statement
	| when_statement
	;

if_equation
	: IF expression THEN equation_loop_ elseif_equation_loop_
		else_part_equation_ END IF {
		Eq_If (([($2, $4)] ++ $5 ++ $6), Annotation [], Comment [])}
	;

elseif_equation_loop_
	: /*empty*/ {
		[]}
	| elseif_equation_loop_ ELSEIF expression THEN equation_loop_ {
		($1 ++ [($3, $5)])}
	;

else_part_equation_
	: /*empty*/ {
		[]}
	| ELSE equation_loop_ {
		[(Otherwise, $2)]}
	;

if_statement
	: IF expression THEN statement_loop_ elseif_statement_loop_
		else_part_statement_ END IF {
		St_If ([($2, $4)] ++ $5 ++ $6, Annotation [], Comment [])}
	;

elseif_statement_loop_
	: /*empty*/ {
		[]}
	| elseif_statement_loop_ ELSEIF expression THEN statement_loop_ {
		($1 ++ [($3, $5)])}
	;

else_part_statement_
	: /*empty*/ {
		[]}
	| ELSE statement_loop_ {
		[(Otherwise, $2)]}
	;

for_equation
	: FOR for_indices LOOP equation_loop_ END FOR {
		Eq_For (($2, $4), Annotation [], Comment [])}
	;

for_statement
	: FOR for_indices LOOP statement_loop_ END FOR {
		St_For ($2, $4, Annotation [], Comment [])}
	;

for_indices
	: for_index {
		[$1]}
	| for_indices "," for_index {
		($1 ++ [$3])}
	;

for_index
	: IDENT {
		(Id $1, Colon)}
	| IDENT IN expression {
		(Id $1, $3)}
	;

while_statement
	: WHILE expression LOOP statement_loop_ END WHILE {
		St_While ($2, $4, Annotation [], Comment [])}
	;

when_equation
	: WHEN expression THEN equation_loop_
		elsewhen_equation_loop_ END WHEN {
		Eq_When (([($2, $4)] ++ $5), Annotation [], Comment [])}
	;

elsewhen_equation_loop_
	: /*empty*/ {
		[]}
	| elsewhen_equation_loop_ ELSEWHEN expression THEN equation_loop_ {
		($1 ++ [($3, $5)])}
	;

when_statement
	: WHEN expression THEN statement_loop_
		elsewhen_statement_loop_ END WHEN {
		St_When ([($2, $4)] ++ $5, Annotation [], Comment [])}
	;

elsewhen_statement_loop_
	: /*empty*/ {
		[]}
	| elsewhen_statement_loop_ ELSEWHEN expression THEN statement_loop_ {
		($1 ++ [($3, $5)])}
	;

connect_clause
	: CONNECT "(" component_reference "," component_reference ")" {
		Eq_Connect (($3, $5), Annotation [], Comment [])}
	;

/* B.2.7 Expressions */

expression
	: simple_expression
	| IF expression THEN expression elseif_expression_loop_ ELSE expression {
		(make_ite ([($2, $4)] ++ $5) $7)
		(*ITE ([($2, $4)] ++ $5 ++ [(Otherwise, $7)])*)}
	;

elseif_expression_loop_
	: /*empty*/ {
		[]}
	| elseif_expression_loop_ ELSEIF expression THEN expression {
		($1 ++ [($3, $5)])}
	;

simple_expression
	: logical_expression
	| logical_expression ":" logical_expression {
		Array_Triple ($1, $3, NONE)}
	| logical_expression ":" logical_expression ":" logical_expression {
		Array_Triple ($1, $3, SOME $5)}
	;

logical_expression
	: logical_term
	| logical_expression OR logical_term {
		App ((make_binary "or"), [$1, $3])
		(*Binary ("or", $1, $3)*)}
	;

logical_term
	: logical_factor
	| logical_term AND logical_factor {
		App ((make_binary "and"), [$1, $3])
		(*Binary ("and", $1, $3)*)}
	;

logical_factor
	: relation
	| NOT relation {
		App ((make_unary "not"), [$2])
		(*Unary ("not", $2)*)}
	;

relation
	: arithmetic_expression
	| arithmetic_expression RELATIONAL_OPERATOR arithmetic_expression {
		App ((make_relational $2), [$1, $3])
		(*Rel ($2, $1, $3)*)}
	;

arithmetic_expression
	: term
	| ADD_OPERATOR term {
		App ((make_unary $1), [$2])
		(*Unary ($1, $2)*)}
	| arithmetic_expression ADD_OPERATOR term {
		App ((make_binary $2), [$1, $3])
		(*Binary ($2, $1, $3)*)}
	;

term
	: factor
	| term MUL_OPERATOR factor {
		App ((make_binary $2), [$1, $3])
		(*Binary ($2, $1, $3)*)}
	;

factor
	: primary
	| primary EXP_OPERATOR primary {
		App ((make_binary $2), [$1, $3])
		(*Binary ($2, $1, $3)*)}
	;

expression_list_rows_
	: expression_list {
		[$1]}
	| expression_list_rows_ ";" expression_list {
		($1 ++ [$3])}
	;

/* Clauses for "end" and "initial" cause conflicts by BYACC, "initial"
   with two shift/reduce conflicts, and "end" with many.  Thus, "end"
   and "initial" are removed from the primary expression.  "end" may
   appear in array subscripts.  The lexer handles "end" as an
   identifier token while parsing in array subscripts.  "initial" may
   appear as a predefined function in a when-clause.  The lexer
   handles pairs "initial algorithm" and "initial equation" as single
   tokens.  Expressions "{...}" are (general) array-constructors.  See
   (10.4 Vector, Matrix and Array Constructors).  Expressions "[...]"
   are array-concatenations.  See (10.4.2 Array Concatenation).  The
   "pure" is used as "pure(f(...))"  to call an impure functionsin a
   pure context.  See (12.3 Pure Modelica Functions). */

primary
	: UNSIGNED_NUMBER {
		(check_literal_number $1)}
	| STRING {
		L_String $1}
	| FALSE {
		L_Bool false}
	| TRUE {
		L_Bool true}
	| component_reference function_call_args {
		App ($1, $2)}
	| DER function_call_args {
		Der $2}
	| PURE function_call_args {
		(* Pure $2 *)
		raise error_pure_expression}
	| component_reference
	| "(" output_expression_list ")" {
		(* Strip parentheses for associativity. *)
		case $2 of
		    [NIL] => Tuple [NIL]
		  | [e] => e
		  | ee => Tuple ee}
	| "[" expression_list_rows_ "]" {
		Array_Concatenation $2}
	| "{" array_arguments "}" {
		$2}
	/*|INITIAL function_call_args*/
	/*|END*/
	;

/* Note the "type-specifier" can begin with "", but the "name" cannot.
   Names starting with a dot are global.  See (5.3.2 Composite Name
   Lookup) and (5.3.3 Global Name Lookup). */

type_specifier
	: name {
		$1}
	| "." name {
		case $2 of Name s => Name ([""] ++ s)}
	;

name
	: IDENT {
		Name [$1]}
	| name "." IDENT {
		case $1 of Name ss => Name (ss ++ [$3])}
	;

/* component_reference is similar to names, but may have subscripts. */

component_reference
	: IDENT {
		Vref (NONE, [(Id $1, [])])}
	| IDENT array_subscripts {
		Vref (NONE, [(Id $1, $2)])}
	| "." IDENT {
		Vref (NONE, [(Id "", []), (Id $2, [])])}
	| "." IDENT array_subscripts {
		Vref (NONE, [(Id "", []), (Id $2, $3)])}
	| component_reference "." IDENT {
		case $1 of
		    Vref (_, v) =>
			Vref (NONE, (v ++ [(Id $3, [])]))
		  | _ => raise Match}
	| component_reference "." IDENT array_subscripts {
		case $1 of
		    Vref (_, v) =>
			Vref (NONE, (v ++ [(Id $3, $4)]))
		  | _ => raise Match}
	;

function_call_args
	: "(" ")" {
		[]}
	| "(" function_arguments ")" {
		$2}
	;

/* The call syntax with "for" is a reduction.  An example is
   "sum(i_for_i_in_1:10)".  See (10.3.4.1 Reduction Expressions).
   Choices of expression or argument_fn_ are unified to
   function_argument. */

function_arguments
	/*
	: expression {
		[$1]}
	| expression "," function_arguments_non_first {
		([$1] ++ $3)}
	| argument_fn_ {
		[$1]}
	| argument_fn_ "," function_arguments_non_first {
		([$1] ++ $3)}
	*/
	: function_argument {
		[$1]}
	| function_argument "," function_arguments_non_first {
		([$1] ++ $3)}
	| expression FOR for_indices {
		[Reduction_Argument ($1, $3)]}
	| named_arguments
	;

function_arguments_non_first
	: function_argument {
		[$1]}
	| function_argument "," function_arguments_non_first {
		([$1] ++ $3)}
	| named_arguments
	;

/* The constructor syntax with "for" is a comprehension.  See (10.4.1
   Array Constructor with Iterators). */

array_arguments
	: expression {
		Array_Constructor [$1]}
	| expression "," array_arguments_non_first {
		Array_Constructor ([$1] ++ $3)}
	| expression FOR for_indices {
		Array_Comprehension ($1, $3)}
	;

array_arguments_non_first
	: expression {
		[$1]}
	| expression "," array_arguments_non_first {
		([$1] ++ $3)}
	;

named_arguments
	: named_argument {
		[$1]}
	| named_arguments "," named_argument {
		($1 ++ [$3])}
	;

named_argument
	: IDENT "=" function_argument {
		Named_Argument ((Name [$1]), $3)}
	;

function_argument
	: expression
	| argument_fn_
	;

argument_fn_
	: FUNCTION name "(" ")" {
		Closure ($2, [])}
	| FUNCTION name "(" named_arguments ")" {
		Closure ($2, $4)}
	;

/* The empty "()" output-expression-list is [NIL].  It is consistent
   with ones such as [NIL,NIL] for "(,)". */

output_expression_list
	: /*empty*/ {
		[NIL]}
	| expression {
		[$1]}
	| output_expression_list "," {
		($1 ++ [NIL])}
	| output_expression_list "," expression {
		($1 ++ [$3])}
	;

expression_list
	: expression {
		[$1]}
	| expression_list "," expression {
		($1 ++ [$3])}
	;

/* The subscripts rule sets the lexer to read END as an identifier.  A
   lookahead by the lexer is always a bracket and it is safe. */

array_subscripts
	: subscripts_in_ "[" array_subscripts_loop_ subscripts_out_ "]" {
		$3}
	;

subscripts_in_
	: /*empty*/ {
		((#yylexstate yysm) := set_end_as_id true (! (#yylexstate yysm)))}
	;

subscripts_out_
	: /*empty*/ {
		((#yylexstate yysm) := set_end_as_id false (! (#yylexstate yysm)))}
	;

array_subscripts_loop_
	: subscript
	| array_subscripts_loop_ "," subscript {
		($1 ++ $3)}
	;

subscript
	: ":" {
		[Colon]}
	| expression {
		[$1]}
	;

comment
	: string_comment {
		(Annotation [], Comment $1)}
	| string_comment annotation {
		($2, Comment $1)}
	;

string_comment
	: /*empty*/ {
		[]}
	| string_comment_list_ {
		$1}
	;

string_comment_list_
	: STRING {
		[$1]}
	| string_comment_list_ "+" STRING {
		($1 ++ [$3])}
	;

annotation
	: ANNOTATION class_modification {
		Annotation $2}
	;

%%

end

(* End of the struct defition. *)
