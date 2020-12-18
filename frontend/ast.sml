(* ast.sml -*-Coding: us-ascii-unix;-*- *)
(* Copyright (C) 2018-2020 RIKEN R-CCS *)

(* PARSER AST of Modelica-3.4. *)

structure ast = struct

(*exception SyntaxError of string*)

fun error_bad_literal_number s = Fail ("Bad number sequence ("^ s ^")")
val error_bad_kind_to_simple_types = Fail ("Bad kind to simple types")
val error_pure_expression = Fail ("Pure expressions not implemented")

(* name_t and id_t are names and identifiers appearing in the grammar.
   A name refers to the unnamed-enclosing-class by a prefix "". *)

datatype name_t = Name of string list
datatype id_t = Id of string

(* instantiation_t indicates a class is used as either a package or a
   state variable.  A class is marked by PKG initially, then it is
   assigned with PKG/VAR at instantiation. *)

datatype instantiation_t = PKG | VAR

(* class_tag_t is a fully-qualified class name which refers to a
   lexical position of a class in files. *)

datatype class_tag_t = Ctag of string list

(* A subject refers to a name rooted at either a package or a model.
   The package root is the unnamed-enclosing-class.  Package-rooted
   names are ".P.P.P" and model-rooted names are "v[i].v[i].v[i]" with
   subscripts optional.  It includes a constant reference via packages
   "P.c[i]", and a package reference via instances "v[i].P". *)

datatype subject_t = Subj of instantiation_t * (id_t * int list) list

(* part_name_t names a main/base part of a class.  A subject specifies
   a main class, and a tag specifies a base part of it.  A part_name
   is often used as a scope. *)

type part_name_t = subject_t * class_tag_t
type scope_t = subject_t * class_tag_t

(* Real (R) or integer (Z). *)

datatype number_type_t = R | Z

(* The predefined operators.  Other overloaded operators are
   represented by functions.  It is used like Opr~Opr_add.  "ew"
   stands for element-wise.  Arithmetics are defined on Real and
   Integer.  expt is on Real, concat is on String.  Relationals are
   defined on the simple-types. *)

datatype predefined_operator_t
    = Opr_id
    | Opr_neg
    | Opr_id_ew
    | Opr_neg_ew
    | Opr_add
    | Opr_sub
    | Opr_add_ew
    | Opr_sub_ew
    | Opr_mul
    | Opr_div
    | Opr_mul_ew
    | Opr_div_ew
    | Opr_expt
    | Opr_expt_ew
    | Opr_not
    | Opr_and
    | Opr_ior
    | Opr_concat
    | Opr_eq
    | Opr_ne
    | Opr_gt
    | Opr_lt
    | Opr_ge
    | Opr_le

(* Expressions.  NIL is an empty element in an output-expression-list.
   Colon is a [:] in a subscript.  Otherwise is a truth for an
   else-part condition.  NIL, Colon, and Otherwise appear alone, and
   not in an expression.  Scoped is an expression in a scope.  Vref
   represents a component reference which includes array indexing.  A
   first optional slot indicates whether it is resolved.  Opr
   represents predefined operators.  Closure is a partially applied
   function.  L_Number, L_String, L_Bool, and L_Enum are literals.
   L_Number has a slot indicating Real or Integer.  Real literals are
   represented by strings to make syntax trees eqtype in SML.  L_Enum
   is introduced when enumerations are processed.  Reduction_Argument
   is an argument list for reductions.  Note that arguments to
   Array_Constructor is non-empty.  Pseudo_Split is an array indexing,
   that is introduced at rewriting a non-each modifier on an array.
   Component_Ref is a component reference, that is introduced at
   rewriting a modifier of class copying.  It is with an array
   dimension which is null for a scalar component.  Instances refers
   to instances, and also it internally refers to a function.  Iref is
   an iterator variable reference.  Others, Array_fill,
   Array_diagonal, etc. are predefined functions. *)

datatype expression_t
    = NIL
    | Colon
    | Otherwise
    | Scoped of expression_t * scope_t
    | Vref of instantiation_t option * component_and_subscript_t list
    | Opr of predefined_operator_t
    | App of expression_t * expression_t list
    | ITE of (expression_t * expression_t) list
    | Der of expression_t list
    | Pure of expression_t list
    | Closure of name_t * expression_t list
    | L_Number of number_type_t * string
    | L_Bool of bool
    | L_Enum of class_tag_t * id_t
    | L_String of string
    | Array_Triple of expression_t * expression_t * expression_t option
    | Array_Constructor of expression_t list
    | Array_Comprehension of expression_t * for_index_t list
    | Array_Concatenation of expression_t list list
    | Tuple of expression_t list
    | Reduction_Argument of expression_t * for_index_t list
    | Named_Argument of name_t * expression_t
    | Pseudo_Split of expression_t * int list
    | Component_Ref of expression_t * id_t
    | Instances of int list * subject_t list
    | Iref of id_t
    | Array_fill of expression_t * expression_t
    | Array_diagonal of expression_t

withtype for_index_t = id_t * expression_t

and component_and_subscript_t = id_t * expression_t list

datatype visibility_t = Protected | Public

datatype analogical_t = Flow | Stream | Effort

(* Variability is related by inclusion.  Constant is the smallest.
   Continuous means unconstrained, and thus declaring continuous
   integers is allowed. *)

datatype variability_t = Constant | Parameter | Discrete | Continuous

(* (It may better Modeless be Acausal). *)

datatype input_or_output_t = Input | Output | Modeless

type each_or_final_t = {Each : bool, Final : bool}

type redeclare_t = {Redeclare : bool}

(* Usually a variable "p" is used for class_prefixes_t, "q" for
   component_prefixes_t, and "r" for both element_prefixes_t and
   modifier_prefixes_t. *)

type class_prefixes_t
     = {Final : bool, Encapsulated : bool, Partial : bool}

type component_prefixes_t
     = (analogical_t * variability_t * input_or_output_t)

type element_prefixes_t
     = {Final : bool, Replaceable : bool, Inner : bool, Outer : bool}

type modifier_prefixes_t
     = {Final : bool, Replaceable : bool, Each : bool}

(* Implied is used by internally introduced modifiers.  See the
   copy_type definition. *)

datatype class_kind_t
    = Bad_Kind
    | Implied
    | Type
    | Class
    | Model
    | Block
    | Record
    | Operator_Record
    | Connector of (*expandable*) bool
    | Package
    | Function of (*pure*) bool
    | Operator
    | Operator_Function of (*pure*) bool

type type_prefixes_t = (class_kind_t * class_prefixes_t)

type component_type_specifier_t = (component_prefixes_t * name_t)

(* Class descriptions.  The parts of a kind and class prefixes are
   defined as a class element, and some parts (including a kind and
   class prefixes) are decorated by short-class-definitions.
   Component type prefixes (analogical and variability, but
   input/output) are only associated to component variables.  Only
   input/output is associated to a class via a
   short-class-definition. *)

type class_specifier_t
     = (class_kind_t * class_prefixes_t * component_prefixes_t)

datatype comment_t = Comment of string list

(* cook_step keeps track of processing steps of a class stored in the
   instance_tree.  Classes are first stored in the loaded_classes at
   E0.  E0 is the loaded state.  E0 classes are ready for searching an
   imported class.  (E1) is a transient state.  It is a guard to
   detect a cycle in processing.  E2 is after resolving imported
   classes.  E2 classes are ready for searching base classes.  E3 is
   after resolving base classes and associating modifications.  E3
   classes are ready for searching component classes.  If a class is
   at E3, its all imported or base classes are also in E3.  When a
   package is processed, it reveals intermediate E0-E3 states to allow
   lookups to see the class.  Binding variables replaces variables by
   qualified names in expressions.  Binding may be partially applied
   to the declarations that are needed for folding constants during
   instantiation.  Partial binding moves a class from E3 to E5.  (E4)
   is a transient state similar to (E1).  Enumerators are created at
   E5. *)

datatype cook_step_t = E0 | E1 | E2 | E3 | E4 | E5

(* In_Modifiers/In_Elements indicates the source of a redeclaration.
   In_Modifiers is redeclarations in-modifiers and In_Elements is
   redeclarations in-elements. *)

datatype redeclaration_source_t = In_Modifiers | In_Elements

(* primitive_type_t is stored in Def_Primitive.  Each corresponds to a
   simple-type.  Even the simple-types have structures, that is, they
   have attributes.  The attributes of them are described by the
   corresponding primitive types.  Note that the primitive types also
   represent values in constant folding. *)

datatype primitive_type_t
    = P_Number of number_type_t
    | P_Boolean
    | P_String
    | P_Enum of class_tag_t

(* Equations.  Eq_List is introduced temporarily. *)

datatype equation_t
    = Eq_Eq of ((expression_t * expression_t)
		* annotation_t * comment_t)
    | Eq_Connect of ((expression_t * expression_t)
		     * annotation_t * comment_t)
    | Eq_If of ((expression_t * equation_t list) list
		* annotation_t * comment_t)
    | Eq_When of ((expression_t * equation_t list) list
		  * annotation_t * comment_t)
    | Eq_For of ((for_index_t list * equation_t list)
		 * annotation_t * comment_t)
    | Eq_App of ((expression_t * expression_t list)
		 * annotation_t * comment_t)
    (*| Eq_List of equation_t list * annotation_t * comment_t*)

(* Statements.  Call has a form: "(v):=f(a)".  A comment on statements
   has a separate entry, while most comments are stored in syntax
   entries. *)

and statement_t
    = St_Break of annotation_t * comment_t
    | St_Return of annotation_t * comment_t
    | St_Assign of (expression_t * expression_t
		    * annotation_t * comment_t)
    | St_Call of (expression_t list * expression_t * expression_t list
		  * annotation_t * comment_t)
    | St_If of ((expression_t * statement_t list) list
		* annotation_t * comment_t)
    | St_For of (for_index_t list * statement_t list
		 * annotation_t * comment_t)
    | St_While of (expression_t * statement_t list
		   * annotation_t * comment_t)
    | St_When of ((expression_t * statement_t list) list
		  * annotation_t * comment_t)
    (*| St_Comment of (annotation_t * comment_t)*)

(* variable_declaration is a tuple of ID and a class definition.  An
   optional expression exists for a condition declaration.  An
   array-subscripts part in the declaration is moved in the class
   definition.  The fields abbreviation is: Defvar(v,q,k,c,a,w). *)

and variable_declaration_t
    = Defvar of (id_t * component_prefixes_t
		 * definition_body_t
		 * expression_t option
		 * annotation_t * comment_t)

(* class_definition is used to refer to a class.  A class-specifier in
   the syntax is a class-definition with a null class-prefixes.  The
   second name field is an enclosing class, which is added at a
   supplementary step in parsing.  The fields abbreviation is:
   Defclass((v,g),k). *)

and class_definition_t
    = Defclass of ((id_t * class_tag_t) * definition_body_t)

and type_marker_t = ENUM | MAIN | BASE | SIMP

(* Def_Body, Def_Der, and Def_Primitive are the only proper classes
   that appear after syntactic processing.  Def_Body is a class
   definition.  The subject slot is an identifier which is set when it
   is associated to a package/instance (it is chiefly used for
   information).  The name 3-tuple is name information.  The first
   class-tag slot is an original name of a body.  The second slot is a
   class name after potential renaming (for an instance).  The third
   slot is an enclosing class (for a package).  Field abbreviation is:
   Def_Body(mk,j,cs,nm,ee,aa,ww).  Def_Der is a derivative definition.
   Def_Body and Def_Der represent the classes after syntaxing.
   Def_Primitive is primitive types.  Def_Name specifies a class name
   in the language.  Def_Scoped replaces Def_Name by attaching scope
   information.  Def_Refine represents class modifications, either
   from a short class definition or from an extends-clause.
   Def_Refine holds component_prefixes but it usually only uses a
   type_prefix part.  The entire component_prefixes are needed at
   instantiation.  Its field abbreviation is:
   Def_Refine(k,t,q,(ss,mm),a,w).  Def_Extending represents an
   extends-redeclaration.  It is a pair of a base with modifiers and a
   body.  The boolean slot is an extended-flag indicating a base class
   is set, and it is true when it replaces a replaceable.  It is used
   only for checking purpose.  Def_Replaced is introduced by a
   redeclaration, and holds an original definition for information.
   The first slot is the new definition.  Def_Primitive represents a
   value of a simple-type and holds its value.  Def_Displaced is a tag
   left in place of a definition body.  Its subject slot indicates an
   enclosing class, to refer to an enclosing class that is modified.
   Def_In_File indicates that a class is yet to be loaded from a file.
   It is only placed in the loaded_classes table.  Such entries are
   created for file/directory entries when a "package.mo" is loaded.
   It is a pair of an outer reference and a matching inner reference.
   Def_Mock_Array is temporarily used to represent an array of
   instances, which is created on accessing the instance_tree.
   Def_Outer_Alias is a record left in the instance_tree to map an
   outer reference to an inner. *)

and definition_body_t
    = Def_Body of
      ((cook_step_t * instantiation_t * type_marker_t)
       * subject_t * class_specifier_t
       * (class_tag_t * subject_t * (*enclosing*) subject_t)
       * element_t list * annotation_t * comment_t)
    | Def_Der of
      (class_tag_t * class_specifier_t
       * name_t * id_t list * annotation_t * comment_t)
    | Def_Primitive of
      (primitive_type_t * (*value*) expression_t)
    | Def_Name of name_t
    | Def_Scoped of (name_t * scope_t)
    | Def_Refine of
      (definition_body_t
       * subject_t option * type_prefixes_t * component_prefixes_t
       * (subscripts_t * modifier_t list)
       * annotation_t * comment_t)
    | Def_Extending of
      ((*extended*) bool * (definition_body_t * modifier_t list)
       * definition_body_t)
    | Def_Replaced of
      (definition_body_t
       * (visibility_t * element_prefixes_t
	  * element_sum_t * constraint_t option))
    | Def_Displaced of class_tag_t * (*enclosing*) subject_t
    | Def_In_File
    | Def_Mock_Array of
      (int list * definition_body_t list * definition_body_t option)
    | Def_Outer_Alias of instantiation_t * subject_t * subject_t

(* Import_Clause has an ID pair (v0,v1) for importing v1=pkg.v0.  Or,
   it is a "*"-form import if the ID part is NONE.  Element_Class and
   Element_State are class definitions and variable declarations.
   Redefine_Class and Redeclare_State are the same as Element_Class
   and Element_State, but ones prefixed by redeclare.  Usual field
   namings are: Element_State(z,r,d,h) and Element_Class(z,r,d,h).
   The entires Element_Import, Element_Base, Base_List, and
   Base_Classes are introduced in syntaxing.  Element_Import replaces
   Import_Clause.  Element_Base replaces Extends_Clause, and names a
   base class.  Base_List lists bases of this class (transitively).
   Base_Classes holds the class definitions to which Element_Base and
   Base_List refers.  Base_Classes only exists in a main (non-base)
   class.  The bases are collected to remove duplicates. *)

and element_t
    = Import_Clause of
      (visibility_t * name_t * (id_t * id_t) option
       * annotation_t * comment_t)
    | Extends_Clause of
      visibility_t * (name_t * modifier_t list) * annotation_t
    | Element_Class of
      (visibility_t * element_prefixes_t
       * class_definition_t * constraint_t option)
    | Element_State of
      (visibility_t * element_prefixes_t
       * variable_declaration_t * constraint_t option)
    | Redefine_Class of
      (visibility_t * element_prefixes_t
       * class_definition_t * constraint_t option)
    | Redeclare_State of
      (visibility_t * element_prefixes_t
       * variable_declaration_t * constraint_t option)
    | Element_Enumerators of
      enum_list_t option
    | Element_Equations of
      (*initial*) bool * equation_t list
    | Element_Algorithms of
      (*initial*) bool * statement_t list
    | Element_External of
      string option * statement_t option * annotation_t
    | Element_Annotation of annotation_t
    | Element_Import of
      (visibility_t * class_tag_t * (id_t * id_t) option
       * annotation_t * comment_t)
    | Element_Base of
      visibility_t * scope_t * annotation_t
    | Base_List of
      scope_t list
    | Base_Classes of
      (class_tag_t * definition_body_t) list

(* Mod_Redefine is a class declaration, and it has a
   short-class-definition in it.  Mod_Redeclare is a component
   redeclaration.  Mod_Entry is a list of modifiers to a variable.
   The modifications consist of attribute modifiers and a value
   setting, like "x(min=0)=10".  Mod_Value is a value setting ("x=10")
   and appears in Mod_Entry.  Expressions in modifiers are explicitly
   scoped in which the names are resolved.  Class definitions are
   scoped, too.  Mod_Elements_Redefine and Mod_Elements_Redeclare are
   internally introduced to handle redeclarations in-elements in a
   similar way as redeclarations in-modifiers. *)

and modifier_t
    = Mod_Redefine of
      (modifier_prefixes_t
       * class_definition_t * constraint_t option)
    | Mod_Elemental_Redefine of
      (visibility_t * element_prefixes_t
       * class_definition_t * constraint_t option)
    | Mod_Redeclare of
      (modifier_prefixes_t
       * variable_declaration_t * constraint_t option)
    | Mod_Elemental_Redeclare of
      (visibility_t * element_prefixes_t
       * variable_declaration_t * constraint_t option)
    | Mod_Entry of
      (each_or_final_t * name_t
       * modifier_t list * comment_t)
    | Mod_Value of expression_t

and annotation_t = Annotation of modifier_t list

(* A naming element in a class is either a class definition or a
   variable declaration. *)

and element_sum_t
    = EL_Class of class_definition_t
    | EL_State of variable_declaration_t

withtype subscripts_t = expression_t list

and constraint_t = (definition_body_t * modifier_t list
		    * annotation_t * comment_t)

and enum_list_t = (id_t * annotation_t * comment_t) list

type binding_element_t = (visibility_t * element_prefixes_t
			  * element_sum_t * constraint_t option)

(* An entry of an element list (definitions/declarations).  It is
   stored in the class_bindings table.  The identifier slot is a
   variable/class name.  The first subject slot is a composite name,
   which is a composition of a defining class and a name.  The second
   subject slot points to an inner when this element is an outer. *)

datatype naming_t
    = Naming of (id_t * subject_t * subject_t option * (*imported*) bool
		 * binding_element_t)

(* ================================================================ *)

type declaration_with_subscripts_t
     = (id_t * (*subscripts*) (expression_t list) * modifier_t list
	* expression_t option * annotation_t * comment_t)

type constraint_no_comment_t = (definition_body_t * modifier_t list)

type class_definition_list_t = (name_t * class_definition_t list)

(* vs_t is a parser stack element.  It includes lexical tokens:
   identifiers, keywords, reserved characters, operators, and
   relations.  They are passed as VS_TOKEN from the lexer. *)

datatype vs_t
    = VS_NOTHING of unit
    | VS_MAIN of class_definition_list_t
    (* Lexical tokens. *)
    | VS_TOKEN of string
    (* AST elements. *)
    | VS_NAME of name_t
    | VS_ID_LIST of id_t list
    | VS_CLASS_PREFIX of type_prefixes_t
    | VS_CLASS_SPECIFIER of class_definition_t
    | VS_CLASS_DEFINITION of class_definition_t
    | VS_CLASS_DEFINITION_LIST of class_definition_t list
    | VS_ELEMENT of element_t
    | VS_ELEMENT_LIST of element_t list
    | VS_DECLARATION of declaration_with_subscripts_t
    | VS_DECLARATION_LIST of declaration_with_subscripts_t list
    | VS_MODIFIER of modifier_t
    | VS_MODIFIER_LIST of modifier_t list
    | VS_EACH_OR_FINAL of each_or_final_t
    | VS_COMPONENT of variable_declaration_t
    | VS_COMPONENT_LIST of variable_declaration_t list
    | VS_PREFIX_REDECLARE of redeclare_t
    | VS_ELEMENT_PREFIXES of element_prefixes_t
    | VS_EQUATION of equation_t
    | VS_EQUATION_LIST of equation_t list
    | VS_STATEMENT of statement_t
    | VS_STATEMENT_LIST of statement_t list
    | VS_TEST_EXPRESSION_LIST of (expression_t * expression_t) list
    | VS_TEST_EQUATIONS_LIST of (expression_t * equation_t list) list
    | VS_TEST_STATEMENTS_LIST of (expression_t * statement_t list) list
    | VS_FOR_INDEX of for_index_t
    | VS_FOR_INDEX_LIST of for_index_t list
    | VS_EXPRESSION of expression_t
    | VS_EXPRESSION_LIST of expression_t list
    | VS_EXPRESSION_LIST_LIST of expression_t list list
    | VS_IDENT_COMMENT_LIST of enum_list_t
    | VS_CONSTRAINT of constraint_no_comment_t
    | VS_COMPONENT_PREFIX of component_prefixes_t
    | VS_COMPONENT_TYPE_SPECIFIER of component_type_specifier_t
    | VS_TYPE_FLOW_OR_STREAM of analogical_t
    | VS_TYPE_INPUT_OR_OUTPUT of input_or_output_t
    | VS_TYPE_VARIABILITY of variability_t
    | VS_LANGUAGE of string
    | VS_STRING_LIST of string list
    | VS_COMMENT of (annotation_t * comment_t)
    | VS_ANNOTATION of annotation_t

val no_class_prefixes : class_prefixes_t
    = {Final=false, Encapsulated=false, Partial=false}

val no_element_prefixes : element_prefixes_t
    = {Final=false, Replaceable=false, Inner=false, Outer=false}

val no_component_prefixes : component_prefixes_t
    = (Effort, Continuous, Modeless)

val bad_tag = Ctag [""]
val bad_subject = Subj (PKG, [(Id "", [])])

(* bad_type is a bad type, temporarily used during parsing before
   assigning a true type. *)

val bad_type : type_prefixes_t = (Bad_Kind, no_class_prefixes)

val bad_class : class_specifier_t
    = (Bad_Kind, no_class_prefixes, no_component_prefixes)

(*val enum_class : class_specifier_t
    = (Bad_Kind, no_class_prefixes, no_component_prefixes, [])*)

(* copy_type is used in modifiers without an explicit kind, indicating
   that a type is determined by a body class. *)

val copy_type : type_prefixes_t = (Implied, no_class_prefixes)

val no_each_or_final : each_or_final_t = {Each=false, Final=false}

(*val xxx_null_class = Defclass ((Id "", bad_tag), Def_Displaced bad_tag)*)
(*fun syntax_error (s : string) = (raise (SyntaxError s))*)

fun syntax_error (s : string) = (raise (Fail s))

fun make_predefinition_body enum body aa ww = (
    Def_Body ((E0, PKG, enum),
	      bad_subject, bad_class,
	      (bad_tag, bad_subject, bad_subject),
	      body, aa, ww))

fun make_short_predefinition k io (ss, mm) aa ww = (
    Def_Refine (k, NONE, bad_type,
		(Effort, Continuous, io), (ss, mm), aa, ww))

fun name_append (Name ss) (Id s) = (Name (ss @ [s]))

(* Returns the prefix and the last part of a name.  It returns (A.B,C)
   for given A.B.C.  It returns (Name[],C) for just C. *)

fun name_prefix (Name ss) : (name_t * id_t) = (
    case (List.rev ss) of
	[] => raise Match
      | (t :: p) => (Name (List.rev p), Id t))

fun qualify_name ((Id v), (Ctag pkg)) = (
    let
	val _ = if ((Ctag pkg) <> bad_tag) then () else raise Match
    in
	Ctag (pkg @ [v])
    end)

(* Combines two array subscripts in the row-major order, such as
   "T[s0]~a[s1]=>T[s1,s0]~a", or "T[s0][s1]=>T[s1,s0]". *)

fun merge_subscripts s0 s1 = (s1 @ s0)

fun set_visibility z e = (
    case e of
	Import_Clause (_, n, v, a, w) =>
	Import_Clause (z, n, v, a, w)
      | Extends_Clause (_, (n, mm), a) =>
	Extends_Clause (z, (n, mm), a)
      | Element_Class (_, r, d, h) =>
	Element_Class (z, r, d, h)
      | Element_State (_, r, d, h) =>
	Element_State (z, r, d, h)
      | Redefine_Class (_, r, d, h) =>
	Redefine_Class (z, r, d, h)
      | Redeclare_State (_, r, d, h) =>
	Redeclare_State (z, r, d, h)
      | Element_Enumerators _ => raise Match
      | Element_Equations _ => raise Match
      | Element_Algorithms _ => raise Match
      | Element_External _ => e
      | Element_Annotation _ => e
      | Element_Import _ => raise Match
      | Element_Base _ => raise Match
      | Base_List _ => raise Match
      | Base_Classes _ => raise Match)

fun set_element_prefix_replaceable
	({Final=f, Replaceable=r, Inner=i, Outer=j} : element_prefixes_t) = (
    {Final=f, Replaceable=true, Inner=i, Outer=j} : element_prefixes_t)

fun set_encapsulated ({Final=f, Encapsulated=c, Partial=p} : class_prefixes_t) = (
    {Final=f, Encapsulated=true, Partial=p} : class_prefixes_t)

fun set_partial ({Final=f, Encapsulated=c, Partial=p} : class_prefixes_t) = (
    {Final=f, Encapsulated=c, Partial=true} : class_prefixes_t)

val modifier_prefixes_replaceable : modifier_prefixes_t
    = {Replaceable=true, Each=false, Final=false}

fun set_modifier_prefixes replaceable {Each=e, Final=f} = (
    {Each=e, Final=f, Replaceable=replaceable} : modifier_prefixes_t)

(* Sets class prefixes.  The body part of the argument is
   "class-specifier" of the syntax rules. *)

fun set_class_prefixes (t1, p1) (Defclass ((v, g), k0)) = (
    let
	fun set_prefixes (t1, p1) k = (
	    case k of
		Def_Body ((u, f, b), j, cs0, (c, n, x), ee, aa, ww) => (
		let
		    val _ = if (cs0 = bad_class) then () else raise Match
		    val (t0, p0, q) = cs0
		    val cs1 = (t1, p1, q)
		in
		    Def_Body ((u, f, b), j, cs1, (c, n, x), ee, aa, ww)
		end)
	      | Def_Der (c, cs0, n, vv, aa, ww) => (
		let
		    val _ = if (cs0 = bad_class) then () else raise Match
		    val (t0, p0, q) = cs0
		    val cs1 = (t1, p1, q)
		in
		    Def_Der (c, cs1, n, vv, aa, ww)
		end)
	      | Def_Primitive _ => raise Match
	      | Def_Name _ => raise Match
	      | Def_Scoped _ => raise Match
	      | Def_Refine (kx, v, ts0, q, (ss, mm), a, w) => (
		let
		    val _ = if (ts0 = bad_type) then () else raise Match
		    val ts1 = (t1, p1)
		in
		    Def_Refine (kx, v, ts1, q, (ss, mm), a, w)
		end)
	      | Def_Extending (g, x, kx) => (
		Def_Extending (g, x, (set_prefixes (t1, p1) kx)))
	      | Def_Replaced _ => raise Match
	      | Def_Displaced _ => raise Match
	      | Def_In_File => raise Match
	      | Def_Mock_Array _ => raise Match)
    in
	Defclass ((v, g), (set_prefixes (t1, p1) k0))
    end)

fun set_class_final (Defclass ((v, g), k0)) = (
    let
	fun set_final ({Final, Encapsulated, Partial} : class_prefixes_t) = (
	    {Final=true, Encapsulated=Encapsulated, Partial=Partial}
	    : class_prefixes_t)

	fun set_body fix k = (
	    case k of
		Def_Body (mk, j, (t, p, q), (c, n, x), ee, aa, ww) => (
		Def_Body (mk, j, (t, (fix p), q), (c, n, x), ee, aa, ww))
	      | Def_Der (c, (t, p, q), n, vv, aa, ww) => (
		Def_Der (c, (t, (fix p), q), n, vv, aa, ww))
	      | Def_Primitive _ => raise Match
	      | Def_Name _ => raise Match
	      | Def_Scoped _ => raise Match
	      | Def_Refine (kx, v, (t, p), q, (ss, mm), aa, ww) => (
		Def_Refine (kx, v, (t, (fix p)), q, (ss, mm), aa, ww))
	      | Def_Extending (g, x, kx) => (
		Def_Extending (g, x, (set_body fix kx)))
	      | Def_Replaced _ => raise Match
	      | Def_Displaced _ => raise Match
	      | Def_In_File => raise Match
	      | Def_Mock_Array _ => raise Match)
    in
	Defclass ((v, g), (set_body set_final k0))
    end)

(* Normalizes a clause by (1) distributing a type to each variable and
   (2) moving array subscripts to a type part.  It is as follows:
   "T~a[2],b[4];=>T[2]~a;T[4]~b;".  (Note "T[4]~a[2];=>T[2,4]~a;",
   see p.85, and T[ss0]~a[ss1]). *)

fun make_component_clause
	((q, n) : component_type_specifier_t)
	(ss0 : subscripts_t)
	((v, ss1, mm, c, a, w) : declaration_with_subscripts_t) = (
    let
	val ssx = (merge_subscripts ss0 ss1)
	val k0 = if ((null ssx) andalso (null mm)) then
		     Def_Name n
		 else
		     Def_Refine (Def_Name n, NONE, copy_type,
				 no_component_prefixes,
				 (ssx, mm), Annotation [], Comment [])
    in
	Defvar (v, q, k0, c, a, w)
    end)

fun attach_comment_to_equation q (aa, ww) = (
    case q of
	Eq_Eq ((x, y), _, _) => Eq_Eq ((x, y), aa, ww)
      | Eq_Connect ((x, y), _, _) => Eq_Connect ((x, y), aa, ww)
      | Eq_If (cc, _, _) => Eq_If (cc, aa, ww)
      | Eq_When (cc, _, _) => Eq_When (cc, aa, ww)
      | Eq_For ((rr, qq), _, _) => Eq_For ((rr, qq), aa, ww)
      | Eq_App ((e, ee), _, _) => Eq_App ((e, ee), aa, ww))

fun attach_comment_to_statement s (aa, ww) = (
    case s of
	St_Break (_, _) => St_Break (aa, ww)
      | St_Return (_, _) => St_Return (aa, ww)
      | St_Assign (x, y, _, _) => St_Assign (x, y, aa, ww)
      | St_Call (vv, f, ee, _, _) => St_Call (vv, f, ee, aa, ww)
      | St_If (cc, _, _) => St_If (cc, aa, ww)
      | St_When (cc, _, _) => St_When (cc, aa, ww)
      | St_For (rr, ss, _, _) => St_For (rr, ss, aa, ww)
      | St_While (e, ss, _, _) => St_While (e, ss, aa, ww))

(* Makes if-then-else, by simply concatenating an else-if part to
   reduce nesting. *)

fun make_ite cc0 elsepart = (
    case elsepart of
	ITE cc1 => ITE (cc0 @ cc1)
      | _ => ITE (cc0 @ [(Otherwise, elsepart)]))

(* Parses a whole string as a decimal integer. *)

fun string_is_int s = (
    let
	val ss = (TextIO.openString s)
	val x = (TextIO.scanStream (Int.scan StringCvt.DEC) ss)
	val eos = (TextIO.endOfStream ss)
	val _ = (TextIO.closeIn ss)
    in
	case (x, eos) of
	    (SOME v, true) => SOME v
	  | _  => NONE
    end)

(* Makes a number literal (real or integer).  The IEEE floating-point
   number reader of SML can read both reals and integers. *)

fun string_to_literal_number s = (
    case (IEEEReal.fromString s) of
	SOME _ => (
	case (string_is_int s) of
	    NONE => L_Number (R, s)
	  | SOME _ => L_Number (Z, s))
      | NONE => (
	raise (error_bad_literal_number s)))

fun make_unary n = (
    case n of
	"+" => Opr Opr_id
      | "-" => Opr Opr_neg
      | ".+" => Opr Opr_id_ew
      | ".-" => Opr Opr_neg_ew
      | "not" => Opr Opr_not
      | _ => raise Match)

fun make_binary n = (
    case n of
	"+" => Opr Opr_add
      | "-" => Opr Opr_sub
      | ".+" => Opr Opr_add_ew
      | ".-" => Opr Opr_sub_ew
      | "*" => Opr Opr_mul
      | "/" => Opr Opr_div
      | ".*" => Opr Opr_mul_ew
      | "./" => Opr Opr_div_ew
      | "^" => Opr Opr_expt
      | ".^" => Opr Opr_expt_ew
      | "and" => Opr Opr_and
      | "or" => Opr Opr_ior
      | _ => raise Match)

fun make_relational n = (
    case n of
	"==" => Opr Opr_eq
      | "<>" => Opr Opr_ne
      | ">" => Opr Opr_gt
      | "<" => Opr Opr_lt
      | ">=" => Opr Opr_ge
      | "<=" => Opr Opr_le
      | _ => raise Match)

fun vs_object_to_string (v : vs_t) : string = (
    case v of
	VS_NOTHING _ => "NOTHING"
      | VS_MAIN _ => "MAIN"
      (* Lexical tokens. *)
      | VS_TOKEN _ => "TOKEN"
      (* AST elements. *)
      | VS_NAME _ => "NAME"
      | VS_ID_LIST _ => "ID_LIST"
      | VS_CLASS_PREFIX _ => "CLASS_PREFIX"
      | VS_CLASS_SPECIFIER _ => "CLASS_SPECIFIER"
      | VS_CLASS_DEFINITION _ => "CLASS_DEFINITION"
      | VS_CLASS_DEFINITION_LIST _ => "CLASS_DEFINITION_LIST"
      | VS_ELEMENT _ => "ELEMENT"
      | VS_ELEMENT_LIST _ => "ELEMENT_LIST"
      | VS_DECLARATION _ => "DECLARATION"
      | VS_DECLARATION_LIST _ => "DECLARATION_LIST"
      | VS_MODIFIER _ => "MODIFIER"
      | VS_MODIFIER_LIST _ => "MODIFIER_LIST"
      | VS_EACH_OR_FINAL _ => "EACH_OR_FINAL"
      | VS_COMPONENT _ => "COMPONENT"
      | VS_COMPONENT_LIST _ => "COMPONENT_LIST"
      | VS_PREFIX_REDECLARE _ => "PREFIX_REDECLARE"
      | VS_ELEMENT_PREFIXES _ => "ELEMENT_PREFIXES"
      | VS_EQUATION _ => "VS_EQUATION"
      | VS_EQUATION_LIST _ => "EQUATION_LIST"
      | VS_STATEMENT _ => "STATEMENT"
      | VS_STATEMENT_LIST _ => "STATEMENT_LIST"
      | VS_TEST_EXPRESSION_LIST _ => "TEST_EXPRESSION_LIST"
      | VS_TEST_EQUATIONS_LIST _ => "TEST_EQUATIONS_LIST"
      | VS_TEST_STATEMENTS_LIST _ => "TEST_STATEMENTS_LIST"
      | VS_FOR_INDEX _ => "FOR_INDEX"
      | VS_FOR_INDEX_LIST _ => "FOR_INDEX_LIST"
      | VS_EXPRESSION _ => "EXPRESSION"
      | VS_EXPRESSION_LIST _ => "EXPRESSION_LIST"
      | VS_EXPRESSION_LIST_LIST _ => "EXPRESSION_LIST_LIST"
      | VS_IDENT_COMMENT_LIST _ => "IDENT_COMMENT_LIST"
      | VS_CONSTRAINT _ => "CONSTRAINT"
      | VS_COMPONENT_PREFIX _ => "COMPONENT_PREFIX"
      | VS_COMPONENT_TYPE_SPECIFIER _ => "COMPONENT_TYPE_SPECIFIER"
      | VS_TYPE_FLOW_OR_STREAM _ => "TYPE_FLOW_OR_STREAM"
      | VS_TYPE_INPUT_OR_OUTPUT _ => "TYPE_INPUT_OR_OUTPUT"
      | VS_TYPE_VARIABILITY _ => "TYPE_VARIABILITY"
      | VS_LANGUAGE _ => "LANGUAGE"
      | VS_STRING_LIST _ => "STRING_LIST"
      | VS_COMMENT _ => "VS_COMMENT"
      | VS_ANNOTATION _ => "VS_ANNOTATION")

fun bad_parser (v : vs_t) = (Fail ("internal: " ^ (vs_object_to_string v)))

end
