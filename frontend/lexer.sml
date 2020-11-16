(* lexer.sml -*-Coding: us-ascii-unix;-*- *)
(* Copyright (C) 2018-2020 RIKEN R-CCS *)

(* LEXER of Modelica-3.4. *)

(* The main entry is lexer.yylex1.  Load this after "ast.sml" and
   "parser.sml".  yylex1 returns zero at EOF. *)

(* NOTE: Input is assumed in UTF-8.  Characters in identifiers are
   handled as 8-bit opaque, since there is no Unicode support in
   SML. *)

structure lexer : sig
val parse_file : string -> ast.class_definition_list_t
end = struct

(*open ast*)

val debug_parser = ref false

val EOF = 0

(* The lexer state is defined in the parser code. *)

type lexstate_t = parser.yylexstate_t
type lexval_t = parser.yyv_t

exception Scanerror of (lexstate_t * string)

fun error_double_quote_in_q_ident s1 = (
    Scanerror (s1, "Double-quote at the beginning of a q-ident"))

fun error_bad_character_in_q_ident s1 = (
    Scanerror (s1, "Bad character in a q-ident"))

fun error_eof_in_comment s1 = (
    Scanerror (s1, "EOF in a comment"))

fun error_eof_in_string s1 = (
    Scanerror (s1, "EOF in a string"))

fun error_eof_in_q_ident s1 = (
    Scanerror (s1, "EOF in a q-ident"))

fun error_bad_character s0 c = (
    Scanerror (s0, "Bad character (" ^ (Int.toString (ord c)) ^ ")"))

fun error_bad_s_escape_character s1 = (
    Scanerror (s1, "Bad s-escape character"))

fun error_bad_number_string s0 s = (
    Scanerror (s0, "Bad number string (" ^ s ^ ")"))

(* Most of scan code return token, token-value, and next-state. *)

type scan_value_t = (int * lexval_t * lexstate_t)

fun digit_p (c : char) = (#"0" <= c andalso c <= #"9")
fun nondigit_p (c : char) = (#"_" = c orelse (letter_p c))
and lower_p c = (#"a" <= c andalso c <= #"z")
and upper_p c = (#"A" <= c andalso c <= #"Z")
and letter_p c = ((lower_p c) orelse (upper_p c))

(* Reads one character and maintains line/column counters.  Every
   reading is done thru this. *)

fun getchar (s0 : lexstate_t) = (
    case (#unget s0) of
	[] => (
	let
	    val c = (TextIO.input1 (#s s0))
	in
	    case c of
		NONE => (NONE, s0)
	      | SOME #"\n" => (
		(SOME #"\n",
		 {s = (#s s0), line= (#line s0) + 1, column = 0,
		  unget = [], end_as_id = (#end_as_id s0)}))
	      | SOME x => (
		(SOME x,
		 {s = (#s s0), line = (#line s0), column = (#column s0) + 1,
		  unget = [], end_as_id = (#end_as_id s0)}))
	end)
      | (c :: tl) => (
	(SOME c,
	 {s = (#s s0), line = (#line s0), column = (#column s0),
	  unget = tl, end_as_id = (#end_as_id s0)})))

(* Returns a character to the input stream.  (The order is reversed,
   i.e., in LIFO.  It is not used to return multiple characters). *)

and ungetchar c0 (s0 : lexstate_t) : lexstate_t = (
    {s = (#s s0), line = (#line s0), column = (#column s0),
     unget = (c0 :: (#unget s0)), end_as_id = (#end_as_id s0)})

and unget_string (u : string) (s0 : lexstate_t) : lexstate_t = (
    {s = (#s s0), line = (#line s0), column = (#column s0),
     unget = ((explode u) @ (#unget s0)), end_as_id = (#end_as_id s0)})

(* Takes a stream and returns a token and a stream.  It returns EOF as
   a token when hitting the end. *)

fun yylex1 (s0 : lexstate_t) : scan_value_t = (
    let
	val (c0, s1) = (skip_whitespaces_and_comments s0)
    in
	case c0 of
	    NONE => (EOF, (ast.VS_TOKEN "eof"), s1)
	  | SOME cc0 => (scan_token c0 s1)
    end)

(* Skips whitespaces and returns zero or one read characters.  It uses
   ungetchar to put back one character to the unget list. *)

and skip_whitespaces_and_comments (s0 : lexstate_t) = (
    let
	val (c0, s1) = (getchar s0)
    in
	case c0 of
	    NONE => (NONE, s1)
	  | SOME #" " => (skip_whitespaces_and_comments s1)
	  | SOME #"\n" => (skip_whitespaces_and_comments s1)
	  | SOME #"\r" => (skip_whitespaces_and_comments s1)
	  | SOME #"\t" => (skip_whitespaces_and_comments s1)
	  | SOME #"\b" => (skip_whitespaces_and_comments s1)
	  | SOME #"\f" => (skip_whitespaces_and_comments s1)
	  | SOME #"\v" => (skip_whitespaces_and_comments s1)
	  | SOME #"/" => (
	    let
		val (c1, s2) = (getchar s1)
	    in
		case c1 of
		    NONE => (c0, s1)
		  | SOME #"*" => (skip_whitespaces_and_comments
				      (skip_comment false s2))
		  | SOME #"/" => (skip_whitespaces_and_comments
				      (skip_eol_comment s2))
		  | SOME c => (c0, (ungetchar c s2))
	    end)
	  | SOME _ => (c0, s1)
    end)

and skip_comment (seestar : bool) (s0 : lexstate_t) = (
    let
	val (c0, s1) = (getchar s0)
    in
	case c0 of
	    NONE => raise (error_eof_in_comment s1)
	  | SOME #"/" => if seestar then s1 else (skip_comment false s1)
	  | SOME #"*" => (skip_comment true s1)
	  | SOME _ => (skip_comment false s1)
    end)

and skip_eol_comment (s0 : lexstate_t) = (
    let
	val (c0, s1) = (getchar s0)
    in
	case c0 of
	    NONE => raise (error_eof_in_comment s1)
	  | SOME #"\n" => s1
	  | SOME _ => (skip_eol_comment s1)
    end)

(* Scans a token starting with a character C. *)

and scan_token (c0 : char option) (s0 : lexstate_t) : scan_value_t = (
    case c0 of
	NONE => (EOF, (ast.VS_TOKEN "eof"), s0)
      | SOME #"\"" => (scan_string [] s0)
      | SOME #"'" => (scan_identifier_q [] s0)
      | SOME c => (
	if (digit_p c) then
	    (scan_integer_part [c] s0)
	else if (nondigit_p c) then
	    (scan_identifier [c] s0)
	else
	    (scan_reserved c s0)))

and scan_reserved (c : char) (s0 : lexstate_t) : scan_value_t = (
    case c of
	#";" => ((Char.ord #";"), (ast.VS_TOKEN ";"), s0)
      | #"," => ((Char.ord #","), (ast.VS_TOKEN ","), s0)
      | #"(" => ((Char.ord #"("), (ast.VS_TOKEN "("), s0)
      | #")" => ((Char.ord #")"), (ast.VS_TOKEN ")"), s0)
      | #"[" => ((Char.ord #"["), (ast.VS_TOKEN "["), s0)
      | #"]" => ((Char.ord #"]"), (ast.VS_TOKEN "]"), s0)
      | #"{" => ((Char.ord #"{"), (ast.VS_TOKEN "{"), s0)
      | #"}" => ((Char.ord #"}"), (ast.VS_TOKEN "}"), s0)
      | #":" => (
	let
	    val (c1, s1) = (getchar s0)
	in
	    case c1 of
		NONE => ((Char.ord #":"), (ast.VS_TOKEN ":"), s1)
	      | SOME #"=" => (parser.DEF, (ast.VS_TOKEN ":="), s1)
	      | SOME c => ((Char.ord #":"), (ast.VS_TOKEN ":"), (ungetchar c s1))
	end)
      (* Operator characters. *)
      | #"=" => (
	let
	    val (c1, s1) = (getchar s0)
	in
	    case c1 of
		NONE => ((Char.ord #"="), (ast.VS_TOKEN "="), s1)
	      | SOME #"=" => (parser.RELATIONAL_OPERATOR, (ast.VS_TOKEN "=="), s1)
	      | SOME c => ((Char.ord #"="), (ast.VS_TOKEN "="), (ungetchar c s1))
	end)
      | #"<" => (
	let
	    val (c1, s1) = (getchar s0)
	in
	    case c1 of
		NONE => (parser.RELATIONAL_OPERATOR, (ast.VS_TOKEN "<"), s1)
	      | SOME #"=" => (parser.RELATIONAL_OPERATOR, (ast.VS_TOKEN "<="), s1)
	      | SOME #">" => (parser.RELATIONAL_OPERATOR, (ast.VS_TOKEN "<>"), s1)
	      | SOME c => (parser.RELATIONAL_OPERATOR, (ast.VS_TOKEN "<"),
			   (ungetchar c s1))
	end)
      | #">" => (
	let
	    val (c1, s1) = (getchar s0)
	in
	    case c1 of
		NONE => (parser.RELATIONAL_OPERATOR, (ast.VS_TOKEN ">"), s1)
	      | SOME #"=" => (parser.RELATIONAL_OPERATOR, (ast.VS_TOKEN ">="), s1)
	      | SOME c => (parser.RELATIONAL_OPERATOR, (ast.VS_TOKEN ">"),
			   (ungetchar c s1))
	end)
      (* Operators. *)
      | #"+" => (parser.ADD_OPERATOR, (ast.VS_TOKEN "+"), s0)
      | #"-" => (parser.ADD_OPERATOR, (ast.VS_TOKEN "-"), s0)
      | #"*" => (parser.MUL_OPERATOR, (ast.VS_TOKEN "*"), s0)
      | #"/" => (parser.MUL_OPERATOR, (ast.VS_TOKEN "/"), s0)
      | #"^" => (parser.EXP_OPERATOR, (ast.VS_TOKEN "^"), s0)
      | #"." => (
	let
	    val (c1, s1) = (getchar s0)
	in
	    case c1 of
		NONE => ((Char.ord #"."), (ast.VS_TOKEN "."), s1)
	      | SOME #"+" => (parser.ADD_OPERATOR, (ast.VS_TOKEN ".+"), s1)
	      | SOME #"-" => (parser.ADD_OPERATOR, (ast.VS_TOKEN ".-"), s1)
	      | SOME #"*" => (parser.MUL_OPERATOR, (ast.VS_TOKEN ".*"), s1)
	      | SOME #"/" => (parser.MUL_OPERATOR, (ast.VS_TOKEN "./"), s1)
	      | SOME #"^" => (parser.EXP_OPERATOR, (ast.VS_TOKEN ".^"), s1)
	      | SOME c => ((Char.ord #"."), (ast.VS_TOKEN "."),
			   (ungetchar c s1))
	end)
      | _ => raise (error_bad_character s0 c))

(* A string is collected in reverse list. *)

and scan_string (ss : char list) (s0 : lexstate_t) : scan_value_t = (
    let
	val (c0, s1) = (getchar s0)
    in
	case c0 of
	    NONE => raise (error_eof_in_string s1)
	  | SOME #"\"" => (
	    (parser.STRING, (ast.VS_TOKEN (implode (List.rev ss))), s1))
	  | SOME #"\\" => (scan_string_escaped ss s1)
	  | SOME c => (scan_string (c :: ss) s1)
    end)

and scan_string_escaped (ss : char list) (s0 : lexstate_t) : scan_value_t = (
    let
	val (c0, s1) = (getchar s0)
    in
	case c0 of
	    NONE => raise (error_eof_in_string s1)
	  | SOME (c as #"\"") => (scan_string (c :: ss) s1)
	  | SOME (c as #"\\") => (scan_string (c :: ss) s1)
	  | SOME (c as #"'") => (scan_string (c :: ss) s1)
	  | SOME (c as #"?") => (scan_string (c :: ss) s1)
	  | SOME #"a" => (scan_string (#"\a" :: ss) s1)
	  | SOME #"b" => (scan_string (#"\b" :: ss) s1)
	  | SOME #"f" => (scan_string (#"\f" :: ss) s1)
	  | SOME #"n" => (scan_string (#"\n" :: ss) s1)
	  | SOME #"r" => (scan_string (#"\r" :: ss) s1)
	  | SOME #"t" => (scan_string (#"\t" :: ss) s1)
	  | SOME #"v" => (scan_string (#"\v" :: ss) s1)
	  | SOME _ => raise (error_bad_s_escape_character s1)
    end)

and scan_integer_part (ss : char list) (s0 : lexstate_t) : scan_value_t = (
    let
	val (c0, s1) = (getchar s0)
    in
	case c0 of
	    NONE => (parse_number (implode ss) s1)
	  | SOME #"." => (scan_fraction_part (ss @ [#"."]) s1)
	  | SOME #"e" => (scan_signed_exponent_part (ss @ [#"e"]) s1)
	  | SOME #"E" => (scan_signed_exponent_part (ss @ [#"e"]) s1)
	  | SOME c => (
	    if (digit_p c) then
		(scan_integer_part (ss @ [c]) s1)
	    else
		(parse_number (implode ss) (ungetchar c s1)))
    end)

and scan_fraction_part (ss : char list) (s0 : lexstate_t) : scan_value_t = (
    let
	val (c0, s1) = (getchar s0)
    in
	case c0 of
	    NONE => (parse_number (implode ss) s1)
	  | SOME #"e" => (scan_signed_exponent_part (ss @ [#"e"]) s1)
	  | SOME #"E" => (scan_signed_exponent_part (ss @ [#"e"]) s1)
	  | SOME c => (
	    if (digit_p c) then
		(scan_fraction_part (ss @ [c]) s1)
	    else
		(parse_number (implode ss) (ungetchar c s1)))
    end)

and scan_signed_exponent_part (ss : char list) (s0 : lexstate_t) : scan_value_t = (
    let
	val (c0, s1) = (getchar s0)
    in
	case c0 of
	    NONE => (parse_number (implode ss) s1)
	  | SOME #"+" => (scan_exponent_part (ss @ [#"+"]) s1)
	  | SOME #"-" => (scan_exponent_part (ss @ [#"-"]) s1)
	  | SOME c => (
	    if (digit_p c) then
		(scan_exponent_part (ss @ [c]) s1)
	    else
		(parse_number (implode ss) (ungetchar c s1)))
    end)

and scan_exponent_part (ss : char list) (s0 : lexstate_t) : scan_value_t = (
    let
	val (c0, s1) = (getchar s0)
    in
	case c0 of
	    NONE => (parse_number (implode ss) s1)
	  | SOME c => (
	    if (digit_p c) then
		(scan_exponent_part (ss @ [c]) s1)
	    else
		(parse_number (implode ss) (ungetchar c s1)))
    end)

and parse_number (s : string) (s0 : lexstate_t) : scan_value_t = (
    case (Real.fromString s) of
	NONE => raise (error_bad_number_string s0 s)
      | SOME x => (parser.UNSIGNED_NUMBER, (ast.VS_TOKEN s), s0))

(* Scans an identifier.  ss collects characters already read. *)

and scan_identifier (ss : char list) (s0 : lexstate_t) : scan_value_t = (
    let
	val (c0, s1) = (getchar s0)
    in
	case c0 of
	    NONE => (check_keyword (implode ss) s1)
	  | SOME c => (
	    if ((digit_p c) orelse (nondigit_p c)) then
		(scan_identifier (ss @ [c]) s1)
	    else
		(check_keyword (implode ss) (ungetchar c s1)))
    end)

(* Decides a string is a keyword or an ID.  It calls yylex1 to peek a
   next token after "initial".  It is safe to call yylex1 again,
   because it is at a tail call.  Note yylex1 always returns a VS_TOKEN
   as a value. *)

and check_keyword (s : string) (s0 : lexstate_t) : scan_value_t = (
    case s of
	"algorithm" => (parser.ALGORITHM, (ast.VS_TOKEN s), s0)
      | "and" => (parser.AND, (ast.VS_TOKEN s), s0)
      | "annotation" => (parser.ANNOTATION, (ast.VS_TOKEN s), s0)
      | "block" => (parser.BLOCK, (ast.VS_TOKEN s), s0)
      | "break" => (parser.BREAK, (ast.VS_TOKEN s), s0)
      | "class" => (parser.CLASS, (ast.VS_TOKEN s), s0)
      | "connect" => (parser.CONNECT, (ast.VS_TOKEN s), s0)
      | "connector" => (parser.CONNECTOR, (ast.VS_TOKEN s), s0)
      | "constant" => (parser.CONSTANT, (ast.VS_TOKEN s), s0)
      | "constrainedby" => (parser.CONSTRAINEDBY, (ast.VS_TOKEN s), s0)
      | "der" => (parser.DER, (ast.VS_TOKEN s), s0)
      | "discrete" => (parser.DISCRETE, (ast.VS_TOKEN s), s0)
      | "each" => (parser.EACH, (ast.VS_TOKEN s), s0)
      | "else" => (parser.ELSE, (ast.VS_TOKEN s), s0)
      | "elseif" => (parser.ELSEIF, (ast.VS_TOKEN s), s0)
      | "elsewhen" => (parser.ELSEWHEN, (ast.VS_TOKEN s), s0)
      | "encapsulated" => (parser.ENCAPSULATED, (ast.VS_TOKEN s), s0)
      | "end" => (
	if (#end_as_id s0) then
	    (parser.IDENT, (ast.VS_TOKEN s), s0)
	else
	    (parser.END, (ast.VS_TOKEN s), s0))
      | "enumeration" => (parser.ENUMERATION, (ast.VS_TOKEN s), s0)
      | "equation" => (parser.EQUATION, (ast.VS_TOKEN s), s0)
      | "expandable" => (parser.EXPANDABLE, (ast.VS_TOKEN s), s0)
      | "extends" => (parser.EXTENDS, (ast.VS_TOKEN s), s0)
      | "external" => (parser.EXTERNAL, (ast.VS_TOKEN s), s0)
      | "false" => (parser.FALSE, (ast.VS_TOKEN s), s0)
      | "final" => (parser.FINAL, (ast.VS_TOKEN s), s0)
      | "flow" => (parser.FLOW, (ast.VS_TOKEN s), s0)
      | "for" => (parser.FOR, (ast.VS_TOKEN s), s0)
      | "function" => (parser.FUNCTION, (ast.VS_TOKEN s), s0)
      | "if" => (parser.IF, (ast.VS_TOKEN s), s0)
      | "import" => (parser.IMPORT, (ast.VS_TOKEN s), s0)
      | "impure" => (parser.IMPURE, (ast.VS_TOKEN s), s0)
      | "in" => (parser.IN, (ast.VS_TOKEN "IN"), s0)
      (*| "initial" => (parser.INITIAL, (ast.VS_TOKEN s), s0)*)
      | "initial" => (
	case yylex1 s0 of
	    (t1, (ast.VS_TOKEN v1), s1) => (
	    if (t1 = parser.ALGORITHM) then
		(parser.INITIALALGORITHM, (ast.VS_TOKEN s), s1)
	    else if (t1 = parser.EQUATION) then
		(parser.INITIALEQUATION, (ast.VS_TOKEN s), s1)
	    else
		(parser.IDENT, (ast.VS_TOKEN s), (unget_string (v1 ^ " ") s1)))
	  | (t1, _, s1) => raise Match)
      | "inner" => (parser.INNER, (ast.VS_TOKEN s), s0)
      | "input" => (parser.INPUT, (ast.VS_TOKEN s), s0)
      | "loop" => (parser.LOOP, (ast.VS_TOKEN s), s0)
      | "model" => (parser.MODEL, (ast.VS_TOKEN s), s0)
      | "not" => (parser.NOT, (ast.VS_TOKEN s), s0)
      | "operator" => (parser.OPERATOR, (ast.VS_TOKEN s), s0)
      | "or" => (parser.OR, (ast.VS_TOKEN s), s0)
      | "outer" => (parser.OUTER, (ast.VS_TOKEN s), s0)
      | "output" => (parser.OUTPUT, (ast.VS_TOKEN s), s0)
      | "package" => (parser.PACKAGE, (ast.VS_TOKEN s), s0)
      | "parameter" => (parser.PARAMETER, (ast.VS_TOKEN s), s0)
      | "partial" => (parser.PARTIAL, (ast.VS_TOKEN s), s0)
      | "protected" => (parser.PROTECTED, (ast.VS_TOKEN s), s0)
      | "public" => (parser.PUBLIC, (ast.VS_TOKEN s), s0)
      | "pure" => (parser.PURE, (ast.VS_TOKEN s), s0)
      | "record" => (parser.RECORD, (ast.VS_TOKEN s), s0)
      | "redeclare" => (parser.REDECLARE, (ast.VS_TOKEN s), s0)
      | "replaceable" => (parser.REPLACEABLE, (ast.VS_TOKEN s), s0)
      | "return" => (parser.RETURN, (ast.VS_TOKEN s), s0)
      | "stream" => (parser.STREAM, (ast.VS_TOKEN s), s0)
      | "then" => (parser.THEN, (ast.VS_TOKEN s), s0)
      | "true" => (parser.TRUE, (ast.VS_TOKEN s), s0)
      | "type" => (parser.TYPE, (ast.VS_TOKEN s), s0)
      | "when" => (parser.WHEN, (ast.VS_TOKEN s), s0)
      | "while" => (parser.WHILE, (ast.VS_TOKEN s), s0)
      | "within" => (parser.WITHIN, (ast.VS_TOKEN s), s0)
      | _ => (parser.IDENT, (ast.VS_TOKEN s), s0))

(* Scans a quoted ('...') identifier. *)

and scan_identifier_q (ss : char list) (s0 : lexstate_t) : scan_value_t = (
    let
	val (c0, s1) = (getchar s0)
    in
	case c0 of
	    NONE => raise (error_eof_in_q_ident s1)
	  | SOME (c as #"!") => (scan_identifier_q (ss @ [c]) s1)
	  | SOME (c as #"#") => (scan_identifier_q (ss @ [c]) s1)
	  | SOME (c as #"$") => (scan_identifier_q (ss @ [c]) s1)
	  | SOME (c as #"%") => (scan_identifier_q (ss @ [c]) s1)
	  | SOME (c as #"&") => (scan_identifier_q (ss @ [c]) s1)
	  | SOME (c as #"(") => (scan_identifier_q (ss @ [c]) s1)
	  | SOME (c as #")") => (scan_identifier_q (ss @ [c]) s1)
	  | SOME (c as #"*") => (scan_identifier_q (ss @ [c]) s1)
	  | SOME (c as #"+") => (scan_identifier_q (ss @ [c]) s1)
	  | SOME (c as #",") => (scan_identifier_q (ss @ [c]) s1)
	  | SOME (c as #"-") => (scan_identifier_q (ss @ [c]) s1)
	  | SOME (c as #".") => (scan_identifier_q (ss @ [c]) s1)
	  | SOME (c as #"/") => (scan_identifier_q (ss @ [c]) s1)
	  | SOME (c as #":") => (scan_identifier_q (ss @ [c]) s1)
	  | SOME (c as #";") => (scan_identifier_q (ss @ [c]) s1)
	  | SOME (c as #"<") => (scan_identifier_q (ss @ [c]) s1)
	  | SOME (c as #">") => (scan_identifier_q (ss @ [c]) s1)
	  | SOME (c as #"=") => (scan_identifier_q (ss @ [c]) s1)
	  | SOME (c as #"?") => (scan_identifier_q (ss @ [c]) s1)
	  | SOME (c as #"@") => (scan_identifier_q (ss @ [c]) s1)
	  | SOME (c as #"[") => (scan_identifier_q (ss @ [c]) s1)
	  | SOME (c as #"]") => (scan_identifier_q (ss @ [c]) s1)
	  | SOME (c as #"^") => (scan_identifier_q (ss @ [c]) s1)
	  | SOME (c as #"{") => (scan_identifier_q (ss @ [c]) s1)
	  | SOME (c as #"}") => (scan_identifier_q (ss @ [c]) s1)
	  | SOME (c as #"|") => (scan_identifier_q (ss @ [c]) s1)
	  | SOME (c as #"~") => (scan_identifier_q (ss @ [c]) s1)
	  | SOME (c as #" ") => (scan_identifier_q (ss @ [c]) s1)
	  | SOME #"\\" => (scan_identifier_q_escaped ss s1)
	  | SOME #"'" => (parser.IDENT, (ast.VS_TOKEN (implode ss)), s1)
	  | SOME #"\"" => (
	    if ((length ss) = 0) then
		raise (error_double_quote_in_q_ident s1)
	    else
		(scan_identifier_q (ss @ [#"\""]) s1))
	  | SOME c => (
	    if ((digit_p c) orelse (nondigit_p c)) then
		(scan_identifier_q (ss @ [c]) s1)
	    else
		raise (error_bad_character_in_q_ident s1))
    end)

and scan_identifier_q_escaped (ss : char list) (s0 : lexstate_t) : scan_value_t = (
    let
	val (c0, s1) = (getchar s0)
    in
	case c0 of
	    NONE => raise (error_eof_in_string s1)
	  | SOME (c as #"\"") => (scan_identifier_q (ss @ [c]) s1)
	  | SOME (c as #"\\") => (scan_identifier_q (ss @ [c]) s1)
	  | SOME (c as #"'") => (scan_identifier_q (ss @ [c]) s1)
	  | SOME (c as #"?") => (scan_identifier_q (ss @ [c]) s1)
	  | SOME #"a" => (scan_identifier_q (ss @ [#"\a"]) s1)
	  | SOME #"b" => (scan_identifier_q (ss @ [#"\b"]) s1)
	  | SOME #"f" => (scan_identifier_q (ss @ [#"\f"]) s1)
	  | SOME #"n" => (scan_identifier_q (ss @ [#"\n"]) s1)
	  | SOME #"r" => (scan_identifier_q (ss @ [#"\r"]) s1)
	  | SOME #"t" => (scan_identifier_q (ss @ [#"\t"]) s1)
	  | SOME #"v" => (scan_identifier_q (ss @ [#"\v"]) s1)
	  | SOME _ => raise (error_bad_s_escape_character s1)
    end)

(* (testing) *)

fun token_to_string (t : int) = (
    (*if (t = parser.EOF) then "*EOF*" else*)
    if (t = parser.ALGORITHM) then "ALGORITHM"
    else if (t = parser.AND) then "AND"
    else if (t = parser.ANNOTATION) then "ANNOTATION"
    else if (t = parser.BLOCK) then "BLOCK"
    else if (t = parser.BREAK) then "BREAK"
    else if (t = parser.CLASS) then "CLASS"
    else if (t = parser.CONNECT) then "CONNECT"
    else if (t = parser.CONNECTOR) then "CONNECTOR"
    else if (t = parser.CONSTANT) then "CONSTANT"
    else if (t = parser.CONSTRAINEDBY) then "CONSTRAINEDBY"
    else if (t = parser.DER) then "DER"
    else if (t = parser.DISCRETE) then "DISCRETE"
    else if (t = parser.EACH) then "EACH"
    else if (t = parser.ELSE) then "ELSE"
    else if (t = parser.ELSEIF) then "ELSEIF"
    else if (t = parser.ELSEWHEN) then "ELSEWHEN"
    else if (t = parser.ENCAPSULATED) then "ENCAPSULATED"
    else if (t = parser.END) then "END"
    else if (t = parser.ENUMERATION) then "ENUMERATION"
    else if (t = parser.EQUATION) then "EQUATION"
    else if (t = parser.EXPANDABLE) then "EXPANDABLE"
    else if (t = parser.EXTENDS) then "EXTENDS"
    else if (t = parser.EXTERNAL) then "EXTERNAL"
    else if (t = parser.FALSE) then "FALSE"
    else if (t = parser.FINAL) then "FINAL"
    else if (t = parser.FLOW) then "FLOW"
    else if (t = parser.FOR) then "FOR"
    else if (t = parser.FUNCTION) then "FUNCTION"
    else if (t = parser.IF) then "IF"
    else if (t = parser.IMPORT) then "IMPORT"
    else if (t = parser.IMPURE) then "IMPURE"
    else if (t = parser.IN) then "IN"
    else if (t = parser.INITIALALGORITHM) then "INITIAL ALGORITHM"
    else if (t = parser.INITIALEQUATION) then "INITIAL EQUATION"
    else if (t = parser.INNER) then "INNER"
    else if (t = parser.INPUT) then "INPUT"
    else if (t = parser.LOOP) then "LOOP"
    else if (t = parser.MODEL) then "MODEL"
    else if (t = parser.NOT) then "NOT"
    else if (t = parser.OPERATOR) then "OPERATOR"
    else if (t = parser.OR) then "OR"
    else if (t = parser.OUTER) then "OUTER"
    else if (t = parser.OUTPUT) then "OUTPUT"
    else if (t = parser.PACKAGE) then "PACKAGE"
    else if (t = parser.PARAMETER) then "PARAMETER"
    else if (t = parser.PARTIAL) then "PARTIAL"
    else if (t = parser.PROTECTED) then "PROTECTED"
    else if (t = parser.PUBLIC) then "PUBLIC"
    else if (t = parser.PURE) then "PURE"
    else if (t = parser.RECORD) then "RECORD"
    else if (t = parser.REDECLARE) then "REDECLARE"
    else if (t = parser.REPLACEABLE) then "REPLACEABLE"
    else if (t = parser.RETURN) then "RETURN"
    else if (t = parser.STREAM) then "STREAM"
    else if (t = parser.THEN) then "THEN"
    else if (t = parser.TRUE) then "TRUE"
    else if (t = parser.TYPE) then "TYPE"
    else if (t = parser.WHEN) then "WHEN"
    else if (t = parser.WHILE) then "WHILE"
    else if (t = parser.WITHIN) then "WITHIN"
    (* Syntactic characters. *)
    else if (t = parser.DEF) then ":="
    else if (t = (Char.ord #"=")) then "="
    else if (t = (Char.ord #":")) then ":"
    else if (t = (Char.ord #";")) then ";"
    else if (t = (Char.ord #".")) then "."
    else if (t = (Char.ord #",")) then ","
    else if (t = (Char.ord #"(")) then "("
    else if (t = (Char.ord #")")) then ")"
    else if (t = (Char.ord #"[")) then "["
    else if (t = (Char.ord #"]")) then "]"
    else if (t = (Char.ord #"{")) then "{"
    else if (t = (Char.ord #"}")) then "}"
    (* Operator characters. *)
    else if (t = parser.RELATIONAL_OPERATOR) then "RELATIONAL_OPERATOR"
    else if (t = parser.ADD_OPERATOR) then "ADD_OPERATOR"
    else if (t = parser.MUL_OPERATOR) then "MUL_OPERATOR"
    else if (t = parser.EXP_OPERATOR) then "EXP_OPERATOR"
    (* Lexical tokens. *)
    (* "\"" ^ s ^ "\"" *)
    else if (t = parser.STRING) then "STRING"
    (* "#|" ^ s ^ "|#" *)
    else if (t = parser.IDENT) then "IDENT"
    (* Real.toString v *)
    else if (t = parser.UNSIGNED_NUMBER) then "NUMBER"
    (*else if (t = 0) then "EOF"*)
    else "*BAD*")

(* It invokes a parser.  It returns (name_t * class_definition_t list)
   with name from a within-clause. *)

fun parse_file (filename : string) = (
    let
	val f = TextIO.openIn filename
	val s = {s = f, line = 0, column = 0, unget = [], end_as_id = false}
	(*lexprint s*)
	val yysm = parser.yyparse (!debug_parser) yylex1 s
	val _ = TextIO.closeIn f
    in
	case (parser.yyvs_ref yysm 0) of
	    ast.VS_MAIN v => v
	  | _ => (ast.syntax_error "(internal)")
    end)

and lexprint (s0 : lexstate_t) = (
    let
	val (t, v, s1) = (yylex1 s0)
    in
	if (t = 0) then
	    ()
	else
	    ((print ("[" ^ (token_to_string t) ^ "]")) ; (lexprint s1))
    end)

end
