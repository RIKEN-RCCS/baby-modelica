(* hashtable.sml -*-Coding: us-ascii-unix;-*- *)

(* STRING-KEY HASHTABLE. *)

(* See smlnj/smlnj-lib/Util/hash-table-sig.sml. *)
(* See polyml/mlsource/MLCompiler/HashTable.ML. *)

structure HashTable :
sig
    type ('a, 'b) hash_table
    val mkTable : (int * exn) -> (string, 'b) hash_table
    val clear : (string, 'b) hash_table -> unit
    val insert : (string, 'b) hash_table -> (string * 'b) -> unit
    val find : (string, 'b) hash_table -> string -> 'b option
    val remove : (string, 'b) hash_table -> string -> 'b
    val listItemsi : (string, 'b) hash_table -> (string * 'b) list
    val appi : ((string * 'b) -> unit) -> (string, 'b) hash_table -> unit
end = struct

datatype ('a, 'b) hash_table
    = Hashtable of {
	count : int ref,
	entries : (string * 'b) list array ref,
	hash : (string -> int) ref}

(* String hasher in the compiler of Polyml. *)

fun hash_string (n : int) (s : string) : int = (
    (Word.toInt
	 (Word.mod
	      ((CharVector.foldr
		    (fn (c, acc) =>
			(Word.fromInt (Char.ord c)) + 0w7*acc)
		    0w0
		    s),
	       (Word.fromInt n)))))

fun mkTable (n, _)  = (
    Hashtable {
	count = ref 0,
	entries = ref (Array.array (n, [])),
	hash = ref (hash_string n)}
    handle Size => (
	raise Fail ("HashTable.mkTable n="^ Int.toString n)))

fun find (Hashtable {entries, hash, ...}) (key : string) : 'b option = (
    let
	fun findloop [] = NONE
	  | findloop ((n, v) :: t) = (
	    if n = key then
		SOME v
	    else
		findloop t)

	val A = !entries
	val hashfn = !hash
	val i = (hashfn key)
    in
	findloop (Array.sub (A, i))
    end)

fun insert (ht as Hashtable {entries, count, hash}) (key : string, value : 'b) = (
    let
	fun insertloop [] = (
	    (count := !count + 1 ;
	     [(key, value)]))
	  | insertloop ((n, v) :: ee) = (
	    if (n = key) then
		((key, value) :: ee)
	    else
		((n, v) :: (insertloop ee)))

	fun copy ht A : unit = (
	    (Array.app (app (insert ht)) A))

	val A = !entries
	val hashfn = !hash
	val N = Array.length A
	val i = (hashfn key)
    in
	(Array.update (A, i, insertloop (Array.sub (A, i))) ;
	 if (!count * 5 <= N * 4) then
	     ()
	 else
	     let
		 val N2 = N * 2
	     in
		 (count := 0 ;
		  entries := Array.array (N2, []) ;
		  hash := hash_string N2 ;
		  copy ht A)
	     end)
    end)

fun remove (ht as Hashtable {entries, count, hash}) (key : string) : 'b = (
    let
	fun removeloop [] = (NONE, [])
	  | removeloop ((n, v) :: t) = (
	    if n = key then (
		(count := !count - 1 ;
		 (SOME v, t)))
	    else
		let
		    val (e, r) = (removeloop t)
		in
		    (e, (n, v) :: r)
		end)

	val A = !entries
	val hashfn = !hash
	val i = (hashfn key)
	val (e, ee) = (removeloop (Array.sub (A, i)))
    in
	case e of
	    NONE => raise Match
	  | SOME v => (
	    (Array.update (A, i, ee) ;
	     v))
    end)

fun clear (ht as Hashtable {entries, count, hash}) = (
    (count := 0 ;
     entries := Array.array (Array.length (!entries), [])))

fun listItemsi (ht as Hashtable {entries, count, hash}) = (
    (Array.foldl (op @) [] (!entries)))

fun appi f (ht as Hashtable {entries, count, hash}) = (
    (Array.app (List.app f) (!entries)))

end
