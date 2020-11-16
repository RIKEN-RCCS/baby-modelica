(* check_hashtable.sml -*-Coding: us-ascii-unix;-*- *)

use "hashtable.sml" ;

fun seq n s = if (n <= 0) then s else seq (n - 1) ((n - 1) :: s)

fun sort (ee : (string * 'b) list) = (
    case ee of
	[] => []
      | (hd :: tl) => (
        ((sort (List.filter (fn e => (#1 e) < (#1 hd)) tl))
	 @ [hd]
	 @ (sort (List.filter (fn e => not ((#1 e) < (#1 hd))) tl)))))

val a : (string, int) HashTable.hash_table
    = HashTable.mkTable (10, Fail "bad") ;

HashTable.insert a ("baka", 1) ;
HashTable.insert a ("baka", 3) ;
HashTable.insert a ("boke", 2) ;
HashTable.insert a ("boke", 4) ;

val x0_ = HashTable.find a "baka" ;
if (x0_ = SOME 3) then () else raise Match ;
val x1_ = HashTable.find a "boke" ;
if (x1_ = SOME 4) then () else raise Match ;

val x2_ = HashTable.listItemsi a ;
if ((length x2_) = 2) then () else raise Match ;
if ((sort x2_) = (sort [("baka", 3), ("boke", 4)])) then () else raise Match ;

val b = seq 10 [] ;
(app (HashTable.insert a) (map (fn i => ((Int.toString i), i)) b)) ;

val x3_ = HashTable.listItemsi a ;
if ((length x3_) = 12) then () else raise Match ;

val x4_ = HashTable.find a "3" ;
if (x4_ = SOME 3) then () else raise Match ;

val c = seq 100 [] ;
(app (HashTable.insert a) (map (fn i => ((Int.toString i), i)) c)) ;
(app (HashTable.insert a) (map (fn i => ((Int.toString i), i)) c)) ;

val x5_ = HashTable.listItemsi a ;
if ((length x5_) = 102) then () else raise Match ;

(*HashTable.appi (fn (k,v) => (print (k ^"->"^ (Int.toString v) ^"\n"))) a ;*)

HashTable.appi
    (fn (k, v) =>
	if (k = "baka") then if (v = 3) then () else raise Match
	else if (k = "boke") then if (v = 4) then () else raise Match
	else if (k = (Int.toString v)) then () else raise Match)
    a ;
