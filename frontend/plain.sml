(* plain.sml -*-Coding: us-ascii-unix;-*- *)
(* Copyright (C) 2018-2020 RIKEN R-CCS *)

(* SIMPLE UTILITY FUNCTIONS. *)

structure plain = struct

val error_dimension_index_mismatch = Match

fun assert (x : bool) : unit = if (x) then () else raise Match

(* It is an error for NONE. *)

val surely = valOf

(* Returns the prefix and the last.  It is SLOW because it reverses a
   list twice. *)

fun split_last ss = (
    case (List.rev ss) of
	[] => raise Match
      | (t :: p) => ((List.rev p), t))

(* Makes prefix lists, shorter lists come in front.  It returns [] =>
   [], and [1,2,3] => [[1],[1,2],[1,2,3]]. *)

fun list_prefixes [] = []
  | list_prefixes (h :: t) = (
    [h] :: (map (fn x => (h :: x)) (list_prefixes t)))

(* Like List.find, but returns the one returned by a function. *)

fun list_find_some f [] = NONE
  | list_find_some f (h :: t) = (
    case (f h) of
	NONE => (list_find_some f t)
      | SOME x => SOME x)

(* Like List.filter, but returns the ones returned by a function.  It
   is slow by appending (O(N2)). *)

fun gather_some f ee = (
    (foldl
	 (fn (e, acc) => case (f e) of
			     NONE => acc
			   | SOME x => (acc @ [x]))
	 [] ee))

(* Maps f along with folding a second argument.  f is called with
   (e0,a0) and returns (e1,a1), for each element e0 and a second
   argument a0. *)

fun map_along f (ee, a) = (
    (foldl
	 (fn (e0, (ee0, a0)) =>
	     let
		 val (e1, a1) = f (e0, a0)
	     in
		 ((ee0 @ [e1]), a1)
	     end)
	 ([], a)
	 ee))

(* Maps f along with folding a passing around a0.  It is like
   map_along but it collects the results by appending. *)

fun gather_along f (ee, a) = (
    (foldl
	 (fn (e0, (ee0, a0)) =>
	     let
		 val (ee1, a1) = f (e0, a0)
	     in
		 ((ee0 @ ee1), a1)
	     end)
	 ([], a)
	 ee))

(* Tries each element until f returns SOME, and returns the list
   except the one found.  Or, it returns d with the original list if
   none is found.  Call it with residue=[]. *)

fun find_and_drop f d residue [] = (d, residue)
  | find_and_drop f d residue (m :: t) = (
    case (f m) of
	NONE => (find_and_drop f d (residue @ [m]) t)
      | SOME v => (v, (residue @ t)))

(* Removes duplicates.  It is a simple O(N^2) algorithm. *)

fun remove_duplicates eq [] = []
  | remove_duplicates eq (a :: t) = (
    (a :: (remove_duplicates eq (List.filter (fn x => not (eq (a, x))) t))))

(* Partitions sets of duplicates with regard to a given equality.
   Non-duplicating sets are singletons *)

fun list_duplicates eq [] = []
  | list_duplicates eq (a :: t) = (
    let
	val (d, r) = (List.partition (fn x => eq (a, x)) t)
    in
	([(a :: d)] @ (list_duplicates eq r))
    end)

(* Uniquifies with respect to eq and keeps the last one.  Slow. *)

fun list_uniquify eq x = (rev (remove_duplicates eq (rev x)))

(* Subtracts a subset sub from a superset sup with regard to
   (=). Slow. *)

fun list_diff sup sub = (
    (foldl (fn (e, residue) => (List.filter (fn x => (not (x = e))) residue))
	   sup sub))

(* Tests if all are equal with regard to a given equality.  It returns
   SOME (SOME e) of a first item, SOME NONE if a list is empty, or
   NONE if not. *)

fun list_all_equal eq [] = SOME NONE
  | list_all_equal eq (e :: t) = (
    if (List.all (fn x => (eq (x, e))) t) then SOME (SOME e) else NONE)

(* Returns an escaped string enclosed by "...". *)

fun quote_string s = ("\""^ (String.toString s) ^ "\"")

(* Returns an integer list from m to n-1. *)

fun int_seq m n = (
    if (m >= n) then
	[]
    else
	(m :: (int_seq (m + 1) n)))

(* Returns a list by calling f on each index in the dimension.  Note
   that an index is one-origin. *)

fun fill_dimension f index0 dim0 = (
    case dim0 of
	[] => [(f index0)]
      | (d :: dim1) => (
	(List.concat
	     (map
		  (fn i => (fill_dimension f (index0 @ [i + 1]) dim1))
		  (int_seq 0 d)))))

(* Partitions a list by n elements each.  It is required that the
   length of a list is multiple of n. *)

fun list_partition_by_n n ee = (
    let
	fun take_n_loop n acc0 acc1 i ee = (
	    if (i = n) then
		(take_n_loop n (acc0 @ [acc1]) [] 0 ee)
	    else
		case ee of
		    [] => (
		    let
			val _ = if (null acc1) then () else raise Match
		    in
			acc0
		    end)
		  | e :: ee' => (
		    (take_n_loop n acc0 (acc1 @ [e]) (i + 1) ee')))
    in
	(take_n_loop n [] [] 0 ee)
    end)

(* Returns a position of (f x)=true in a list l (call it with i=0). *)

fun list_index f l i = (
    case l of
	[] => NONE
      | (x :: t) => (
	if (f x) then SOME i else (list_index f t (i + 1))))

(* Returns the shortest one in a list of lists. *)

fun list_shortest ll = (
    case ll of
	[] => raise Match
      | (h :: tl) => (
	(#1 (foldl (fn (e, (x, xlen)) => (
			if ((length e) < xlen) then
			    (e, (length e))
			else
			    (x, xlen)))
		   (h, (length h)) tl))))

(* Returns an offset for an index.  It is row-major.  An index is
   1-origin.  Call it with offset=0.  ([i+1,j+1,k+1] in an [4,3,2]
   array is (3*2*i+2*j+k).  It accepts an index shorter than a
   dimension, in which case it returns a start offset of a
   subarray. *)

fun array_index dimension0 index0 offset = (
    case (dimension0, index0) of
	([], []) => offset
      | ([], _) => raise error_dimension_index_mismatch
      | (d :: dimension1, []) => (
	(array_index dimension1 [] ((d * offset) + 0)))
      | (d :: dimension1, i :: index1) => (
	(array_index dimension1 index1 ((d * offset) + (i - 1)))))

fun array_size dimension = (
    (array_index dimension [] 1))

fun list_prefix eq x y = (
    ((length x) < (length y)) andalso (List.all eq (ListPair.zip (x, y))))

fun list_suffix eq x y = (
    (list_prefix eq (List.rev x) (List.rev y)))

end
