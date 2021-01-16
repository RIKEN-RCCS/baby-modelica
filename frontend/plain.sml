(* plain.sml -*-Coding: us-ascii-unix;-*- *)
(* Copyright (C) 2018-2021 RIKEN R-CCS *)

(* SIMPLE UTILITY FUNCTIONS. *)

structure plain = struct

val error_dimension_index_mismatch = Match
val error_array_index = Match

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

(* Partitions a list by groups with regard to a given equality.
   Non-groups are singletons. *)

fun list_groups eq [] = []
  | list_groups eq (a :: tt) = (
    let
	val (gg, rr) = (List.partition (fn x => eq (a, x)) tt)
    in
	([(a :: gg)] @ (list_groups eq rr))
    end)

(* Uniquifies with respect to eq and keeps the last one.  Slow. *)

fun list_uniquify eq x = (rev (remove_duplicates eq (rev x)))

(* Subtracts a subset sub from a superset sup with regard to
   (=). Slow. *)

fun list_diff sup sub = (
    (foldl (fn (e, residue) => (List.filter (fn x => (not (x = e))) residue))
	   sup sub))

(* Tests if all are equal with regard to a given equality. *)

fun list_all_equal eq ee = (
    case ee of
	[] => true
      | (e :: tt) => (List.all (fn x => (eq (e, x))) tt))

(* Returns a unique value if all are equal with regard to a given
   equality.  It errs on an empty list.  It returns the first element
   as (SOME e) or NONE. *)

fun list_unique_value eq ee = (
    case ee of
	[] => raise Match
      | e :: tt => (if (list_all_equal eq ee) then (SOME e) else NONE))

(* Returns an escaped string enclosed by "...". *)

fun quote_string s = ("\""^ (String.toString s) ^ "\"")

(* Returns an integer list from m to n-1. *)

fun int_seq m n = (
    if (m >= n) then
	[]
    else
	(m :: (int_seq (m + 1) n)))

fun z_seq lb step (n :int) : int list = (
    if (n <= 0) then
	[]
    else
	lb :: (z_seq (lb + step) step (n - 1)))

fun r_seq lb step (n : int): real list = (
    if (n <= 0) then
	[]
    else
	lb :: (r_seq (lb + step) step (n - 1)))

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

fun iterate_dimension f dim = (fill_dimension f [] dim)

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

fun check_array_index dimension index = (
    if (List.all (op >=) (ListPair.zip (dimension, index))) then ()
    else raise error_array_index)

(* Returns an offset for an index.  An array is row-major, and an
   index is 1-origin.  Call it with offset=0.  (An offset of
   [i+1,j+1,k+1] in a [4,3,2] array is (3*2*i+2*j+k).  It accepts an
   index shorter than a dimension, in which case it returns a start
   offset of a subarray. *)

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

(* Drops the first n dimensions. *)

fun array_drop_dimensions dimension count = (
    (List.drop (dimension, count)))

(* Accesses an index-th row of an array.  It returns a pair of a
   dimension and contents. *)

fun array_access index (dim0, ee0) = (
    let
	val _ = (check_array_index dim0 index)
	val dim1 = (List.drop (dim0, (length index)))
	val size = (array_size dim1)
	val offset = (array_index dim0 index 0)
	val ee1 = (List.take ((List.drop (ee0, offset)), size))
    in
	(dim1, ee1)
    end)

(* Accesses a i-th row (1-origin) of an array.  It returns a pair of a
   dimension and contents. *)

fun array_access1__ i (dim0, ee0) = (
    case dim0 of
	[] => raise Match
      | (d :: dim1) => (
	let
	    val size = (array_size dim1)
	    val offset = ((i - 1) * size)
	    val ee1 = (List.drop (ee0, offset))
	    val ee2 = (List.take (ee1, size))
	in
	    (dim1, ee2)
	end))

fun list_prefix eq x y = (
    ((length x) <= (length y)) andalso (List.all eq (ListPair.zip (x, y))))

fun list_suffix eq x y = (
    (list_prefix eq (List.rev x) (List.rev y)))

(* Unions sets in a bag if they intersect.  It takes a list of lists
   as a bag of sets.  Do not enter the empty set. *)

fun make_unions eq bag = (
    let
	fun intersects eq uu vv = (
	    (List.exists (fn y => (List.exists (fn x => (eq (x, y))) vv)) uu))

	fun insert eq x ww = (
	    if (List.exists (fn y => (eq (x, y))) ww) then ww else (x :: ww))

	fun merge eq (uu, vv) = (
	    (foldl (fn (x, ww) => (insert eq x ww)) vv uu))

	fun merge_if_intersects eq x uu = (
	    let
		val (vv, others) = (List.partition (intersects eq x) uu)
	    in
		((foldl (merge eq) [] (x :: vv)) :: others)
	    end)
    in
	(foldl (fn (x, uu) => (merge_if_intersects eq x uu)) [] bag)
    end)

(* Filters list elements by a list of booleans. *)

fun list_select bitmap xx = (
    (foldl (fn ((b, x), acc) => if b then x :: acc else acc)
	   [] (ListPair.zip (bitmap, xx))))

(* Repeats v in a list n times. *)

fun list_repeat v n acc = (
    if (n <= 0) then
	acc
    else
	(list_repeat v (n - 1) (v :: acc)))

(* Transposes a list of lists.  Element lists are truncated to the
   shortest one. *)

fun list_transpose ee = (
    if (List.exists null ee) then
	[]
    else
	let
	    val hds = (map hd ee)
	    val tls = (map tl ee)
	in
	    hds :: (list_transpose tls)
	end)

(* Sorts a list to make each cmp (ai,aj) true for (i<j). *)

fun list_sort cmp (ee : 'a list) = (
    case ee of
	[] => []
      | p :: tl => (
	let
	    val (ll, hh) = (List.partition (fn e => cmp (e, p)) tl)
	in
	    ((list_sort cmp ll) @ [p] @ (list_sort cmp hh))
	end))

fun foldl_one_and_others_loop f acc dd ee = (
    case ee of
	[] => acc
      | e :: tl => (
	foldl_one_and_others_loop f (f (e, (dd @ tl), acc)) (dd @ [e]) tl))

(* Calls f with (e,ee\e,acc) one (e) and the others (ee\e) with a
   folding result (acc). *)

fun foldl_one_and_others f acc ee = (
    (foldl_one_and_others_loop f acc [] ee))

end
