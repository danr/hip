theory CaseAnalysis_L2
imports CaseAnalysis2
begin

datatype 'a List =
    nil    ("[]")
  | cons 'a  "'a List"    (infixr "#" 65)
syntax
  -- {* list Enumeration *}
  "@list" :: "args => 'a List"    ("[(_)]")
translations
  "[x, xs]" == "x#[xs]"
  "[x]" == "x#[]"

fun append :: "'a List => 'a List => 'a List" (infixr "@" 65)
where
  append_Nil:"[] @ ys = ys"
  | append_Cons: "(x#xs) @ ys = x # xs @ ys"
declare append_Nil[wrule]
declare append_Cons[wrule]

fun last :: "'a List => 'a"
where
last_cons : "last(x#xs) = (if xs=[] then x else last xs)"
declare last_cons[wrule]

fun butlast :: "'a List => 'a List"
  where
  butlast_nil: "butlast []= []"
  | butlast_cons: "butlast(x#xs) = (if xs=[] then [] else x#butlast xs)"
declare butlast_cons[wrule]
declare butlast_nil[wrule]

fun map :: "('a=>'b) => ('a List => 'b List)"
  where
  map_nil: "map f [] = []"
  | map_cons :"map f (x#xs) = f(x)#map f xs"
declare map_cons[wrule]
declare map_nil[wrule]

fun rev :: "'a List => 'a List"
  where 
  rev_nil: "rev([]) = []"
  | rev_cons: "rev(x#xs) = rev(xs) @ [x]"
declare rev_cons[wrule]
declare rev_nil[wrule]

fun filter :: "('a => bool) => 'a List => 'a List"
where
  filter_nil: "filter P [] = []"
  | filter_cons: "filter P (x#xs) = (if P x then x#filter P xs else filter P xs)"
declare filter_cons[wrule]
declare filter_nil[wrule]

fun takeWhile :: "('a => bool) => 'a List => 'a List"
  where
  takeWhile_nil: "takeWhile P [] = []"
  | takeWhile_cons: "takeWhile P (x#xs) = (if P x then x#takeWhile P xs else [])"
declare takeWhile_cons[wrule]
declare takeWhile_nil[wrule]

fun dropWhile :: "('a => bool) => 'a List => 'a List"
where
  dropWhile_nil: "dropWhile P [] = []"
  | dropWhile_cons: "dropWhile P (x#xs) = (if P x then dropWhile P xs else x#xs)"
declare dropWhile_cons[wrule]
declare dropWhile_nil[wrule]

fun member :: "'a => 'a List => bool" (infixl "mem" 55)
where 
  mem_nil: "x mem [] <-> False"
  | mem_cons: "x mem (y#ys) <-> (if y = x then True else x mem ys)"
declare mem_nil[wrule]
declare mem_cons[wrule]

fun delete :: "'a => 'a List => 'a List"
where
	  del_nil: "delete x [] = []"
	| del_cons: "delete x (y#ys) = (if (x=y) then (delete x ys) else y#(delete x ys))"
declare del_nil[wrule]
declare del_cons[wrule]

fun drop :: "N => 'a List => 'a List" 
where
	drop_Nil:"drop n [] = []"
	|	drop_Cons: "drop n (x#xs) = (case n of 0 => x#xs | suc(m) => drop m xs)"
declare drop_Nil[wrule]
declare drop_Cons[wrule]

fun take :: "N => 'a List => 'a List"
where
 	take_Nil:"take n [] = []"
  | take_Cons: "take n (x#xs) = (case n of 0 => [] | suc(m) => x # take m xs)"
declare take_Nil[wrule]
declare take_Cons[wrule]

fun zip :: "'a List => 'a List => ('a * 'a) List"
where
	zip_nil: "zip xs [] = []"
  | zip_Cons: "zip xs (y#ys) = (case xs of [] => [] | z#zs => (z,y)#zip zs ys)"
declare zip_nil[wrule]
declare zip_Cons[wrule]

fun len :: "'a List => N"   ("len _" [500] 500)
where
  len_nil:     "len [] = 0" |
  len_cons:    "len (h # t) = suc (len t)"
declare len_nil[wrule]
declare len_cons[wrule]

fun ins :: "N => (N List) => (N List)" 
where	
	insert_nil: "ins n [] = [n]" |
	insert_cons: "ins n (h#t) = (if (n less h) then n#h#t else h#(ins n t))"
declare insert_nil[wrule]
declare insert_cons[wrule]

(* Like insertion in set, only allows one of each element *)
fun ins_1 :: "'a => ('a List) => ('a List)" 
where
	ins_1_nil: "ins_1 n [] = [n]" |
	ins_1_cons: "ins_1 n (h#t) = (if n=h then (n#t) else h#(ins_1 n t))"
declare ins_1_nil[wrule]
declare ins_1_cons[wrule]


fun count :: "'a => 'a List => N"
where
		count_nil[simp]: "count x [] = 0" |
		count_cons[simp]: "count x (y#ys) = (if (x=y) then (suc(count x ys)) else (count x ys))"
declare count_nil[wrule]
declare count_cons[wrule]

fun sorted :: "N List => bool" 
where
		sorted_nil: "sorted [] = True" |
		sorted_cons: "sorted (x#xs) = 
      (case xs of [] => True 
       | (y#ys) => (x leq y) & sorted (y#ys))"

fun insort :: "N => N List => N List" where
		insort_nil: "insort x [] = [x]" |
		insort_cons: "insort x (y#ys) = (if (x leq y) then (x#y#ys) else y#(insort x ys))"

fun sort :: "N List => N List" where
		sort_nil: "sort [] = []" |
		sort_cons: "sort (x#xs) = insort x (sort xs)"

declare sorted_nil[wrule]
declare sorted_cons[wrule]
declare insort_nil[wrule]
declare insort_cons[wrule]
declare sort_nil[wrule]
declare sort_cons[wrule]

end
