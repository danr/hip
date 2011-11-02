-- http://dream.inf.ed.ac.uk/projects/lemmadiscovery/case_results.php

theory CaseAnalysis2
imports ATP_Linkup IsaP
begin

datatype N = zero  ("zero")
           | suc N ("suc _" [100] 100)
instance N :: one ..
instance N :: ord ..
instance N :: plus ..
instance N :: times ..

translations "0" == "zero"
declare N.inject[wrule]

primrec
  add_0[wrule]    :  "(0 + y) = (y :: N)"
  add_suc[wrule]  :  "suc x + y = suc (x + y)"

primrec
  mult_0[wrule]    :  "(x * 0) = (0 :: N)"
  mult_suc[wrule]  :  "x * (suc y) = x + (x * y)"

fun minus :: "N => N => N" (infix "minus" 520)
where
  minus_0:     "0 minus m = 0"
  | minus_suc: "(suc m) minus n = (case n of 0 => (suc m) | suc k => m minus k)"
declare minus_0[wrule]
declare minus_suc[wrule]

fun less :: "N => N => bool" (infix "less" 520)
where
  less_0  : "(x :: N) less 0 = False" |
  less_suc : "x less (suc y) = (case x of 0 => True | suc z => (z less y))"
declare less_0[wrule]
declare less_suc[wrule]

fun less_eq :: "N => N => bool" (infix "leq" 520)
where
  less_eq_0: "(0::N) leq y = True" |
  less_eq_suc:  "(suc x) leq y = (case y of 0 => False | suc z => (x leq z))"
declare less_eq_0[wrule]
declare less_eq_suc[wrule]

 fun max :: "N \<Rightarrow> N \<Rightarrow> N"
where
    max_0: "max 0 y = y"
  | max_suc: "max (suc x) y = (case y of 0 => (suc x) | suc z => suc(max x z))"
declare max_0[wrule]
declare max_suc[wrule]

fun min :: "N \<Rightarrow> N \<Rightarrow> N"
where
    min_0: "min 0 y = 0"
  | min_suc: "min (suc x) y = (case y of 0 => y | suc z => suc(min x z))"
declare min_0[wrule]
declare min_suc[wrule]

end
