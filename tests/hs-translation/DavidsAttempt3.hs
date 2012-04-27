flip f a b = f b a
swap = flip (,)

d a b c = let d a = b in d a

(++) = (++)

(>>) = (>>)

let_in x y =let in'let'in=let in let in x in
	     let in let
    let'in let_ _in =
      let_>>_in in
     in'let'in++
		    let in_let'in=let
	        	  in y in let'in
  in_let'in in'let'in
