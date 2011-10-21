
mix a b = case Tup2 a b of
               { Tup2 Zero y -> a
               ; Tup2 x    y -> b
               } ;
