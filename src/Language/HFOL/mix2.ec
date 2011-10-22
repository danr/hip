
f a b = a;

mix a b = case f a b of
               { Zero -> a
               ; x    -> j
               } ;
