
if b t f = case b of
         { True -> t
         ; _    -> f
         };

deleteAdjacent eq xs = case xs of 
   { Cons x (Cons y ys) -> if (eq x y) (deleteAdjacent (Cons x ys))
                                     (Cons x (deleteAdjacent (Cons y ys))) 
   ; d -> d
   };

