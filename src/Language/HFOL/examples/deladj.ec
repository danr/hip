
data True 0 False 0;
data Cons 2 Nil 0;

if b t f = case b of
         { True -> t
         ; _    -> f
         };

deleteAdjacent eq xs = case xs of
   { Cons x (Cons y ys) -> if (eq x y) (deleteAdjacent eq (Cons x ys))
                                     (Cons x (deleteAdjacent eq (Cons y ys)))
   ; d -> d
   };

