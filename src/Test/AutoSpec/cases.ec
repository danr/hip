rest x y b xs = case b of {
                   True  -> rmadjdups (Cons x xs) ;
                   False -> Cons y (rmadjdups (Cons x xs)) ;
                   mystery -> fail ;
                   } ;

rmadjdups xs = case xs of {
                    Nil -> Nil ;
                    (Cons x Nil) -> Cons x Nil ;
                    (Cons y (Cons x xs)) -> rest x y (equals x y) xs ;                    
                    } ;
