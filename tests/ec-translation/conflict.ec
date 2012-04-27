data T = A | B | C;

conflict p x = case p x of
           { True -> A
           ; _ | p x -> B
           ; _ -> C
           };