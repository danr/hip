data A 0 B 0 C 0;

conflict p x = case p x of
           { True -> A
           ; _ | p x -> B
           ; _ -> C
           };