
if b t f = case b of
    { True  -> t
    ; False -> f
    };

if2 b t f = case b of
    { True -> t
    ; _    -> f
    };

