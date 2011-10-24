
const a b = a;

mix a b = case Tup3 a    b (const a b) of
             { Tup3 Zero y    z -> z
             ; Tup3 x    Zero z -> const x z
             ; j                -> b
             };

