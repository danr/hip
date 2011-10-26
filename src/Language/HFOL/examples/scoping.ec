data T 2;

bugged p a b = case T a b of
            { T x y | p x -> x
            ; x           -> b
            };

fixed p a b = case T a b of
            { T x y | p x -> x
            ; r           -> b
            };