
data T 2;
data True 0 False 0;

bugged p a b = case T a b of
            { T x y | p x -> x
            ; x           -> b
            };

fixed p a b = case T a b of
            { T x y | p x -> x
            ; r           -> b
            };