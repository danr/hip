
mix a b f = case Tup3 a b (f a b) of
              { Tup3 Zero y z -> z
              ; Tup3 x y Zero -> f b y
              ; Tup3 x y    z -> f y z
              } ;
