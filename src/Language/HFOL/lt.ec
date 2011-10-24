lt n m = case Tup2 n m of {
              Tup2 _      Zero   -> False;
              Tup2 Zero   _      -> True;
              Tup2 (Succ n2) (Succ m2) -> lt n2 m2 };

