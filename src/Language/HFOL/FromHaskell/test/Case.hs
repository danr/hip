data Nat = Succ Nat | Zero

plus m n = case m of
               Zero -> n
               Succ m' -> plus m' n

filter p [] = []
filter p (x:xs) = case p x of
                     True  -> x : filter p xs
                     False -> filter p xs

filter' p [] = []
filter' p (x:xs) = case p x of
                     True  -> x : rest
                     False -> rest
  where rest = filter' p xs
