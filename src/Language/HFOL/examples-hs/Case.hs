data Nat = Succ Nat | Zero
data List a = Nil | Cons a (List a)

plus m n = case m of
               Zero -> n
               Succ m' -> plus m' n

filter p Nil = Nil
filter p (x `Cons` xs) = case p x of
                     True  -> x `Cons` filter p xs
                     False -> filter p xs

filter' p Nil = Nil
filter' p (x `Cons` xs) = case p x of
                     True  -> x `Cons` rest
                     False -> rest
  where rest = filter' p xs

