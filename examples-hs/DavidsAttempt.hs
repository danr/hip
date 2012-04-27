module DavidsAttempt where

davidsfix f = let x = f x in x

davidsfix' f = x
  where x = f x
