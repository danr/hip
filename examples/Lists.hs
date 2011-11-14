module Lists where

import Prelude ()

(++) :: [a] -> [a] -> [a]
(x:xs) ++ ys = x:(xs ++ ys)
[]     ++ ys = ys

prove = prove
(==) = (==)

prop_append_assoc :: [a] -> [a] -> [a] -> ()
prop_append_assoc xs ys zs = prove (((xs ++ ys) ++ zs) == ((xs ++ ys) ++ zs))