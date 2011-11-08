

f . g = \x -> f (g x)

data  Bool  =  False | True     deriving (Eq, Ord, Enum, Read, Show, Bounded)

-- Boolean functions


(&&), (||)       :: Bool -> Bool -> Bool
True  && x       =  x
False && _       =  False
True  || _       =  True
False || x       =  x


not              :: Bool -> Bool
not True         =  False
not False        =  True


otherwise        :: Bool
otherwise        =  True

data  Maybe a  =  Nothing | Just a      deriving (Eq, Ord, Read, Show)


maybe              :: b -> (a -> b) -> Maybe a -> b
maybe n f Nothing  =  n
maybe n f (Just x) =  f x



data  Either a b  =  Left a | Right b   deriving (Eq, Ord, Read, Show)


either               :: (a -> c) -> (b -> c) -> Either a b -> c
either f g (Left x)  =  f x
either f g (Right y) =  g y


fst              :: (a,b) -> a
fst (x,y)        =  x


snd              :: (a,b) -> b
snd (x,y)        =  y

-- curry converts an uncurried function to a curried function;
-- uncurry converts a curried function to a function on pairs.

curry            :: ((a, b) -> c) -> a -> b -> c
curry f x y      =  f (x, y)


uncurry          :: (a -> b -> c) -> ((a, b) -> c)
uncurry f p      =  f (fst p) (snd p)




until            :: (a -> Bool) -> (a -> a) -> a -> a
until p f x
     | p x       =  x
     | otherwise =  until p f (f x)


undefined = undefined


infixl 9  !!
infixr 5  ++
infix  4  `elem`, `notElem`

-- Map and append

map :: (a -> b) -> [a] -> [b]
map f []     = []
map f (x:xs) = f x : map f xs

foldr            :: (a -> b -> b) -> b -> [a] -> b
foldr f z []     =  z
foldr f z (x:xs) =  f x (foldr f z xs)


foldr1           :: (a -> a -> a) -> [a] -> a
foldr1 f [x]     =  x
foldr1 f (x:xs)  =  f x (foldr1 f xs)
foldr1 _ []      =  undefined


scanr             :: (a -> b -> b) -> b -> [a] -> [b]
scanr f q0 []     =  [q0]
scanr f q0 (x:xs) =  f x q : qs
                     where qs = scanr f q0 xs
                           q = case qs of
                                 q : _ -> q


scanr1          :: (a -> a -> a) -> [a] -> [a]
scanr1 f []     =  []
scanr1 f [x]    =  [x]
scanr1 f (x:xs) =  f x q : qs
                   where qs = scanr1 f xs
                         q = case qs of
                               q : _ -> q


foldl            :: (a -> b -> a) -> a -> [b] -> a
foldl f z []     =  z
foldl f z (x:xs) =  foldl f (f z x) xs


foldl1           :: (a -> a -> a) -> [a] -> a
foldl1 f (x:xs)  =  foldl f x xs
foldl1 _ []      =  undefined


scanl            :: (a -> b -> a) -> a -> [b] -> [a]
scanl f q xs     =  q : (case xs of
                            []   -> []
                            x:xs -> scanl f (f q x) xs)


scanl1           :: (a -> a -> a) -> [a] -> [a]
scanl1 f (x:xs)  =  scanl f x xs
scanl1 _ []      =  []

(++) :: [a] -> [a] -> [a]
[]     ++ ys = ys
(x:xs) ++ ys = x : (xs ++ ys)


filter :: (a -> Bool) -> [a] -> [a]
filter p []                 = []
filter p (x:xs) | p x       = x : filter p xs
                | otherwise = filter p xs


concat :: [[a]] -> [a]
concat xss = foldr (++) [] xss


concatMap :: (a -> [b]) -> [a] -> [b]
concatMap f = concat . map f

-- head and tail extract the first element and remaining elements,
-- respectively, of a list, which must be non-empty.  last and init
-- are the dual functions working from the end of a finite list,
-- rather than the beginning.


head             :: [a] -> a
head (x:_)       =  x
head []          =  undefined


tail             :: [a] -> [a]
tail (_:xs)      =  xs
tail []          =  undefined


last             :: [a] -> a
last [x]         =  x
last (_:xs)      =  last xs
last []          =  undefined


init             :: [a] -> [a]
init [x]         =  []
init (x:xs)      =  x : init xs
init []          =  undefined


null             :: [a] -> Bool
null []          =  True
null (_:_)       =  False



iterate          :: (a -> a) -> a -> [a]
iterate f x      =  x : iterate f (f x)

-- repeat x is an infinite list, with x the value of every element.

repeat           :: a -> [a]
repeat x         =  xs where xs = x:xs

-- cycle ties a finite list into a circular one, or equivalently,
-- the infinite repetition of the original list.  It is the identity
-- on infinite lists.


cycle            :: [a] -> [a]
cycle []         =  undefined
cycle xs         =  xs' where xs' = xs ++ xs'



takeWhile               :: (a -> Bool) -> [a] -> [a]
takeWhile p []          =  []
takeWhile p (x:xs)
            | p x       =  x : takeWhile p xs
            | otherwise =  []


dropWhile               :: (a -> Bool) -> [a] -> [a]
dropWhile p []          =  []
dropWhile p (x:xs)
            | p x       =  dropWhile p xs
            | otherwise =  (x:xs)


and, or          :: [Bool] -> Bool
and              =  foldr (&&) True
or               =  foldr (||) False

-- Applied to a predicate and a list, any determines if any element
-- of the list satisfies the predicate.  Similarly, for all.

any, all         :: (a -> Bool) -> [a] -> Bool
any p            =  or . map p
all p            =  and . map p



zipWith          :: (a->b->c) -> [a]->[b]->[c]
zipWith z (a:as) (b:bs)
                 =  z a b : zipWith z as bs
zipWith _ _ _    =  []


zipWith3         :: (a->b->c->d) -> [a]->[b]->[c]->[d]
zipWith3 z (a:as) (b:bs) (c:cs)
                 =  z a b c : zipWith3 z as bs cs
zipWith3 _ _ _ _ =  []


zip              :: [a] -> [b] -> [(a,b)]
zip              =  zipWith (,)


zip3             :: [a] -> [b] -> [c] -> [(a,b,c)]
zip3             =  zipWith3 (,,)



unzip            :: [(a,b)] -> ([a],[b])
unzip            =  foldr (\(a,b) (as,bs) -> (a:as,b:bs)) ([],[])


unzip3           :: [(a,b,c)] -> ([a],[b],[c])
unzip3           =  foldr (\(a,b,c) (as,bs,cs) -> (a:as,b:bs,c:cs))
                          ([],[],[])

