
data T = T T T | E

data E = E0 | E1 | E2 | E3 | E4

f :: T -> e
f (T (T a b) (T c d)) = E0
f (T (T a b) c      ) = E1
f (T a       (T c d)) = E2
f (T a       c      ) = E3
f E                   = E4

bottom :: a
bottom = f True where f False = f False

prop :: Prop E
prop = f (T (T E E) bottom) =:= bottom
