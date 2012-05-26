{-# LANGUAGE PatternGuards, DeriveDataTypeable, ParallelListComp #-}
{-

   Structural Induction - the heart of HipSpec

     Example 1:

       data Nat = Succ Nat | Zero

       ∀ (x : Nat) (y : Nat) . P x y

       Induction on x:

       I.   ∀ (y : Nat) . P Zero y
       II.  ∀ (x : Nat) (y : Nat) . (∀ y₀ . P x y₀) → P (Succ x) y

       Induction on y on II:

       III. ∀ (x : Nat) (y : Nat) . (∀ y₀ . P x y₀) → P (Succ x) Zero
       IV.  ∀ (x : Nat) (y : Nat) . (∀ y₀ . P x y₀) ∧ (∀ x₀ . P x₀ y → P (Succ x₀ y)) → P (Succ x) (Succ y)

     Example 2:

       data Ord = ... | Lim (Nat -> Ord)

       Lim step case:

       ∀ f . (∀ x . P (f x)) → P (Lim f)

     Example 3:

       data Tree a = Leaf a | Fork (Tree a) (Tree a)

       ∀ (t : Tree a) . P x

       Induction on t:

       I.  ∀ (x : a) . P (Leaf a)
       II. ∀ (l r : Tree a) . P l ∧ P r → P (Fork l r)

       Induction on l:

       Base case, instantiate l with Leaf
       II′. ∀ (x : a, r : Tree a) . P (Leaf x) ∧ P r → P (Fork (Leaf x) r)
                           --   P on only constructors is never reallyneeded

       Step case, instantiate l with Fork ll lr, hypotheses ll and lr:

       P′ l = ∀ r : Tree a . P l ∧ P r → P (Fork l r)

       ∀ ll lr . P′(ll) ∧ P′(lr) → P (Fork ll lr)

       ~> Inline P′

       ∀ ll lr . (∀ r₀ . P ll ∧ P r₀ → P (Fork ll r₀))
               ∧ (∀ r₀ . P lr ∧ P r₀ → P (Fork lr r₀))
               → (∀ r  . P (Fork ll lr) ∧ P r → P (Fork (Fork ll lr) r))

       ~> Shuffle ∀ r

       ∀ ll lr r . (∀ r₀ . P ll ∧ P r₀ → P (Fork ll r₀))
                 ∧ (∀ r₀ . P lr ∧ P r₀ → P (Fork lr r₀))
                 → P (Fork ll lr) ∧ P r → P (Fork (Fork ll lr) r)

       ~> exponentials

       ∀ ll lr r . (∀ r₀ . P ll ∧ P r₀ → P (Fork ll r₀))
                 ∧ (∀ r₀ . P lr ∧ P r₀ → P (Fork lr r₀))
                 ∧ P (Fork ll lr)
                 ∧ P r
                 → P (Fork (Fork ll lr) r)

       Done!

       Now, induction on r:

       P′ r = ∀ ll lr . (∀ r₀ . P ll ∧ P r₀ → P (Fork ll r₀))
                      ∧ (∀ r₀ . P lr ∧ P r₀ → P (Fork lr r₀))
                      ∧ P (Fork ll lr)
                      ∧ P r
                      → P (Fork (Fork ll lr) r)

       Base:

       ∀ x . P′ (Leaf x)

       ~>

       ∀ x ll lr . (∀ r₀ . P ll ∧ P r₀ → P (Fork ll r₀))
                 ∧ (∀ r₀ . P lr ∧ P r₀ → P (Fork lr r₀))
                 ∧ P (Fork ll lr)
                 ∧ P (Leaf x)
                 → P (Fork (Fork ll lr) (Leaf x))

       Step:

       ∀ rl rr . P′ rl ∧ P′ rr → P′ (Fork rl rr)

       ~> Inline P′

       ∀ rl rr . (∀ ll₀ lr₀ . (∀ r₀ . P ll₀ ∧ P r₀ → P (Fork ll₀ r₀))
                            ∧ (∀ r₀ . P lr₀ ∧ P r₀ → P (Fork lr₀ r₀))
                            ∧ P (Fork ll₀ lr₀)
                            ∧ P rl
                            → P (Fork (Fork ll₀ lr₀) rl)
               ∧ (∀ ll₀ lr₀ . (∀ r₀ . P ll₀ ∧ P r₀ → P (Fork ll₀ r₀))
                            ∧ (∀ r₀ . P lr₀ ∧ P r₀ → P (Fork lr₀ r₀))
                            ∧ P (Fork ll₀ lr₀)
                            ∧ P rr
                            → P (Fork (Fork ll₀ lr₀) rr)
               → (∀ ll lr . (∀ r₀ . P ll ∧ P r₀ → P (Fork ll r₀))
                            ∧ (∀ r₀ . P lr ∧ P r₀ → P (Fork lr r₀))
                            ∧ P (Fork ll lr)
                            ∧ P (Fork rr rl)
                            → P (Fork (Fork ll lr) (Fork rr rl))

       ~> quantifiers, exponentials

       ∀ rl rr ll lr . (∀ ll₀ lr₀ . (∀ r₀ . P ll₀ ∧ P r₀ → P (Fork ll₀ r₀))
                                  ∧ (∀ r₀ . P lr₀ ∧ P r₀ → P (Fork lr₀ r₀))
                                  ∧ P (Fork ll₀ lr₀)
                                  ∧ P rl
                                  → P (Fork (Fork ll₀ lr₀) rl)
                     ∧ (∀ ll₀ lr₀ . (∀ r₀ . P ll₀ ∧ P r₀ → P (Fork ll₀ r₀))
                                  ∧ (∀ r₀ . P lr₀ ∧ P r₀ → P (Fork lr₀ r₀))
                                  ∧ P (Fork ll₀ lr₀)
                                  ∧ P rr
                                  → P (Fork (Fork ll₀ lr₀) rr)
                     ∧ (∀ r₀ . P ll ∧ P r₀ → P (Fork ll r₀))
                     ∧ (∀ r₀ . P lr ∧ P r₀ → P (Fork lr r₀))
                     ∧ P (Fork ll lr)
                     ∧ P (Fork rr rl)
                     → P (Fork (Fork ll lr) (Fork rr rl))

       Skolemise, clauses

       1. (∀ ll₀ lr₀ . (∀ r₀ . P ll₀ ∧ P r₀ → P (Fork ll₀ r₀))
                     ∧ (∀ r₀ . P lr₀ ∧ P r₀ → P (Fork lr₀ r₀))
                     ∧ P (Fork ll₀ lr₀)
                     ∧ P rl
                     → P (Fork (Fork ll₀ lr₀) rl)
       2. (∀ ll₀ lr₀ . (∀ r₀ . P ll₀ ∧ P r₀ → P (Fork ll₀ r₀))
                     ∧ (∀ r₀ . P lr₀ ∧ P r₀ → P (Fork lr₀ r₀))
                     ∧ P (Fork ll₀ lr₀)
                     ∧ P rr
                     → P (Fork (Fork ll₀ lr₀) rr)
       3. (∀ r₀ . P ll ∧ P r₀ → P (Fork ll r₀))
       4. (∀ r₀ . P lr ∧ P r₀ → P (Fork lr r₀))
       5. P (Fork ll lr)
       6. P (Fork rr rl)
       7. ~ P (Fork (Fork ll lr) (Fork rr rl))

       Eprover cnfs this to

       # Unprocessed positive unit clauses:
       cnf(i_0_22,plain,(p(fork(rr,rl)))).
       cnf(i_0_21,plain,(p(fork(ll,lr)))).

       # Unprocessed negative unit clauses:
       cnf(i_0_23,negated_conjecture,(~p(fork(fork(ll,lr),fork(rr,rl))))).

       # Unprocessed non-unit clauses:
       cnf(i_0_19,plain,(p(fork(ll,X1))|~p(ll)|~p(X1))).
       cnf(i_0_20,plain,(p(fork(lr,X1))|~p(lr)|~p(X1))).
       cnf(i_0_9,plain,(p(fork(fork(X1,X2),rl))|p(X1)|p(X2)|~p(fork(X1,X2))|~p(rl))).
       cnf(i_0_18,plain,(p(fork(fork(X1,X2),rr))|p(X1)|p(X2)|~p(fork(X1,X2))|~p(rr))).
       cnf(i_0_6,plain,(p(fork(fork(X1,X2),rl))|p(esk1_2(X1,X2))|p(X2)|~p(fork(X1,X2))|~p(rl))).
       cnf(i_0_15,plain,(p(fork(fork(X1,X2),rr))|p(esk3_2(X1,X2))|p(X2)|~p(fork(X1,X2))|~p(rr))).
       cnf(i_0_8,plain,(p(fork(fork(X1,X2),rl))|p(esk2_2(X1,X2))|p(X1)|~p(fork(X1,X2))|~p(rl))).
       cnf(i_0_17,plain,(p(fork(fork(X1,X2),rr))|p(esk4_2(X1,X2))|p(X1)|~p(fork(X1,X2))|~p(rr))).
       cnf(i_0_3,plain,(p(fork(fork(X1,X2),rl))|p(X2)|~p(fork(X1,esk1_2(X1,X2)))|~p(fork(X1,X2))|~p(rl))).
       cnf(i_0_12,plain,(p(fork(fork(X1,X2),rr))|p(X2)|~p(fork(X1,esk3_2(X1,X2)))|~p(fork(X1,X2))|~p(rr))).
       cnf(i_0_7,plain,(p(fork(fork(X1,X2),rl))|p(X1)|~p(fork(X2,esk2_2(X1,X2)))|~p(fork(X1,X2))|~p(rl))).
       cnf(i_0_16,plain,(p(fork(fork(X1,X2),rr))|p(X1)|~p(fork(X2,esk4_2(X1,X2)))|~p(fork(X1,X2))|~p(rr))).
       cnf(i_0_5,plain,(p(fork(fork(X1,X2),rl))|p(esk2_2(X1,X2))|p(esk1_2(X1,X2))|~p(fork(X1,X2))|~p(rl))).
       cnf(i_0_14,plain,(p(fork(fork(X1,X2),rr))|p(esk4_2(X1,X2))|p(esk3_2(X1,X2))|~p(fork(X1,X2))|~p(rr))).
       cnf(i_0_4,plain,(p(fork(fork(X1,X2),rl))|p(esk1_2(X1,X2))|~p(fork(X2,esk2_2(X1,X2)))|~p(fork(X1,X2))|~p(rl))).
       cnf(i_0_2,plain,(p(fork(fork(X1,X2),rl))|p(esk2_2(X1,X2))|~p(fork(X1,esk1_2(X1,X2)))|~p(fork(X1,X2))|~p(rl))).
       cnf(i_0_13,plain,(p(fork(fork(X1,X2),rr))|p(esk3_2(X1,X2))|~p(fork(X2,esk4_2(X1,X2)))|~p(fork(X1,X2))|~p(rr))).
       cnf(i_0_11,plain,(p(fork(fork(X1,X2),rr))|p(esk4_2(X1,X2))|~p(fork(X1,esk3_2(X1,X2)))|~p(fork(X1,X2))|~p(rr))).
       cnf(i_0_1,plain,(p(fork(fork(X1,X2),rl))|~p(fork(X2,esk2_2(X1,X2)))|~p(fork(X1,esk1_2(X1,X2)))|~p(fork(X1,X2))|~p(rl))).
       cnf(i_0_10,plain,(p(fork(fork(X1,X2),rr))|~p(fork(X2,esk4_2(X1,X2)))|~p(fork(X1,esk3_2(X1,X2)))|~p(fork(X1,X2))|~p(rr))).

       Which is pretty sweet

   What we want to do:

   We have

       ∀ (x : R) (y : S) (z : T) . P x y z

   Say we want to do induction on y. S has two constructors:

       data S = C Bool | D S S

   Then make this formula:

       phi = ∀ (x : R) (z : T) . P x y z

   Where y is free. We want:

       ∀ (b : Bool) . phi(C b/y),    and

       ∀ (u v : S) . phi(u/y) ∧ phi(v/y) ==> phi(D u v/y)

   We want to do the instantiations with fresh x and z in the antecedent.
   We get some dangling quantifiers in the consequent above,
   so we move them back to the top level, getting something like this:

      ∀ (x : R) (b : Bool) (z : T) . P x (C b) z,

    and

      ∀ (x : R) (u v : S) (z : T) . (∀ (x₀ : R) (z₀ : T) . P x₀ u z₀)
                                  ∧ (∀ (x₀ : R) (z₀ : T) . P x₀ v z₀)
                                  → P x (D u v) z

   Done, and ready to return or do induction on any of the variables.
   We can also locate which variables are of relevance corresponding to
   the initial variables, namely or [x, u and v, z].

-}
module Hip.Trans.StructuralInduction where

import Control.Arrow hiding ((<+>))
import Control.Applicative hiding (empty)
import Control.Monad
import Control.Monad.State
import Control.Monad.Identity

import Data.Generics.Uniplate.Data

import Data.Data
import Data.List
import Data.Maybe

import Hip.Util (concatMapM,(.:))

import Text.PrettyPrint hiding (Style)

import Safe

data Formula c v t = Forall [(v,t)] (Formula c v t)
                   | [Formula c v t] :=> Formula c v t
                   | P [Term c v]
                   -- ^ The actual predicate that we are doing induction on
  deriving (Eq,Ord,Show,Data,Typeable)

(==>) :: [Formula c v t] -> Formula c v t -> Formula c v t
xs ==> (ys :=> x) = (xs ++ ys) ==> x
xs ==> x          = case tidy xs of
                         [] -> x
                         ts -> ts :=> x

tidy :: [Formula c v t] -> [Formula c v t]
tidy = filter (not . isAtom)
  where
    isAtom (P tm) = all isAtomTm tm
    isAtom _      = False

    isAtomTm (Con x xs) = all isAtomTm xs
    isAtomTm _          = False

-- An argument to a constructor can be recursive or non-recursive.
--
-- For instance, when doing induction on [a], then (:) has two arguments,
-- NonRec a and Rec [a].
--
-- If doing induction on [Nat], then (:) has NonRec Nat and Rec [Nat]
--
-- So Rec signals that there should be emitted an induction hypothesis here.
--
-- Data types can also be exponential. Consider
--
-- @
--     data Ord = Zero | Succ Ord | Lim (Nat -> Ord)
-- @
--
-- Here, the Lim constructor is exponential, create it with
--
-- @
--     Exp (Nat -> Ord) [Nat]
-- @
--
-- The first argument is the type of the function, and the second
-- argument are the arguments to the function. The apparent duplication
-- is there because the type is kept entirely abstract in this module.
data Arg t = Rec t
           | NonRec t
           | Exp t [t]
  deriving (Eq,Ord,Show)

-- | Get the representation of the argument
argRepr :: Arg t -> t
argRepr (Rec t)    = t
argRepr (NonRec t) = t
argRepr (Exp t _)  = t

forall' :: [(v,t)] -> Formula c v t -> Formula c v t
forall' xs (Forall ys phi) = Forall (xs ++ ys) phi
forall' [] phi             = phi
forall' xs phi             = Forall xs phi


mdelete :: Eq a => a -> [(a,b)] -> [(a,b)]
mdelete x = filter (\(y,_) -> x /= y)

data Term c v = Var v
              | Con c [Term c v]
              | Fun v [Term c v]
              -- ^ Exponentials yield function application
  deriving (Eq,Ord,Show,Data,Typeable)

-- | Substitution. The rhs of the substitutions must be only fresh variables.
subst :: (Data c,Data v,Data t,Eq v)
      => [(v,Term c v)] -> Formula c v t -> Formula c v t
subst subs = transformBi $ \ tm ->
    case tm of
        Var x | Just tm' <- lookup x subs -> tm'
        _                                 -> tm

type Fresh = State Integer

-- Cheap way of book-keeping fresh variables
type V v = (v,Integer)

-- | Create a new fresh variable
newFresh :: v -> Fresh (V v)
newFresh v = do
    x <- get
    modify succ
    return (v,x)

-- | Create a fresh variable that has a type
newTyped :: v -> t -> Fresh (V v,t)
newTyped v t = flip (,) t <$> newFresh v

-- | Refresh variable
newFreshV :: V v -> Fresh (V v)
newFreshV (v,_) = newFresh v

-- | Refresh a variable that has a type
newTypedV :: V v -> t -> Fresh (V v,t)
newTypedV v t = flip (,) t <$> newFreshV v

-- | Formulas with fresh-tagged variables
type FormulaV c v t = Formula c (V v) t

-- | Terms with fresh-tagged variables
type TermV c v = Term c (V v)

-- | Flattens out fresh variable names, in a monad
unVM :: Monad m => (v -> Integer -> m v) -> FormulaV c v t -> m (Formula c v t)
unVM f = go
  where
    go phi = case phi of
        Forall xs psi -> liftM2 Forall (forM xs $ \(x,t) -> liftM (flip (,) t)
                                                                  (uncurry f x))
                                       (go psi)
        xs :=> x      -> liftM2 (:=>) (mapM go xs) (go x)
        P xs          -> liftM P (mapM go' xs)

    go' tm = case tm of
        Var x     -> liftM Var (uncurry f x)
        Con c tms -> liftM (Con c) (mapM go' tms)
        Fun x tms -> liftM2 Fun (uncurry f x) (mapM go' tms)

-- | Flattens out fresh variable names
unV :: (v -> Integer -> v) -> FormulaV c v t -> Formula c v t
unV f = runIdentity . unVM (return .: f)

-- | Induction on a variable, given one constructor and the type of
--   its arguments.
--
--   Specifically, given the constructor C t1 .. tn and formula
--
--     ∀ (x,xs) . φ
--
--   yields
--
--     ∀ (x1 : t1..xn : tn,xs) .
--
--         ∧ (forall i . if     ti nonrec    : []
--                       elseif ti recursive : (∀ xs' . φ′(xi/x))
--                       elseif ti exp ts    : (∀ xs' . ∀ (ys : ts) . φ′(xi(ys)/x))
--                                 as a function call)
--
--         → φ(C x1 .. xn/x)
--
--    where φ′ = φ(xs'/xs)
indCon :: (Data c,Data v,Data t,Eq v)
       => FormulaV c v t -> V v -> c -> [Arg t] -> Fresh (FormulaV c v t)
indCon (Forall qs phi) x con arg_types = do

   let xs = mdelete x qs

   xs' <- mapM (uncurry newTypedV) (mdelete x qs)

   let phi' = subst [(v,Var v') | (v,_) <- xs | (v',_) <- xs' ] phi

   x1xn_typed <- mapM (newTypedV x) arg_types

   let x1xn = map fst x1xn_typed

       hypothesis xi r = case r of
           NonRec _ -> return Nothing
           Rec t    -> return (Just $ forall' xs' (subst [(x,Var xi)] phi'))
           Exp _ exp_arg_types -> do
               args_typed <- mapM (newTypedV x) exp_arg_types
               return $ Just
                      $ forall' (xs' ++ args_typed)
                      $ subst [(x,Fun xi (map (Var . fst) args_typed))] phi'

   antecedents <- catMaybes <$> mapM (uncurry hypothesis) x1xn_typed

   let consequent = subst [(x,Con con (map Var x1xn))] phi

   return (forall' (map (second argRepr) x1xn_typed ++ xs)
                   (antecedents ==> consequent))
{- Note:

   There are cases where this is not correct... Consider

     ∀ x . P(x) => P(succ(x))

   And we do induction on x, then we end up with

     ∀ x . (P(x) => P(succ(x))) => (P(succ(x)) => P(succ(succ(x))))

   When we really would want to see

     ∀ x . P(x) & P(succ(x)) => P(succ(succ(x))))

-}

-- | Induction on a variable, given all its constructors and their types
--   Returns a number of clauses to be proved, one for each constructor.
induction :: (Data c,Data v,Data t,Eq v)
          => FormulaV c v t -> V v -> [(c,[Arg t])] -> Fresh [FormulaV c v t]
induction phi x cons = sequence [ indCon phi x con arg_types
                                | (con,arg_types) <- cons ]


-- Given a type, returns the constructors and the types of their arguments,
-- and also if the arguments are recursive, non-recursive or exponential (see Arg).
--
-- The function should instantiate type variables.
-- For instance, looking up the type List Nat, should return the constructors
-- Nil with args [], and Cons with args [NonRec Nat,Rec (List Nat)].
--
-- If it is not possible to do induction on this type, return Nothing.
-- Examples are function spaces and type variables.
type TyEnv c t = t -> Maybe [(c,[Arg t])]

-- | Folds and concats in a monad
concatFoldM :: Monad m => (a -> i -> m [a]) -> a -> [i] -> m [a]
concatFoldM k a []     = return [a]
concatFoldM k a (x:xs) = do rs <- k a x
                            concatMapM (\r -> concatFoldM k r xs) rs

-- Induction on a term. When we have picked out an argument to the
-- predicate P, it may just as well be a constructor x : xs, and then
-- we can do induction on x and xs (possibly).
inductionTm :: (Data c,Data v,Data t,Eq v)
            => TyEnv c t -> FormulaV c v t -> TermV c v -> Fresh [FormulaV c v t]
inductionTm ty_env phi tm = case tm of
    Var x -> case phi of
                 Forall xs _ -> case lookup x xs of
                                   Just ty -> case ty_env ty of
                                                  Just cons -> induction phi x cons
                                                  Nothing   -> return [phi]
                                   _  -> error "inductionTm: x not in quantifier list xs"
                 _ -> error "inductionTm: x not in non-existent quantifier list"
    Con c tms -> concatFoldM (inductionTm ty_env) phi tms
    Fun _ _   -> error "inductionTm: cannot do induction on a function"

-- | Gets the n:th argument of P, in the consequent
getNthArg :: Int -> Formula c v t -> Term c v
getNthArg i = go
  where
    go (Forall _ phi) = go phi
    go (_ :=> phi)    = go phi
    go (P xs)         = atNote "StructuralInduction.getNthArg" xs i

-- Induction on the term on the n:th coordinate of the predicate.
inductionNth :: (Data c,Data v,Data t,Eq v)
             => TyEnv c t -> FormulaV c v t -> Int -> Fresh [FormulaV c v t]
inductionNth ty_env phi i = inductionTm ty_env phi (getNthArg i phi)


-- | Performs repeated lexicographic induction, given the typing environment
--
--     * the constructors and their Arg types, for any type
--
--     * arguments and their types
--
--     * which coordinates to do induction on, in order
structuralInduction :: (Data c,Data v,Data t,Eq v)
                    => TyEnv c t
                    -- ^ Constructor typed environment
                    -> [(v,t)]
                    -- ^ The initial arguments and types to P
                    -> [Int]
                    -- ^ The coordinates to do induction on in P, in order
                    -> [FormulaV c v t]
                    -- ^ The set of clauses to prove
structuralInduction ty_env args coordinates = flip evalState 0 $ do

    args_fresh <- mapM (uncurry newTyped) args

    let phi = forall' args_fresh (P (map (Var . fst) args_fresh))

    concatFoldM (inductionNth ty_env) phi coordinates

testEnv :: TyEnv String String
testEnv "Ord" = Just [("zero",[])
                     ,("succ",[Rec "Nat"])
                     ,("lim",[Exp "Nat -> Ord" ["Nat"]])
                     ]
testEnv "Nat" = Just [("zero",[])
                     ,("succ",[Rec "Nat"])
                     ]
testEnv list@('L':'i':'s':'t':' ':a) =
    Just [("nil",[])
         ,("cons",[NonRec a,Rec list])
         ]
testEnv tree@('T':'r':'e':'e':' ':a) =
    Just [("leaf",[NonRec a])
         ,("fork",[Rec tree,Rec tree])
         ]
testEnv xs = Nothing

testStrInd :: [(String,String)] -> [Int] -> IO ()
testStrInd vars coords = putStr
                       $ unlines
                       $ map ((++ ".") . render . linFormula strStyle)
                       $ map (unV (\x i -> x ++ show i))
                       $ structuralInduction testEnv vars coords

natInd = testStrInd [("X","Nat")] [0]

natIndTwice = testStrInd [("X","Nat")] [0,0]

natIndThrice = testStrInd [("X","Nat")] [0,0,0]

natInd2 = testStrInd [("X","Nat"),("Y","Nat")] [0,1]

natListInd = testStrInd [("Xs","List Nat")] [0,0,0]

ordInd = testStrInd [("X","Ord")] [0]

treeInd = testStrInd [("T","Tree a")] [0,0]

data Style c v t = Style { linc :: c -> Doc
                         , linv :: v -> Doc
                         , lint :: t -> Doc
                         }

strStyle :: Style String String String
strStyle = Style { linc = text
                 , linv = text
                 , lint = text
                 }

linTerm :: Style c v t -> Term c v -> Doc
linTerm st tm = case tm of
    Var v    -> linv st v
    Con c [] -> linc st c
    Con c ts -> linc st c <> parens (csv (map (linTerm st) ts))
    Fun v ts -> linv st v <> parens (csv (map (linTerm st) ts))

linTypedVar :: Style c v t -> v -> t -> Doc
linTypedVar st v t = linv st v <+> colon <+> lint st t

linForm :: Style c v t -> (Doc -> Doc) -> Formula c v t -> Doc
linForm st par form = case form of
    Forall qs f -> par $ hang (bang <+> brackets (csv (map (uncurry (linTypedVar st)) qs)) <+> colon)
                              4
                              (linForm st parens f)
    xs :=> f -> par $ cat $ (parList $ punctuate (fluff ampersand)
                                                 (map (linForm st parens) xs))
                          ++ [darrow <+> linForm st parens f]
    P xs -> char 'P' <> parens (csv (map (linTerm st) xs))

linFormula :: Style c v t -> Formula c v t -> Doc
linFormula st = linForm st id

csv :: [Doc] -> Doc
csv = hcat . punctuate comma

parList :: [Doc] -> [Doc]
parList []     = [parens empty]
parList [x]    = [x]
parList (x:xs) = (lparen <> x) : init xs ++ [last xs <> rparen]

ampersand :: Doc
ampersand = char '&'

pipe :: Doc
pipe = char '|'

bang :: Doc
bang = char '!'

fluff :: Doc -> Doc
fluff d = space <> d <> space

darrow :: Doc
darrow = text "=>"
