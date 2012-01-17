module ListInduction where

open import Data.List hiding ([_])
open import Data.List.NonEmpty
open import Data.Nat
open import Data.Bool

depth-two-ind : (P : List ℕ → Set)
              → P []
              → P (zero ∷ [])
              → (∀ x → P (x ∷ []) → P (suc x ∷ []))
              → (∀ x y xs → P (x ∷ xs) → P (y ∷ xs) → P (x ∷ y ∷ xs))
              → ∀ xs → P xs
depth-two-ind P nil [zero] [suc] ∷-∷ []           = nil
depth-two-ind P nil [zero] [suc] ∷-∷ (zero ∷ [])  = [zero]
depth-two-ind P nil [zero] [suc] ∷-∷ (suc x ∷ []) = [suc] x (depth-two-ind P nil [zero] [suc] ∷-∷ (x ∷ []))
depth-two-ind P nil [zero] [suc] ∷-∷ (x ∷ y ∷ xs) = ∷-∷ x y xs (depth-two-ind P nil [zero] [suc] ∷-∷ (x ∷ xs))
                                                               (depth-two-ind P nil [zero] [suc] ∷-∷ (y ∷ xs))


depth-two : (P : List ℕ → Set)
          → P []
          → P (zero ∷ [])
          → (∀ x → P (x ∷ []) → P (suc x ∷ []))
          → (∀ y xs → P (zero ∷ y    ∷ xs) → P (zero  ∷ suc y ∷ xs))
          → (∀ x xs → P (x    ∷ zero ∷ xs) → P (zero  ∷ zero  ∷ xs))
          → (∀ x y xs → P (x ∷ y ∷ xs)       → P (suc x ∷ suc y ∷ xs))
          → ∀ xs → P xs
depth-two = {!!}

min : ℕ → ℕ → ℕ
min zero    zero    = zero
min zero    (suc y) = zero
min (suc x) zero    = zero
min (suc x) (suc y) = suc (min x y)

max : ℕ → ℕ → ℕ
max zero    zero    = zero
max zero    (suc y) = suc y
max (suc x) zero    = suc x
max (suc x) (suc y) = suc (max x y)

_<=_ : ℕ → ℕ → Bool
zero  <= y     = true
suc x <= zero  = false
suc x <= suc y = x <= y

minimum : List⁺ ℕ → ℕ
minimum [ x ]    = x
minimum (x ∷ xs) = min x (minimum xs)

maximum : List⁺ ℕ → ℕ
maximum [ x ]    = x
maximum (x ∷ xs) = max x (maximum xs)

open import Relation.Binary.PropositionalEquality

prop : ∀ xs → minimum xs <= maximum xs ≡ true
prop [ zero ]     = refl
prop [ suc n ]    = prop [ n ]
prop (zero ∷ [ zero  ]) = refl
prop (zero ∷ [ suc n ]) = refl
prop (zero ∷ zero ∷ xs) = {!prop (zero ∷ xs)!}
prop (zero ∷ suc n ∷ xs) = {!!}
prop (suc n ∷ xs) = {!!}
