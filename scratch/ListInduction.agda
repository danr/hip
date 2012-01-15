module ListInduction where

open import Data.List
open import Data.Nat

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

