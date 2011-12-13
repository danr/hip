module Rotate where

open import Data.List hiding (length)
open import Data.Nat
open import Relation.Binary.PropositionalEquality
open import Function

rotate : {A : Set} → ℕ → List A → List A
rotate zero    xs       = xs
rotate (suc n) []       = []
rotate (suc n) (x ∷ xs) = rotate n (xs ++ [ x ])

length : {A : Set} → List A → ℕ
length []       = zero
length (_ ∷ xs) = suc (length xs)

rotateLengthLemma : {A : Set} (x : A) (xs : List A)
                 → rotate (length xs) (xs ++ [ x ]) ≡ x ∷ rotate (length xs) xs
rotateLengthLemma x []        = refl
rotateLengthLemma x (x′ ∷ xs) = {!!}
                      ⟨ trans ⟩ (cong (_∷_ x) (rotateLengthLemma x′ xs))
                      ⟨ trans ⟩ cong (_∷_ x)  (sym (rotateLengthLemma x′ xs))

rotateLength : {A : Set} (xs : List A) → rotate (length xs) xs ≡ xs
rotateLength []       = refl
rotateLength (x ∷ xs) = rotateLengthLemma x xs ⟨ trans ⟩ cong (_∷_ x) (rotateLength xs)