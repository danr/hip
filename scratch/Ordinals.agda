module Ordinals where

open import Data.Nat renaming (_+_ to _+ℕ_ ; _*_ to _*ℕ_)
open import Relation.Binary.PropositionalEquality

data Ord : Set where
  zero : Ord
  suc  : (x : Ord) → Ord
  lim  : (f : ℕ → Ord) → Ord

_+_ : Ord → Ord → Ord
zero  + y = y
suc x + y = suc (x + y)
lim f + y = lim (λ n → f n + y)

fromℕ : ℕ → Ord
fromℕ zero    = zero
fromℕ (suc x) = suc (fromℕ x)

ω : Ord
ω = lim fromℕ

infix 4 _≣_

-- Extensional equality over ordinal numbers
data _≣_ : Ord → Ord → Set where
  ≣-zero : zero ≣ zero
  ≣-suc  : ∀ {x y} → x ≣ y → suc x ≣ suc y
  ≣-lim  : ∀ {f₁ f₂} → (∀ α → f₁ α ≣ f₂ α) → lim f₁ ≣ lim f₂

≣-refl : ∀ {x} → x ≣ x
≣-refl {zero} = ≣-zero
≣-refl {suc x} = ≣-suc ≣-refl
≣-refl {lim f} = ≣-lim (λ _ → ≣-refl)

+-assoc : ∀ α β γ → α + (β + γ) ≣ (α + β) + γ
+-assoc zero    β γ = ≣-refl
+-assoc (suc α) β γ = ≣-suc (+-assoc α β γ)
+-assoc (lim f) β γ = ≣-lim (λ α → +-assoc (f α) β γ)
