module SymmetricInduction where

open import Data.Nat

data Tree : Set where
   E  : Tree
   Br : (t₁ t₂ : Tree) → Tree

sym-tree : {P : Tree → Set}
     → P E
     → P (Br E E)
     → (∀ t₁ t₂ → P t₁ → P t₂ → P (Br t₁ t₂) → P (Br E (Br t₁ t₂)))
     → (∀ t₁ t₂ → P t₁ → P t₂ → P (Br t₁ t₂) → P (Br (Br t₁ t₂) E))
     → (∀ t₁ t₂ t₃ t₄ → P t₁ → P t₂ → P t₃ → P t₄
                      → P (Br t₁ t₂) → P (Br t₃ t₄)
                      → P (Br (Br t₁ t₂) (Br t₃ t₄)))
     → (t : Tree)
     → P t
sym-tree h s₁ s₂ s₃ s₄ E = h
sym-tree h s₁ s₂ s₃ s₄ (Br E E) = s₁
sym-tree h s₁ s₂ s₃ s₄ (Br E (Br t₁ t₂)) = s₂ t₁ t₂ (sym-tree h s₁ s₂ s₃ s₄ t₁)
                                                    (sym-tree h s₁ s₂ s₃ s₄ t₂)
                                                    (sym-tree h s₁ s₂ s₃ s₄ (Br t₁ t₂))
sym-tree h s₁ s₂ s₃ s₄ (Br (Br t₁ t₂) E) = s₃ t₁ t₂ (sym-tree h s₁ s₂ s₃ s₄ t₁)
                                                    (sym-tree h s₁ s₂ s₃ s₄ t₂)
                                                    (sym-tree h s₁ s₂ s₃ s₄ (Br t₁ t₂))
sym-tree h s₁ s₂ s₃ s₄ (Br (Br t₁ t₂) (Br t₃ t₄)) = s₄ t₁ t₂ t₃ t₄ (sym-tree h s₁ s₂ s₃ s₄ t₁)
                                                                   (sym-tree h s₁ s₂ s₃ s₄ t₂)
                                                                   (sym-tree h s₁ s₂ s₃ s₄ t₃)
                                                                   (sym-tree h s₁ s₂ s₃ s₄ t₄)
                                                                   (sym-tree h s₁ s₂ s₃ s₄ (Br t₁ t₂))
                                                                   (sym-tree h s₁ s₂ s₃ s₄ (Br t₃ t₄))

sym-nat : {P : ℕ → ℕ → Set}
      → P zero zero
      → (∀ x → P x zero → P (suc x) zero)
      → (∀ y → P zero y → P zero (suc y))
      → (∀ x y → P x y → P (suc x) y → P x (suc y) → P (suc x) (suc y))
      → ∀ x y → P x y
sym-nat zz sz zs ss zero zero = zz
sym-nat zz sz zs ss zero (suc y) = zs y (sym-nat zz sz zs ss zero y)
sym-nat zz sz zs ss (suc x) zero = sz x (sym-nat zz sz zs ss x zero)
sym-nat zz sz zs ss (suc x) (suc y) = ss x y (sym-nat zz sz zs ss x y)
                                             (sym-nat zz sz zs ss (suc x) y)
                                             (sym-nat zz sz zs ss x (suc y))
