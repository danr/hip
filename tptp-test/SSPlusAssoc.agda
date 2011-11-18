module SSPlusAssoc where

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero        + y = y
suc zero    + y = suc y
suc (suc x) + y = suc (suc (x + y))

open import Relation.Binary.PropositionalEquality
open import Function

+-assoc : ∀ x y z → x + (y + z) ≡ (x + y) + z
+-assoc zero          y z = refl
    -- suc (y + z) ≡ suc y + z lemma needed
+-assoc (suc zero) zero z = refl
+-assoc (suc zero) (suc y) z = sym (cong suc (+-assoc (suc zero) y z))
+-assoc (suc (suc x)) y z = cong (λ p → suc (suc p)) (+-assoc x y z)

_+'_ : ℕ → ℕ → ℕ
zero  +' y = y
suc x +' y = suc (x +' y)

-- Surprise, + of commutative can be proved without lemmas if you do
-- induction on both variables. (in a non-trivial way)
+-comm : ∀ x y → x +' y ≡ y +' x
+-comm zero    zero    = refl
+-comm (suc x) zero    = cong suc (+-comm x zero)
+-comm zero    (suc y) = cong suc (+-comm zero y)
+-comm (suc x) (suc y) = cong suc (+-comm x (suc y)) ⟨ trans ⟩
                         cong suc (cong suc (+-comm y x) ⟨ trans ⟩ (+-comm (suc x) y))
