module InductionPrinciples where

open import Data.Product
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Sum
open import Function

data ℕ : Set where
   zero : ℕ
   suc  : (n : ℕ) → ℕ

data List (A : Set) : Set where
   nil  : List A
   cons : (x : A) (xs : List A) → List A

ind-nat-two : (P : ℕ → ℕ → Set)
            → P zero zero
            → (∀ y → P zero y → P zero (suc y))
            → (∀ x → P x zero → P (suc x) zero)
            → (∀ x y → P x y → P (suc x) (suc y))
            → ∀ x y → P x y
ind-nat-two P zz zs sz ss zero    zero    = zz
ind-nat-two P zz zs sz ss zero    (suc y) = zs y (ind-nat-two P zz zs sz ss zero y)
ind-nat-two P zz zs sz ss (suc x) zero    = sz x (ind-nat-two P zz zs sz ss x zero)
ind-nat-two P zz zs sz ss (suc x) (suc y) = ss x y (ind-nat-two P zz zs sz ss x y)


ind2nat : (P : ℕ → ℕ → Set)
        → P zero zero
        → (∀ y → P zero y → P zero (suc y))
        → (∀ x y → P x y → P (suc x) y)
        → ∀ x y → P x y
ind2nat P zz zs sy zero    zero    = zz
ind2nat P zz zs sy zero    (suc y) = zs y (ind2nat P zz zs sy zero y)
ind2nat P zz zs sy (suc x) y       = sy x y (ind2nat P zz zs sy x y)

negind : (P : ℕ → Set)
       → ∄ (λ a → ¬ P a)
       → ∀ x → ¬ ¬ P x
negind P nope x = λ ¬Px → nope (x , ¬Px)


⋀

not-ind-nat-two : ¬ ((P : ℕ → ℕ → Set)
                    → P zero zero
                    → (∀ x y → P x y → P (suc x) (suc y))
                    → ∀ x y → P x y)
not-ind-nat-two ind-nat-two-fake = 0≢1 (ind-nat-two-fake _≡_ refl (λ x y → cong suc) zero (suc zero))
  where
    0≢1 : zero ≢ suc zero
    0≢1 ()

ind1 : (P : ℕ → Set)
     → P zero
     → (∀ x → P x → P (suc x))
     → ∀ x → P x
ind1 P z s zero    = z
ind1 P z s (suc x) = s x (ind1 P z s x)

ind11 : (P : ℕ → Set)
      → P zero
      → P (suc zero)
      → (∀ x → P x → P (suc x) → P (suc (suc x)))
      → ∀ x → P x
ind11 P z sz ss zero          = z
ind11 P z sz ss (suc zero)    = sz
ind11 P z sz ss (suc (suc x)) = ss x (ind11 P z sz ss x) (ind11 P z sz ss (suc x))

-- Two step induction is derivable from one step induction
-- Crucial is to make a pair rather than an implication, and project out the relevant bit
ind11′ : (P : ℕ → Set)
       → P zero
       → P (suc zero)
       → (∀ x → P x → P (suc x) → P (suc (suc x)))
       → ∀ x → P x
ind11′ P z sz ss x = ind1 P z (λ x₁ Px₁ → proj₂
                                    ( ind1 (λ n → P n × P (suc n))
                                           (z , sz)
                                           (λ x₂ → λ { ( Px₂ , Psx₂ ) → Psx₂ , ss x₂ Px₂ Psx₂ } )
                                           x₁)) x

ind2 : (P : ℕ → ℕ → Set)
     → P zero zero
     → (∀ y → P zero y → P zero (suc y))
     → (∀ x → P x zero → P (suc x) zero)
     → (∀ x y → (∀ x₀ → P x₀ y) → P (suc x) y → P (suc x) (suc y))
     → ∀ x y → P x y
ind2 P zz zs sz ss zero zero       = zz
ind2 P zz zs sz ss zero (suc y)    = zs y (ind2 P zz zs sz ss zero y)
ind2 P zz zs sz ss (suc x) zero    = sz x (ind2 P zz zs sz ss x zero)
ind2 P zz zs sz ss (suc x) (suc y) = ss x y (λ x₀ → ind2 P zz zs sz ss x₀ y)
                                            (ind2 P zz zs sz ss (suc x) y)


