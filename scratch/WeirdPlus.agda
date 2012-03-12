2module WeirdPlus where

open import Relation.Binary.PropositionalEquality
open import Function

data ℕ : Set where
  zero : ℕ
  suc  : (x : ℕ) → ℕ

open ≡-Reasoning

-- Plus with the second argument as accumulator -------------------------------

_+_ : ℕ → ℕ → ℕ
zero  + y = y
suc x + y = x + suc y

-- This lemma is of most importance -------------------------------------------

+-lemma : ∀ x y → suc (x + y) ≡ x + suc y
+-lemma zero    y = refl
+-lemma (suc x) y = +-lemma x (suc y)            -- lexicographic induction

-- Associativity, identity and commutativity ----------------------------------

+-assoc : ∀ x y z → x + (y + z) ≡ (x + y) + z
+-assoc zero    y z = refl
+-assoc (suc x) y z = begin
      x + suc (y + z)  ≡⟨ cong (_+_ x) (+-lemma y z) ⟩
      x + (y + suc z)  ≡⟨ +-assoc x (suc y) z ⟩  -- lexicographic induction
      (x + suc y) + z
    ∎

+-left-id : ∀ x → zero + x ≡ x
+-left-id x = refl

+-right-id : ∀ x → x + zero ≡ x
+-right-id zero    = refl
+-right-id (suc x) = begin
      x + suc zero   ≡⟨ sym (+-lemma x zero) ⟩
      suc (x + zero) ≡⟨ cong suc (+-right-id x) ⟩
      suc x
    ∎

+-comm : ∀ x y → x + y ≡ y + x
+-comm zero    y = sym (+-right-id y)
+-comm (suc x) y = begin
     x + suc y   ≡⟨ sym (+-lemma x y) ⟩
     suc (x + y) ≡⟨ cong suc (+-comm x y) ⟩
     suc (y + x) ≡⟨ +-lemma y x ⟩
     y + suc x
   ∎

-- Normal definition of + -----------------------------------------------------

_+′_ : ℕ → ℕ → ℕ
zero  +′ y = y
suc x +′ y = suc (x +′ y)

-- The definitions are equivalent (lemma needed) ------------------------------

+-+′-equivalent : ∀ x y → x + y ≡ x +′ y
+-+′-equivalent zero    y = refl
+-+′-equivalent (suc x) y = begin
     x + suc y    ≡⟨ sym (+-lemma x y) ⟩
     suc (x + y)  ≡⟨ cong suc (+-+′-equivalent x y) ⟩
     suc (x +′ y)
   ∎

-- If we use "symmetric induction" we only need to use lemma in a simple case -

+-+′-equivalent′ : ∀ x y → x + y ≡ x +′ y
+-+′-equivalent′ zero    y = refl
+-+′-equivalent′ (suc x) zero    = begin
     x + suc zero   ≡⟨ sym (+-lemma x zero) ⟩
     suc (x + zero) ≡⟨ cong suc (+-+′-equivalent′ x zero) ⟩
     suc (x +′ zero)
   ∎
+-+′-equivalent′ (suc x) (suc y) = begin
     x + suc (suc y)    ≡⟨ +-+′-equivalent′ (suc (suc x)) y ⟩
     suc (suc (x +′ y)) ≡⟨ cong suc (sym (+-+′-equivalent′ (suc x) y)) ⟩
     suc (x + suc y)    ≡⟨ cong suc (+-+′-equivalent′ x (suc y)) ⟩
     suc (x +′ suc y)
   ∎
