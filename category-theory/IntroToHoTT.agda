-- Based on the book "Introduction to Homotopy Type Theory" by Rijke

open import Data.List
open import Data.Nat
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality hiding ([_])

module IntroToHoTT
  (Type-Name : Set)
  (Type-Name-eq-dec : ∀ {x y : Type-Name} → (x ≡ y) ⊎ (x ≢ y))
  where

data Ix : ℕ → ℕ → Set where
  Ix-Here : ∀ {n} → Ix n zero
  Ix-There : ∀ {n i} → Ix n i → Ix (suc n) (suc i)

Ix-≤ : ∀ {n i} → Ix n i → i ≤ n
Ix-≤ Ix-Here = z≤n
Ix-≤ (Ix-There x) = s≤s (Ix-≤ x)

Ix-relabel : ∀ {n m i} → n ≤ m → Ix n i → Ix m i
Ix-relabel prf Ix-Here = Ix-Here
Ix-relabel (s≤s prf) (Ix-There ix) = Ix-There (Ix-relabel prf ix)

Var : ℕ → Set
Var n = ∃[ i ] Ix n i

record Name (loc : ℕ) : Set where
  field
    params : List (Var loc)

data Precontext : ℕ → Set where
  ∅ : Precontext 0
  _,,_ : ∀ {n} → Precontext n → Name n → Precontext (suc n)

-- data Context : ℕ → Set where
--   ∅ : Context 0
--   _,,_∶_ : ∀ {n i} → Context n → Ix n i → Name n → Context (suc n)

-- _⊕_ : ∀ {n m} → Context n → Context m → Context (n + m)
-- ∅ ⊕ ∅ = ∅
-- ∅ ⊕ (b ,, x ∶ x₁) = b ,, x ∶ x₁
-- (a ,, x ∶ x₁) ⊕ ∅ = a ,, x ∶ x₁
-- (a ,, x ∶ x₁) ⊕ (b ,, x₂ ∶ x₃) = {!!}

-- data Judgment : Set where
--   _⊢_type : ∀ {n} → Context n → Name n → Judgment
--   _⊢_≐_type : ∀ {n} → Context n → Name n → Name n → Judgment
--   _⊢_∶_ : ∀ {n} → Context n → Var n → Name n → Judgment
--   _⊢_≐_∶_ : ∀ {n} → Context n → Var n → Var n → Name n → Judgment


-- data Infers : List Judgment → Judgment → Set where
--   Infers-TF-form : ∀ {n} → {Γ : Context n} {i : ℕ} {x : Ix n i} → ∀ {A} {B} →
--     Infers
--       [ (Γ ,, x ∶ A) ⊢ B type ]
--       -------
--       (Γ ⊢ A type)

--   Infers-≐-type-left-form : ∀ {n} {Γ : Context n} {A} {B} →
--     Infers
--       [ Γ ⊢ A ≐ B type ]
--       --------
--       (Γ ⊢ A type)

--   Infers-≐-type-right-form : ∀ {n} {Γ : Context n} {A} {B} →
--     Infers
--       [ Γ ⊢ A ≐ B type ]
--       --------
--       (Γ ⊢ B type)

--   Infers-∶-form : ∀ {n} {Γ : Context n} {A} {x} →
--     Infers
--       [ Γ ⊢ x ∶ A ]
--       --------
--       (Γ ⊢ A type)

--   Infers-≐-left-form : ∀ {n} {Γ : Context n} {A} {a b} →
--     Infers
--       [ Γ ⊢ a ≐ b ∶ A ]
--       --------
--       (Γ ⊢ a ∶ A)

--   Infers-≐-right-form : ∀ {n} {Γ : Context n} {A} {a b} →
--     Infers
--       [ Γ ⊢ a ≐ b ∶ A ]
--       --------
--       (Γ ⊢ b ∶ A)

--   ---- Judgmental equality is an equivalence relation ----

--   Infers-≐-type-refl : ∀ {n} {Γ : Context n} {A} →
--     Infers
--       [ Γ ⊢ A type ]
--       --------
--       (Γ ⊢ A ≐ A type)

--   Infers-≐-type-sym : ∀ {n} {Γ : Context n} {A B} →
--     Infers
--       [ Γ ⊢ A ≐ B type ]
--       --------
--       (Γ ⊢ B ≐ A type)

--   Infers-≐-type-trans : ∀ {n} {Γ : Context n} {A B C} →
--     Infers
--       ((Γ ⊢ A ≐ B type) ∷ (Γ ⊢ B ≐ C type) ∷ [])
--       --------
--       (Γ ⊢ A ≐ C type)

--   Infers-≐-refl : ∀ {n} {Γ : Context n} {A} {a} →
--     Infers
--       [ Γ ⊢ a ∶ A ]
--       --------
--       (Γ ⊢ a ≐ a ∶ A)

--   Infers-≐-sym : ∀ {n} {Γ : Context n} {A} {a b} →
--     Infers
--       [ Γ ⊢ a ≐ b ∶ A ]
--       --------
--       (Γ ⊢ b ≐ a ∶ A)

--   Infers-≐-trans : ∀ {n} {Γ : Context n} {A} {a b c} →
--     Infers
--       ((Γ ⊢ a ≐ b ∶ A) ∷ (Γ ⊢ b ≐ c ∶ A) ∷ [])
--       --------
--       (Γ ⊢ a ≐ c ∶ A)
