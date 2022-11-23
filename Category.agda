-- Based on "Formalizing Category Theory in Agda" (Hu and Carette, 2020)

open import Relation.Binary.Structures
open import Agda.Primitive

module CategoryRecord
  where

record Category (ℓ : Level) : Set (lsuc ℓ) where
  field
    Obj : Set ℓ
    _⇒_ : Obj → Obj → Set
    _∘_ : ∀ {A B C} → (B ⇒ C) → (A ⇒ B) → (A ⇒ C)
    _≈_ : ∀ {A B} → (f g : A ⇒ B) → Set
    equiv : ∀ {A B} → IsEquivalence (_≈_ {A} {B})
    ∘-resp-≈ : ∀ {A B C} → {f h : B ⇒ C} {g i : A ⇒ B} →
                    (f ≈ h) → (g ≈ i) → ((f ∘ g) ≈ (h ∘ i))

    id : ∀ {A} → (A ⇒ A)
    left-id : ∀ {A B} → ∀ {f : A ⇒ B} → (id ∘ f) ≈ f
    right-id : ∀ {A B} → ∀ {f : A ⇒ B} → (f ∘ id) ≈ f
    ∘-assoc : ∀ {A B C D} → ∀ {f : C ⇒ D} {g : B ⇒ C} {h : A ⇒ B} →
                    ((f ∘ g) ∘ h) ≈ (f ∘ (g ∘ h))
