open import Relation.Binary.Structures
open import Relation.Binary.PropositionalEquality

open import Level

module NiceEquiv
  {ℓ : Level}
  {A : Set ℓ}
  where

record NEquiv (_≈_ : A → A → Set ℓ) : Set ℓ where
  field
    NEquiv-equiv : IsEquivalence _≈_
    NEquiv-cong : ∀ (f : A → A) →
               {x x′ : A} →
               x ≈ x′ →
               f x ≈ f x′
    NEquiv-cong₂ : ∀ (f : A → A → A) →
               {x x′ : A} →
               {y y′ : A} →
               x ≈ x′ →
               y ≈ y′ →
               f x y ≈ f x′ y′

    -- NEquiv-ext : ∀ {f g : A → A}

≡-IsEquivalence : ∀ {m} {A : Set m} → IsEquivalence {_} {m} {A} _≡_
≡-IsEquivalence = record { refl = _≡_.refl ; sym = Relation.Binary.PropositionalEquality.sym ; trans = Relation.Binary.PropositionalEquality.trans }

≡-NEquiv : NEquiv _≡_
≡-NEquiv =
  record
  { NEquiv-equiv = ≡-IsEquivalence
  ; NEquiv-cong = cong
  ; NEquiv-cong₂ = cong₂
  }

module NiceEquiv-Ops
  (_≈_ : A → A → Set ℓ)
  (NE : NEquiv _≈_)
  where

  open NEquiv NE

  Nrefl : ∀ {x} → x ≈ x
  Nrefl = IsEquivalence.refl NEquiv-equiv

  Nsym : ∀ {x y} → x ≈ y → y ≈ x
  Nsym = IsEquivalence.sym NEquiv-equiv

  Ntrans : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z
  Ntrans = IsEquivalence.trans NEquiv-equiv
