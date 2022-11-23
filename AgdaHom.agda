open import CategoryRecord
open import Agda
open import Relation.Binary

open import Level

module AgdaHom
  (e : Level)
  (ℓ : Level)
  (ℂ : Category e (suc ℓ) e)

  (_≈ₒ_ : ∀ {m} {A : Set m} → A → A → Set m)
  (≈ₒ-equiv : ∀ {m} {A : Set m} → IsEquivalence {_} {m} {A} _≈ₒ_)
  (≈ₒ-cong : ∀ {m} {A B : Set m} → (f : A → B) →
               {x x′ : A} →
               x ≈ₒ x′ →
               f x ≈ₒ f x′)
  (≈ₒ-cong₂ : ∀ {m} {A B C : Set m} → (f : A → B → C) →
               {x x′ : A} → {y y′ : B} →
               x ≈ₒ x′ →
               y ≈ₒ y′ →
               f x y ≈ₒ f x′ y′)
  where

Agda′ : Category (suc (suc ℓ)) (suc ℓ) (suc ℓ ⊔ e)
Agda′ = Agda ℓ e _≈ₒ_ ≈ₒ-equiv ≈ₒ-cong ≈ₒ-cong₂

Hom :
  (A : Category.Obj ℂ) → (B : Category.Obj ℂ) →
  Category.Obj Agda′
Hom A B = A ⇒[ ℂ ] B

Hom-Initial :
  {𝟘 : Category.Obj ℂ} → CategoryProperties.IsInitial ℂ 𝟘 →
  ∀ {A} →
  (Hom 𝟘 A)
Hom-Initial 𝟘-initial {A} = CategoryProperties.𝟘-map ℂ 𝟘-initial

_∘[Hom]_ :
  ∀ {A B C} →
  Hom B C →
  Hom A B →
  Hom A C
_∘[Hom]_ f g = f ∘[ ℂ ] g
