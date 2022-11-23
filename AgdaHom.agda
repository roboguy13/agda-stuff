open import CategoryRecord
open import Agda
open import Relation.Binary using (IsEquivalence)

open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Level

module AgdaHom
  (e : Level)
  (ℓ : Level)
  (ℂ : Category e (suc ℓ) e)
  (let _≈_ = Category._≈_ ℂ)

  -- (_≈ₒ_ : ∀ {m} {A : Set m} → A → A → Set m)
  -- (≈ₒ-equiv : ∀ {m} {A : Set m} → IsEquivalence {_} {m} {A} _≈ₒ_)
  -- (≈-cong : ∀ {m} {A B : Set m} → (f : A → B) →
  --              {x x′ : A} →
  --              x ≈ x′ →
  --              f x ≈ f x′)
  -- (≈-cong₂ : ∀ {m} {A B C : Set m} → (f : A → B → C) →
  --              {x x′ : A} → {y y′ : B} →
  --              x ≈ x′ →
  --              y ≈ y′ →
  --              f x y ≈ f x′ y′)
  where

open Category ℂ
open CategoryProperties ℂ

-- open IsEquivalence (Category.equiv ℂ {{!!}} {{!!}})

Agda′ : Category (suc (suc ℓ)) (suc ℓ) (suc ℓ ⊔ e)
Agda′ = Agda ℓ e _≡_ ≡-IsEquivalence cong cong₂
-- Agda′ = Agda ? ? (Category._≈_ ℂ) ? ? ? --≈-cong ≈-cong₂

-- reflₒ : ∀ {A B} {f : A ⇒[ Agda′ ] B} → f ≈ₒ f
-- reflₒ = IsEquivalence.refl ≈ₒ-equiv
-- symₒ : ∀ {A B} {f g : A ⇒[ Agda′ ] B} → f ≈ₒ g → g ≈ₒ f
-- symₒ = IsEquivalence.sym ≈ₒ-equiv
-- transₒ : ∀ {A B} {f g h : A ⇒[ Agda′ ] B} → f ≈ₒ g → g ≈ₒ h → f ≈ₒ h
-- transₒ = IsEquivalence.trans ≈ₒ-equiv

Hom :
  (A : Category.Obj ℂ) → (B : Category.Obj ℂ) →
  Category.Obj Agda′
Hom A B = A ⇒[ ℂ ] B

infixr 9 _∘[Hom]_
_∘[Hom]_ :
  ∀ {A B C} →
  Hom B C →
  Hom A B →
  Hom A C
_∘[Hom]_ f g = f ∘[ ℂ ] g

Hom-whisker-right : ∀ {A B X} →
  (f : X ⇒[ ℂ ] A) →
  Hom A B →
  Hom X B
Hom-whisker-right f H = H ∘[Hom] f

Hom-whisker-left : ∀ {A B X} →
  (f : B ⇒[ ℂ ] X) →
  Hom A B →
  Hom A X
Hom-whisker-left f H = f ∘[Hom] H

    -- fmap-id : ∀ {A} →
    --   (fmap (Category.id Src {A})) ≈[ Tgt ] (Category.id Tgt)

Hom-F : Functor (Op ℂ ×cat ℂ) Agda′
Hom-F =
  record
  { act = λ (A , B) → Hom A B
  ; fmap = λ {A} {B} (f₁ , f₂) g → f₂ ∘ g ∘ f₁
  ; fmap-id = λ {T} x →
            let
              A , B = T
              eq : (id ∘ x) ≡ x
              eq = (Category.∘-resp-≈ Agda′ {!!} {!!} ?)
              -- eq = lower (Category.left-id Agda′ {{!!}} {{!!}} {x} ?)
            in
            -- lift (lower (Category.∘-resp-≈ Agda′ {!!} {!!} (λ z → z)))
            lift (IsEquivalence.trans ≡-IsEquivalence (lower (Category.left-id Agda′ {Hom A A} {Hom A B} {λ h → {!!}} id)) {!!})
            -- lift (IsEquivalence.trans ≡-IsEquivalence (lower (Category.left-id Agda′ {Hom {!!} {!!}} {Hom {!!} {!!}} {λ x₁ → x ∘ id} {!!})) {!!})
            -- -- lift (IsEquivalence.trans ≈ₒ-equiv (lower (Category.left-id Agda′ {Hom A B} {Hom A B} {{!!}} x)) (lower (Category.left-id Agda′ x)))
            -- let
            --   eq0 : (id ∘ x ∘ id)  (id ∘ x)
            --   eq0 = {!!}

            --   -- x : Hom A B
            --   eq1 : (id ∘ x) ≈ₒ x
            --   eq1 = left-id {A} {B} {x}

            --   eq : (id ∘ x ∘ id) ≈ₒ x
            --   eq = IsEquivalence.trans ≈ₒ-equiv eq0 eq1
            --     -- IsEquivalence.trans ≈ₒ-equiv (lower (Category.left-id Agda′ {Hom A B} {Hom A B} {λ x₁ → {!!}} x))
            --     --   (IsEquivalence.trans ≈ₒ-equiv (lower (Category.left-id Agda′ {Hom A B} {Hom A B} {λ x₁ → x₁} x)) {!!})
            -- in
            -- lift (IsEquivalence.trans ≈ₒ-equiv eq (IsEquivalence.refl ≈ₒ-equiv))
    -- left-id : ∀ {A B} → ∀ {f : A ⇒ B} → (id ∘ f) ≈ f
  ; fmap-∘ = {!!}
  }


Hom-Initial :
  {𝟘 : Category.Obj ℂ} → IsInitial 𝟘 →
  ∀ {A} →
  Hom 𝟘 A
Hom-Initial 𝟘-initial {A} = 𝟘-map 𝟘-initial

Hom-Terminal :
  ∀ {𝟙} → IsTerminal 𝟙 →
  ∀ {A} →
  Hom A 𝟙
Hom-Terminal 𝟙-terminal {A} = 𝟙-map 𝟙-terminal


Hom-Const : ∀ {𝟙} → IsTerminal 𝟙 →
  ∀ {A B} →
  (b : Hom 𝟙 B) →
  Hom A B
Hom-Const {𝟙} 𝟙-terminal {A} {B} b = b ∘[Hom] (Hom-Terminal 𝟙-terminal)

Hom-𝟘 : ∀ {𝟘} → IsInitial 𝟘 →
  ∀ {A B} →
  Hom A 𝟘 →
  Hom A B
Hom-𝟘 {𝟘} 𝟘-initial H = Hom-Initial 𝟘-initial ∘[Hom] H

Hom-× :
  (_⊗_ : Obj → Obj → Obj) →
  (∀ A B → IsProduct A B (A ⊗ B)) →
  ∀ {X A B} →
  Hom X A × Hom X B →
  Hom X (A ⊗ B)
Hom-× _⊗_ product (f , g) = joined-bimap _⊗_ product f g

Hom-×-Iso :
  (_⊗_ : Obj → Obj → Obj) →
  (∀ A B → IsProduct A B (A ⊗ B)) →
  ∀ {X A B} →
  CategoryProperties._≅_ Agda′ (Hom X A × Hom X B) (Hom X (A ⊗ B))
Hom-×-Iso _⊗_ product =
  (λ x → Hom-× _⊗_ product x) , (λ x → {!!} , {!!}) , (λ x → lift {!!}) , λ x → lift {!!}
