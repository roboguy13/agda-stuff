open import CategoryRecord
open import Agda
open import Relation.Binary using (IsEquivalence)

open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Level

module AgdaHom
  (e : Level)
  (ℓ : Level)
  (Eq-ℂ : Eq-Category e (suc ℓ) )
  -- (let _≈_ = Category._≈_ Eq-ℂ)

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

ℂ = Cat Eq-ℂ

open Category ℂ
open CategoryProperties ℂ hiding (refl; trans; sym)

-- open IsEquivalence (Category.equiv ℂ {{!!}} {{!!}})

Agda′ : Category (suc (suc ℓ)) (suc ℓ) (suc ℓ ⊔ e)
Agda′ = Agda ℓ e
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
  ; fmap-id = λ {T} →
            let
              eq1 : (λ g → id {proj₂ T} ∘ g ∘ id {proj₁ T}) ≡ (λ g → id ∘ g)
              eq1 = fun-ext ℓ ℓ λ x →
                let
                  p = Category.right-id ℂ {_} {_} {id ∘ x}
                in
                trans (sym (Category.∘-assoc ℂ)) p

              eq2 : (λ (g : proj₁ T ⇒ proj₂ T) → id {proj₂ T} ∘ g) ≡ Category.id Agda′
              eq2 = fun-ext ℓ ℓ λ x → Category.left-id ℂ {_} {_} {x}
            in
            lift (trans eq1 eq2)
  ; fmap-∘ = λ {X} {A} {B} {f} {g} →
           let
             eq1 :   (λ h → proj₂ f ∘ h ∘ proj₁ f)
                        ∘[ Agda′ ]
                     (λ i → proj₂ g ∘ i ∘ proj₁ g)
                   ≡
                     λ z → proj₂ f ∘ (proj₂ g ∘ z ∘ proj₁ g) ∘ proj₁ f
             eq1 = refl

             p z = proj₂ g ∘ z ∘ proj₁ g
             p1 = proj₂ f
             p2 = proj₂ g
             p3 = proj₁ g
             p4 = proj₁ f
             q = (λ (z : proj₁ X ⇒ proj₂ X) → proj₂ f ∘ (proj₂ g ∘ z ∘ proj₁ g) ∘ proj₁ f)

             eq2 :  (λ (z : proj₁ X ⇒ proj₂ X) → proj₂ f ∘ (proj₂ g ∘ z ∘ proj₁ g) ∘ proj₁ f)
                   ≡
                    (λ (z : proj₁ X ⇒ proj₂ X) → (proj₂ f ∘ proj₂ g) ∘ z ∘ (proj₁ g ∘ proj₁ f))
             eq2 = fun-ext ℓ ℓ λ z → ∘-assoc5-mid
           in
           lift (trans eq1 eq2)
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

-- Hom-×-Iso :
--   (_⊗_ : Obj → Obj → Obj) →
--   (∀ A B → IsProduct A B (A ⊗ B)) →
--   ∀ {X A B} →
--   CategoryProperties._≅_ Agda′ (Hom X A × Hom X B) (Hom X (A ⊗ B))
-- Hom-×-Iso _⊗_ product =
--   (λ x → Hom-× _⊗_ product x) , (λ x → {!!} , {!!}) , (λ x → lift {!!}) , λ x → lift {!!}
