open import Category
open import FunctorDefs
import ElementaryProperties

open import Data.Product
open import Level

open import Relation.Binary.PropositionalEquality hiding (Extensionality)

module FunctorProperties
  where

-- --              !m
--        AxB  ----> AxB
--       f/ \g      p/ \q
--       A   B      A   B
Product-Functor : ∀ {o ℓ} {ℂ : Category o ℓ} →
  (_⊗_ : Category.Obj ℂ → Category.Obj ℂ → Category.Obj ℂ) →
  (∀ X Y → ElementaryProperties.IsProduct ℂ X Y (X ⊗ Y)) →
  Functor (ℂ ×cat ℂ) ℂ
Product-Functor {_} {_} {ℂ} _⊗_ product =
  record
    { act = λ (x , y) → x ⊗ y
    ; fmap′ = λ A B (f , g) → bimap _⊗_ product f g
    ; fmap-id′ = λ (A , B) → bimap-id _⊗_ product
    ; fmap-∘′ = λ R S T f g →
              let
                f1 , f2 = f
                g1 , g2 = g

                q1 : proj₁ (comp (ℂ ×cat ℂ) f g) ≡ (f1 ∘ g1)
                q1 = refl

                q2 : proj₂ (comp (ℂ ×cat ℂ) f g) ≡ (f2 ∘ g2)
                q2 = refl

                r : proj₁
                      (proj₂ (proj₂ (product (proj₁ T) (proj₂ T)))
                        (proj₁ (comp (ℂ ×cat ℂ) f g) ∘ proj₁ (product (proj₁ R) (proj₂ R)))
                        (proj₂ (comp (ℂ ×cat ℂ) f g) ∘
                          proj₁ (proj₂ (product (proj₁ R) (proj₂ R)))))
                    ≡
                    proj₁
                      (proj₂ (proj₂ (product (proj₁ T) (proj₂ T)))
                        ((f1 ∘ g1) ∘ proj₁ (product (proj₁ R) (proj₂ R)))
                        ((f2 ∘ g2) ∘
                          proj₁ (proj₂ (product (proj₁ R) (proj₂ R)))))
                r = refl

              in
              trans (rewrite-left-∘ (sym (bimap-canon _⊗_ product)) refl) (trans (trans (bimap-∘ _⊗_ product) (sym r)) (sym (bimap-canon _⊗_ product)))
    }
  where
  open ElementaryProperties ℂ
  open Category.Category ℂ
  open CatBasics ℂ

Functor-⊗′ : ∀ {o₁ ℓ₁ o₂ ℓ₂} {ℂ : Category o₁ ℓ₁} {𝔻 : Category o₂ ℓ₂} →
  (_⊗_ : Category.Obj 𝔻 → Category.Obj 𝔻 → Category.Obj 𝔻) →
  (∀ X Y → ElementaryProperties.IsProduct 𝔻 X Y (X ⊗ Y)) →
  (F G : Functor ℂ 𝔻) →
  Functor (ℂ ×cat ℂ) 𝔻
Functor-⊗′ _⊗_ product F G =
  Product-Functor _⊗_ product ∘F (Functor-⊗ F G)

Functor-⊗′-proj₁ : ∀ {o₁ ℓ₁ o₂ ℓ₂} {ℂ : Category o₁ ℓ₁} {𝔻 : Category o₂ ℓ₂} →
  (_⊗_ : Category.Obj 𝔻 → Category.Obj 𝔻 → Category.Obj 𝔻) →
  (product : ∀ X Y → ElementaryProperties.IsProduct 𝔻 X Y (X ⊗ Y)) →
  (F G : Functor ℂ 𝔻) →
  NatTrans (Functor-⊗′ _⊗_ product F G) (F ∘F ×cat-proj₁)
Functor-⊗′-proj₁ {_} {_} {_} {_} {ℂ} {𝔻} _⊗_ product F G = {!!}
  -- record
  --   { component = λ x → {!!} ∘[ 𝔻 ] Functor.fmap (Functor-⊗′ _⊗_ product F G) {!!}
  --               -- {!CategoryProperties.bimap _⊗_ product!} -- {!!} ∘[ 𝔻 ] Functor.fmap (Functor-⊗′ _⊗_ product F G) {!!}
  --   -- { component = λ x → {!!} ∘[ 𝔻 ] {!!}
  --   ; natural = {!!}
  --   }

-- ×cat-proj₁ : ∀ {o₁ ℓ₁ o₂ ℓ₂} {ℂ : Category o₁ ℓ₁} {𝔻 : Category o₂ ℓ₂} → Functor (ℂ ×cat 𝔻) ℂ
-- ×cat-proj₁ {_} {_} {_} {_} {ℂ} {𝔻} =
--   record
--     { act = proj₁
--     ; fmap′ = λ _ _ (f , g) → f
--     ; fmap-id′ = λ A → refl
--     ; fmap-∘′ = λ A B C f g → refl
--     }

-- ×cat-proj₂ : ∀ {o₁ ℓ₁ o₂ ℓ₂} {ℂ : Category o₁ ℓ₁} {𝔻 : Category o₂ ℓ₂} → Functor (ℂ ×cat 𝔻) 𝔻

-- Functor-⊗′-IsProduct : ∀ {o₁ ℓ₁ o₂ ℓ₂} {ℂ : Category o₁ ℓ₁} {𝔻 : Category o₂ ℓ₂} →
--   (_⊗_ : Category.Obj 𝔻 → Category.Obj 𝔻 → Category.Obj 𝔻) →
--   (product : ∀ X Y → ElementaryProperties.IsProduct {_} {_} 𝔻 X Y (X ⊗ Y)) →
--   ∀ (F G : Category.Obj [ ℂ ,, 𝔻 ]) →
--   -- ElementaryProperties.IsProduct {_} {_} [ ℂ ,, 𝔻 ] F G (Functor-⊗′ _⊗_ product F G)
--   ElementaryProperties.IsProduct {_} {_} ? F G (Functor-⊗′ _⊗_ product F G)
-- Functor-⊗′-IsProduct _⊗_ product F G =
--   {!!} , {!!}

-- Lift universe level
Lifted-Cat : ∀ {o₁ ℓ₁ o₂ ℓ₂} →
  (ℂ : Category o₁ ℓ₁) →
  Category (o₁ ⊔ o₂) (ℓ₁ ⊔ ℓ₂)
Lifted-Cat {o₁} {ℓ₁} {o₂} {ℓ₂} ℂ =
  record
    { Obj = Lift (o₁ ⊔ o₂) (Category.Obj ℂ)
    ; _⇒_ = λ A B → Lift ℓ₂ (lower A ⇒[ ℂ ] lower B)
    ; _∘_ = λ f g → lift (lower f ∘[ ℂ ] lower g)
    ; id = lift (Category.id ℂ)
    ; left-id = cong lift (Category.left-id ℂ)
    ; right-id = cong lift (Category.right-id ℂ)
    ; ∘-assoc = cong lift (Category.∘-assoc ℂ)
    }

-- -- -- Lower-Cat : ∀ {o₁ ℓ₁ o₂ ℓ₂} →
-- -- --   {ℂ : Category (o₁ ⊔ o₂) (ℓ₁ ⊔ ℓ₂)} →
-- -- --   Lifted-Cat {o₁} {ℓ₁} ℂ →
-- -- --   Category o₁ ℓ₁
-- -- -- Lower-Cat {o₁} {ℓ₁} {o₂} {ℓ₂} {ℂ} _ = ℂ


Lifting-Functor : ∀ {o₁ ℓ₁} o₂ ℓ₂ →
  {ℂ : Category o₁ ℓ₁} →
  Functor ℂ (Lifted-Cat {_} {_} {o₂} {ℓ₂} ℂ)
Lifting-Functor {o₁} {ℓ₁} o₂ ℓ₂ {ℂ} =
  record
    { act = lift
    ; fmap′ = λ A B f → lift f
    ; fmap-id′ = λ A → cong lift refl
    ; fmap-∘′ = λ A B C f g → cong lift refl
    }

Lowering-Functor : ∀ {o₁ ℓ₁} o₂ ℓ₂ →
  {ℂ : Category o₁ ℓ₁} →
  Functor (Lifted-Cat {_} {_} {o₂} {ℓ₂} ℂ) ℂ
Lowering-Functor {o₁} {ℓ₁} o₂ ℓ₂ {ℂ} =
  record
    { act = lower
    ; fmap′ = λ A B f → lower f
    ; fmap-id′ = λ A → refl
    ; fmap-∘′ = λ A B C f g → refl
    }
