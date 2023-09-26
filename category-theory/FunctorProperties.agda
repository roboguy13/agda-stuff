open import Category
open import FunctorDefs
import ElementaryProperties

open import Data.Product
open import Level

open import Relation.Binary.PropositionalEquality hiding (Extensionality)

module FunctorProperties
  where

Op-Op : ∀ {o ℓ} → {ℂ : Category o ℓ} →
  Op (Op ℂ) ≡ ℂ
Op-Op {o} {ℓ} {record { Obj = Obj ; _⇒_ = _⇒_ ; _∘_ = _∘_ ; id = id ; left-id = left-id ; right-id = right-id ; ∘-assoc = ∘-assoc }} = {!!}


-- F(A, -)
F-Left : ∀ {o₁ ℓ₁ o₂ ℓ₂ o₃ ℓ₃} → {ℂ : Category o₁ ℓ₁} {𝔻 : Category o₂ ℓ₂} {𝔼 : Category o₃ ℓ₃} →
  Functor (ℂ ×cat 𝔻) 𝔼 →
  Category.Obj ℂ →
  Functor 𝔻 𝔼
F-Left {_} {_} {_} {_} {_} {_} {ℂ} {𝔻} {𝔼} F A =
  record
    { act = λ B → actf F (A , B)
    ; fmap′ = λ B C f → Functor.fmap F (Category.id ℂ , f)
    ; fmap-id′ = λ B → Functor.fmap-id F
    ; fmap-∘′ = λ B C D f g →
              let
                p : ∀ {T} →
                    comp 𝔼 (Functor.fmap F (Category.id ℂ {T} , f)) (Functor.fmap F (Category.id ℂ , g))
                    ≡ Functor.fmap F (Category.id ℂ ∘[ ℂ ] Category.id ℂ , comp 𝔻 f g)
                p = Functor.fmap-∘ F

                q : ∀ {T} →
                    Functor.fmap F (Category.id ℂ {T} ∘[ ℂ ] Category.id ℂ , comp 𝔻 f g)
                    ≡
                    Functor.fmap F (Category.id ℂ , comp 𝔻 f g)
                q =
                  cong (λ z → Functor.fmap F (z , comp 𝔻 f g))
                    (Category.left-id ℂ)
              in
              trans p q
    }

-- F(-, B)
F-Right : ∀ {o₁ ℓ₁ o₂ ℓ₂ o₃ ℓ₃} → {ℂ : Category o₁ ℓ₁} {𝔻 : Category o₂ ℓ₂} {𝔼 : Category o₃ ℓ₃} →
  Functor (ℂ ×cat 𝔻) 𝔼 →
  Category.Obj 𝔻 →
  Functor ℂ 𝔼
F-Right {_} {_} {_} {_} {_} {_} {ℂ} {𝔻} {𝔼} F B =
  record
    { act = λ A → actf F (A , B)
    ; fmap′ = λ B C f → Functor.fmap F (f , Category.id 𝔻)
    ; fmap-id′ = λ B → Functor.fmap-id F
    ; fmap-∘′ = λ B C D f g →
              let
                p : ∀ {T} →
                    comp 𝔼 (Functor.fmap F (f , Category.id 𝔻 {T})) (Functor.fmap F (g , Category.id 𝔻))
                    ≡ Functor.fmap F (comp ℂ f g , Category.id 𝔻 ∘[ 𝔻 ] Category.id 𝔻)
                p = Functor.fmap-∘ F

                q : ∀ {T} →
                    Functor.fmap F (comp ℂ f g , Category.id 𝔻 {T} ∘[ 𝔻 ] Category.id 𝔻)
                    ≡
                    Functor.fmap F (comp ℂ f g , Category.id 𝔻)
                q =
                  cong (λ z → Functor.fmap F (comp ℂ f g , z))
                    (Category.left-id 𝔻)
              in
              trans p q
    }


Is-NatIso : ∀ {o₁ ℓ₁ o₂ ℓ₂} {ℂ : Category o₁ ℓ₁} {𝔻 : Category o₂ ℓ₂} →
  (F G : Functor ℂ 𝔻) →
  NatTrans F G →
  Set (o₁ ⊔ ℓ₂)
Is-NatIso {_} {_} {_} {_} {ℂ} {𝔻} F G α =
  ∀ x → ∃[ α⁻¹x ] (Iso 𝔻 (NatTrans.component α x) (α⁻¹x))
  where
  open ElementaryProperties

NatIso : ∀ {o₁ ℓ₁ o₂ ℓ₂} {ℂ : Category o₁ ℓ₁} {𝔻 : Category o₂ ℓ₂} →
  (F G : Functor ℂ 𝔻) →
  Set (suc o₁ ⊔ suc ℓ₁ ⊔ suc o₂ ⊔ suc ℓ₂)
NatIso {_} {_} {_} {_} {ℂ} {𝔻} F G =
  Σ (NatTrans F G) (Is-NatIso F G)
  where
  open ElementaryProperties

_≃_ : ∀ {o₁ ℓ₁ o₂ ℓ₂} {ℂ : Category o₁ ℓ₁} {𝔻 : Category o₂ ℓ₂} →
  (F G : Functor ℂ 𝔻) →
  Set (suc o₁ ⊔ suc ℓ₁ ⊔ suc o₂ ⊔ suc ℓ₂)
_≃_ F G = NatIso F G

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

-- Functor-⊗′-proj₁ : ∀ {o₁ ℓ₁ o₂ ℓ₂} {ℂ : Category o₁ ℓ₁} {𝔻 : Category o₂ ℓ₂} →
--   (_⊗_ : Category.Obj 𝔻 → Category.Obj 𝔻 → Category.Obj 𝔻) →
--   (product : ∀ X Y → ElementaryProperties.IsProduct 𝔻 X Y (X ⊗ Y)) →
--   (F G : Functor ℂ 𝔻) →
--   NatTrans (Functor-⊗′ _⊗_ product F G) (F ∘F ×cat-proj₁)
-- Functor-⊗′-proj₁ {_} {_} {_} {_} {ℂ} {𝔻} _⊗_ product F G = {!!}
--   -- record
--   --   { component = λ x → {!!} ∘[ 𝔻 ] Functor.fmap (Functor-⊗′ _⊗_ product F G) {!!}
--   --               -- {!CategoryProperties.bimap _⊗_ product!} -- {!!} ∘[ 𝔻 ] Functor.fmap (Functor-⊗′ _⊗_ product F G) {!!}
--   --   -- { component = λ x → {!!} ∘[ 𝔻 ] {!!}
--   --   ; natural = {!!}
--   --   }

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
