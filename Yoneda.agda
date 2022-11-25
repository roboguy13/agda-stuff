
open import Category
open import CategoryRecord
open import Agda
open import Level
open import Agda.Primitive

open import Relation.Binary.PropositionalEquality hiding (Extensionality)
open import Relation.Binary.Structures

open import Axiom.Extensionality.Propositional

module Yoneda
  (o ℓ : Level)
  (Eq-ℂ : Eq-Category o ℓ)
  -- (≈-is-≡ : ∀ {A B} → Category. ℂ {A} {B} ≡ _≡_)
  where

-- postulate fun-ext : ∀ {m n} → Extensionality m n
-- postulate fun-ext-gen : ∀ {m n} → Extensionality m n

-- Agda' : Category ? ? ? --Category (suc (suc e)) (suc e) (suc e ⊔ ℓ)
-- Agda' = Agda e ℓ
-- Agda' : Category (suc (o ⊔ ℓ)) (o ⊔ ℓ) (o ⊔ ℓ)
-- Agda' = Agda (o ⊔ ℓ) ℓ ℓ
Agda' : Category (suc ℓ) ℓ (ℓ ⊔ ℓ)
Agda' = Agda ℓ ℓ ℓ

ℂ : Category o ℓ ℓ
ℂ = Cat Eq-ℂ

-- ℂop : Category lzero (lsuc lzero) (lsuc lzero)
ℂop : Category o ℓ ℓ -- e (suc ℓ) (suc ℓ) --Category e (suc ℓ) (suc ℓ)
ℂop = Op ℂ

Rep : (A : Category.Obj ℂop) → Functor ℂop Agda'
Rep A =
  record
  { act = λ X → (A ⇒[ ℂop ] X)
  ; fmap = λ f → λ t → (f ∘[ ℂop ] t)
  ; fmap-id = λ {_} → lift (fun-ext ℓ ℓ ℓ λ x → Category.right-id ℂ)
  ; fmap-∘ = lift (fun-ext ℓ ℓ ℓ (λ x → Category.∘-assoc ℂ))
  ; fmap-cong = λ x →
              lift (IsEquivalence.trans ≡-IsEquivalence {!!} {!!})
  }

よ : Functor ℂ [ ℂop ,, Agda' ]
よ =
  record
    { act = λ x → {!!}
    ; fmap = {!!}
    ; fmap-id = {!!}
    ; fmap-∘ = {!!}
    ; fmap-cong = {!!}
    }

-- よ : (A : Category.Obj ℂop) → Functor ℂop (Agda ℓ ℓ ℓ)
-- よ A = record
--   { act = λ X → (A ⇒[ ℂop ] X)
--   ; fmap = λ f → λ t → (f ∘[ ℂop ] t)
--   ; fmap-id = λ {_} → lift (fun-ext ℓ ℓ ℓ λ x → Eq-Category.right-id ℂ)
--   ; fmap-∘ = lift (fun-ext ℓ ℓ ℓ (λ x → Eq-Category.∘-assoc ℂ))
--   }

open Category.Category ℂop
open CategoryProperties
open import Data.Product

-- ×-canon-proj₁-eq : ∀ {A B X : Set (o ⊔ ℓ)} {f : X → A} {g : X → B} →
--   f ≡ (proj₁ ∘[ Agda' ] (λ x → f x , g x))
-- ×-canon-proj₁-eq = fun-ext ℓ ℓ ℓ λ x → _≡_.refl

-- ×-pair-eq : ∀ {A B X : Set (o ⊔ ℓ)} → {f : X → A} → {g : X → B} → {n : X → (A × B)} →
--   f ≡ (proj₁ ∘[ Agda' ] n) →
--   g ≡ (proj₂ ∘[ Agda' ] n) →
--   ∀ x →
--   n x ≡ (f x , g x)
-- ×-pair-eq  {A} {B} {X} {f} {g} _≡_.refl _≡_.refl x with ×-canon-proj₁-eq {A} {B} {X} {f} {g}
-- ... | _≡_.refl = _≡_.refl

-- ×-canon-proj₁-eq-よ : ∀ {A B : Obj} {X} {f : X ⇒[ Agda' ] actf よ A} {g : X ⇒[ Agda' ] actf よ B} →
--   f ≡ (proj₁ ∘[ Agda' ] (λ x → f x , g x))
-- ×-canon-proj₁-eq-よ = fun-ext ℓ ℓ ℓ λ x → _≡_.refl

-- ×-pair-eq-よ : ∀ {A B : Obj} {X} →
--   {f : X ⇒[ Agda' ] actf よ A} → {g : X ⇒[ Agda' ] actf よ B} → {n : X ⇒[ Agda' ] (actf よ A × actf よ B)} →
--   f ≡ (proj₁ ∘[ Agda' ] n) →
--   g ≡ (proj₂ ∘[ Agda' ] n) →
--   ∀ x →
--   n x ≡ (f x , g x)
-- ×-pair-eq-よ {A} {B} {X} {f} {g} _≡_.refl _≡_.refl x with ×-canon-proj₁-eq-よ {A} {B} {X} {f} {g}
-- ... | _≡_.refl = _≡_.refl

-- よ-× : ∀ (A B : Category.Obj ℂop) →
--   IsProduct Agda' (actf よ A) (actf よ B) (actf よ A × actf よ B)
-- よ-× A B =
--   (λ (a , b) → a) ,
--   (λ (a , b) → b) ,
--   λ {X} f g → (λ x → f x , g x) ,
--           (lift (lift _≡_.refl) , lift _≡_.refl) ,
--           (λ n (lift x , y) →
--             lift (fun-ext ℓ ℓ ℓ (×-pair-eq-よ (lower x) (lower y))))

-- よ-exp : ∀ {A B Z : Category.Obj ℂop} →
--   IsExponential (Agda (o ⊔ ℓ) ℓ ℓ) {actf よ A} {actf よ B} _×_ (λ X Y → ×-IsProduct (o ⊔ ℓ) ℓ ℓ X Y)
--     (actf よ A → actf よ B)
--     λ (f , x) → f x
-- よ-exp Z e =
--   (λ x x₁ → e (x , x₁)) , lift _≡_.refl , λ n (lift p) → lift (fun-ext ℓ ℓ ℓ λ x → {!!})

-- --   -- IsExponential : ∀ {A B : Obj} →
-- --   --   (_⊗_ : Obj → Obj → Obj) →
-- --   --   (∀ X Y → IsProduct X Y (X ⊗ Y)) →
-- --   --   (A⟶B : Obj) →
-- --   --   (ev : (A⟶B ⊗ A) ⇒ B) →
-- --   --   Set (o ⊔ ℓ ⊔ e)
-- --   -- IsExponential {A} {B} _⊗_ product A⟶B ev =
