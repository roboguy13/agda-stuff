
open import CategoryRecord
open import Agda
open import Level
open import Agda.Primitive

open import Relation.Binary.PropositionalEquality hiding (Extensionality)
open import Relation.Binary.Structures

open import Axiom.Extensionality.Propositional

module Yoneda
  (ℂ : Eq-Category (lsuc lzero) (lsuc lzero))
  -- (≈-is-≡ : ∀ {A B} → Category. ℂ {A} {B} ≡ _≡_)
  where

postulate fun-ext : ∀ {m n} → Extensionality m n
-- postulate fun-ext-gen : ∀ {m n} → Extensionality m n

Agda' : ∀ m → Category (suc (suc m)) (suc m) (suc m)
Agda' m = Agda m (lsuc m) _≡_ ≡-IsEquivalence cong cong₂

-- ℂop : Category lzero (lsuc lzero) (lsuc lzero)
ℂop : Category (lsuc lzero) (lsuc lzero) (lsuc lzero)
ℂop = Op (Cat ℂ)

よ : Functor ℂop (Agda' lzero)
よ = record
  { act = λ X → (∀ Y → (Y ⇒[ ℂop ] X))
  ; fmap = λ f → λ t Y → (f ∘[ ℂop ] t Y)
  ; fmap-id = λ {A} f → lift (fun-ext λ v →
      let
        w : f v ≡ Category.id (Agda' zero) f v
        w = refl

        z : comp ℂop (Category.id ℂop) (f v) ≡ f v
        z = Category.left-id ℂop {_} {_} {f v}

        r : comp ℂop (Category.id ℂop) (f v) ≡ Category.id (Agda' zero) f v
        r = trans z w
      in
      r)
  ; fmap-∘ = λ f → lift (fun-ext λ x → Eq-Category.∘-assoc ℂ)
  }

open Category ℂop
open CategoryProperties
open import Data.Product

×-canon-proj₁-eq : ∀ {m} {A B X : Set (suc m)} {f : X → A} {g : X → B} →
  f ≡ (proj₁ ∘[ Agda' m ] (λ x → f x , g x))
×-canon-proj₁-eq = fun-ext λ x → _≡_.refl

×-pair-eq : ∀ {m} {A B X : Set (suc m)} → {f : X → A} → {g : X → B} → {n : X → (A × B)} →
  f ≡ (proj₁ ∘[ Agda' m ] n) →
  g ≡ (proj₂ ∘[ Agda' m ] n) →
  ∀ x →
  n x ≡ (f x , g x)
×-pair-eq {m} {A} {B} {X} {f} {g} _≡_.refl _≡_.refl x with ×-canon-proj₁-eq {_} {A} {B} {X} {f} {g}
... | _≡_.refl = _≡_.refl

×-canon-proj₁-eq-よ : ∀ {A B : Obj} {X} {f : X ⇒[ Agda' zero ] actf よ A} {g : X ⇒[ Agda' zero ] actf よ B} →
  f ≡ (proj₁ ∘[ Agda' zero ] (λ x → f x , g x))
×-canon-proj₁-eq-よ = fun-ext λ x → _≡_.refl

×-pair-eq-よ : ∀ {A B : Obj} {X} →
  {f : X ⇒[ Agda' zero ] actf よ A} → {g : X ⇒[ Agda' zero ] actf よ B} → {n : X ⇒[ Agda' zero ] (actf よ A × actf よ B)} →
  f ≡ (proj₁ ∘[ Agda' zero ] n) →
  g ≡ (proj₂ ∘[ Agda' zero ] n) →
  ∀ x →
  n x ≡ (f x , g x)
×-pair-eq-よ {A} {B} {X} {f} {g} _≡_.refl _≡_.refl x with ×-canon-proj₁-eq-よ {A} {B} {X} {f} {g}
... | _≡_.refl = _≡_.refl

よ-× : ∀ {A B : Category.Obj ℂop} →
  IsProduct (Agda' zero) (actf よ A) (actf よ B) (actf よ A × actf よ B)
よ-× {A} {B} =
  (λ (a , b) → a) ,
  (λ (a , b) → b) ,
  λ {X} f g → (λ x → f x , g x) ,
          (lift (λ x → lift _≡_.refl) , λ x → lift _≡_.refl) ,
          (λ n (lift x , y) a →
            lift (×-pair-eq-よ {A} {B} {X} {f} {g} {n} (fun-ext λ x₁ → lower (x x₁)) (fun-ext λ y₁ → lower (y y₁)) a))
