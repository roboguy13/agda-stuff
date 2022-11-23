
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

-- postulate fun-ext : ∀ {m n} → Extensionality m n
-- postulate fun-ext-gen : ∀ {m n} → Extensionality m n

Agda' : ∀ m → Category (suc (suc m)) (suc m) (suc m)
Agda' m = Agda m (lsuc m)

-- ℂop : Category lzero (lsuc lzero) (lsuc lzero)
ℂop : Category (lsuc lzero) (lsuc lzero) (lsuc lzero)
ℂop = Op (Cat ℂ)

よ : Functor ℂop (Agda' lzero)
よ = record
  { act = λ X → (∀ Y → (Y ⇒[ ℂop ] X))
  ; fmap = λ f → λ t Y → (f ∘[ ℂop ] t Y)
  ; fmap-id = λ {_} → lift (fun-ext zero zero λ f →
      let
        w : ∀ x → f x ≡ Category.id (Agda' zero) f x
        w x = refl

        z : ∀ x → comp ℂop (Category.id ℂop) (f x) ≡ f x
        z x = Category.left-id ℂop {_} {_} {f x}

        r : ∀ x → comp ℂop (Category.id ℂop) (f x) ≡ Category.id (Agda' zero) f x
        r x = trans (z x) (w x)
      in
      fun-ext zero zero r)
  ; fmap-∘ = lift (fun-ext zero zero λ x →
               fun-ext zero zero (λ x → Eq-Category.∘-assoc ℂ))
  }

open Category ℂop
open CategoryProperties
open import Data.Product

×-canon-proj₁-eq : ∀ {m} {A B X : Set (suc m)} {f : X → A} {g : X → B} →
  f ≡ (proj₁ ∘[ Agda' m ] (λ x → f x , g x))
×-canon-proj₁-eq {m} = fun-ext m m λ x → _≡_.refl

×-pair-eq : ∀ {m} {A B X : Set (suc m)} → {f : X → A} → {g : X → B} → {n : X → (A × B)} →
  f ≡ (proj₁ ∘[ Agda' m ] n) →
  g ≡ (proj₂ ∘[ Agda' m ] n) →
  ∀ x →
  n x ≡ (f x , g x)
×-pair-eq {m} {A} {B} {X} {f} {g} _≡_.refl _≡_.refl x with ×-canon-proj₁-eq {_} {A} {B} {X} {f} {g}
... | _≡_.refl = _≡_.refl

×-canon-proj₁-eq-よ : ∀ {A B : Obj} {X} {f : X ⇒[ Agda' zero ] actf よ A} {g : X ⇒[ Agda' zero ] actf よ B} →
  f ≡ (proj₁ ∘[ Agda' zero ] (λ x → f x , g x))
×-canon-proj₁-eq-よ = fun-ext zero zero λ x → _≡_.refl

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
          (lift (lift _≡_.refl) , lift _≡_.refl) ,
          (λ n (lift x , y) →
            lift (fun-ext zero zero (×-pair-eq-よ (lower x) (lower y))))
