
open import CategoryRecord
open import Agda
open import Level
open import Agda.Primitive

open import Relation.Binary.PropositionalEquality hiding (Extensionality)
open import Relation.Binary.Structures

open import Axiom.Extensionality.Propositional

module Yoneda
  (ℂ : Eq-Category lzero (lsuc lzero))
  -- (≈-is-≡ : ∀ {A B} → Category. ℂ {A} {B} ≡ _≡_)
  where

postulate fun-ext : Extensionality ℓ (lsuc ℓ)

Agda' : ∀ m → Category (suc (suc m)) (suc m) (suc m)
Agda' m = Agda m (lsuc m) _≡_ ≡-IsEquivalence cong cong₂

ℂop : Category lzero (lsuc lzero) (lsuc lzero)
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

open CategoryProperties
open import Data.Product

よ-× : ∀ {A B : Category.Obj ℂop} →
  IsProduct (Agda' zero) (actf よ A) (actf よ B) (actf よ A × actf よ B)
よ-× =
  (λ (a , b) Y → {!!}) ,
  (λ (a , b) Y → {!!}) ,
  λ f g → (λ x → {!!}) ,
          ({!!} , {!!}) ,
          (λ n x x₁ → {!!})
