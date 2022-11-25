
open import Category
open import CategoryRecord
open import Agda
open import Level
open import Agda.Primitive

open import Relation.Binary.PropositionalEquality hiding (Extensionality)
open import Relation.Binary.Structures

open import Axiom.Extensionality.Propositional

open CatBasics
open Category.Category

module Yoneda
  (o ℓ : Level)
  (ℂ : Category o ℓ)
  where

Agda' : Category (suc ℓ) ℓ
Agda' = Agda

ℂop : Category o ℓ
ℂop = Op ℂ

Rep : (A : Category.Obj ℂop) → Functor ℂop Agda'
Rep A =
  record
  { act = λ X → (A ⇒[ ℂop ] X)
  ; fmap′ = λ _ _ f → λ t → (f ∘[ ℂop ] t)
  ; fmap-id′ = λ _ → (fun-ext λ x → Category.right-id ℂ)
  ; fmap-∘′ = λ _ _ _ _ _ → (fun-ext (λ x → Category.∘-assoc ℂ))
  }

-- Corep : (A : Category.Obj ℂ) → Functor ℂ Agda'
-- Corep A =
--   record
--   { act = λ X → (X ⇒[ ℂ ] A)
--   ; fmap′ = λ B C f → λ t → ({!!} ∘[ ℂ ] {!!})
--   ; fmap-id′ = λ _ → (fun-ext λ x → Category.right-id ℂ)
--   ; fmap-∘′ = λ _ _ _ _ _ → (fun-ext (λ x → (Category.∘-assoc ℂ)))
--   }


よ : Functor ℂ [ ℂop ,, Agda' ]
よ =
  record
    { act = λ x → Rep x
    ; fmap′ = λ A B f →
            record
              { component = λ x x₁ → x₁ ∘[ ℂop ] f
              ; natural = λ x y f₁ →
                  fun-ext λ x₁ →
                    let
                      q : comp Agda' (λ x₂ → comp ℂop x₂ f) (Functor.fmap (Rep A) f₁) x₁
                               ≡
                          (Functor.fmap (Rep A) f₁ x₁ ∘[ ℂop ] f)
                      q = refl

                      q2 : (Functor.fmap (Rep A) f₁ x₁ ∘[ ℂop ] f)
                               ≡
                          ((f₁ ∘[ ℂop ] x₁) ∘[ ℂop ] f)
                      q2 = refl


                      q3 : ((f₁ ∘[ ℂop ] x₁) ∘[ ℂop ] f)
                               ≡
                           (f₁ ∘[ ℂop ] (x₁ ∘[ ℂop ] f))
                      q3 = ∘-assoc ℂop
                        --------------------


                      w0 : (f₁ ∘[ ℂop ] (x₁ ∘[ ℂop ] f))
                                ≡
                           (Functor.fmap (Rep B) f₁ (x₁ ∘[ ℂop ] f))
                      w0 = refl

                      w : (Functor.fmap (Rep B) f₁ (x₁ ∘[ ℂop ] f))
                               ≡
                          (comp Agda' (Functor.fmap (Rep B) f₁) (λ x₂ → comp ℂop x₂ f) x₁)
                      w = refl
                    in
                    trans q (trans q2 (trans q3 (trans w0 w)))
              }
    ; fmap-id′ = λ A → NatTrans-η (fun-ext λ x → fun-ext λ y → left-id ℂ)
    ; fmap-∘′ = λ A B C f g → NatTrans-η (fun-ext λ x → fun-ext λ y →
        let
          α : NatTrans (Rep B) (Rep C)
          α = (record
                    { component = λ x₁ x₂ → comp ℂop x₂ f
                    ; natural = λ x₁ y₁ f₁ → fun-ext (λ x₂ → trans (∘-assoc ℂop) refl)
                    })

          β : NatTrans (Rep A) (Rep B)
          β = (record
                    { component = λ x₁ x₂ → comp ℂop x₂ g
                    ; natural = λ x₁ y₁ f₁ → fun-ext (λ x₂ → trans (∘-assoc ℂop) refl)
                    })
          p : NatTrans.component
                (comp [ ℂop ,, Agda' ] α β) x y
                  ≡
              comp ℂop (comp ℂop y g) f
          p = refl

          q0 : ∀ {A′ B′ C′} {u : A′ ⇒[ ℂ ] B′} {v : B′ ⇒[ ℂ ] C′} → comp ℂop u v ≡ comp ℂ v u
          q0 = refl

          q : comp ℂ f  (comp ℂ g  y) ≡ comp ℂop y (comp ℂ f g)
          q = trans (sym (∘-assoc ℂ)) (sym q0)
        in
        trans p q)
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

よ-× : ∀ (A B : Category.Obj ℂop) →
  IsProduct [ ℂop ,, Agda' ] (actf よ A) (actf よ B) (actf (Product-Functor [ ℂop ,, Agda' ] {!!} {!!}) {!!})
よ-× = {!!}

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
