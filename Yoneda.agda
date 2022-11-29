
open import Category
import ElementaryProperties
open import FunctorDefs
open import Agda
open import FunctorProperties

open import Level
open import Agda.Primitive

open import Relation.Binary.PropositionalEquality hiding (Extensionality)
open import Relation.Binary.Structures

open import Axiom.Extensionality.Propositional

open CatBasics
open Category.Category

module Yoneda
  {ℓ : Level}
  (ℂ : Category (suc ℓ) (ℓ))
  where

Agda' : Category (suc ℓ) ℓ
Agda' = Agda {ℓ} {ℓ}

ℂop : Category (suc ℓ) ℓ
ℂop = Op ℂ

Rep : (A : Category.Obj ℂop) → Functor ℂop Agda'
Rep A =
  record
  { act = λ X → Lift ℓ (A ⇒[ ℂop ] X)
  ; fmap′ = λ _ _ f → lift λ t → lift (f ∘[ ℂop ] lower t)
  ; fmap-id′ = λ _ → cong lift (fun-ext λ x → cong lift (Category.right-id ℂ))
  ; fmap-∘′ = λ _ _ _ _ _ → cong lift (fun-ext (λ x → cong lift (Category.∘-assoc ℂ)))
  }

-- Corep : (A : Category.Obj ℂ) → Functor ℂ Agda'
-- Corep A =
--   record
--   { act = λ X → (X ⇒[ ℂ ] A)
--   ; fmap′ = λ B C f → λ t → ({!!} ∘[ ℂ ] {!!})
--   ; fmap-id′ = λ _ → (fun-ext λ x → Category.right-id ℂ)
--   ; fmap-∘′ = λ _ _ _ _ _ → (fun-ext (λ x → (Category.∘-assoc ℂ)))
--   }


lower-Arr : ∀ {A B} →
  (Lift ℓ A ⇒[ Agda' ] Lift ℓ B) →
  (A ⇒[ Agda' ] B)
lower-Arr f = lift λ x → lower (lower f (lift x))

_∘[A]_ : ∀ {A B C} →
  (Lift ℓ B ⇒[ Agda' ] Lift ℓ C) →
  (Lift ℓ A ⇒[ Agda' ] Lift ℓ B) →
  (A ⇒[ Agda' ] C)
_∘[A]_ f g = (lower-Arr f ∘[ Agda' ] lower-Arr g)

Rep-fmap : ∀ {A B} → (Z : Category.Obj ℂop) → (A ⇒[ ℂop ] B) → Functor.act (Rep Z) A → (Z ⇒[ ℂop ] B)
Rep-fmap Z f = λ x → lower (lower (Functor.fmap (Rep Z) f) x)

-- Rep⁻¹ : Functor ℂop Agda' → Category.Obj ℂop
-- Rep⁻¹ F =
--   let
--     p = Functor.fmap F (Category.id {!!})
--   in
--   {!!}

よ : Functor ℂ [ ℂop ,, Agda ]
よ =
  record
    { act = λ x → Rep x
    ; fmap′ = λ A B f →
            record
              { component = λ x → lift λ x₁ → lift (lower x₁ ∘[ ℂop ] f)
              ; natural = λ x y f₁ →
                        cong lift
                  (fun-ext λ x₁ →
                    let
                      -- rep-fmap = 
                  --     q : comp Agda' (λ x₂ → comp ℂop x₂ f) (Functor.fmap (Rep A) f₁) x₁
                      q : lower ((comp Agda' (lift (λ x₂ → comp ℂop x₂ f))) (lower-Arr (Functor.fmap (Rep A) f₁))) (lower x₁)
                               ≡
                          -- (lower (lower (Functor.fmap (Rep A) f₁) x₁) ∘[ ℂop ] f)
                          (Rep-fmap A f₁ x₁ ∘[ ℂop ] f)
                      q = refl

                      q2 : (Rep-fmap A f₁ x₁ ∘[ ℂop ] f)
                               ≡
                          ((f₁ ∘[ ℂop ] lower x₁) ∘[ ℂop ] f)
                      q2 = refl


                      q3 : ((f₁ ∘[ ℂop ] lower x₁) ∘[ ℂop ] f)
                               ≡
                           (f₁ ∘[ ℂop ] (lower x₁ ∘[ ℂop ] f))
                      q3 = ∘-assoc ℂop
                        --------------------


                      w0 : (f₁ ∘[ ℂop ] (lower x₁ ∘[ ℂop ] f))
                                ≡
                           (Rep-fmap B f₁ (lift (lower x₁ ∘[ ℂop ] f)))
                           -- (Rep-fmap B f₁ (lower {!!}))
                      w0 = refl

                      w : (Rep-fmap B f₁ (lift (lower x₁ ∘[ ℂop ] f)))
                               ≡
                          lower (lower (comp Agda' (Functor.fmap (Rep B) f₁) (lift (λ x₂ → lift (comp ℂop x₂ f)))) (lower x₁))
                      w = refl
                    in
                    -- {!!}
                    trans (cong lift q) (trans (cong lift q2) (trans (cong lift q3) (trans (cong lift w0) (cong lift w))))
                    )
              }
    ; fmap-id′ = λ A → NatTrans-η (fun-ext λ x → cong lift (fun-ext λ y → cong lift (left-id ℂ)))
    -- ; fmap-id′ = λ A → NatTrans-η (fun-ext λ x → fun-ext λ y → left-id ℂ)
    ; fmap-∘′ = λ A B C f g → NatTrans-η (fun-ext λ x → cong lift (fun-ext λ y →
        let
          α : NatTrans (Rep B) (Rep C)
          α = (record
                    { component = λ x₁ → lift λ x₂ → lift (comp ℂop (lower x₂) f)
                    ; natural = λ x₁ y₁ f₁ → cong lift (fun-ext (λ x₂ → trans (cong lift (∘-assoc ℂop)) refl))
                    })

          β : NatTrans (Rep A) (Rep B)
          β = (record
                    { component = λ x₁ → lift λ x₂ → lift (comp ℂop (lower x₂) g)
                    ; natural = λ x₁ y₁ f₁ → cong lift (fun-ext (λ x₂ → trans (cong lift (∘-assoc ℂop)) refl))
                    })
          p : lower (NatTrans.component
                (comp [ ℂop ,, Agda' ] α β) x) y
                  ≡
              lift (comp ℂop (comp ℂop (lower y) g) f)
          p = refl

          q0 : ∀ {A′ B′ C′} {u : A′ ⇒[ ℂ ] B′} {v : B′ ⇒[ ℂ ] C′} → comp ℂop u v ≡ comp ℂ v u
          q0 = refl

          q : comp ℂ f  (comp ℂ g  (lower y)) ≡ comp ℂop (lower y) (comp ℂ f g)
          q = trans (sym (∘-assoc ℂ)) (sym q0)
        in
        trans p (cong lift q)))
    }

