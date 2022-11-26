
open import Category
open import CategoryRecord hiding (o)
open import Agda
open import Level
open import Agda.Primitive

open import Relation.Binary.PropositionalEquality hiding (Extensionality)
open import Relation.Binary.Structures

open import Axiom.Extensionality.Propositional

open CatBasics
open Category.Category

module Yoneda
  (ℓ : Level)
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

-- よ : (A : Category.Obj ℂop) → Functor ℂop (Agda ℓ ℓ ℓ)
-- よ A = record
--   { act = λ X → (A ⇒[ ℂop ] X)
--   ; fmap = λ f → λ t → (f ∘[ ℂop ] t)
--   ; fmap-id = λ {_} → lift (fun-ext ℓ ℓ ℓ λ x → Eq-Category.right-id ℂ)
--   ; fmap-∘ = lift (fun-ext ℓ ℓ ℓ (λ x → Eq-Category.∘-assoc ℂ))
--   }

-- open Category.Category ℂop
open CategoryProperties
open import Data.Product

-- p : Functor ? ?
-- p A B = 

Agda-Product : ∀ (A B : Category.Obj ℂop) → Functor ℂ ([ ℂop ,, Agda ] ×cat [ ℂop ,, Agda ])
-- Agda-Product A B = (Product-Functor {_} {_} {Agda'} _×_ ×-IsProduct)
-- Agda-Product A B = ((Functor-⊗ (actf よ A) (actf よ B)))
-- Agda-Product A B = ((Product-Functor {_} {_} {Agda'} _×_ ×-IsProduct ∘F Functor-⊗ (actf よ A) (actf よ B)) ∘F {!!}) --(FΔ ∘F {!!}))
-- Agda-Product A B = ((Product-Functor {_} {_} {{!!}} _×_ ×-IsProduct ∘F Functor-⊗ (Rep A) (Rep B)) ∘F Functor-⊗ {!!} {!!}) --(FΔ ∘F {!!}))
Agda-Product A B = Functor-⊗ よ よ ∘F FΔ

Agda-Product′ : ∀ (A B : Category.Obj ℂop) → Functor {!!} {!!}
Agda-Product′ A B = Product-Functor {_} {_} {[ {!!} ,, {!!} ]} (Functor-⊗′ _×_ ×-IsProduct) {!!} ∘F {!!}


-- よ-× : ∀ (A B : Category.Obj ℂop) →
--   -- IsProduct [ ℂop ,, Agda' ] (actf よ A) (actf よ B) (actf (Product-Functor [ ℂop ,, Agda' ] {!!} {!!}) {!!})
--   IsProduct [ ℂop ,, Agda' ] (actf よ A) (actf よ B) 
-- よ-× A B =
--   let
--     p = ?
--   in
--   {!!}

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
