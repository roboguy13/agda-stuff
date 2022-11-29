
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

open import Data.Product

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

Agda-lift : ∀ {ℓ} {𝔻 : Category (lsuc ℓ) ℓ} {A B X Y} →
  (F : Functor 𝔻 (Agda {ℓ} {ℓ})) →
  actf F X →
  ((A ⇒[ 𝔻 ] B) → (actf F X ⇒[ Agda {ℓ} {ℓ} ] actf F Y)) →
  (Lift ℓ (A ⇒[ 𝔻 ] B) ⇒[ Agda {ℓ} {ℓ} ] actf F Y)
Agda-lift F F-x f = lift (λ z → lower (f (lower z)) F-x)

-- Agda-lift-NatTrans : ∀ {ℓ} {𝔻 : Category (lsuc ℓ) ℓ} →
--   (F G : Functor 𝔻 (Agda {ℓ} {ℓ})) →
--   NatTrans {!!} {!!}
-- Agda-lift-NatTrans F G =
--   record { component = λ x → Agda-lift F {!!} (Functor.fmap F) ; natural = {!!} }
--   -- Agda-lift F c (Functor.fmap F) ∘[ Agda ] Functor.fmap G
--   --   ≡
--   -- Functor.fmap F ∘[ Agda ] Agda-lift F

よ-NatTrans : ∀ {X : Functor (Op ℂ) Agda} →
  ∀ {c} →
  actf X c →
  NatTrans (actf よ c) X
よ-NatTrans {X} {c} X-c =
  record
    { component = λ y →
                lift (λ z → lower (Functor.fmap X (lower z)) X-c)
    ; natural = λ x y f →
      cong lift (fun-ext λ z →
        let
          q : lower (Functor.fmap X f) (lower (Functor.fmap X (lower z)) X-c)
                ≡
              lower ((Functor.fmap X f) ∘[ Agda ] (Functor.fmap X (lower z))) X-c
          q = refl

          q2 : lower ((Functor.fmap X f) ∘[ Agda ] (Functor.fmap X (lower z))) X-c
                ≡
               lower (Functor.fmap X (f ∘[ ℂop ] lower z)) X-c
          q2 = cong₂ lower (Functor.fmap-∘ X) refl
        in
        trans (trans refl (sym q2)) (sym q))
    }

module _ where
  open import ElementaryProperties (Agda {suc (suc ℓ)} {ℓ})

  open import AgdaHom ([ Op ℂ ,, Agda' ])

  よ-fmap-id : ∀ {c c′ : Obj ℂop} {f : c ⇒[ ℂop ] c′} →
    lower (Functor.fmap (actf よ c) f) (lift (id ℂop)) ≡ lift f
  よ-fmap-id {c} {c′} {f} =
    let
      p : (Functor.fmap (actf よ c) f)
            ≡
          (Functor.fmap (Rep c) f)
      p = refl

      p2 : Functor.fmap (Rep c) f ≡ (lift λ t → lift (f ∘[ ℂop ] lower t))
      p2 = refl
    in
    trans (cong₂ lower (trans p p2) refl) (cong lift (Category.right-id ℂop))

  Yoneda-lemma : ∀ {X : Functor (Op ℂ) Agda} →
    ∀ {c : Category.Obj ℂ} →
      let
        lifted = Lift (suc (suc ℓ))
      in
        (Hom (actf よ c) X)
          ≅
        (lifted (actf X c))
  Yoneda-lemma {X} {c} =
    lift (λ x →
      let
        hc = NatTrans.component x c
        q = lower hc (lift (Category.id ℂop))
      in lift q) ,

    lift (λ x →
      let
        w = lower (Functor.fmap X (Category.id ℂop)) (lower x)
      in
      よ-NatTrans w) ,

    cong lift (fun-ext λ z →
      let
        p : よ-NatTrans {X} {c}
              (lower (Functor.fmap X (id ℂop))
                (lower (NatTrans.component z c) (lift (id ℂop))))
              ≡
            よ-NatTrans
              (lower (Functor.fmap X (id ℂop) ∘[ Agda ] NatTrans.component z c) (lift (id ℂop)))
        p = refl

        p2 : よ-NatTrans {X} {c}
              (lower (Functor.fmap X (id ℂop) ∘[ Agda ] NatTrans.component z c) (lift (id ℂop)))
               ≡
             よ-NatTrans
              (lower ((NatTrans.component z c) ∘[ Agda ] (Functor.fmap (actf よ c) (id ℂop))) (lift (id ℂop)))
        p2 = cong よ-NatTrans (cong₂ lower (sym (NatTrans.natural z c c (id ℂop))) refl)

        p3′ : (NatTrans.component z c) ∘[ Agda ] (Functor.fmap (actf よ c) (id ℂop))
                ≡ NatTrans.component z c ∘[ Agda ] Category.id Agda
        p3′ = cong (λ w → NatTrans.component z c ∘[ Agda ] w) (Functor.fmap-id (actf よ c))

        p3′′ : (NatTrans.component z c) ∘[ Agda ] (Functor.fmap (actf よ c) (id ℂop))
                ≡ NatTrans.component z c
        p3′′ = trans p3′ (Category.right-id Agda)

        p3 : よ-NatTrans {X} {c}
              (lower ((NatTrans.component z c) ∘[ Agda ] (Functor.fmap (actf よ c) (id ℂop))) (lift (id ℂop)))
               ≡
             よ-NatTrans (lower (NatTrans.component z c) (lift (id ℂop)))
        p3 = cong よ-NatTrans (cong₂ lower p3′′ refl)

        p4 : よ-NatTrans (lower (NatTrans.component z c) (lift (id ℂop)))
               ≡ z
        p4 = NatTrans-η (fun-ext λ x → cong lift (fun-ext λ x₁ →
          let
            q : lower (Functor.fmap X (lower x₁)) (lower (NatTrans.component z c) (lift (id ℂop)))
                  ≡
                lower (Functor.fmap X (lower x₁) ∘[ Agda ] NatTrans.component z c) (lift (id ℂop))
            q = refl

            q2 : lower (Functor.fmap X (lower x₁) ∘[ Agda ] NatTrans.component z c) (lift (id ℂop))
                   ≡
                 lower (NatTrans.component z x ∘[ Agda ] Functor.fmap (actf よ c) (lower x₁)) (lift (id ℂop))
            q2 = cong₂ lower (sym (NatTrans.natural z c x (lower x₁))) refl

            q3 : lower (NatTrans.component z x ∘[ Agda ] Functor.fmap (actf よ c) (lower x₁)) (lift (id ℂop))
                    ≡
                  lower (NatTrans.component z x) (lower (Functor.fmap (actf よ c) (lower x₁)) (lift (id ℂop)))
            q3 = refl

            q4 : lower (NatTrans.component z x) (lower (Functor.fmap (actf よ c) (lower x₁)) (lift (id ℂop)))
                     ≡
                   lower (NatTrans.component z x) x₁
            q4 = cong₂ lower {NatTrans.component z x} refl (よ-fmap-id {c} {x} {lower x₁})
          in
          trans q (trans q2 (trans q3 q4))))

        q5 : ∀ {z} → lower (Functor.fmap X {c} (id ℂop)) z ≡ z
        q5 = trans (cong₂ lower (Functor.fmap-id X) refl) refl

        p5 : よ-NatTrans {X} (lower (Functor.fmap X (id ℂop)) (lower (NatTrans.component z c) (lift (id ℂop))))
               ≡
             よ-NatTrans     (lower (NatTrans.component z c) (lift (id ℂop)))
        p5 = cong よ-NatTrans q5
      in
      trans p5 p4) ,

    cong lift (fun-ext λ z →
      let
        q5 : ∀ {z} → lower (Functor.fmap X {c} (id ℂop)) z ≡ z
        q5 = trans (cong₂ lower (Functor.fmap-id X) refl) refl
      in
      trans (cong lift q5) (cong lift q5))
