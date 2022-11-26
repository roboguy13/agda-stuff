open import Category
open import FunctorDefs
open import FunctorProperties
import ElementaryProperties
open import Yoneda
open import Agda
open import AgdaHom

open import Level renaming (suc to lsuc)

open import Data.Nat
open import Data.Fin hiding (lift)
open import Data.Empty
open import Data.Unit
open import Data.Product

open import Relation.Binary.PropositionalEquality hiding (Extensionality)

open import Axiom.UniquenessOfIdentityProofs.WithK

module Limits
  where

Fin-Cat : (n : ℕ) → Category Level.zero Level.zero
Fin-Cat n =
  record
    { Obj = Fin n
    ; _⇒_ = λ A B → A ≡ B
    ; _∘_ = λ f g → trans g f
    ; id = refl
    ; left-id = λ {A} {B} {f} → uip (trans f refl) f
    ; right-id = refl -- TODO: Why the asymmetry here?
    ; ∘-assoc = λ {A} {B} {C} {D} {f} {g} {h} → uip (trans h (trans g f)) (trans (trans h g) f)
    }

Cone : ∀ {o₁ ℓ₁ o₂ ℓ₂} {ℂ : Category o₁ ℓ₁} {𝔻 : Category o₂ ℓ₂} →
  (F : Functor ℂ 𝔻) →
  (c : Category.Obj 𝔻) →
  Set (Level.suc o₁ Level.⊔ Level.suc ℓ₁ Level.⊔ Level.suc o₂ Level.⊔ Level.suc ℓ₂)
Cone F c =
  NatTrans (Const-Functor c) F

ACone : ∀ {o₁ ℓ₁ o₂ ℓ₂} {ℂ : Category o₁ ℓ₁} {𝔻 : Category o₂ ℓ₂} →
  (F : Functor ℂ 𝔻) →
  Set (Level.suc o₁ Level.⊔ Level.suc ℓ₁ Level.⊔ Level.suc o₂ Level.⊔
         Level.suc ℓ₂)
ACone F = ∃[ c ] (Cone F c)

Is-Universal-Cone : ∀ {o₁ ℓ₁ o₂ ℓ₂} {ℂ : Category o₁ ℓ₁} {𝔻 : Category o₂ ℓ₂} →
  (F : Functor ℂ 𝔻) →
  (c : Category.Obj 𝔻) →
  Cone F c →
  Set (lsuc o₁ Level.⊔ lsuc ℓ₁ Level.⊔ lsuc o₂ Level.⊔ lsuc ℓ₂)
Is-Universal-Cone {_} {_} {_} {_} {ℂ} {𝔻} F c cone =
  ∀ c′ (cone′ : Cone F c′) →
  Σ (c′ ⇒[ 𝔻 ] c) λ m →
  ∀ (A : Category.Obj 𝔻) (f : c ⇒[ 𝔻 ] A) (g : c′ ⇒[ 𝔻 ] A) →
  g ≡ (f ∘[ 𝔻 ] m)

Lim : ∀ {o₁ ℓ₁ o₂ ℓ₂} {ℂ : Category o₁ ℓ₁} {𝔻 : Category o₂ ℓ₂} →
  (F : Functor ℂ 𝔻) →
  Set (lsuc o₁ Level.⊔ lsuc ℓ₁ Level.⊔ lsuc o₂ Level.⊔ lsuc ℓ₂)
Lim F = ∃[ c ] ∃[ cone ] (Is-Universal-Cone F c cone)

-- Point : ∀ {o ℓ o₂ ℓ₂} {𝔻 : Category o ℓ} →
--   Functor 𝔻 (Agda {o₂} {ℓ₂})
-- Point {_} {_} {o₂} = Const-Functor (Lift o₂ ⊤)

-- -- Hom_C(c, F(-))
-- Hom-left : ∀ {o₁ ℓ₁ o₂ ℓ₂} {ℂ : Category o₁ ℓ₁} {𝔻 : Category o₂ ℓ₂} →
--   (A : Category.Obj (Op ℂ)) →
--   (F : Functor (Op 𝔻) ℂ) →
--   Functor (Op 𝔻) (Agda {ℓ₁} {ℓ₂})
-- Hom-left {_} {_} {_} {_} {ℂ} {𝔻} c F =
--   record
--     { act = λ x → (c ⇒[ ℂ ] (actf F x))
--     ; fmap′ = λ A B f → lift λ t → Functor.fmap F f ∘[ ℂ ] t
--     ; fmap-id′ = λ A → {!!}
--     ; fmap-∘′ = λ A B C f g → {!!}
--     }

-- -- Called "lîm" on nlab
-- PreLim : ∀ {o₁ ℓ₁ o₂ ℓ₂} {I : Category o₁ ℓ₁} {ℂ : Category o₂ ℓ₂} →
--   (F : Functor (Op I) ℂ) →
--   Category.Obj ℂ →
--   Set (lsuc o₁ Level.⊔ lsuc ℓ₁ Level.⊔ lsuc (lsuc ℓ₂))
-- PreLim {_} {_} {_} {_} {I} {ℂ} F c =
--   Hom [ Op I ,, Agda ] Point (Hom-left c F)

-- PreLim-Functor : ∀ {o₁ ℓ₁ o₂ ℓ₂} {I : Category o₁ ℓ₁} {ℂ : Category o₂ ℓ₂} →
--   (F : Functor (Op I) ℂ) →
--   Functor ℂ Agda
-- PreLim-Functor = {!!}

-- Is-Lim : ∀ {o₁ ℓ₁ o₂ ℓ₂} {I : Category o₁ ℓ₁} {ℂ : Category o₂ ℓ₂} →
--   {F : Functor (Op I) ℂ} →
--   {c : Category.Obj ℂ} →
--   (limF : PreLim F c) →
--   Set {!!}
-- Is-Lim {_} {_} {_} {_} {I} {ℂ} {F} {c} limF =
--   {!!}
--   -- Σ (NatIso (Hom ? c ?) ?) ?

-- -- Lim : ∀ {o₁ ℓ₁ o₂ ℓ₂} {ℂ : Category o₁ ℓ₁} {𝔻 : Category o₂ ℓ₂} →
-- --   Functor ℂ 𝔻 →
-- --   Set {!!}
-- -- Lim {_} {_} {_} {_} {ℂ} {𝔻} F =
-- --   ∃[ c ]
-- --   Σ (Cone F c) λ cone →
-- --   ∀ c′ (cone′ : Cone F c′) →
-- --   Σ![ c′ ⇒[ 𝔻 ] c ] (Is-NatIso ? ? cone)

-- -- HasLimit : ∀ {o₁ ℓ₁ o₂ ℓ₂} {J : Category o₁ ℓ₁} {ℂ : Category o₂ ℓ₂} →
-- --   (Lim-D : Cone F )

-- -- Cone-Cat : ∀ {o₁ ℓ₁ o₂ ℓ₂} {ℂ : Category o₁ ℓ₁} {𝔻 : Category o₂ ℓ₂} →
-- --   Functor (Op ℂ) 𝔻 →
-- --   Category.Obj 𝔻 →
-- --   Category {!!} {!!}
-- -- Cone-Cat {_} {_} {_} {_} {ℂ} {𝔻} F c =
-- --   record
-- --     { Obj = Cone F c
-- --     ; _⇒_ = λ A B → {!!}
-- --     ; _∘_ = {!!}
-- --     ; id = {!!}
-- --     ; left-id = {!!}
-- --     ; right-id = {!!}
-- --     ; ∘-assoc = {!!}
-- --     }

