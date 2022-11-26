open import Category
open import FunctorDefs
open import FunctorProperties
import ElementaryProperties
open import Yoneda
open import Agda

open import Level

open import Data.Nat
open import Data.Fin
open import Data.Empty
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

-- Called "lîm" on nlab
PreLim : ∀ {o₁ ℓ₁ o₂ ℓ₂} {I : Category o₁ ℓ₁} {ℂ : Category o₂ ℓ₂} →
  (F : Functor (Op I) ℂ) →
  Set {!!}
PreLim F = {!!}

-- Lim : ∀ {o₁ ℓ₁ o₂ ℓ₂} {ℂ : Category o₁ ℓ₁} {𝔻 : Category o₂ ℓ₂} →
--   Functor ℂ 𝔻 →
--   Set {!!}
-- Lim {_} {_} {_} {_} {ℂ} {𝔻} F =
--   ∃[ c ]
--   Σ (Cone F c) λ cone →
--   ∀ c′ (cone′ : Cone F c′) →
--   Σ![ c′ ⇒[ 𝔻 ] c ] (Is-NatIso ? ? cone)

-- HasLimit : ∀ {o₁ ℓ₁ o₂ ℓ₂} {J : Category o₁ ℓ₁} {ℂ : Category o₂ ℓ₂} →
--   (Lim-D : Cone F )

-- Cone-Cat : ∀ {o₁ ℓ₁ o₂ ℓ₂} {ℂ : Category o₁ ℓ₁} {𝔻 : Category o₂ ℓ₂} →
--   Functor (Op ℂ) 𝔻 →
--   Category.Obj 𝔻 →
--   Category {!!} {!!}
-- Cone-Cat {_} {_} {_} {_} {ℂ} {𝔻} F c =
--   record
--     { Obj = Cone F c
--     ; _⇒_ = λ A B → {!!}
--     ; _∘_ = {!!}
--     ; id = {!!}
--     ; left-id = {!!}
--     ; right-id = {!!}
--     ; ∘-assoc = {!!}
--     }

