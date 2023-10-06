-- See https://well-typed.com/blog/2015/05/parametricity/

open import Syntax

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Product

module Parametricity where

data Is-Const-Type {V} : Type V → Set where
  Unit-Const : Is-Const-Type Unit
  Pair-Const : ∀ {A B} →
    Is-Const-Type A →
    Is-Const-Type B →
    Is-Const-Type (Pair A B)
  Sum-Const : ∀ {A B} →
    Is-Const-Type A →
    Is-Const-Type B →
    Is-Const-Type (Sum A B)
  -- ⇒-Const : ∀ {A B} →
  --   Is-Const-Type A →
  --   Is-Const-Type B →
  --   Is-Const-Type (A ⇒ B)

_𝓡[_]_ : ∀ {V} → Term V → Type V → Term V → Set
_𝓡[_]_ x Unit x′ = x ≡ x′
_𝓡[_]_ f (A ⇒ B) f′ =
  ∀ x x′ fx fx′ →
      x 𝓡[ A ] x′ →
      f ∙ x ⇓ fx →
      f ∙ x′ ⇓ fx′ →
      fx 𝓡[ B ] fx′
_𝓡[_]_ x (Pair A B) x′ =
  (fst x 𝓡[ A ] fst x′)
    ×
  (snd x 𝓡[ B ] snd x′)
-- _𝓡[_]_ x (Sum A B) x′ =

fundamental-thm : ∀ {V} {t : Term V} {A} →
  ∅ ⊢ t ⦂ A →
  t 𝓡[ A ] t
fundamental-thm = {!!}

-- data _𝓡[_]_ {V} : Term V → Type V → Term V → Set where
--   𝓡-const : ∀ {x x′ A} →
--     Is-Const-Type A →
--     x ≡ x′ →
--     x 𝓡[ A ] x′

--   𝓡-⇒ : ∀ {f f′ A B} →
--     (∀ x x′ →
--       x 𝓡[ A ] x′ →
--       (f ∙ x) 𝓡[ B ] (f ∙ x′)) →
--     f 𝓡[ A ⇒ B ] f′
