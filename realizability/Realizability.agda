open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Agda.Primitive
open import Level

open import LeastRelation

module Realizability
  (A : Set)
  (_·_ : A → A → A)
  (_↓_ : A → A → Set)
  (let ↓-refl′ : ∀ (R : A → A → Set) → Set; ↓-refl′ R = ∀ {a} → R a a)
  (let ↓-app′ : ∀ (R : A → A → Set) → Set; ↓-app′ R = ∀ {t s a b c} → R (t · s) a → (R t b) × (R s c) × ((b · c) ≡ a))
  (let app-↓′ : ∀ (R : A → A → Set) → Set; app-↓′ R = ∀ {t s a b c} → (R t b) → (R s c) → ((b · c) ≡ a) → R (t · s) a)

  (↓-refl : ↓-refl′ _↓_)
  (↓-app : ↓-app′ _↓_)
  (app-↓ : app-↓′ _↓_)

  (let ↓-like : ∀ (R : A → A → Set) → Set; ↓-like R = ↓-refl′ R × ↓-app′ R × app-↓′ R)

  (↓-least′ : LeastRel _↓_ {↓-like} (↓-refl , ↓-app , app-↓))
  where

-- data _↓_ : A → A → Set where
--   ↓-refl : ∀ {a} → a ↓ a
--   ↓-app : ∀ {t s a b c} → (t ↓ b) → (s ↓ c) → ((b · c) ≡ a) → (t · s) ↓ a


-- app-↓′ : ∀ {t s u a b c} → u ≡ (t · s) → u ↓ a → (t ↓ b) × (s ↓ c) × ((b · c) ≡ a)
-- app-↓′ eq ↓-refl = {!!} , {!!} , {!!}
-- app-↓′ eq (↓-app prf prf₁ x) = {!!} , {!!} , {!!}

_↓ : ∀ t → Set
t ↓ = ∃[ a ] (t ↓ a)

↓-deterministic : ∀ {t a b} →
  t ↓ a →
  t ↓ b →
  a ≡ b
↓-deterministic {t} {a} {b} prf-a prf-b =
  let z = app-↓ prf-a prf-b {!!}
      w-1 , w-2 , w-3 = ↓-app {_} {_} {_} {a} {b} z
  in
  {!!}

-- ↓-deterministic : ∀ {t a b} →
--   t ↓ a →
--   t ↓ b →
--   a ≡ b
-- ↓-deterministic {t} {a} {b} prf-a prf-b =
--   let z = app-↓ prf-a prf-b {!!}
--       w-1 , w-2 , w-3 = ↓-app {_} {_} {_} {a} {b} z
--   in
--   {!!}
