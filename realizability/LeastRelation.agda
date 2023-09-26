open import Agda.Primitive
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contraposition)

module LeastRelation
  where

-- record LeastRel {ℓ} {m} {A : Set ℓ} (R : A → A → Set m) {P : (A → A → Set m) → Set m} (pr-prf : P R) : Set (ℓ ⊔ lsuc m) where
--   field
--     prf : ∀ (R′ : A → A → Set m) →
--           P R′ →
--           ∀ a b → R a b → R′ a b

Rel≤ : ∀ {ℓ m} {A : Set (lsuc ℓ)} (R : A → A → Set (lsuc m)) {P : (A → A → Set (lsuc m)) → Set (lsuc m)} → P R → (R′ : A → A → Set (lsuc m)) → P R′ → Set (lsuc ℓ ⊔ lsuc m)
Rel≤ {_} {m} {A} R {P} R-prf R′ R′-prf =
  ∀ a b → R a b → R′ a b

-- LeastRel : ∀ {A : Set} (R : A → A → Set) {P : (A → A → Set) → Set} → P R → Set (lsuc lzero)
-- LeastRel {A} R {P} prf =
LeastRel : ∀ {ℓ m} {A : Set ℓ} (R : A → A → Set m) {P : (A → A → Set m) → Set m} → P R → Set (ℓ ⊔ lsuc m)
LeastRel {_} {m} {A} R {P} prf =
  ∀ (R′ : A → A → Set m) →
  P R′ →
  ∀ a b → R a b → R′ a b

LeastRel-fewest-preds :
  ∀ {ℓ m} {A : Set ℓ} (R : A → A → Set m) {P : (A → A → Set m) → Set m} → (PR : P R) →
  LeastRel {ℓ} {m} {A} R {P} PR →
  (R-1 : A → A → Set m) →
  P R-1 →
  ∀ a b →
  ¬ R-1 a b →
  ¬ R a b
LeastRel-fewest-preds R {P} PR R-least R-1 PR-1 a b =
  contraposition (R-least R-1 PR-1 a b)
