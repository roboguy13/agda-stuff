-- Category of Agda types and functions

open import CategoryRecord
open import Agda.Primitive

open import Level

open import Data.Sum
open import Data.Product
open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Relation.Nullary
open import Data.List.Relation.Unary.Any
open import Relation.Binary.Structures
-- open import Relation.Binary.PropositionalEquality
open import Algebra.Definitions

-- open ≡-Reasoning

-- Congruent : {A : Set} -> Rel A -> Set
-- Congruent {A} _R_ = (f : A -> A)(x y : A) -> x R y -> f x R f y

module Agda
  (ℓ : Level)
  (e : Level)
  (_≈ₒ_ : ∀ {m} {A : Set m} → A → A → Set m)
  (≈ₒ-equiv : ∀ {m} {A : Set m} → IsEquivalence {_} {m} {A} _≈ₒ_)
  (≈ₒ-cong : ∀ {m} {A B : Set m} → (f : A → B) →
               {x x′ : A} →
               x ≈ₒ x′ →
               f x ≈ₒ f x′)
  (≈ₒ-cong₂ : ∀ {m} {A B C : Set m} → (f : A → B → C) →
               {x x′ : A} → {y y′ : B} →
               x ≈ₒ x′ →
               y ≈ₒ y′ →
               f x y ≈ₒ f x′ y′)
  where

-- Congruence : ∀ {m} {A} → (A → A → Set m) → Set (lsuc m)
-- Congruence {m} _R_ =
--   ∀ {A B : Set m} → (f : A → B) →
--                {x x′ : A} →
--                x R x′ →
--                f x R f x′

-- Congruence₂ : ∀ {m} → (∀ {A : Set m} → A → A → Set m) → Set (lsuc m)
  -- Congruence₂ {m} _R_ =
  --   ∀ {A B C : Set m} → (f : A → B → C) →
  --                {x x′ : A} → {y y′ : B} →
--                x R x′ →
--                y R y′ →
--                f x y R f x′ y′

-- open IsEquivalence ≈-equiv

eqv-refl : ∀ {A : Set (lsuc ℓ)} {x : A} → x ≈ₒ x
eqv-refl = IsEquivalence.refl ≈ₒ-equiv

eqv-trans : ∀ {A : Set (lsuc ℓ)} {x y z : A} → x ≈ₒ y → y ≈ₒ z → x ≈ₒ z
eqv-trans = IsEquivalence.trans ≈ₒ-equiv

eqv-sym : ∀ {A : Set (lsuc ℓ)} {x y : A} → x ≈ₒ y → y ≈ₒ x
eqv-sym = IsEquivalence.sym ≈ₒ-equiv

-- _Agda-≈_ : ∀ {A B : Set} → (f g : Lift (lsuc ℓ) (A → B)) → Set (lsuc ℓ)
-- _Agda-≈_ = λ f g → (∀ x → Lift (lsuc ℓ) (lower f x ≈ lower g x))

Agda : Category (suc (suc ℓ)) (suc ℓ) (suc ℓ ⊔ e)
Agda = record
  { Obj = Set (lsuc ℓ)
  ; _⇒_ = λ A B → (A → B)
  ; _∘_ = λ f g → λ z → f (g z)
  -- -- ; _≈_ = λ f g → (∀ x → Lift (lsuc ℓ) (lift (lower f x) ≈ lift (lower g x)))
  ; _≈_ = λ f g → (∀ x → Lift e (f x ≈ₒ g x))
  -- -- ; _≈_ = _Agda-≈_
  ; equiv = λ {A} → record
      { refl = λ {f} x → lift eqv-refl
      ; sym = λ eqv x → lift (eqv-sym (lower (eqv x)))
      ; trans = λ eqv-1 eqv-2 a →
              (lift (eqv-trans (lower (eqv-1 a)) (lower (eqv-2 a))))
      }
  ; ∘-resp-≈ = λ {_} {_} {_} {f} {h} {g} {i} eqv-1 eqv-2 a → lift (eqv-trans (≈ₒ-cong₂ (λ _ → f) (lower (eqv-2 a)) (lower (eqv-2 a)))
                                                               (lower (eqv-1 (i a))))
  ; id = λ x → x
  ; left-id = λ x → lift eqv-refl
  ; right-id = λ x → lift eqv-refl
  ; ∘-assoc = λ x → lift eqv-refl
  }

open Category Agda
open CategoryProperties Agda

case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
case x of f = f x

⊤-lift-canon : (x : Lift (suc ℓ) ⊤) → x ≈ₒ lift tt
⊤-lift-canon (lift tt) = eqv-refl

⊤-IsTerminal : IsTerminal (Lift (lsuc ℓ) ⊤)
⊤-IsTerminal = λ A → (λ _ → lift tt) , (lift tt , (λ n x x₁ → lift (⊤-lift-canon (lift tt)))) --(λ _ → lift tt) , lift tt , (λ f x a → lift (⊤-lift-canon (lift tt)))

⊥-IsInitial : IsInitial (Lift (lsuc ℓ) ⊥)
⊥-IsInitial = λ B → (λ x → ⊥-elim (lower x)) , lift tt , (λ x x₁ ())

⊤-IsSeparator : IsSeparator (Lift (lsuc ℓ) ⊤)
⊤-IsSeparator = λ f x → (f (λ _ → x) (lift tt))

nondegen : Nondegenerate ⊤-IsTerminal ⊥-IsInitial
nondegen = λ z → lower (proj₁ z (lift tt)) -- lift λ z → lower (proj₁ z (lift tt))

×-canon : ∀ {m} {A B : Set m} {a×b : A × B} → a×b ≈ₒ (proj₁ a×b , proj₂ a×b)
×-canon {_} {_} {_} {fst , snd} = IsEquivalence.refl ≈ₒ-equiv

×-IsProduct : ∀ {A B} → IsProduct A B (A × B)
×-IsProduct {A} {B} =
  proj₁ , proj₂ , λ f g → (λ x → f x , g x) , (lift (λ x → lift eqv-refl) ,
    (λ x → lift eqv-refl)) , λ n (s , t) x →
      lift (≈ₒ-cong₂ (λ x₁ x₂ → x₁ , x₂) (eqv-sym (lower (lower s x))) (eqv-sym (lower (t x))))

⊎-match : ∀ {m} {A B X : Set m} (a+b : A ⊎ B) (f : A → X) (g : B → X) → X
⊎-match (inj₁ x) f g = f x
⊎-match (inj₂ y) f g = g y

⊎-canon : ∀ {A B : Set (lsuc ℓ)} (X : Set (lsuc ℓ)) (a+b : A ⊎ B) {f : A → X} {g : B → X} {h : A ⊎ B → X} →
  (∀ a → f a ≈ₒ h (inj₁ a)) →
  (∀ b → g b ≈ₒ h (inj₂ b)) →
  h a+b ≈ₒ ⊎-match a+b f g
⊎-canon _ (inj₁ x) prf-1 prf-2 = eqv-sym (prf-1 x)
⊎-canon _ (inj₂ y) prf-1 prf-2 = eqv-sym (prf-2 y)

⊎-IsCoproduct : ∀ {A B} → IsCoproduct A B (A ⊎ B)
⊎-IsCoproduct {A} {B} =
  inj₁ , inj₂ , λ {X} f g → (λ x → ⊎-match x (f) (g)) , (lift (λ x → lift eqv-refl) , (λ x → lift eqv-refl)) ,
    λ n (p , q) a+b → lift (⊎-canon X a+b {f} {g} {n} (λ a → lower (lower p a)) λ b → lower (q b))

→true : Lift (lsuc ℓ) ⊤ ⇒ Lift (lsuc ℓ) Bool
→true = λ tt → lift true

→false : Lift (lsuc ℓ) ⊤ ⇒ Lift (lsuc ℓ) Bool
→false = λ tt → lift false

Agda-nondegen : Nondegenerate ⊤-IsTerminal ⊥-IsInitial
Agda-nondegen = λ z → lower (proj₁ z (lift tt)) -- lift (λ x → lower (proj₁ x (lift tt)))

-- Bool-IsCoseparator : IsCoseparator Bool
-- Bool-IsCoseparator {T} {A} {a₀} {a₁} f x =
--   let
--     z = ⊤-IsSeparator (λ x₁ x₂ → {!!}) A
--   in
--   {!!}
