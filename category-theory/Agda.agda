-- Category of Agda types and functions

-- {-# OPTIONS --cumulativity #-}

open import Category
import ElementaryProperties
open import FunctorDefs
open import Agda.Primitive

open import Level

open import Data.Sum
open import Data.Product
open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Relation.Nullary
open import Data.List.Relation.Unary.Any
-- open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding (Extensionality)
open import Algebra.Definitions
-- open import Function.Equality hiding

-- open Setoid

-- open ≡-Reasoning

-- Congruent : {A : Set} -> Rel A -> Set
-- Congruent {A} _R_ = (f : A -> A)(x y : A) -> x R y -> f x R f y

module Agda
  {o ℓ : Level}
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
-- _Agda-≈_ : ∀ {A B : Set} → (f g : Lift (lsuc ℓ) (A → B)) → Set (lsuc ℓ)
-- _Agda-≈_ = λ f g → (∀ x → Lift (lsuc ℓ) (lower f x ≈ lower g x))

-- Agda : Set (suc o) → Category (suc o) o (o ⊔ e)
Agda : Category (suc o) (o ⊔ ℓ)
Agda = record
  { Obj = Set o
  ; _⇒_ = λ A B → Lift ℓ (A → B)
  ; _∘′_ = λ _ _ _ f g → lift (λ z → lower f (lower g z))
  ; id′ = λ _ → lift λ x → x
  ; left-id = refl
  ; right-id = refl
  ; ∘-assoc = refl
  }


-- Hom-Initial : {ℂ : Category e (suc ℓ) e} →
--   {𝟘 : Category.Obj ℂ} → CategoryProperties.IsInitial ℂ 𝟘 →
--   ∀ {A B} →
--   (f : Hom {ℂ} A 𝟘) →
--   (g : Hom {ℂ} A B)


-- ¬Hom𝟘 : ∀ {ℂ : Category e (suc ℓ) e} →
--   {𝟘 : Category.Obj ℂ} → CategoryProperties.IsInitial ℂ 𝟘 →
--   ∀ {A} →
--   ¬ (Hom {ℂ} A 𝟘)
-- ¬Hom𝟘 {ℂ} {𝟘} 𝟘-initial {A} prf = {!!}



open Category.Category Agda
open ElementaryProperties Agda

-- open import Axiom.Extensionality.Propositional

-- postulate fun-ext : ∀ {m n} → Extensionality m n

⊤-lift-canon : ∀ {A : Set o} → (x : Lift ℓ (A → Lift o ⊤)) → x ≡ (lift (λ _ → lift tt))
⊤-lift-canon f = cong (λ z → lift z) (fun-ext λ x → refl)
-- ⊤-lift-canon (lift tt) = refl

⊤-IsTerminal : IsTerminal (Lift o ⊤)
⊤-IsTerminal = λ A → lift (λ _ → lift tt) , (tt , (λ n x → ⊤-lift-canon n))

⊥-IsInitial : IsInitial (Lift o ⊥)
⊥-IsInitial = λ B → lift (λ x → ⊥-elim (lower x)) , tt , λ n x → cong lift (fun-ext λ x₁ → ⊥-elim (lower x₁))

⊤-IsSeparator : IsSeparator (Lift o ⊤)
⊤-IsSeparator {A} {B} {f₁} {f₂} = λ g → cong lift (fun-ext (λ x →
  let
    z a = (g (lift (λ x → a)))

    w0 : ∀ a b → (λ z₁ → lower f₁ a) b ≡ (λ z₁ → lower f₂ a) b
    w0 a b = cong (λ x₁ → lower x₁ b) (z a)

    w1 : ∀ a → lower f₁ a ≡ lower f₂ a
    w1 a = w0 a (lift tt)
  in
  w1 x))
-- ⊤-IsSeparator = λ f x → (f (λ _ → x) (lift tt))

nondegen : Nondegenerate ⊤-IsTerminal ⊥-IsInitial
nondegen z = lower (lower (proj₁ z) (lift tt))

-- ×-canon : ∀  {A B : Set (suc ℓ)} {a×b : A × B} → a×b ≈ₒ (proj₁ a×b , proj₂ a×b)
-- ×-canon {_} {_} {_} {fst , snd} = IsEquivalence.refl ≈ₒ-equiv

×-IsProduct : ∀ A B → IsProduct A B (A × B)
×-IsProduct A B =
  lift proj₁ , lift proj₂ , λ f g → lift (λ x → lower f x , lower g x) , (refl ,
    refl) , λ n (s , t) →
      cong lift
        (cong₂ (λ f g x → lower f x , lower g x) (sym s) (sym t))

⊎-match : ∀ {m} {A B X : Set m} (a+b : A ⊎ B) (f : A → X) (g : B → X) → X
⊎-match (inj₁ x) f g = f x
⊎-match (inj₂ y) f g = g y

⊎-canon : ∀ {A B : Set o} (X : Set o) (a+b : A ⊎ B) {f : A → X} {g : B → X} {h : A ⊎ B → X} →
  -- (∀ a → f a ≡ h (inj₁ a)) →
  -- (∀ b → g b ≡ h (inj₂ b)) →
  (h a+b) ≡ ⊎-match a+b (λ a → h (inj₁ a)) (λ b → h (inj₂ b))
⊎-canon _ (inj₁ x) = refl
⊎-canon _ (inj₂ y) = refl

⊎-canon-ext : ∀ {A B : Set o} (X : Set o) {f : Lift ℓ (A → X)} {g : Lift ℓ (B → X)} {h : Lift ℓ (A ⊎ B → X)} →
  (f ≡ lift λ a → lower h (inj₁ a)) →
  (g ≡ lift λ b → lower h (inj₂ b)) →
  h ≡ lift λ x → (⊎-match x (lower f) (lower g))
⊎-canon-ext {A} {B} X {lift .(λ a → lower₃ (inj₁ a))} {lift .(λ b → lower₃ (inj₂ b))} {lift lower₃} refl refl =
  cong lift (fun-ext λ x → ⊎-canon {A} {B} X x {(λ a → lower₃ (inj₁ a))} {(λ b → lower₃ (inj₂ b))} {lower₃})

⊎-IsCoproduct : ∀ {A B} → IsCoproduct A B (A ⊎ B)
⊎-IsCoproduct {A} {B} =
  lift inj₁ , lift inj₂ , λ {X} f g → lift (λ x → ⊎-match x (lower f) (lower g)) , (refl , refl) ,
    λ n (p , q) → ⊎-canon-ext X p q

→true : Lift o ⊤ ⇒ Lift o Bool
→true = lift λ tt → lift true

→false : Lift o ⊤ ⇒ Lift o Bool
→false = lift λ tt → lift false

Agda-nondegen : Nondegenerate ⊤-IsTerminal ⊥-IsInitial
Agda-nondegen = λ z → lower (lower (proj₁ z) (lift tt)) -- lift (λ x → lower (proj₁ x (lift tt)))

-- -- Bool-IsCoseparator : IsCoseparator Bool
-- -- Bool-IsCoseparator {T} {A} {a₀} {a₁} f x =
-- --   let
-- --     z = ⊤-IsSeparator (λ x₁ x₂ → {!!}) A
-- --   in
-- --   {!!}

